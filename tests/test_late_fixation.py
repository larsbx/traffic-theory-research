"""Exact CLASSIC controls for new formation bounds and original-tag waits."""
from collections import Counter
from fractions import Fraction
from itertools import accumulate

import numpy as np
import pytest

from bml.barriers import (
    coordinate_barrier_formation_upper_bound, coordinate_barrier_pattern,
    guarded_barrier_board, guarded_barrier_formation_upper_bound, verify_guarded_barrier,
)
from bml.capture import find_blocker_cycles
from bml.certificates import _ahead, trace_labeled
from bml.exhaustive import JAM, classify_all, decode
from bml.fixation import verify_fixation
from bml.guarded_queue import construct_guarded_queue
from bml.model import EAST, EMPTY, NORTH, step
from bml.probability import has_full_lane


@pytest.mark.parametrize("side,rounds", ((5, 1), (8, 1), (9, 1), (14, 2), (29, 2), (41, 3)))
def test_coordinate_probes_clear_every_admissible_revealed_envelope(side, rounds):
    stride = 2 * rounds + 2
    trials = (side - rounds) // stride
    root_x, root_y = side - 1, -1
    for j in range(0, trials * stride, stride):
        for east_steps in range(j + 1):
            x, y = root_x + east_steps, root_y + j - east_steps
            revealed = {(a % side, b % side)
                        for a in range(root_x - rounds, x + rounds + 1)
                        for b in range(root_y - rounds, y + rounds + 1)}
            for direction in (EAST, NORTH):
                pattern = coordinate_barrier_pattern(side, rounds, x, y, direction)
                assert pattern.corner == (x + rounds + 1, y + rounds + 1)
                footprint = {(a, b) for a, b, _ in pattern.initial_cells}
                assert len(footprint) == 4 * rounds + 2
                assert footprint.isdisjoint(revealed)


def test_next_coordinate_probe_can_reuse_a_revealed_cell():
    # A pure N column can reach checkpoint (0,4), but the candidate guard
    # wraps into the first inspected box, which saw a hole at (1,7).
    side = 8
    pattern = coordinate_barrier_pattern(side, 1, 0, 4, NORTH)
    assert (1, 7, NORTH) in pattern.initial_cells
    board = np.zeros((side, side), dtype=np.int8)
    board[:, 0] = NORTH
    evolved, _ = step(board)
    assert tuple(evolved[:5, 0]) == (NORTH,) * 5
    assert board[7, 1] == EMPTY


@pytest.mark.parametrize("rounds", (1, 2, 5))
def test_coordinate_probe_stops_the_actual_blocker_path(rounds):
    rng = np.random.default_rng(1570 + rounds)
    side = 3 * rounds + 2
    for direction in (EAST, NORTH):
        pattern = coordinate_barrier_pattern(side, rounds, side - 1, side - 2, direction)
        for probabilities in ((0.9, 0.05, 0.05), (0.1, 0.45, 0.45), (0, 1, 0), (0, 0, 1)):
            outside = rng.choice(3, size=(side, side), p=probabilities)
            board = guarded_barrier_board(pattern, exterior=outside.tolist())
            result = verify_guarded_barrier(board, pattern)
            evolved = result.states[-1]
            start = (pattern.y0 % side) * side + pattern.x0 % side
            assert occupied_depth(evolved, start, side) < 2 * rounds + 1


def test_coordinate_bound_strictly_improves_the_old_guarded_bound():
    p = Fraction(1, 5)
    assert coordinate_barrier_formation_upper_bound(5, p, 1) == (
        Fraction(1, 2) * (1 - (1 - p) * (p / 2) ** 5))
    for side in (1, 2, 5, 8, 9, 173):
        for rounds in (0, 1, 2, 4):
            for density in (Fraction(0), p, Fraction(1, 2), Fraction(9, 10), Fraction(1)):
                assert coordinate_barrier_formation_upper_bound(side, density, rounds) <= (
                    guarded_barrier_formation_upper_bound(side, density, rounds))


def occupied_depth(cells, root, side):
    """Occupied edges before the first hole, capped at the area for cycles."""
    seen = set()
    while cells[root]:
        if root in seen:
            return side ** 2
        seen.add(root)
        root = _ahead(root, cells[root], side, side)
    return len(seen) - 1


def orbit_index(orbit, t):
    if t < len(orbit.states):
        return t
    return orbit.cycle_start + (t - orbit.cycle_start) % orbit.period


def tag_moves_before(orbit, prefix, t):
    if t < len(prefix):
        return prefix[t]
    loops, leftover = divmod(t - orbit.cycle_start, orbit.period)
    recurrent_moves = prefix[-1] - prefix[orbit.cycle_start]
    return loops * recurrent_moves + prefix[orbit.cycle_start + leftover]


@pytest.mark.parametrize("side", (2, 3))
def test_complete_small_tori_wait_and_lap_reductions(side):
    area, cutoff = side ** 2, 1
    powers = tuple(3 ** i for i in range(area))
    production = classify_all(side, side)
    domain = decode(np.arange(3 ** area), side, side).tolist()
    mixed = [any(c.mixed for c in find_blocker_cycles(rows)) for rows in domain]
    flat_boards = [tuple(c for row in rows for c in row) for rows in domain]
    depths = [tuple(occupied_depth(cells, root, side) for root in range(area))
              for cells in flat_boards]
    early, late, tagged_late, eligible = Counter(), Counter(), Counter(), Counter()
    survived, failed = [Counter() for _ in range(3)], [Counter() for _ in range(3)]
    edges = 0
    for code, rows in enumerate(domain):
        orbit = trace_labeled(rows)
        edges += len(orbit.moved)
        colors = {-1: 0, **dict(orbit.species)}
        snapshots = [sum(colors[label] * place for label, place in zip(state, powers))
                     for state in orbit.states]
        assert all(production.f[index] == snapshots[orbit_index(orbit, t + 1)]
                   for t, index in enumerate(snapshots))
        tau = next((t for t, index in enumerate(snapshots) if mixed[index]), None)
        n = len(orbit.species)
        ringless = not has_full_lane(rows)
        assert (tau is not None) == (ringless and production.cls[code] == JAM)
        if tau is not None:
            (early if tau <= cutoff else late)[n] += 1
        if rows[0][0] == EMPTY:
            continue

        moves = tuple(0 in current for current in orbit.moved)
        prefix = tuple(accumulate(moves, initial=0))
        stops = prefix[-1] == prefix[orbit.cycle_start]
        if ringless:
            assert stops == (tau is not None)
        wait = 2 ** n - 1
        window = side * wait
        for t, state in enumerate(orbit.states):
            root = state.index(0)
            for d in range(1, min(3, n) + 1):
                length = 2 ** d - 1
                if tag_moves_before(orbit, prefix, t + length) == prefix[t]:
                    assert any(depths[snapshots[orbit_index(orbit, u)]][root] >= d
                               for u in range(t, t + length + 1))
            stayed = tag_moves_before(orbit, prefix, t + wait) == prefix[t]
            assert stayed == (stops and prefix[t] == prefix[-1])
            if stayed and ringless:
                assert tau is not None and tau <= t + wait
            if ringless:
                lap_failed = tag_moves_before(orbit, prefix, t + window) - prefix[t] < side
                if tau is not None and tau <= t:
                    assert lap_failed
                if lap_failed:
                    assert tau is not None and tau <= t + window

        if not ringless or (tau is not None and tau <= cutoff):
            continue
        eligible[n] += 1
        tagged_late[n] += int(stops)
        from_cutoff = tag_moves_before(orbit, prefix, cutoff)
        for j in range(3):
            previous = tag_moves_before(orbit, prefix, cutoff + j * window)
            after = tag_moves_before(orbit, prefix, cutoff + (j + 1) * window)
            if previous - from_cutoff >= j * side:
                survived[j][n] += 1
                if after - from_cutoff < (j + 1) * side:
                    failed[j][n] += 1
    assert edges == {2: 177, 3: 162141}[side]
    if side == 3:
        assert late == {6: 279, 7: 1503, 8: 630}
        assert failed[1] == {6: 17, 7: 87}
    for n in range(area + 1):
        assert area * tagged_late[n] == n * late[n]
        assert sum(c[n] for c in failed) == tagged_late[n]
        assert survived[0][n] == eligible[n]
        for j in range(2):
            assert survived[j + 1][n] == survived[j][n] - failed[j][n]
    expected_risk = {Fraction(1, 5): Fraction(303, 342269),
                     Fraction(1, 2): Fraction(607, 9363),
                     Fraction(9, 10): Fraction(1982452077, 3254192201)}
    for p, risk in expected_risk.items():
        weights = [(p / 2) ** n * (1 - p) ** (area - n) for n in range(area + 1)]

        def mass(hist):
            return sum(weight * hist[n] for n, weight in enumerate(weights))

        assert mass(early) <= coordinate_barrier_formation_upper_bound(side, p, cutoff)
        product = Fraction(1)
        for at_risk, lost in zip(survived, failed):
            if mass(at_risk):
                product *= 1 - mass(lost) / mass(at_risk)
        assert mass(tagged_late) / p == (mass(eligible) / p) * (1 - product)
        if side == 3:
            assert mass(tagged_late) / mass(eligible) == risk


def test_tag_completes_a_lap_after_cutoff_before_its_first_mixed_cycle():
    board = ((2, 1, 2), (1, 1, 2), (0, 0, 0))
    orbit = trace_labeled(board)
    assert verify_fixation(board, orbit).gridlock
    assert not has_full_lane(board)
    assert orbit.cycle_start == 6
    assert [t for t, edge in enumerate(orbit.moved) if 0 in edge] == [2, 3, 4]
    assert orbit.states[5][0] == 0
    assert not any(c.mixed for t in range(6) for c in find_blocker_cycles(orbit.rows(t)))
    assert any(c.mixed for c in find_blocker_cycles(orbit.rows(6)))


def test_protected_queue_waits_but_the_original_tag_keeps_moving():
    rounds = 8
    board = construct_guarded_queue(rounds + 3, 2, rounds)
    orbit = trace_labeled(board)
    check = verify_fixation(board, orbit)
    assert min(t for t, moved in enumerate(orbit.moved) if 0 in moved) == rounds
    assert 0 not in check.stopped_labels and not check.full_lane


@pytest.mark.parametrize("side,bands,rounds", ((12, 2, 2), (20, 2, 5), (30, 3, 10), (36, 6, 7)))
def test_balanced_fixed_density_family_moves_through_cutoff_then_forms_a_cycle(side, bands, rounds):
    east = {2 * j for j in range(bands)}
    north_start = 2 * (bands - 1) + 2 * rounds + 1
    north = {north_start + 2 * j for j in range(bands)}
    board = tuple(tuple(EAST if (x - y) % side in east else
                        NORTH if (x - y) % side in north else EMPTY
                        for x in range(side)) for y in range(side))
    assert not has_full_lane(board)
    orbit = trace_labeled(board)
    assert verify_fixation(board, orbit).gridlock
    assert len(orbit.species) == 2 * bands * side
    assert all(len(orbit.moved[t]) == len(orbit.species) for t in range(rounds))
    assert next(t for t in range(len(orbit.states))
                if any(c.mixed for c in find_blocker_cycles(orbit.rows(t)))) == rounds
    # Compare with a board of the same profile whose two species are separated
    # by co-moving height classes.
    free_north = {2 * (bands + j) for j in range(bands)}
    free_board = tuple(tuple(EAST if (x + y) % side in east else
                             NORTH if (x + y) % side in free_north else EMPTY
                             for x in range(side)) for y in range(side))
    free_orbit = trace_labeled(free_board)
    assert verify_fixation(free_board, free_orbit).free
    assert free_orbit.cycle_start == 0
    for w in (board, free_board):
        assert all(row.count(EAST) == bands for row in w)
        assert all(sum(row[x] == NORTH for row in w) == bands for x in range(side))
