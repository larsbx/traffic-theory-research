"""Finite controls for locality, initial cuts, and torus wraparound."""
from fractions import Fraction

import numpy as np
import pytest

from bml.capture import find_blocker_cycles
from bml.exhaustive import decode
from bml.formation import diagonal_cut_probability, diagonal_formation_upper_bound
from bml.model import EAST, EMPTY, NORTH, TRAIN, step


def projected_box(side, x, y, radius):
    return {((x + dx) % side, (y + dy) % side)
            for dx in range(-radius, radius + 1) for dy in range(-radius, radius + 1)}


def cut_origins(side, x, y, rounds, first):
    # Count from the actual possible path endpoints after the first known turn.
    distance_after_first = 3 * rounds
    x, y = x + (first == EAST), y + (first == NORTH)
    endpoints = {((x + i) % side, (y + distance_after_first - i) % side)
                 for i in range(distance_after_first + 1)}
    east = {((a - d) % side, b) for a, b in endpoints for d in range(rounds + 1)}
    north = {(a, (b - d) % side) for a, b in endpoints for d in range(rounds + 1)}
    return endpoints, east, north


def test_every_one_round_local_input_on_a_wrapped_torus():
    # Embed all 3^9 possible stencils into two different exteriors of a 5x5.
    patches = decode(np.arange(3 ** 9), 3, 3)
    board = np.zeros((len(patches), 5, 5), dtype=np.int8)
    other = np.full_like(board, NORTH)
    for dy in range(-1, 2):
        for dx in range(-1, 2):
            board[:, dy, dx] = other[:, dy, dx] = patches[:, dy + 1, dx + 1]
    evolved, _ = step(board)
    changed_exterior, _ = step(other)
    output = evolved[:, 0, 0]
    assert np.array_equal(output, changed_exterior[:, 0, 0])
    assert np.any(evolved != changed_exterior)
    assert np.all((output != EAST) | (board[:, 0, 0] == EAST) | (board[:, 0, -1] == EAST))
    assert np.all((output != NORTH) | (board[:, 0, 0] == NORTH) | (board[:, -1, 0] == NORTH))


def test_next_east_then_north_corner_can_influence_the_current_site():
    # The (+1,+1) corner lies two height layers ahead. Dropping it would make
    # the computation of the exposed history unsound even at T=1.
    board = np.zeros((5, 5), dtype=np.int8)
    board[0, 0], board[1, 0] = NORTH, EAST
    modified = board.copy()
    modified[1, 1] = NORTH
    evolved, _ = step(board)
    changed, _ = step(modified)
    assert (evolved[0, 0], changed[0, 0]) == (EMPTY, NORTH)


def test_one_round_cut_full_initial_product_count_and_arbitrary_exteriors():
    for first in (EAST, NORTH):
        # Coordinates deliberately cross both torus seams.
        endpoints, east, north = cut_origins(7, 6, 6, 1, first)
        sites = sorted(east | north)
        values = decode(np.arange(3 ** len(sites)), 3, 3).reshape(-1, len(sites))
        probability = diagonal_cut_probability(1, Fraction(2, 3))
        good = np.ones(len(values), dtype=bool)
        for index, site in enumerate(sites):
            if site in east:
                good &= values[:, index] != EAST
            if site in north:
                good &= values[:, index] != NORTH
        assert Fraction(int(good.sum()), len(values)) == probability == Fraction(4, 19683)
        # Check every admissible cut assignment under three different exterior
        # completions, including maximal supplies of either species.
        for outside in (EMPTY, EAST, NORTH):
            boards = np.full((int(good.sum()), 7, 7), outside, dtype=np.int8)
            for index, (a, b) in enumerate(sites):
                boards[:, b, a] = values[good, index]
            evolved, _ = step(boards)
            assert all((evolved[:, b, a] == EMPTY).all() for a, b in endpoints)


@pytest.mark.parametrize("side,rounds", ((2, 0), (7, 1), (11, 1), (12, 2), (19, 2), (25, 3), (34, 4)))
def test_every_checkpoint_cut_is_disjoint_from_all_preceding_path_stencils(side, rounds):
    p = Fraction(2, 5)
    stride = 3 * rounds + 1
    # Build the union of all histories, which contains the actually exposed
    # sites regardless of how the path adapted its directions to earlier data.
    previously_possible = set()
    for j in range(side - 2 * rounds):
        for x in range(j + 1):
            previously_possible |= projected_box(side, side - 1 + x, 1 + j - x, rounds)
        if j % stride or j + stride + 2 * rounds >= side:
            continue
        for x in range(j + 1):
            for first in (EAST, NORTH):
                _, east, north = cut_origins(side, side - 1 + x, 1 + j - x, rounds, first)
                assert not (east | north) & previously_possible
                exact_weight = (1 - p) ** len(east & north) * (1 - p / 2) ** len(east ^ north)
                assert exact_weight == diagonal_cut_probability(rounds, p)


def test_a_probe_beyond_the_first_wrap_can_reuse_an_exposed_site():
    # Two stride-four probes on side seven would claim an invalid second trial.
    exposed_at_root = projected_box(7, 0, 0, 1)
    _, east, north = cut_origins(7, 4, 0, 1, EAST)
    assert (1, 0) in exposed_at_root & (east | north)


def test_initial_inequality_on_every_small_square_state():
    for side in (2, 3):
        states = decode(np.arange(3 ** (side * side)), side, side)
        cars = np.count_nonzero(states, axis=(1, 2))
        targets = [i for i, board in enumerate(states)
                   if any(cycle.mixed for cycle in find_blocker_cycles(board.tolist()))]
        counts = np.bincount(cars[targets], minlength=side * side + 1)
        for p in (Fraction(0), Fraction(1, 5), Fraction(1, 2), Fraction(2, 3), Fraction(1)):
            actual = sum(int(n) * (p / 2) ** k * (1 - p) ** (side * side - k)
                         for k, n in enumerate(counts))
            bound = diagonal_formation_upper_bound(side, p)
            assert actual <= bound == min(Fraction(1), side * p ** side / 2)


def test_positive_time_bound_and_rule_guard():
    # An exact nontrivial bound beyond T=0 and a torus too short for any probe.
    assert diagonal_formation_upper_bound(400, Fraction(1, 5), 1) < Fraction(1, 1000)
    assert diagonal_formation_upper_bound(6, Fraction(1, 5), 1) == Fraction(3, 5)
    assert diagonal_formation_upper_bound(1, 1, 10) == 0
    with pytest.raises(ValueError):
        diagonal_formation_upper_bound(8, Fraction(1, 2), 1, rule=TRAIN)


def test_unread_cuts_through_multiple_actual_rounds():
    rng = np.random.default_rng(68317)
    side, rounds = 19, 3
    for first in (EAST, NORTH):
        endpoints, east, north = cut_origins(side, side - 2, side - 2, rounds, first)
        initial = rng.integers(0, 3, size=(160, side, side), dtype=np.int8)
        for x, y in east | north:
            allowed = [c for c in (EMPTY, EAST, NORTH)
                       if (c != EAST or (x, y) not in east) and (c != NORTH or (x, y) not in north)]
            initial[:, y, x] = rng.choice(allowed, size=len(initial))
        state = initial
        for _ in range(rounds):
            state, _ = step(state)
        assert all((state[:, y, x] == EMPTY).all() for x, y in endpoints)
