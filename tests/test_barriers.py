"""Finite initial-law and actual-kernel controls for guarded corner barriers."""
from dataclasses import replace
from fractions import Fraction
from itertools import product

import numpy as np
import pytest

from bml import barriers
from bml.barriers import (
    BarrierPattern, combined_barrier_formation_upper_bound, guarded_barrier_board,
    guarded_barrier_formation_upper_bound, guarded_barrier_pattern,
    guarded_barrier_probability, verify_guarded_barrier,
)
from bml.capture import find_blocker_cycles
from bml.exhaustive import decode
from bml.formation import diagonal_cut_probability, diagonal_formation_upper_bound
from bml.model import CLASSIC, EAST, EMPTY, NORTH, TRAIN, half_step, step
from scripts.check_freeflow import scalar_phase


def exteriors(pattern):
    fixed = {y * pattern.width + x: c for x, y, c in pattern.initial_cells}
    free = [i for i in range(pattern.width * pattern.height) if i not in fixed]
    for values in product(range(3), repeat=len(free)):
        cells = [0] * (pattern.width * pattern.height)
        for i, c in fixed.items():
            cells[i] = c
        for i, c in zip(free, values):
            cells[i] = c
        yield tuple(tuple(cells[y * pattern.width:(y + 1) * pattern.width])
                    for y in range(pattern.height))


@pytest.mark.parametrize("w,h,t,a,b", ((1, 1, 0, 0, 0), (2, 2, 0, 1, 1),
                                      (2, 3, 1, 1, 1), (3, 3, 1, 2, 1), (3, 4, 1, 2, 2)))
def test_every_small_exterior_and_both_phase_oracles(w, h, t, a, b):
    pattern = guarded_barrier_pattern(w, h, t, east_length=a, north_length=b, x0=-1, y0=-1)
    for rows in exteriors(pattern):
        result = verify_guarded_barrier(rows, pattern)
        current = tuple(c for row in rows for c in row)
        for time in range(t):
            middle, em = scalar_phase(current, w, h, EAST)
            current, nm = scalar_phase(middle, w, h, NORTH)
            assert middle == result.east_states[time]
            assert current == result.states[time + 1]
            assert (em, nm) == result.phase_moves[time]
        assert all(current[y * w + x] == c for x, y, c in pattern.target_cells)


def test_longer_times_seams_and_arbitrary_sampled_exteriors():
    rng = np.random.default_rng(714003)
    for t in (2, 3, 5, 8):
        w, h = 2 * t + 3, 3 * t + 2
        for x0, y0 in ((0, 0), (w - 1, h - 1), (-w - 1, -h - 2)):
            pattern = guarded_barrier_pattern(w, h, t, x0=x0, y0=y0)
            for index in range(15):
                outside = (np.full((h, w), index) if index < 3
                           else rng.integers(0, 3, size=(h, w)))
                before = outside.copy()
                rows = guarded_barrier_board(pattern, exterior=outside.tolist())
                verify_guarded_barrier(rows, pattern)
                assert np.array_equal(before, outside)
                fixed = {(x, y) for x, y, _ in pattern.initial_cells}
                assert all(rows[y][x] == outside[y, x] for y in range(h) for x in range(w)
                           if (x, y) not in fixed)


def test_target_walls_stop_every_interior_direct_path():
    pattern = guarded_barrier_pattern(4, 4, 1, x0=3, y0=3)
    # Exhaust the four cells strictly inside the two walls. Exterior values
    # cannot affect the direct path because the wall arrows point to the hole.
    for values in product(range(3), repeat=4):
        board = np.full((4, 4), NORTH, dtype=np.int8)
        for (dx, dy), c in zip(product(range(2), repeat=2), values):
            board[(3 + dy) % 4, (3 + dx) % 4] = c
        for x, y, c in pattern.target_cells:
            board[y, x] = c
        x, y = 3, 3
        for _ in range(5):
            c = board[y % 4, x % 4]
            if c == EMPTY:
                break
            x, y = x + int(c == EAST), y + int(c == NORTH)
        else:
            pytest.fail("a direct path crossed a prescribed barrier")


def test_initial_support_weight_is_exact_and_linear_in_time():
    p = Fraction(2, 5)
    for t in range(8):
        pattern = guarded_barrier_pattern(7 * t + 2, 7 * t + 2, t)
        cells = pattern.initial_cells
        assert len({(x, y) for x, y, _ in cells}) == len(cells) == 6 * t + 1
        assert sum(c == EMPTY for _, _, c in cells) == 1
        weight = Fraction(1)
        for _, _, c in cells:
            weight *= 1 - p if c == EMPTY else p / 2
        assert weight == guarded_barrier_probability(t, p)
    pattern = guarded_barrier_pattern(9, 9, 1)
    required = tuple(c for _, _, c in pattern.initial_cells)
    accepted = sum(values == required for values in product(range(3), repeat=len(required)))
    assert accepted == 1
    assert Fraction(accepted, 3 ** len(required)) == guarded_barrier_probability(1, Fraction(2, 3))
    assert guarded_barrier_probability(10, Fraction(1, 2)) > diagonal_cut_probability(10, Fraction(1, 2))


def projected_box(side, x, y, radius):
    return {((x + dx) % side, (y + dy) % side)
            for dx in range(-radius, radius + 1) for dy in range(-radius, radius + 1)}


@pytest.mark.parametrize("side,t", ((2, 0), (7, 0), (9, 1), (19, 1), (16, 2), (34, 2), (48, 3)))
def test_every_admissible_probe_is_fresh_for_every_possible_history(side, t):
    stride = 4 * t + 1
    trials = max(0, (side - 3 * t - 1) // stride)
    history = set()
    for j in range((trials - 1) * stride + 1):
        for x in range(j + 1):
            history |= projected_box(side, side - 1 + x, 1 + j - x, t)
        if j % stride:
            continue
        for x in range(j + 1):
            for first in (EAST, NORTH):
                pattern = guarded_barrier_pattern(side, side, t,
                    x0=side - 1 + x + (first == EAST), y0=1 + j - x + (first == NORTH))
                support = {(a, b) for a, b, _ in pattern.initial_cells}
                assert len(support) == 6 * t + 1 and not support & history
                heights = [a + b for a, b, _ in pattern.lifted_initial_cells]
                assert min(heights) == side + j + 2 * t + 1
                assert max(heights) == side + j + 5 * t + 1


def test_next_probe_beyond_cutoff_can_reuse_an_exposed_initial_cell():
    history = projected_box(9, 0, 0, 1)
    second = guarded_barrier_pattern(9, 9, 1, x0=6, y0=0)
    support = {(x, y): c for x, y, c in second.initial_cells}
    assert (8, 0) in history and support[(8, 0)] == NORTH
    # A transcript exposing this cell as empty has conditional pattern mass
    # zero, although the unconditioned initial product weight is positive.
    assert guarded_barrier_probability(1, Fraction(1, 2)) > 0


def test_empty_guards_can_be_filled_before_the_hole_reaches_the_corner():
    pattern = guarded_barrier_pattern(5, 7, 2)
    board = np.array(guarded_barrier_board(pattern, exterior=np.full((7, 5), EAST).tolist()))
    x, y = pattern.corner
    for j in range(1, 3):
        board[(y + j) % 7, (x - 1) % 5] = EMPTY
    with pytest.raises(ValueError, match="initial board"):
        verify_guarded_barrier(board.tolist(), pattern)
    evolved, _ = step(board)
    evolved, _ = step(evolved)
    assert evolved[y, x] != EMPTY


def test_verifier_rejects_wrong_phase_counts_and_wrong_phase_order(monkeypatch):
    pattern = guarded_barrier_pattern(3, 4, 1)
    rows = guarded_barrier_board(pattern)
    real = barriers.half_step
    def wrong_count(board, species, rule=CLASSIC):
        after, moves = real(board, species, rule)
        return after, moves + 1
    monkeypatch.setattr(barriers, "half_step", wrong_count)
    with pytest.raises(ValueError, match="production phase"):
        verify_guarded_barrier(rows, pattern)
    monkeypatch.setattr(barriers, "half_step", lambda board, species, rule=CLASSIC:
                        real(board, NORTH if species == EAST else EAST, rule))
    with pytest.raises(ValueError, match="production phase"):
        verify_guarded_barrier(rows, pattern)


def test_zero_time_bound_on_every_two_by_two_initial_board():
    boards = decode(np.arange(3 ** 4), 2, 2)
    counts = [0] * 5
    for board in boards:
        if any(c.mixed for c in find_blocker_cycles(board.tolist())):
            counts[int(np.count_nonzero(board))] += 1
    for p in (Fraction(0), Fraction(1, 5), Fraction(1, 2), Fraction(2, 3), Fraction(1)):
        actual = sum(n * (p / 2) ** k * (1 - p) ** (4 - k) for k, n in enumerate(counts))
        assert actual <= guarded_barrier_formation_upper_bound(2, p) == p ** 2


def test_bounds_endpoints_cutoff_and_combination():
    for t in range(5):
        for p in (Fraction(0), Fraction(1, 5), Fraction(1, 2), Fraction(6, 7), Fraction(1)):
            assert guarded_barrier_formation_upper_bound(1, p, t) == 0
            for side in (2, 7 * t + 1, 7 * t + 2, 20):
                result = guarded_barrier_formation_upper_bound(side, p, t)
                assert 0 <= result <= 1
                assert combined_barrier_formation_upper_bound(side, p, t) == min(
                    result, diagonal_formation_upper_bound(side, p, t))
    assert guarded_barrier_formation_upper_bound(8, Fraction(1, 5), 1) == Fraction(4, 5)
    assert guarded_barrier_formation_upper_bound(9, Fraction(1, 5), 1) == (
        Fraction(9, 10) * (1 - Fraction(4, 5) * Fraction(1, 10) ** 6))


@pytest.mark.parametrize("bad", (-1, True, 1.5, "1"))
def test_rejects_invalid_horizons(bad):
    with pytest.raises(ValueError):
        guarded_barrier_probability(bad, Fraction(1, 2))
    with pytest.raises(ValueError):
        guarded_barrier_pattern(5, 5, bad)


@pytest.mark.parametrize("bad", (-1, 2, True, 0.5, "1/2"))
def test_rejects_nonexact_or_out_of_range_densities(bad):
    with pytest.raises(ValueError):
        guarded_barrier_formation_upper_bound(9, bad, 1)


def test_invalid_footprints_boards_and_train_are_rejected():
    for args in ((2, 4, 1), (3, 3, 1), (1, 4, 1), (0, 1, 0)):
        with pytest.raises(ValueError):
            guarded_barrier_pattern(*args)
    pattern = guarded_barrier_pattern(3, 4, 1)
    with pytest.raises(ValueError):
        replace(pattern, x0=True)
    with pytest.raises(ValueError):
        guarded_barrier_board(pattern, exterior=((0,),))
    with pytest.raises(ValueError):
        verify_guarded_barrier(((0,),), pattern)
    with pytest.raises(ValueError):
        verify_guarded_barrier(((0,),), object())
    for action in (lambda: guarded_barrier_probability(1, Fraction(1, 2), rule=TRAIN),
                   lambda: guarded_barrier_formation_upper_bound(9, Fraction(1, 2), 1, rule=TRAIN),
                   lambda: guarded_barrier_board(pattern, rule=TRAIN),
                   lambda: verify_guarded_barrier(guarded_barrier_board(pattern), pattern, rule=TRAIN)):
        with pytest.raises(ValueError, match="CLASSIC"):
            action()


def test_all_moving_prefix_can_end_in_a_new_mixed_jam():
    for side in range(4, 13):
        t = (side - 2) // 2
        board = np.zeros((side, side), dtype=np.int8)
        for i in range(side):
            assert not board[i, (i - t) % side]
            board[i, (i - t) % side] = EAST
            assert not board[(i - t) % side, (i + 1) % side]
            board[(i - t) % side, (i + 1) % side] = NORTH
        for _ in range(t):
            assert not any(c.mixed for c in find_blocker_cycles(board.tolist()))
            board, moves = step(board)
            assert moves == 2 * side
        assert any(c.mixed for c in find_blocker_cycles(board.tolist()))
        following, moves = step(board)
        assert moves == 0 and np.array_equal(board, following)
