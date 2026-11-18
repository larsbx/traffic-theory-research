"""Independent controls for initial-law formation bounds and dynamic capture."""
from fractions import Fraction
from itertools import product

import numpy as np
import pytest

from bml.capture import find_blocker_cycles
from bml.exhaustive import classify_all, decode
from bml.formation import (
    geometric_formation_upper_bound, mixed_formation_upper_bound,
    staircase_capture_lower_bound, staircase_one_round_probability,
    staircase_preimage, staircase_present, staircase_transfer_matrix,
)
from bml.model import TRAIN, step


def scalar_step(rows):
    """Independent source/destination loop, including the phase snapshot rule."""
    h, w = len(rows), len(rows[0])
    state = [list(row) for row in rows]
    for species, dx, dy in ((1, 1, 0), (2, 0, 1)):
        old = [row[:] for row in state]
        for y in range(h):
            for x in range(w):
                xx, yy = (x + dx) % w, (y + dy) % h
                if old[y][x] == species and old[yy][xx] == 0:
                    state[y][x], state[yy][xx] = 0, species
    return state


def test_local_conditional_integration_exhaustive():
    # A,B,C are integrated independently. D,Q are held fixed. No evolved
    # independence is used. This checks every one of 3^5 local assignments.
    for p in (Fraction(0), Fraction(1, 5), Fraction(1, 2), Fraction(2, 3), Fraction(1)):
        u, v = p / 2, 1 - p
        weights = (v, u, u)
        a, b = u * u * (1 + v), u * v * v
        matrix = staircase_transfer_matrix(p)
        for d, q in product(range(3), repeat=2):
            actual = Fraction()
            for aa, bb, cc in product(range(3), repeat=3):
                good_e = (bb == 1 and cc != 0) or (bb == 0 and aa == 1)
                good_n = cc == 2 or (d == 2 and ((cc == 0 and bb != 1) or (cc == 1 and q == 0)))
                if good_e and good_n:
                    actual += weights[aa] * weights[bb] * weights[cc]
            expected = a + (b + (a if q == 0 else 0) if d == 2 else 0)
            assert actual == expected
            assert matrix[d][q] == actual * weights[q]


@pytest.mark.parametrize("side", (4, 5, 7, 12))
def test_local_preimage_agrees_with_two_independent_kernels(side):
    rng = np.random.default_rng(194927 + side)
    for rows in rng.integers(0, 3, size=(120, side, side), dtype=np.int8):
        actual, _ = step(rows)
        independent = scalar_step(rows.tolist())
        assert np.array_equal(actual, independent)
        for offset in range(side):
            assert staircase_preimage(rows.tolist(), offset) == staircase_present(independent, offset)


def test_certified_predecessors_ignore_arbitrary_exterior_and_form_actual_cycles():
    # Three disjoint local cases per row, with a fourth case testing the
    # adjacent-D coupling in the exact transfer calculation.
    rng = np.random.default_rng(165498)
    for side in (4, 5, 8):
        for case in (0, 1, 2):
            for offset in range(side):
                rows = rng.integers(0, 3, size=(side, side), dtype=np.int8)
                for y in range(side):
                    x = (y + offset) % side
                    if case == 0:
                        rows[y, x], rows[y, (x + 1) % side] = 1, 2
                    else:
                        rows[y, (x - 1) % side], rows[y, x] = 1, 0
                        rows[y, (x + 1) % side] = 2 if case == 1 else 0
                        if case == 2:
                            rows[(y - 1) % side, (x + 1) % side] = 2
                assert staircase_preimage(rows.tolist(), offset)
                actual = scalar_step(rows.tolist())
                assert staircase_present(actual, offset)
                assert any(cycle.mixed for cycle in find_blocker_cycles(actual))
        # C's old E moves away into Q; N at D replaces it. That extra case
        # requires D_(y+1)=0 and cannot be multiplied independently by row.
        rows = np.zeros((side, side), dtype=np.int8)
        for y in range(side):
            rows[y, y], rows[y, (y + 1) % side] = 1, 2
        rows[0, 1], rows[side - 1, 1] = 1, 2
        assert staircase_preimage(rows.tolist())
        assert staircase_present(scalar_step(rows.tolist()))


@pytest.mark.parametrize("p", (Fraction(0), Fraction(1, 5), Fraction(1, 2), Fraction(2, 3), Fraction(1)))
def test_trace_recurrence_and_strict_failure_of_evolved_independence(p):
    matrix = np.array(staircase_transfer_matrix(p), dtype=object)
    for side in (4, 5, 8, 16):
        h = staircase_one_round_probability(side, p)
        assert h == sum(np.linalg.matrix_power(matrix, side).diagonal())
        u, v = p / 2, 1 - p
        assert 0 <= (u * u * (1 + v + v * v)) ** side <= h <= 1
        if 0 < p < 1:
            assert h > u ** (2 * side)
        assert staircase_capture_lower_bound(side, p) == 1 - (1 - h) ** (side // 4)
    assert staircase_one_round_probability(4, Fraction(1, 2)) == Fraction(6647, 33554432)
    assert staircase_one_round_probability(4, Fraction(2, 3)) == Fraction(39889, 43046721)


def test_early_mixed_bounds_against_complete_small_torus_maps():
    for side in (2, 3):
        graph = classify_all(side, side)
        states = decode(np.arange(3 ** (side * side)), side, side)
        targets = np.array([any(c.mixed for c in find_blocker_cycles(s.tolist())) for s in states])
        n = np.count_nonzero(states, axis=(1, 2))
        for rounds in (0, 1, 2):
            current = np.arange(len(states))
            for _ in range(rounds):
                current = graph.f[current]
            reached = targets[current]
            by_cars = np.bincount(n[reached], minlength=side * side + 1)
            for p in (Fraction(1, 10), Fraction(1, 5), Fraction(1, 2), Fraction(2, 3), Fraction(1)):
                actual = sum(int(count) * (p / 2) ** k * (1 - p) ** (side * side - k)
                             for k, count in enumerate(by_cars))
                sharp = mixed_formation_upper_bound(side, p, rounds)
                coarse = geometric_formation_upper_bound(side, p, rounds)
                assert actual <= sharp <= coarse <= 1


@pytest.mark.parametrize("bad", (True, -1, 1.5, "4"))
def test_invalid_sides_and_rounds_rejected(bad):
    with pytest.raises(ValueError):
        mixed_formation_upper_bound(bad, Fraction(1, 2))
    with pytest.raises(ValueError):
        mixed_formation_upper_bound(4, Fraction(1, 2), bad)
    with pytest.raises(ValueError):
        staircase_one_round_probability(bad, Fraction(1, 2))


@pytest.mark.parametrize("bad", (True, -1, 1.01, 0.5, "0.5", Fraction(3, 2)))
def test_nonexact_or_invalid_densities_rejected(bad):
    with pytest.raises(ValueError):
        mixed_formation_upper_bound(4, bad)
    with pytest.raises(ValueError):
        staircase_one_round_probability(4, bad)


def test_rule_and_geometric_domain_guards():
    with pytest.raises(ValueError):
        mixed_formation_upper_bound(4, Fraction(1, 2), rule=TRAIN)
    with pytest.raises(ValueError):
        staircase_capture_lower_bound(4, Fraction(1, 2), rule=TRAIN)
    with pytest.raises(ValueError):
        staircase_one_round_probability(3, Fraction(1, 2))
    with pytest.raises(ValueError):
        staircase_preimage([[0] * 4] * 3)
    with pytest.raises(ValueError):
        staircase_present([[0] * 4] * 4, 4)
    assert mixed_formation_upper_bound(1, Fraction(1)) == 0
    assert geometric_formation_upper_bound(4, Fraction(0), 100) == 0
