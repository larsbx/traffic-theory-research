"""Exact profile witnesses and finite bounds on lane-count-only certificates."""
from fractions import Fraction
from itertools import product
from math import comb

import numpy as np
import pytest

from bml import profiles
from bml.certificates import trace_labeled
from bml.exhaustive import decode
from bml.model import TRAIN
from bml.profiles import (
    admissible_profile_count, construct_jam_profile, is_constructible_profile,
    profile_certificate_bounds, profile_certificate_upper_bound,
    profile_pair_overflow_probability, verify_jam_profile,
)


def scalar_step(rows):
    state = [list(row) for row in rows]
    side, moves = len(state), []
    for species, dx, dy in ((1, 1, 0), (2, 0, 1)):
        old = [row[:] for row in state]
        moving = [(x, y, (x + dx) % side, (y + dy) % side)
                  for y in range(side) for x in range(side)
                  if old[y][x] == species and old[(y + dy) % side][(x + dx) % side] == 0]
        for x, y, xx, yy in moving:
            state[y][x], state[yy][xx] = 0, species
        moves.append(len(moving))
    return tuple(tuple(row) for row in state), tuple(moves)


def probability_by_cars(counts, side, p):
    return sum((int(count) * (p / 2) ** n * (1 - p) ** (side * side - n)
                for n, count in enumerate(counts)), Fraction())


def test_nonuniform_profile_matches_the_shared_diagonal_convention():
    east, north = (1, 2, 3, 1), (1, 1, 1, 1)
    rows = construct_jam_profile(east, north)
    assert rows == ((1, 2, 0, 0), (1, 1, 2, 0), (1, 1, 1, 2), (2, 0, 0, 1))
    verify_jam_profile(rows, east, north)
    assert scalar_step(rows) == (rows, (0, 0))
    orbit = trace_labeled(rows)
    assert orbit.cycle_start == 0 and orbit.period == 1 and orbit.moved == ((),)


@pytest.mark.parametrize("side,expected", ((2, 1), (3, 15), (4, 386)))
def test_every_admissible_small_profile_has_the_exact_frozen_representative(side, expected):
    count = 0
    for east in product(range(1, side), repeat=side):
        for north in product(range(1, side - max(east) + 1), repeat=side):
            assert is_constructible_profile(east, north)
            rows = construct_jam_profile(east, north)
            assert tuple(sum(cell == 1 for cell in row) for row in rows) == east
            assert tuple(sum(rows[y][x] == 2 for y in range(side)) for x in range(side)) == north
            verify_jam_profile(rows, east, north)
            assert scalar_step(rows) == (rows, (0, 0))
            count += 1
    assert count == expected == admissible_profile_count(side)
    assert admissible_profile_count(5) == 16090


@pytest.mark.parametrize("side", (5, 8, 16, 31))
def test_maximum_sum_equality_and_nonuniform_numpy_profiles(side):
    a = side // 2
    east = np.array([1 + y % a for y in range(side)], dtype=np.int64)
    north = np.array([1 + x % (side - a) for x in range(side)], dtype=np.int64)
    assert int(east.max() + north.max()) == side
    rows = construct_jam_profile(east, north)
    verify_jam_profile(rows, east, north)
    assert scalar_step(rows) == (rows, (0, 0))
    assert all(type(cell) is int for row in rows for cell in row)


def test_same_profiles_do_not_make_an_arbitrary_board_jammed():
    east = north = (1, 1, 1)
    free_rows = ((2, 1, 0), (1, 0, 2), (0, 2, 1))
    assert scalar_step(free_rows)[1] == (3, 3)
    with pytest.raises(ValueError, match="empty target"):
        verify_jam_profile(free_rows, east, north)
    with pytest.raises(ValueError, match="exact requested lane"):
        verify_jam_profile(construct_jam_profile((1, 2, 3, 1), (1, 1, 1, 1)),
                           (3, 2, 1, 1), (1, 1, 1, 1))


def test_the_condition_is_sufficient_and_not_necessary_for_jam():
    rows = ((1, 1, 2), (2, 0, 1), (2, 0, 0))
    east, north = (2, 1, 0), (2, 0, 1)
    assert not is_constructible_profile(east, north)
    assert scalar_step(rows) == (rows, (0, 0))
    with pytest.raises(ValueError, match="positive lane counts"):
        construct_jam_profile(east, north)


def test_both_actual_movement_counts_are_checked(monkeypatch):
    rows = construct_jam_profile((1, 1, 1), (1, 1, 1))
    for moving_species in (1, 2):
        monkeypatch.setattr(profiles, "half_step", lambda state, species, **kwargs:
                            (state.copy(), int(species == moving_species)))
        with pytest.raises(ValueError, match="zero actual movement"):
            verify_jam_profile(rows, (1, 1, 1), (1, 1, 1))


def test_reversing_the_north_diagonal_keeps_counts_but_fails_movement():
    side = 4
    rows = tuple(tuple(1 if x == y else 2 if (y - x) % side == 1 else 0
                       for x in range(side)) for y in range(side))
    assert scalar_step(rows)[1] != (0, 0)
    with pytest.raises(ValueError, match="empty target"):
        verify_jam_profile(rows, (1,) * side, (1,) * side)


@pytest.mark.parametrize("east,north", [
    (None, (1, 1)), ((), ()), ((1,), (1, 1)), ((1, True), (1, 1)),
    ((1, 1), (1, np.bool_(True))), ((1, 1.0), (1, 1)),
    ((-1, 1), (1, 1)), ((3, 1), (1, 1)), (([1], 1), (1, 1)),
    ("11", (1, 1)),
])
def test_malformed_profile_metadata_is_rejected(east, north):
    for operation in (is_constructible_profile, construct_jam_profile):
        with pytest.raises(ValueError):
            operation(east, north)


@pytest.mark.parametrize("east,north", [
    ((0, 1), (1, 1)), ((1, 1), (1, 0)), ((2, 2, 2), (2, 2, 2)), ((1,), (1,)),
])
def test_missing_construction_hypotheses_are_rejected(east, north):
    assert not is_constructible_profile(east, north)
    with pytest.raises(ValueError, match="positive lane counts"):
        construct_jam_profile(east, north)


@pytest.mark.parametrize("rows", [None, [], [[]], [[1, 2, 0]], [[1], [1, 2]], [[True]], [[1.0]], [[3]]])
def test_bad_grid_or_dimension_metadata_is_rejected(rows):
    with pytest.raises(ValueError):
        verify_jam_profile(rows, (1, 1), (1, 1))


@pytest.mark.parametrize("side", (1, 2, 3))
def test_complete_initial_law_checks_admissibility_and_shared_pair_distribution(side):
    states = decode(np.arange(3 ** (side * side)), side, side)
    east = (states == 1).sum(axis=2)
    north = (states == 2).sum(axis=1)
    cars = np.count_nonzero(states, axis=(1, 2))
    admissible = ((east > 0).all(axis=1) & (north > 0).all(axis=1)
                  & (east.max(axis=1) + north.max(axis=1) <= side))
    failure_counts = np.bincount(cars[~admissible], minlength=side * side + 1)
    pair = east[:, 0] + north[:, 0]
    pair_counts = [np.bincount(cars[pair == value], minlength=side * side + 1)
                   for value in range(2 * side + 1)]
    for p in (Fraction(0), Fraction(1, 5), Fraction(1, 2), Fraction(2, 3), Fraction(1)):
        bound = profile_certificate_bounds(side, p)
        actual_failure = probability_by_cars(failure_counts, side, p)
        assert actual_failure <= bound.cutoff_upper_bound
        assert actual_failure <= bound.pair_upper_bound
        assert bound.best_upper_bound == min(bound.cutoff_upper_bound, bound.pair_upper_bound)
        assert profile_certificate_upper_bound(side, p) == bound.best_upper_bound
        u, trials = p / 2, 2 * side - 2

        def mass(value):
            return (Fraction(comb(trials, value)) * u ** value * (1 - u) ** (trials - value)
                    if 0 <= value <= trials else Fraction())

        for value, counts in enumerate(pair_counts):
            actual = probability_by_cars(counts, side, p)
            assert actual == (1 - p) * mass(value) + p * mass(value - 1)
        actual_overflow = sum((probability_by_cars(pair_counts[value], side, p)
                               for value in range(side + 1, 2 * side + 1)), Fraction())
        assert actual_overflow == profile_pair_overflow_probability(side, p)


def test_false_independence_at_the_shared_cell_changes_the_exact_pair_tail():
    assert profile_pair_overflow_probability(3, Fraction(1, 2)) == Fraction(7, 256)
    naive = sum(Fraction(comb(6, count) * 3 ** (6 - count), 4 ** 6) for count in range(4, 7))
    assert naive == Fraction(77, 2048)
    assert naive != profile_pair_overflow_probability(3, Fraction(1, 2))


def test_pair_bound_is_a_substantial_exact_finite_improvement():
    bounds = profile_certificate_bounds(64, Fraction(1, 2))
    assert bounds.pair_upper_bound < Fraction(1, 100000)
    assert bounds.cutoff_upper_bound > Fraction(1, 10000)
    assert bounds.best_upper_bound == bounds.pair_upper_bound
    assert bounds.zero_lane_probability == Fraction(3, 4) ** 64


def test_endpoints_singletons_and_numpy_side_are_exact():
    assert admissible_profile_count(1) == 0
    for side in (1, 2, 3, 8):
        for p in (Fraction(0), Fraction(1)):
            bounds = profile_certificate_bounds(side, p)
            assert bounds.cutoff_upper_bound == bounds.pair_upper_bound == 1
    assert profile_pair_overflow_probability(1, Fraction(1, 2)) == 0
    bounds = profile_certificate_bounds(np.int64(4), np.int64(1))
    assert type(bounds.side) is type(bounds.cutoff) is int
    assert isinstance(bounds.p, Fraction)
    assert type(admissible_profile_count(np.int64(5))) is int


@pytest.mark.parametrize("side", [True, np.bool_(True), 0, -1, 2.0, "3", None])
def test_invalid_sides_are_rejected(side):
    for operation in (admissible_profile_count,):
        with pytest.raises(ValueError):
            operation(side)
    for operation in (profile_certificate_bounds, profile_certificate_upper_bound,
                      profile_pair_overflow_probability):
        with pytest.raises(ValueError):
            operation(side, Fraction(1, 2))


@pytest.mark.parametrize("p", [True, 0.5, float("nan"), -1, Fraction(11, 10), "1/2", None])
def test_invalid_densities_are_rejected(p):
    for operation in (profile_certificate_bounds, profile_certificate_upper_bound,
                      profile_pair_overflow_probability):
        with pytest.raises(ValueError):
            operation(3, p)


def test_train_rule_is_rejected_for_every_dynamical_or_probability_claim():
    rows = construct_jam_profile((1, 1), (1, 1))
    for operation in (
        lambda: is_constructible_profile((1, 1), (1, 1), rule=TRAIN),
        lambda: construct_jam_profile((1, 1), (1, 1), rule=TRAIN),
        lambda: verify_jam_profile(rows, (1, 1), (1, 1), rule=TRAIN),
        lambda: profile_certificate_bounds(2, Fraction(1, 2), rule=TRAIN),
        lambda: profile_certificate_upper_bound(2, Fraction(1, 2), rule=TRAIN),
        lambda: profile_pair_overflow_probability(2, Fraction(1, 2), rule=TRAIN),
    ):
        with pytest.raises(ValueError, match="CLASSIC"):
            operation()
