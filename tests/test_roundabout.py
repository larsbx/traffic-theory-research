"""Roundabout BML (TDD spec for bml.roundabout; docs/research/2026-11-24-roundabout-bml.md).

Finite checks of Lemma RB-0, Theorem RB-G, Lemma RB-R and Theorem RB-F. The exhaustive tests
decide freeness and gridlock from the dynamics alone, never from the formulas under test.
"""
from itertools import product
from math import gcd

import numpy as np
import pytest
from hypothesis import given, settings, strategies as st

from bml.model import EMPTY, EAST, NORTH
from bml.roundabout import (
    State, all_states, classes, counts, empty, free_feasible, free_levels, free_with,
    gridlock_with, is_fixed, is_free, is_free_static, max_free, min_gridlock, period, step, transpose,
)

PRIORITIES = (EAST, NORTH)
EXHAUSTIVE = [(h, w) for h in range(1, 6) for w in range(1, 6) if h * w <= 5]
BOARDS = [(h, w) for h in range(1, 7) for w in range(1, 7)]


@st.composite
def states(draw, max_side=6, density=st.floats(0, 1)):
    h, w = draw(st.integers(1, max_side)), draw(st.integers(1, max_side))
    rng = np.random.default_rng(draw(st.integers(0, 2**32 - 1)))
    p = draw(density)
    return State(rng.random((h, w)) < p, rng.choice([EMPTY, EAST, NORTH], (h, w), p=[1 - p, p / 2, p / 2]).astype(np.int8),
                 rng.random((h, w)) < p)


def place(h, w, **cars) -> State:
    s = empty(h, w)
    for name, cells in cars.items():
        for y, x in cells:
            if name in "ab":
                getattr(s, name)[y, x] = True
            else:
                s.c[y, x] = {"e": EAST, "n": NORTH}[name]
    return s


def same(s: State, t: State) -> bool:
    return all((u == v).all() for u, v in zip(s, t))


# ---- the kernel ------------------------------------------------------------------------
def test_east_car_alternates_private_and_shared_cells_round_its_row():
    s = place(1, 2, a=[(0, 0)])
    route = [place(1, 2, e=[(0, 0)]), place(1, 2, a=[(0, 1)]), place(1, 2, e=[(0, 1)]), s]
    for expected in route:
        s, moved = step(s)
        assert moved == 1 and same(s, expected)


def test_north_car_alternates_shared_and_private_cells_round_its_column():
    s = place(2, 1, n=[(0, 0)])
    route = [place(2, 1, b=[(0, 0)]), place(2, 1, n=[(1, 0)]), place(2, 1, b=[(1, 0)]), s]
    for expected in route:
        s, moved = step(s)
        assert moved == 1 and same(s, expected)


def test_merge_goes_to_the_priority_species_only():
    s = place(2, 2, a=[(1, 0)], b=[(0, 0)])            # both want c(x=0, y=1)
    assert same(step(s, EAST)[0], place(2, 2, e=[(1, 0)], b=[(0, 0)]))
    assert same(step(s, NORTH)[0], place(2, 2, a=[(1, 0)], n=[(1, 0)]))
    assert step(s, EAST)[1] == step(s, NORTH)[1] == 1


def test_no_car_enters_a_cell_vacated_in_the_same_step():
    s = place(1, 2, a=[(0, 0)], e=[(0, 0)])
    assert same(step(s)[0], place(1, 2, a=[(0, 0), (0, 1)]))


@given(states(), st.sampled_from(PRIORITIES))
def test_step_conserves_species_and_does_not_mutate(s, priority):
    before = State(*(v.copy() for v in s))
    t, moved = step(s, priority)
    assert same(s, before) and counts(t) == counts(s) and 0 <= moved <= sum(counts(s))


@given(states(), st.sampled_from(PRIORITIES))
def test_transpose_conjugates_the_two_yield_rules(s, priority):
    other = NORTH if priority == EAST else EAST
    assert same(transpose(step(s, priority)[0]), step(transpose(s), other)[0])
    assert counts(transpose(s)) == counts(s)[::-1]


def test_all_states_enumerates_each_configuration_once():
    s = all_states(1, 2)
    codes = {(tuple(a.ravel()), tuple(c.ravel()), tuple(b.ravel())) for a, c, b in zip(*s)}
    assert len(codes) == 12 ** 2


# ---- Lemma RB-0 and Theorem RB-G: gridlock ---------------------------------------------
@given(states(), st.sampled_from(PRIORITIES))
def test_rb0_fixed_iff_no_move_iff_every_next_cell_occupied(s, priority):
    t, moved = step(s, priority)
    assert bool(is_fixed(s)) == (moved == 0) == same(s, t)


@pytest.mark.parametrize("h,w", BOARDS)
def test_rbg_construction_is_a_gridlock_at_every_admissible_count(h, w):
    for n in range(min_gridlock(h, w), 3 * h * w + 1):
        s = gridlock_with(h, w, n)
        assert sum(counts(s)) == n and is_fixed(s)


@pytest.mark.parametrize("h,w", EXHAUSTIVE)
def test_rbg_exhaustive_gridlock_counts_are_exactly_the_interval(h, w):
    s = all_states(h, w)
    n = sum(counts(s))
    assert set(n[is_fixed(s) & (n > 0)].tolist()) == set(range(2 * min(h, w), 3 * h * w + 1))


# ---- Lemma RB-R: static criterion for free flow ----------------------------------------
@pytest.mark.parametrize("h,w", EXHAUSTIVE)
@pytest.mark.parametrize("priority", PRIORITIES)
def test_rbr_exhaustive_static_criterion_equals_dynamic_freeness(h, w, priority):
    s = all_states(h, w)
    assert (is_free(s, priority) == is_free_static(s)).all()


@settings(max_examples=400)
@given(states(density=st.floats(0, 0.25)), st.sampled_from(PRIORITIES))
def test_rbr_static_criterion_equals_dynamic_freeness_on_sparse_states(s, priority):
    assert bool(is_free(s, priority)) == bool(is_free_static(s))


@given(states(density=st.floats(0, 0.2)))
def test_free_configuration_returns_after_one_period_and_classes_advance_by_one(s):
    if not is_free(s):
        return
    t = step(s)[0]
    assert all((np.roll(k, 1) == k1).all() for k, k1 in zip(classes(s), classes(t)))
    for _ in range(period(*s.c.shape) - 1):
        t = step(t)[0]
    assert same(s, t)


# ---- Theorem RB-F: capacity and species frontier ---------------------------------------
@pytest.mark.parametrize("h,w", BOARDS)
def test_rbf_construction_is_free_with_the_requested_species_counts(h, w):
    for n_e, n_n in product(range(h * w + 2), repeat=2):
        if free_feasible(h, w, n_e, n_n):
            s = free_with(h, w, n_e, n_n)
            assert counts(s) == (n_e, n_n) and is_free(s, EAST) and is_free(s, NORTH)


@pytest.mark.parametrize("h,w", BOARDS)
def test_rbf_capacity_is_one_car_per_roundabout_and_mixing_needs_gcd_two(h, w):
    feasible = {(e, n) for e in range(h * w + 2) for n in range(h * w + 2) if free_feasible(h, w, e, n)}
    assert max(e + n for e, n in feasible) == max_free(h, w) == h * w
    mixed = {e + n for e, n in feasible if e and n}
    assert (max(mixed) == h * w) if gcd(h, w) >= 2 else not mixed


@pytest.mark.parametrize("h,w", EXHAUSTIVE)
@pytest.mark.parametrize("priority", PRIORITIES)
def test_rbf_exhaustive_species_frontier(h, w, priority):
    s = all_states(h, w)
    free = is_free(s, priority)
    realised = set(zip(counts(s)[0][free].tolist(), counts(s)[1][free].tolist()))
    assert realised == {(e, n) for e in range(3 * h * w + 1) for n in range(3 * h * w + 1)
                        if free_feasible(h, w, e, n)}


SEARCHED = [(2, 2), (2, 3), (3, 2), (3, 3), (2, 4), (4, 2)]      # gcd 1, 2 and 3


@pytest.mark.parametrize("h,w", SEARCHED)
@pytest.mark.parametrize("priority", PRIORITIES)
def test_rbf_species_frontier_from_every_free_configuration(h, w, priority):
    levels = free_levels(h, w, priority)
    realised = {pair for s in levels for pair in zip(*(k.tolist() for k in counts(s)))}
    assert len(levels) - 1 == max_free(h, w)
    assert realised == {(e, n) for e in range(h * w + 1) for n in range(h * w + 1)
                        if free_feasible(h, w, e, n)}
    assert all(is_free_static(s).all() for s in levels)


@pytest.mark.parametrize("h,w", SEARCHED)
def test_rbf_at_capacity_shared_cells_alternate_and_mixed_cities_pulse_in_unison(h, w):
    """Corollary RB-P, on every free configuration with WH cars: each shared cell is occupied
    at exactly every second step; with both species present, all of them at the same steps."""
    s = free_levels(h, w)[-1]
    mixed = (counts(s)[0] > 0) & (counts(s)[1] > 0)
    assert mixed.any() == (gcd(h, w) >= 2)
    for _ in range(period(h, w)):
        full = s.c != EMPTY
        assert (full.all(axis=(-2, -1)) | ~full.any(axis=(-2, -1)))[mixed].all()
        s = step(s)[0]
        assert (full != (s.c != EMPTY)).all()
