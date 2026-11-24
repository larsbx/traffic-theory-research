"""Mixed signal/roundabout grid (TDD spec for bml.mixed;
docs/research/2026-11-24-mixed-roundabout-grid.md). Finite checks of Lemma MX-0, Theorem MX-G
and Corollaries MX-E, MX-P; gridlock is always decided from the dynamics or the blocker graph."""
from fractions import Fraction
from itertools import product

import numpy as np
import pytest
from hypothesis import assume, given, settings, strategies as st

from bml import extremal, model, roundabout
from bml.model import EMPTY, EAST, NORTH
from bml.roundabout import State
from bml.mixed import (
    Linked, counts, empty, laps,
    all_cells, balanced, best_min_gridlock, cells, free_levels, girth, gridlock_with, is_fixed,
    is_free, junction_load, min_gridlock, random_min_gridlock_tail, step, valid, worst_min_gridlock,
)

PRIORITIES = (EAST, NORTH)


def masks(h, w):
    return (np.array(bits, bool).reshape(h, w) for bits in product((False, True), repeat=h * w))


@st.composite
def boards(draw, max_side=5):
    h, w = draw(st.integers(1, max_side)), draw(st.integers(1, max_side))
    rng = np.random.default_rng(draw(st.integers(0, 2**32 - 1)))
    ring = rng.random((h, w)) < draw(st.floats(0, 1))
    p = draw(st.floats(0, 1))
    c = rng.choice([EMPTY, EAST, NORTH], (h, w), p=[1 - p, p / 2, p / 2]).astype(np.int8)
    return ring, State(ring & (rng.random((h, w)) < p), c, ring & (rng.random((h, w)) < p))


def same(s, t):
    return all((u == v).all() for u, v in zip(s, t))


def all_states(ring):
    """Every valid state of a small board: 3 values per signal cell, 12 per roundabout."""
    h, w = ring.shape
    base = np.where(ring.ravel(), 12, 3)
    digits = np.arange(base.prod())[:, None] // np.concatenate([[1], base.cumprod()[:-1]]) % base
    grid = digits.reshape(-1, h, w)
    return State(ring & (grid // 3 % 2 == 1), (grid % 3).astype(np.int8), ring & (grid // 6 == 1))


# ---- the kernel reduces to both parents ------------------------------------------------
@given(boards())
def test_without_roundabouts_two_ticks_are_one_bml_step(board):
    ring, s = board
    ring = np.zeros_like(ring)
    s = State(s.a & ring, s.c, s.b & ring)
    mid, m0 = step(s, ring, 0)
    end, m1 = step(mid, ring, 1)
    expected, moved = model.step(s.c)
    assert (end.c == expected).all() and m0 + m1 == moved and not (end.a | end.b).any()


@given(boards(), st.integers(0, 1), st.sampled_from(PRIORITIES))
def test_with_only_roundabouts_every_tick_is_a_roundabout_step(board, tick, priority):
    ring, s = board
    full = np.ones_like(ring)
    got, moved = step(s, full, tick, priority)
    expected, expected_moved = roundabout.step(s, priority)
    assert same(got, expected) and moved == expected_moved


@given(boards(), st.integers(0, 1), st.sampled_from(PRIORITIES))
def test_tick_conserves_species_keeps_validity_and_moves_only_into_vacant_cells(board, tick, priority):
    ring, s = board
    t, moved = step(s, ring, tick, priority)
    assert counts(t) == counts(s) and valid(t, ring) and 0 <= moved <= sum(counts(s))
    changed = sum(int((u != v).sum()) for u, v in zip(s, t))
    assert changed == 2 * moved


def test_signal_holds_each_species_on_its_red_tick():
    ring = np.zeros((2, 2), bool)
    s = State(ring.copy(), np.array([[EAST, EMPTY], [EMPTY, EMPTY]], np.int8), ring.copy())
    assert step(s, ring, 1)[1] == 0 and step(s, ring, 0)[1] == 1
    n = State(s.a, np.array([[NORTH, EMPTY], [EMPTY, EMPTY]], np.int8), s.b)
    assert step(n, ring, 0)[1] == 0 and step(n, ring, 1)[1] == 1


def test_car_leaves_a_signal_into_a_roundabout_on_any_tick():
    ring = np.array([[False, True]])
    s = State(np.zeros((1, 2), bool), np.array([[EAST, EMPTY]], np.int8), np.zeros((1, 2), bool))
    for tick in (0, 1):
        t, moved = step(s, ring, tick)
        assert moved == 1 and t.a[0, 1] and t.c[0, 0] == EMPTY


# ---- Lemma MX-0 ------------------------------------------------------------------------
@given(boards(), st.sampled_from(PRIORITIES))
def test_mx0_no_move_in_two_consecutive_ticks_iff_every_next_cell_occupied(board, priority):
    ring, s = board
    t, m0 = step(s, ring, 0, priority)
    u, m1 = step(t, ring, 1, priority)
    assert bool(is_fixed(s, ring)) == (m0 + m1 == 0)
    assert not is_fixed(s, ring) or same(s, u)


# ---- Theorem MX-G ----------------------------------------------------------------------
@pytest.mark.parametrize("h,w", [(1, 1), (1, 3), (2, 2), (2, 3), (3, 2), (3, 3), (2, 4), (4, 2)])
def test_mxg_formula_equals_blocker_graph_girth_for_every_placement(h, w):
    for ring in masks(h, w):
        assert min_gridlock(ring) == girth(ring)


@settings(max_examples=60, deadline=None)
@given(boards(max_side=7))
def test_mxg_formula_equals_blocker_graph_girth_on_random_placements(board):
    ring, _ = board
    assert min_gridlock(ring) == girth(ring)


@pytest.mark.parametrize("h,w", [(1, 1), (1, 2), (2, 1), (2, 2), (1, 3), (3, 1)])
def test_mxg_exhaustive_gridlock_counts_are_exactly_the_interval(h, w):
    for ring in masks(h, w):
        s = all_states(ring)
        n = sum(counts(s))
        assert set(n[is_fixed(s, ring) & (n > 0)].tolist()) == set(range(min_gridlock(ring), cells(ring) + 1))


@pytest.mark.parametrize("h,w", [(2, 3), (3, 2)])
def test_mxg_exhaustive_gridlock_counts_with_at_most_two_roundabouts(h, w):
    for ring in masks(h, w):
        if ring.sum() <= 2:
            s = all_states(ring)
            n = sum(counts(s))
            assert set(n[is_fixed(s, ring) & (n > 0)].tolist()) == set(range(min_gridlock(ring), cells(ring) + 1))


@settings(max_examples=40, deadline=None)
@given(boards(max_side=5))
def test_mxg_construction_is_a_gridlock_at_every_admissible_count(board):
    ring, _ = board
    for n in range(min_gridlock(ring), cells(ring) + 1):
        s = gridlock_with(ring, n)
        assert sum(counts(s)) == n and valid(s, ring) and is_fixed(s, ring)
        assert step(s, ring, 0)[1] == 0 and step(s, ring, 1)[1] == 0


def test_mxg_endpoints_are_bml_g1_and_roundabout_rbg():
    for h, w in product(range(1, 6), repeat=2):
        assert min_gridlock(np.zeros((h, w), bool)) == min(h, w)
        assert min_gridlock(np.ones((h, w), bool)) == roundabout.min_gridlock(h, w)
        assert len(all_cells(np.ones((h, w), bool))) == 3 * h * w


# ---- Corollary MX-E: extremes over placements of k roundabouts -------------------------
@pytest.mark.parametrize("h,w", [(1, 1), (1, 4), (2, 2), (2, 3), (3, 2), (3, 3), (2, 5), (4, 3), (4, 4)])
def test_mxe_best_and_worst_placements_over_every_mask(h, w):
    values = {}
    for ring in masks(h, w):
        values.setdefault(int(ring.sum()), set()).add(min_gridlock(ring))
    for k, seen in values.items():
        assert max(seen) == best_min_gridlock(h, w, k) and min(seen) == worst_min_gridlock(h, w, k)


@pytest.mark.parametrize("h,w", list(product(range(1, 8), repeat=2)))
def test_mxe_balanced_placement_attains_the_best_value(h, w):
    for k in range(h * w + 1):
        ring = balanced(h, w, k)
        assert ring.sum() == k and min_gridlock(ring) == best_min_gridlock(h, w, k)
        assert set(ring.sum(axis=1).tolist()) <= {k // h, -(-k // h)}
        assert set(ring.sum(axis=0).tolist()) <= {k // w, -(-k // w)}


# ---- Corollary MX-P: independent random placement --------------------------------------
@pytest.mark.parametrize("h,w", [(2, 1), (4, 2), (5, 2), (6, 3)])
@pytest.mark.parametrize("rho", [Fraction(0), Fraction(1, 3), Fraction(1, 2), Fraction(4, 5), Fraction(1)])
def test_mxp_exact_law_of_the_least_gridlock(h, w, rho):
    tail = [Fraction()] * (w + 2)
    for ring in masks(h, w):
        k = int(ring.sum())
        weight = rho ** k * (1 - rho) ** (h * w - k)
        for j in range(min_gridlock(ring) - w + 1):
            tail[j] += weight
    assert tail[: w + 1] == [random_min_gridlock_tail(h, w, rho, j) for j in range(w + 1)]


# ---- Proposition MX-F and the capacity census ------------------------------------------
def capacity(ring):
    return len(free_levels(ring)) - 1


@pytest.mark.parametrize("h,w", [(1, 3), (2, 2), (2, 3), (3, 2)])
@pytest.mark.parametrize("priority", PRIORITIES)
def test_mxf_every_free_configuration_respects_every_junction_budget(h, w, priority):
    for ring in masks(h, w):
        for level in free_levels(ring, priority):
            assert valid(level, ring).all()
            for a, c, b in zip(*level):
                assert junction_load(State(a, c, b), ring).max() <= 1


@pytest.mark.parametrize("h,w", [(1, 4), (2, 2), (2, 3), (3, 3)])
def test_free_capacity_endpoints_are_bml_f_and_roundabout_rbc(h, w):
    assert capacity(np.zeros((h, w), bool)) == extremal.max_free(h, w)
    assert capacity(np.ones((h, w), bool)) == roundabout.max_free(h, w)


def test_free_capacity_is_not_monotone_in_the_roundabout_set():
    """Exhaustive on 3×3: no roundabout gives 6, every single roundabout gives 5, and some
    two-roundabout placements give 4."""
    single = {capacity(ring) for ring in masks(3, 3) if ring.sum() == 1}
    double = {capacity(ring) for ring in masks(3, 3) if ring.sum() == 2}
    assert capacity(np.zeros((3, 3), bool)) == 6 and single == {5} and double == {4, 5}


@settings(max_examples=30, deadline=None)
@given(boards(max_side=4), st.sampled_from(PRIORITIES))
def test_free_configurations_are_never_stopped_by_a_car(board, priority):
    ring, s = board
    if is_free(s, ring, priority):
        assert junction_load(s, ring).max() <= 1 and (not is_fixed(s, ring) or sum(counts(s)) == 0)


# ---- the link-cell variant -------------------------------------------------------------
LINKS = (False, True)


@st.composite
def linked_boards(draw, max_side=5):
    ring, s = draw(boards(max_side))
    rng = np.random.default_rng(draw(st.integers(0, 2**32 - 1)))
    p = draw(st.floats(0, 1))
    return ring, Linked(*s, rng.random(ring.shape) < p, rng.random(ring.shape) < p)


def all_linked_states(ring):
    """Every valid linked state: 12 values per signal intersection, 48 per roundabout."""
    h, w = ring.shape
    base = np.where(ring.ravel(), 48, 12)
    digits = np.arange(base.prod())[:, None] // np.concatenate([[1], base.cumprod()[:-1]]) % base
    grid = digits.reshape(-1, h, w)
    return Linked(ring & (grid // 12 % 2 == 1), (grid % 3).astype(np.int8), ring & (grid // 24 == 1),
                  grid // 3 % 2 == 1, grid // 6 % 2 == 1)


@given(linked_boards(), st.integers(0, 1), st.sampled_from(PRIORITIES))
def test_linked_tick_conserves_species_and_moves_only_into_vacant_cells(board, tick, priority):
    ring, s = board
    t, moved = step(s, ring, tick, priority)
    assert counts(t) == counts(s) and valid(t, ring) and isinstance(t, Linked)
    assert sum(int((u != v).sum()) for u, v in zip(s, t)) == 2 * moved


def test_with_links_a_car_waits_for_its_signal_on_the_link_not_in_the_roundabout():
    ring = np.array([[True, False]])                      # roundabout at x=0, signal at x=1
    s = empty(1, 2, link=True)
    s.c[0, 0] = EAST
    t, moved = step(s, ring, 1)                           # leaves the roundabout on a red tick
    assert moved == 1 and t.e[0, 0] and t.c[0, 0] == EMPTY
    assert step(t, ring, 1)[1] == 0 and step(t, ring, 0)[0].c[0, 1] == EAST


@settings(max_examples=60, deadline=None)
@given(boards(max_side=5), st.sampled_from(LINKS), st.sampled_from([EAST, NORTH]), st.integers(0, 24))
def test_a_lone_car_is_free_and_laps_its_street_in_the_stated_number_of_ticks(board, link, species, where):
    ring, _ = board
    h, w = ring.shape
    y, x = where % h, where % w
    assume(link or ring[y, x] or (w if species == EAST else h) > 1)     # else it is its own blocker
    s = empty(h, w, link)
    s.c[y, x] = species
    assert is_free(s, ring)
    lap = laps(ring, link)[0][y] if species == EAST else laps(ring, link)[1][x]
    warm = 2 * (lap + 1)
    for tick in range(warm):
        s = step(s, ring, tick)[0]
    t = s
    for tick in range(warm, warm + lap):
        t = step(t, ring, tick)[0]
    assert same(s, t) and (lap % 2 == 0 or ring.all(axis=1 if species == EAST else 0)[y if species == EAST else x])


@given(linked_boards(), st.sampled_from(PRIORITIES))
def test_mx0_with_links(board, priority):
    ring, s = board
    t, m0 = step(s, ring, 0, priority)
    assert bool(is_fixed(s, ring)) == (m0 + step(t, ring, 1, priority)[1] == 0)


@pytest.mark.parametrize("h,w", [(1, 1), (1, 3), (2, 2), (2, 3), (3, 2), (3, 3)])
def test_mxg_with_links_formula_equals_blocker_graph_girth_for_every_placement(h, w):
    for ring in masks(h, w):
        assert min_gridlock(ring, link=True) == girth(ring, link=True)
        assert len(all_cells(ring, link=True)) == cells(ring, link=True)


@pytest.mark.parametrize("h,w,most", [(1, 1, 1), (1, 2, 2), (2, 1, 2), (2, 2, 1)])
def test_mxg_with_links_exhaustive_gridlock_counts_are_exactly_the_interval(h, w, most):
    for ring in masks(h, w):
        if ring.sum() <= most:
            s = all_linked_states(ring)
            n = sum(counts(s))
            assert set(n[is_fixed(s, ring) & (n > 0)].tolist()) == set(
                range(min_gridlock(ring, True), cells(ring, True) + 1))


@settings(max_examples=30, deadline=None)
@given(boards(max_side=4))
def test_mxg_with_links_construction_is_a_gridlock_at_every_admissible_count(board):
    ring, _ = board
    for n in range(min_gridlock(ring, True), cells(ring, True) + 1):
        s = gridlock_with(ring, n, link=True)
        assert sum(counts(s)) == n and valid(s, ring) and is_fixed(s, ring)
        assert step(s, ring, 0)[1] == 0 and step(s, ring, 1)[1] == 0


@pytest.mark.parametrize("h,w", [(1, 4), (2, 2), (2, 3), (3, 3), (4, 3)])
def test_mxe_with_links_best_and_worst_placements_over_every_mask(h, w):
    values = {}
    for ring in masks(h, w):
        values.setdefault(int(ring.sum()), set()).add(min_gridlock(ring, link=True))
    for k, seen in values.items():
        assert max(seen) == best_min_gridlock(h, w, k, True) == min_gridlock(balanced(h, w, k), True)
        assert min(seen) == worst_min_gridlock(h, w, k, True)


@pytest.mark.parametrize("h,w", [(1, 3), (2, 2)])
def test_mxf_with_links_every_free_configuration_respects_every_junction_budget(h, w):
    for ring in masks(h, w):
        for level in free_levels(ring, link=True):
            for layers in zip(*level):
                assert junction_load(Linked(*layers), ring).max() <= 1
