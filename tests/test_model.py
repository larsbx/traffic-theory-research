"""Properties of the BML step map on the W×H torus (TDD spec for bml.model)."""
import numpy as np
from hypothesis import given, settings, strategies as st

from bml.model import EMPTY, EAST, NORTH, half_step, step, is_fixed, blocker_cycle, counts

shapes = st.tuples(st.integers(1, 6), st.integers(1, 6))


@st.composite
def configs(draw):
    h, w = draw(shapes)
    cells = draw(st.lists(st.sampled_from([EMPTY, EAST, NORTH]), min_size=h * w, max_size=h * w))
    return np.array(cells, dtype=np.int8).reshape(h, w)


def test_single_east_car_moves_east_with_wraparound():
    s = np.zeros((1, 3), np.int8); s[0, 2] = EAST
    t, moved = half_step(s, EAST)
    assert t[0, 0] == EAST and moved == 1


def test_blocked_car_stays():
    s = np.array([[EAST, NORTH]], np.int8)
    assert (half_step(s, EAST)[0] == s).all()


def test_input_is_not_mutated():
    s = np.array([[EAST, EMPTY]], np.int8); s0 = s.copy()
    step(s)
    assert (s == s0).all()


@given(configs())
def test_step_conserves_each_species(s):
    assert counts(step(s)[0]) == counts(s)


@given(configs())
def test_moves_bounded_by_cars(s):
    nE, nN = counts(s)
    assert 0 <= step(s)[1] <= nE + nN


@given(configs())
def test_fixed_iff_step_is_identity(s):
    assert is_fixed(s) == bool((step(s)[0] == s).all())


@given(configs())
def test_fixed_point_with_cars_has_at_least_min_side_cars(s):
    """Theorem G1: a gridlocked configuration holds >= min(W, H) cars."""
    nE, nN = counts(s)
    if is_fixed(s) and nE + nN > 0:
        assert nE + nN >= min(s.shape)


@settings(max_examples=300)
@given(configs())
def test_blocker_cycle_is_closed_monotone_loop(s):
    """In a gridlock every blocker chain ends in a cycle of winding (a,b) with length aW+bH."""
    nE, nN = counts(s)
    if not (is_fixed(s) and nE + nN > 0):
        return
    cyc = blocker_cycle(s)
    h, w = s.shape
    east = sum(1 for (y, x) in cyc if s[y, x] == EAST)
    north = len(cyc) - east
    assert east % w == 0 and north % h == 0 and len(cyc) > 0


def test_full_row_is_minimal_gridlock():
    s = np.zeros((4, 5), np.int8); s[2, :] = EAST
    assert is_fixed(s) and sum(counts(s)) == 5
    t = np.zeros((4, 5), np.int8); t[:, 1] = NORTH
    assert is_fixed(t) and sum(counts(t)) == 4
