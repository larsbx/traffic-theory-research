"""Austin–Benjamini's TRAIN rule: their Proposition 6, extended to rectangles, checked
exhaustively; and their Proposition 1 (m < N/2 ⇒ speed one), checked for both rules."""
import numpy as np
import pytest
from hypothesis import given, settings, strategies as st

from bml.model import EMPTY, EAST, NORTH, CLASSIC, TRAIN, step, half_step
from bml.exhaustive import classify_all, JAM
from bml.extremal import train_stuck_with, is_stuck


def test_full_row_rotates_under_train_but_freezes_under_classic():
    s = np.array([[EAST, EAST, EAST]], np.int8)
    assert half_step(s, EAST, TRAIN)[1] == 3 and half_step(s, EAST, CLASSIC)[1] == 0


def test_train_moves_whole_line_behind_a_gap():
    s = np.array([[EAST, EAST, EMPTY, NORTH]], np.int8)
    t, m = half_step(s, EAST, TRAIN)
    assert m == 2 and t.tolist() == [[EMPTY, EAST, EAST, NORTH]]


@pytest.mark.parametrize("h,w", [(h, w) for h in range(1, 5) for w in range(1, 5) if h * w <= 12])
def test_AB_prop6_rectangles_stuck_iff_n_at_least_w_plus_h(h, w):
    """Stuck configurations exist exactly for W+H ≤ n ≤ WH (an empty range when W or H is 1)."""
    c = classify_all(h, w, TRAIN)
    n = c.n_east.astype(int) + c.n_north
    stuck_ns = sorted(set(n[(c.cls == JAM) & (n > 0)].tolist()))
    assert stuck_ns == list(range(w + h, h * w + 1))


def naive_reaches_free(s, rule):
    n = int((s != 0).sum())
    seen, orbit = {}, []
    while (k := s.tobytes()) not in seen:
        seen[k] = len(orbit)
        s, m = step(s, rule)
        orbit.append(int(m))
    return min(orbit[seen[k]:]) == n


@settings(max_examples=300, deadline=None)
@given(st.integers(3, 14), st.data(), st.sampled_from([CLASSIC, TRAIN]))
def test_AB_prop1_fewer_than_half_N_cars_attain_speed_one(N, data, rule):
    m = data.draw(st.integers(1, (N - 1) // 2))
    cells = data.draw(st.lists(st.integers(0, N * N - 1), min_size=m, max_size=m, unique=True))
    kinds = data.draw(st.lists(st.sampled_from([EAST, NORTH]), min_size=m, max_size=m))
    s = np.zeros(N * N, np.int8); s[cells] = kinds
    assert naive_reaches_free(s.reshape(N, N), rule)


@pytest.mark.parametrize("h,w", [(h, w) for h in range(2, 9) for w in range(2, 9)])
def test_train_stuck_construction_every_n(h, w):
    for n in range(w + h, h * w + 1):
        s = train_stuck_with(h, w, n)
        assert int((s != 0).sum()) == n and is_stuck(s, TRAIN)
        assert step(s, TRAIN)[1] == 0
