"""Non-trivial non-monotonicity: adding one car revives cars that would otherwise freeze."""
import numpy as np
import pytest

from bml.model import EMPTY as o, EAST as E, NORTH as N, step
from bml.nonmonotone import recurrent_movers, witnesses


def grid(rows_top_down):
    return np.array(rows_top_down[::-1], np.int8)          # printed top row is y = H-1


X = grid([[N, N, E, o],
          [E, E, o, N],
          [o, o, o, E]])
Y = X.copy(); Y[0, 0] = E                                  # one extra EAST car at (y,x)=(0,0)


def test_3x4_witness_x_freezes_completely():
    assert recurrent_movers(X) == set()


def test_3x4_witness_one_car_revives_seven():
    assert recurrent_movers(Y) == {0, 1, 2, 3, 4, 5, 6, 7}   # id 0 is the added car


def test_recurrent_movers_on_free_flow_is_everyone():
    s = np.zeros((3, 3), np.int8); s[0, 0] = E; s[1, 2] = N
    assert recurrent_movers(s) == {0, 1}


@pytest.mark.parametrize("h,w", [(2, 2), (2, 3), (3, 2), (3, 3)])
def test_small_tori_unjamming_is_always_trivial(h, w):
    assert next(witnesses(h, w), None) is None


@pytest.mark.parametrize("h,w", [(h, w) for h in range(2, 11) for w in range(2, 11) if max(h, w) >= 4])
def test_gated_witness_is_genuine_on_every_shape(h, w):
    """Theorem U (existence): x jams exactly, y never jams, and an original car moves forever."""
    from bml.levels import jams
    from bml.nonmonotone import gated_witness
    x, y, cell = gated_witness(h, w)
    assert int((y != 0).sum()) == int((x != 0).sum()) + 1 and x[cell] == 0
    jx, jy = jams(np.stack([x, y]))
    assert jx and not jy
    assert recurrent_movers(y) - {0}          # the added car at (0,0) has id 0


@pytest.mark.parametrize("n", range(1, 9))
def test_single_lane_tori_never_unjam(n):
    """Theorem U (min side 1): adding a car to a jamming configuration never un-jams."""
    from bml.exhaustive import classify_all, JAM
    for h, w in ((1, n), (n, 1)):
        c = classify_all(h, w)
        idx = np.arange(len(c.cls), dtype=np.int64)
        for i in range(h * w):
            free = ((idx // 3 ** i) % 3) == 0
            for sp in (1, 2):
                x = idx[free]
                assert not ((c.cls[x] == JAM) & (c.cls[x + sp * 3 ** i] != JAM)).any()
