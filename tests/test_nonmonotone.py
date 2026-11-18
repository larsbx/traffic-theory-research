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
