"""Numerical checks of the lemmas in formal/blueprint.md, so provers are not handed false lemmas."""
from math import gcd, lcm

import numpy as np
import pytest

from bml.model import EMPTY, EAST, NORTH, CLASSIC, TRAIN, step, half_step, movers_mask, AXIS, is_fixed
from bml.exhaustive import decode
from bml.extremal import train_stuck_with, is_stuck

SHAPES = [(h, w) for h in range(1, 9) for w in range(1, 9)]


def column_major(h, w, n):
    """B1 construction (w >= 2): east car at (x, y) iff x*h + y < n."""
    y, x = np.indices((h, w))
    return np.where(x * h + y < n, EAST, EMPTY).astype(np.int8)


@pytest.mark.parametrize("h,w", [(h, w) for h, w in SHAPES if w >= 2])
def test_B1_column_major_never_freezes(h, w):
    for n in range(1, h * w):
        s = column_major(h, w, n)
        assert int((s != 0).sum()) == n
        y0 = 0 if n <= (w - 1) * h else h - 1                   # Lemma B1.1
        assert s[y0, 0] == EAST and s[y0, w - 1] == EMPTY
        for _ in range(2 * w * h):                               # invariant I is preserved
            assert not is_fixed(s)
            assert (s == EAST)[y0].any() and (s == EMPTY)[y0].any() and not (s == NORTH).any()
            s, _ = step(s)


@pytest.mark.parametrize("h", range(2, 9))
def test_B1_width_one_column_never_freezes(h):
    for n in range(1, h):
        s = np.zeros((h, 1), np.int8); s[:n, 0] = NORTH
        for _ in range(2 * h):
            assert not is_fixed(s)
            s, _ = step(s)


def bezout(m, n):
    """Lemma B2.1, by the same gcd recursion the blueprint uses."""
    if m == 0:
        return 0, 1
    x1, y1 = bezout(n % m, m)                                  # x1*(n % m) + y1*m = g
    return y1 - x1 * (n // m), x1                              # (y1 - x1*(n//m))*m + x1*n = g


@pytest.mark.parametrize("h,w", SHAPES)
def test_B2_coset_identity_and_constructive_witness(h, w):
    g = gcd(w, h)
    x, y = bezout(w, h)
    assert x * w + y * h == g
    for a in range(w):
        for b in range(h):
            in_coset = any(t % w == a and (b + t) % h == 0 for t in range(lcm(w, h)))
            assert in_coset == ((a + b) % g == 0)
            if in_coset:                                       # the (→) construction
                k = (a + b) // g
                t = a - x * k * w
                assert t % w == a and (b + t) % h == 0


@pytest.mark.parametrize("h,w", [(h, w) for h in range(1, 4) for w in range(1, 4)])
def test_B3_1_rigid_half_step(h, w):
    """If every sp-car can move, halfStep(s)[p] == sp  iff  s[prev p] == sp."""
    for s in decode(np.arange(3 ** (h * w), dtype=np.int64), h, w):
        for sp in (EAST, NORTH):
            mv = movers_mask(s, sp, CLASSIC)
            if ((s == sp) == mv).all():
                t, _ = half_step(s, sp)
                assert ((t == sp) == (np.roll(s, 1, axis=AXIS[sp]) == sp)).all()


@pytest.mark.parametrize("h,w", [(h, w) for h in range(2, 9) for w in range(2, 9)])
def test_B5_staircase_attains_w_plus_h(h, w):
    s = train_stuck_with(h, w, w + h)
    assert int((s != 0).sum()) == w + h and is_stuck(s, TRAIN)
