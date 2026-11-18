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
            if in_coset:                                       # the (→) construction (needs a < w)
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


def test_B2_representative_bound_is_necessary():
    """Without a < w the statement fails: w = h = 2, a = 2, b = 0."""
    w = h = 2; a, b = 2, 0
    assert (a + b) % gcd(w, h) == 0
    assert not any(t % w == a for t in range(-10, 10))


@pytest.mark.parametrize("h,w", [(3, 3), (4, 4), (3, 6), (5, 5), (6, 6), (8, 4)])
def test_B4_theorem_F_matches_independent_dp(h, w):
    """Independent of the packing proof: max-plus DP over the Lemma R conditions.
    Covers g = 5 and g = 6, beyond the exhaustive tables (WH <= 16)."""
    from bml.freeflow_dp import max_free_exact
    from bml.extremal import max_free
    assert max_free_exact(h, w) == max_free(h, w)


@pytest.mark.parametrize("l", range(1, 40))
def test_B4_block_value_bound(l):
    """Block B^s A^r . of length l = s+r+1: ceil(s/2) + ceil(r/2) <= floor(2l/3)."""
    for s in range(l):
        r = l - 1 - s
        assert (s + 1) // 2 + (r + 1) // 2 <= (2 * l) // 3


def test_B4_floor_superadditive_and_V():
    for a in range(60):
        for b in range(60):
            assert (2 * a) // 3 + (2 * b) // 3 <= (2 * (a + b)) // 3
    assert all((g + g // 3) // 2 == (2 * g) // 3 for g in range(200))


def _occupied_classes(s, g):
    y, x = np.indices(s.shape)
    return {int(c) for c in ((x + y) % g)[s != 0]}


@pytest.mark.parametrize("h,w", [(2, 2), (3, 3), (2, 4), (4, 2), (2, 6)])
def test_B6_release_and_survival_exhaustive(h, w):
    """B6.1: Occ_t(z) ∧ ¬Occ_t(z+1) → Occ_{t+1}(z).   B6.2: Occ_t(z+1) → Occ_{t+1}(z) ∨ Occ_{t+1}(z+1)."""
    g = gcd(h, w)
    for s in decode(np.arange(3 ** (h * w), dtype=np.int64), h, w):
        O0 = _occupied_classes(s, g)
        O1 = {(c - 1) % g for c in _occupied_classes(step(s)[0], g)}   # Y-values at t+1
        for z in range(g):
            if z in O0 and (z + 1) % g not in O0:
                assert z in O1
            if (z + 1) % g in O0:
                assert z in O1 or (z + 1) % g in O1


@pytest.mark.parametrize("seed", range(40))
def test_B6_each_car_blocked_at_most_g_minus_2_times(seed):
    from bml.nonmonotone import labelled_step
    rng = np.random.default_rng(seed)
    N = int(rng.integers(5, 15)); h, w = (N, N) if seed % 2 else (N, 2 * N)
    g = gcd(h, w); m = int(rng.integers(1, (g - 1) // 2 + 1))
    s = np.zeros(h * w, np.int8); s[rng.choice(h * w, m, replace=False)] = rng.choice([EAST, NORTH], m)
    s = s.reshape(h, w); ids = np.full(s.shape, -1); ids[s != 0] = np.arange(m)
    blocks = np.zeros(m, int)
    for _ in range(4 * g * m + 50):
        s, ids, moved = labelled_step(s, ids)
        for i in set(range(m)) - moved:
            blocks[i] += 1
    assert blocks.max() <= g - 2
