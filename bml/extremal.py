"""Worst-case thresholds: gridlock and free flow on the W×H torus (see docs/theorems.md)."""
from __future__ import annotations

from math import gcd, lcm

import numpy as np

from bml.model import EMPTY, EAST, NORTH, CLASSIC, TRAIN, step, half_step, counts


# ---- gridlock (Theorems G1, G2) -------------------------------------------------------
def min_gridlock(h: int, w: int) -> int:
    """G1: least car count of a gridlock (fixed point with ≥1 car)."""
    return min(h, w)


def gridlock_with(h: int, w: int, n: int) -> np.ndarray:
    """G1 tightness: a gridlock with exactly n cars, min(h,w) ≤ n ≤ hw. Full shorter
    line, then cars stacked behind it (column-/row-wise), each blocked by its successor."""
    assert min(h, w) <= n <= h * w
    s = np.zeros((h, w), np.int8)
    if w <= h:   # full row y=0 of EAST cars; NORTH cars filled downwards from y=h-1
        s[0, :] = EAST
        rest = [(y, x) for x in range(w) for y in range(h - 1, 0, -1)]
        sp = NORTH
    else:        # full column x=0 of NORTH cars; EAST cars filled leftwards from x=w-1
        s[:, 0] = NORTH
        rest = [(y, x) for y in range(h) for x in range(w - 1, 0, -1)]
        sp = EAST
    for c in rest[: n - min(h, w)]:
        s[c] = sp
    return s


def non_gridlock_with(h: int, w: int, n: int) -> np.ndarray:
    """G2: for 0 ≤ n < hw a configuration that never gridlocks: single-species lines,
    at least one of which holds ≥1 car and ≥1 hole."""
    assert 0 <= n < h * w
    sp, (L, M) = (EAST, (h, w)) if w >= 2 else (NORTH, (w, h))   # L lines of length M
    per = [M] * (n // M) + ([n % M] if n % M else [])
    if n % M == 0 and n:                    # all lines full or empty: shift one car
        per[-1] -= 1; per.append(1)
    lines = np.zeros((L, M), np.int8)
    for i, k in enumerate(per):
        lines[i, :k] = sp
    return lines if sp == EAST else lines.T.copy()


# ---- free flow (Lemma R, Theorem F) ---------------------------------------------------
def phase_class(h: int, w: int) -> np.ndarray:
    """φ(y,x) = x + y mod gcd(w,h): the cosets of ⟨(1,-1)⟩ in Z_w × Z_h."""
    y, x = np.indices((h, w))
    return (x + y) % gcd(h, w)


def statically_free(s: np.ndarray) -> bool:
    """Lemma R: s flows freely forever ⇔ no EAST car directly west of an EAST car,
    no NORTH car directly south of a NORTH car, and φ(q) − φ(e) ∉ {0, 1} (mod g)
    for every NORTH car q and EAST car e."""
    h, w = s.shape
    g, phi = gcd(h, w), phase_class(h, w)
    if ((s == EAST) & (np.roll(s, -1, axis=1) == EAST)).any():
        return False
    if ((s == NORTH) & (np.roll(s, -1, axis=0) == NORTH)).any():
        return False
    A, B = set(phi[s == EAST].tolist()), set(phi[s == NORTH].tolist())
    return not any((b - a) % g in (0, 1 % g) for a in A for b in B)


def dynamically_free(s: np.ndarray) -> bool:
    """Every car moves at every step for lcm(w,h) steps (then the state recurs)."""
    n = sum(counts(s))
    for _ in range(lcm(*s.shape)):
        s, m = step(s)
        if m != n:
            return False
    return True


def V(g: int) -> int:
    return (g + g // 3) // 2


def max_free(h: int, w: int) -> int:
    """Theorem F: the largest car count admitting free flow."""
    g = gcd(h, w)
    return max(h * (w // 2), w * (h // 2)) if g == 1 else (h * w // g) * V(g)


def max_free_config(h: int, w: int) -> np.ndarray:
    """Theorem F tightness. g = 1: alternate cars along the longer-capacity direction.
    g ≥ 2: label classes Z_g by k blocks 'N E ·' then blocks 'E ·' (k = ⌊g/3⌋ − parity fix)."""
    g = gcd(h, w)
    if g == 1:
        y, x = np.indices((h, w))
        if h * (w // 2) >= w * (h // 2):
            return np.where((x % 2 == 0) & (x < 2 * (w // 2)), EAST, EMPTY).astype(np.int8)
        return np.where((y % 2 == 0) & (y < 2 * (h // 2)), NORTH, EMPTY).astype(np.int8)
    k = g // 3 - ((g // 3 - g) % 2)
    labels = [NORTH, EAST, EMPTY] * k + [EAST, EMPTY] * ((g - 3 * k) // 2)
    return np.array(labels, np.int8)[phase_class(h, w)]


# ---- Austin–Benjamini TRAIN rule (Proposition 6, extended to W×H) ---------------------
def is_stuck(s: np.ndarray, rule: str = CLASSIC) -> bool:
    """No car can move: neither half-step moves anything (then nothing ever moves)."""
    return half_step(s, EAST, rule)[1] == 0 and half_step(s, NORTH, rule)[1] == 0


def train_stuck_with(h: int, w: int, n: int) -> np.ndarray:
    """A TRAIN-stuck configuration with exactly n cars, W+H <= n <= WH.

    The W+H-car core follows E^(W-1) N^(H-1) E N. Every column has
    a permanent EAST blocker and every row has a permanent NORTH blocker.
    Remaining NORTH cars fill the non-bottom cells of successive non-rightmost
    columns from top to bottom. A prefix of this order preserves blockage and
    cannot create a rotating homogeneous ring.

    This closed form is the construction used in formal/lean/Train/Threshold.lean.
    """
    assert h >= 2 and w >= 2 and w + h <= n <= h * w
    extra = n - (w + h)
    y, x = np.indices((h, w))
    rank = x * (h - 1) + (h - 1 - y)
    return np.where(
        x == w - 1,
        np.where(y == h - 1, EAST, NORTH),
        np.where(y == 0, EAST, np.where(rank <= extra, NORTH, EMPTY)),
    ).astype(np.int8)
