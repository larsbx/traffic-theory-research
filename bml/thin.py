"""Thin tori: exact bounds on the iid jam probability of the 2×W torus.

CLASSIC rule. The torus has two cells along one axis and W along the other. A *plug* is a
two-cell line (column of a 2×W board) holding two cars of the species that moves along it.
A *lone* car is the only one of that species in its two-cell line. Lines between consecutive
plugs, going against the long-axis flow, are the *gaps* of a configuration.

Structure (proved in docs/research/2026-11-21-thin-torus-nonmonotonicity.md, tested here):
  * With fewer than W cars, a jam has a plug, and plugs never form or dissolve.
  * Jam with n < W  ⇒  in every gap, #long-axis cars ≥ distance of its farthest lone car
    (``gap_condition``).
  * A plug and no lone car  ⇒  jam.
So, with a = (p/2)², c = (1 − p/2)², the iid jam probability q satisfies

    lower(W, p) = (a + c)^W − c^W  ≤  q(p)  ≤  P(Bin(2W, p) ≥ W) + P(plug ∧ every gap OK) = upper(W, p).

Both bounds are computed in exact rational arithmetic.
"""
from __future__ import annotations

from fractions import Fraction

import numpy as np

from bml.model import EAST, NORTH

# On a board of shape (2, W) (rows, columns), NORTH cars move along the 2-cell columns
# and EAST cars along the W-cell rows. For shape (W, 2) the roles swap; ``canonical``
# transposes and swaps species so that both orientations use the same code.


def canonical(s: np.ndarray) -> np.ndarray:
    """Return an equivalent (2, W) view: short axis first, short-axis movers coded NORTH."""
    if s.shape[0] == 2:
        return s
    assert s.shape[1] == 2
    t = s.T.copy()
    out = np.zeros_like(t)
    out[t == EAST], out[t == NORTH] = NORTH, EAST
    return out


def column_types(s: np.ndarray) -> list[str]:
    """Per long-axis index: 'P' plug, 'L' lone short-axis car, 'O' none."""
    c = canonical(s)
    k = (c == NORTH).sum(axis=0)
    return ["P" if v == 2 else "L" if v == 1 else "O" for v in k]


def gap_condition(s: np.ndarray) -> bool:
    """Static necessary condition for a jam with fewer than W cars: some plug exists, and in each
    gap the long-axis movers number at least the distance from the farthest lone car to the
    plug at the gap's downstream end."""
    c = canonical(s)
    t = column_types(c)
    W = len(t)
    plugs = [x for x in range(W) if t[x] == "P"]
    if not plugs:
        return False
    longs = (c == EAST).sum(axis=0)
    for x in plugs:                       # gap west of plug x: columns x-1, x-2, … until a plug
        e = dmax = 0
        for d in range(1, W):
            y = (x - d) % W
            if t[y] == "P":
                break
            e += int(longs[y])
            if t[y] == "L":
                dmax = d
        if e < dmax:
            return False
    return True


def plug_without_lone(s: np.ndarray) -> bool:
    t = column_types(s)
    return "P" in t and "L" not in t


# ---- exact bounds ------------------------------------------------------------------------

def _num(p):
    """Exact Fraction unless p is a float (fast search mode)."""
    return p if isinstance(p, float) else Fraction(p)


def _column_weights(p):
    """(D, weights): per-column probabilities times D. Exact mode uses integers with
    D = (2·denominator(p))², so a run of g columns has denominator D^g; float mode uses m = 1, D = 4."""
    if isinstance(p, float):
        D, k, m = 4.0, p, 1.0
    else:
        D, k, m = p.denominator ** 2 * 4, p.numerator, p.denominator
    #   per cell, times 2m: empty 2(m−k), E k, N k
    E0, EE = 2 * (m - k), k
    return D, dict(plug=EE * EE, lone_e=2 * EE * EE, lone_0=2 * EE * E0,
                   e0=E0 * E0, e1=2 * EE * E0, e2=EE * EE)


def lower(W: int, p):
    p = _num(p)
    a, c = (p / 2) ** 2, (1 - p / 2) ** 2
    return (a + c) ** W - c ** W


def _gap_ok_scaled(K: int, p):
    """Numerators G[g]·D^g of G (see gap_ok), and D."""
    D, q = _column_weights(p)
    M = 2 * K + 1
    st = np.zeros((M, K + 1), dtype=float if isinstance(p, float) else object)
    st[:] = 0
    st[0, 0] = 1
    ok = np.arange(M)[:, None] >= np.arange(K + 1)[None, :]
    out = [st[0, 0]]
    for s in range(1, K):
        nst = q["e0"] * st
        nst[1:] += q["e1"] * st[:-1]
        nst[2:] += q["e2"] * st[:-2]
        lone = st.sum(axis=1)
        nst[:, s] += q["lone_0"] * lone
        nst[1:, s] += q["lone_e"] * lone[:-1]
        st = nst
        out.append(st[ok].sum())
    return out, D


def gap_ok(K: int, p) -> list:
    """G[g] = unnormalized iid mass of g columns that are non-plug and satisfy the gap condition, g = 0 … K−1.

    Independent of the torus length. DP state: (long-axis cars so far, farthest lone car)."""
    p = _num(p)
    G, D = _gap_ok_scaled(K, p)
    return [x / D ** g if isinstance(p, float) else Fraction(x, D ** g) for g, x in enumerate(G)]


def binomial_tail(n: int, p, k: int):
    from math import comb
    p = _num(p)
    return sum((comb(n, j) * p ** j * (1 - p) ** (n - j) for j in range(k, n + 1)), type(p)(0))


def gap_event(W: int, p):
    """P(gap_condition) on the 2×W torus, summing over cyclic plug/gap compositions.

    Block = a plug and the gap behind it; b_l = P(block of length l). Linear sequences c_m
    satisfy the renewal equation, and the block covering cell 0 gives the cyclic sum. In exact
    mode b_l and c_m are integer numerators over D^l and D^m."""
    p = _num(p)
    G, D = _gap_ok_scaled(W, p)
    plug = _column_weights(p)[1]["plug"]
    b = [0] + [plug * G[l - 1] for l in range(1, W + 1)]
    c = [1] + [0] * W
    for m in range(1, W + 1):
        c[m] = sum(b[l] * c[m - l] for l in range(1, m + 1))
    cyclic = sum(l * b[l] * c[W - l] for l in range(1, W + 1))
    return cyclic / D ** W if isinstance(p, float) else Fraction(cyclic, D ** W)


def upper(W: int, p):
    """P(#long-axis cars ≥ W) + P(gap_condition) ≥ q(p).

    A jam with fewer than W long-axis movers satisfies the gap condition: a winding blocking
    cycle needs W of them, and every other cycle is a plug. The count is Bin(2W, p/2)."""
    p = _num(p)
    return gap_event(W, p) + binomial_tail(2 * W, p / 2, W)


def certificate(W: int, p1, p2) -> dict:
    """Exact witness of non-monotonicity: p1 < p2 and q(p1) ≥ lower > upper ≥ q(p2)."""
    p1, p2 = Fraction(p1), Fraction(p2)
    lo, up = lower(W, p1), upper(W, p2)
    return dict(W=W, p1=str(p1), p2=str(p2), lower=float(lo), upper=float(up),
                holds=bool(p1 < p2 and lo > up))


def find_certificate(W: int, n1: int = 1000, n2: int = 200) -> dict:
    """Float search on the grids k/n1 (p1) and k/n2 (p2), then an exact check."""
    p1s = [k / n1 for k in range(1, n1)]
    lows = [lower(W, p) for p in p1s]
    best = None
    for k in range(1, n2):
        p2 = k / n2
        cand = [(lo, p) for lo, p in zip(lows, p1s) if p < p2]
        if not cand:
            continue
        lo, p1 = max(cand)
        margin = lo - upper(W, p2)
        if best is None or margin > best[0]:
            best = (margin, Fraction(round(p1 * n1), n1), Fraction(k, n2))
    return certificate(W, best[1], best[2])


def _e_minus_2_lower() -> Fraction:
    """A rational lower bound for e^-2, from e^2 < Σ_{k<20} 2^k/k! + 2·2^20/20!."""
    from math import factorial
    e2 = sum(Fraction(2 ** k, factorial(k)) for k in range(20)) + Fraction(2 * 2 ** 20, factorial(20))
    return 1 / e2


def renewal_radius(p, theta, z, K: int = 60) -> Fraction:
    """β(z) = Σ_g a·G(g)·z^(g+1) over all gap lengths g ≥ 0, bounded above in exact arithmetic.

    The first K terms are exact. For g ≥ K the exponential-moment bound
        G(g) ≤ s^g + (w_L/w) Σ_{d=1}^{g} r^d s^(g−d),
    with b = 1 − p + pθ/2, s = b², w_L = p·b, w = s + w_L, r = w/θ, sums in closed form
    when sz < 1 and rz < 1."""
    p, theta, z = Fraction(p), Fraction(theta), Fraction(z)
    a = (p / 2) ** 2
    b = 1 - p + p * theta / 2
    sq, wL = b * b, p * b
    w = sq + wL
    r = w / theta
    assert theta >= 1 and sq * z < 1 and r * z < 1

    def bound(g):
        return sq ** g + (wL / w) * sum(r ** d * sq ** (g - d) for d in range(1, g + 1))

    total = z / (1 - sq * z) + (wL / w) * z * (r * z) / ((1 - r * z) * (1 - sq * z))
    head_bound = sum(bound(g) * z ** (g + 1) for g in range(K))
    G = gap_ok(K, p)
    head = sum(G[g] * z ** (g + 1) for g in range(K))
    return a * (head + total - head_bound)


def asymptotic_certificate(p2, theta, z, W1: int, K: int = 60) -> dict:
    """For every W ≥ W1:  q(2/W) ≥ e^-2(1/W − 1/(2W²)) > (p2(2−p2))^W + W z^-W/(1−β(z)) ≥ q(p2).

    Checked exactly at W1. Both terms on the right, multiplied by W, decrease from W1 on
    (the ratio conditions below), and the left side times W increases."""
    p2, z = Fraction(p2), Fraction(z)
    beta = renewal_radius(p2, theta, z, K)
    x = p2 * (2 - p2)                     # Chernoff: P(Bin(2W, p/2) ≥ W) ≤ (4·(p/2)(1 − p/2))^W
    e2 = _e_minus_2_lower()
    lhs = e2 * (1 - Fraction(1, 2 * W1))
    rhs = W1 * x ** W1 + W1 ** 2 / (z ** W1 * (1 - beta))
    holds = (beta < 1 and Fraction(2, W1) < p2 and (1 + Fraction(1, W1)) ** 2 <= z
             and (1 + Fraction(1, W1)) * x <= 1 and lhs > rhs)
    return dict(W1=W1, p2=str(p2), theta=str(Fraction(theta)), z=str(z), K=K,
                beta=float(beta), lhs=float(lhs), rhs=float(rhs), holds=bool(holds))


def decay_certificate(p, theta, z, K: int = 60) -> dict:
    """Exponential decay of q on 2×W at fixed density p, for every W:

        q_W(p) ≤ (p(2−p))^W + W·z^−W/(1−β(z)),   valid when β(z) < 1 (checked exactly).
    """
    p, z = Fraction(p), Fraction(z)
    beta = renewal_radius(p, theta, z, K)
    return dict(p=str(p), theta=str(Fraction(theta)), z=str(z), K=K, beta=float(beta),
                holds=bool(beta < 1), tail_base=float(p * (2 - p)), renewal_base=float(1 / z))
