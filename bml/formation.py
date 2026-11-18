"""Initial-law bounds and an exact one-round capture probability for CLASSIC.

All probabilities refer to independent *initial* cells with law (1-p,p/2,p/2).
The transfer calculation integrates initial cells; it does not assign an iid law
to an evolved configuration. The bounds do not prove a positive critical density.
"""
from __future__ import annotations

from fractions import Fraction
from math import comb
from numbers import Integral, Rational
from typing import Sequence

import numpy as np

from bml.model import CLASSIC
from bml.probability import _classic, _density, _rows


def _natural(value: int, name: str, minimum: int = 0) -> int:
    if (isinstance(value, (bool, np.bool_)) or not isinstance(value, Integral)
            or value < minimum):
        raise ValueError(f"{name} must be an integer at least {minimum}")
    return int(value)


def mixed_formation_upper_bound(
    side: int, p: Rational, rounds: int = 0, *, rule: str = CLASSIC,
) -> Fraction:
    """Union bound for a mixed direct cycle formed by the specified round.

Cycles persist, so formation by T is equivalent to presence at T. Each cycle
car has at most min(T+1,L) possible initial positions on its invariant lane.
Only injective assignments represent actual ancestors; including every choice
overcounts. The sum further overcounts non-simple words as possible cycles.
This is an upper bound on capture formation, not on *eventual* capture.
"""
    _classic(rule)
    side = _natural(side, "side", 1)
    rounds = _natural(rounds, "rounds")
    p = _density(p)
    if side == 1 or p == 0:
        return Fraction()
    base = p * min(rounds + 1, side)
    if base >= 1:
        return Fraction(1)
    weight = base / 2
    result = sum((
        Fraction(side * side, winding * side)
        * sum(comb(winding * side, east * side) for east in range(1, winding))
        * weight ** (winding * side)
        for winding in range(2, side + 1)
    ), Fraction())
    return min(Fraction(1), result)


def geometric_formation_upper_bound(
    side: int, p: Rational, rounds: int = 0, *, rule: str = CLASSIC,
) -> Fraction:
    """Coarser L*b^(2L)/(2*(1-b)), b=p*min(T+1,L), capped at one."""
    _classic(rule)
    side = _natural(side, "side", 1)
    rounds = _natural(rounds, "rounds")
    p = _density(p)
    if side == 1 or p == 0:
        return Fraction()
    base = p * min(rounds + 1, side)
    if base >= 1:
        return Fraction(1)
    return min(Fraction(1), Fraction(side, 2) * base ** (2 * side) / (1 - base))


def staircase_present(rows: Sequence[Sequence[int]], offset: int = 0) -> bool:
    """A specified 2L-cycle: E at (y+a,y), N at (y+a+1,y)."""
    h, w, flat = _rows(rows)
    if h != w or h < 4:
        raise ValueError("the one-round staircase calculation requires a square of side >= 4")
    offset = _natural(offset, "offset")
    if offset >= w:
        raise ValueError("offset must be less than the side")
    return all(flat[y * w + (y + offset) % w] == 1
               and flat[y * w + (y + offset + 1) % w] == 2 for y in range(h))


def staircase_preimage(rows: Sequence[Sequence[int]], offset: int = 0) -> bool:
    """Exact initial-site predicate for the staircase to be present after one round.

For each y let B=(y+a,y), C=east(B), A=west(B), D=south(C),
and Q=east(C)=D_(y+1). The predicate uses four diagonals x-y in
{a-1,a,a+1,a+2}. It permits every assignment of all exterior cells.
"""
    h, w, flat = _rows(rows)
    if h != w or h < 4:
        raise ValueError("the one-round staircase calculation requires a square of side >= 4")
    offset = _natural(offset, "offset")
    if offset >= w:
        raise ValueError("offset must be less than the side")

    def at(x: int, y: int) -> int:
        return flat[(y % w) * w + x % w]

    for y in range(w):
        x = y + offset
        a, b, c, d, q = at(x - 1, y), at(x, y), at(x + 1, y), at(x + 1, y - 1), at(x + 2, y)
        east_filled = (b == 1 and c != 0) or (b == 0 and a == 1)
        north_filled = c == 2 or (d == 2 and ((c == 0 and b != 1) or (c == 1 and q == 0)))
        if not (east_filled and north_filled):
            return False
    return True


def staircase_transfer_matrix(p: Rational) -> tuple[tuple[Fraction, ...], ...]:
    """Exact initial-law transfer matrix, D alphabet (empty,east,north).

Given D_y=d,D_(y+1)=e, the conditional local weight is
g(d,e)=a+1_(d=N)*(b+a*1_(e=0)), with a=u^2*(1+v), b=u*v^2,
u=p/2,v=1-p. Matrix entries are g(d,e)*P(D=e).
"""
    p = _density(p)
    u, v = p / 2, 1 - p
    a, b = u * u * (1 + v), u * v * v
    weights = (v, u, u)
    return tuple(tuple((a + (b + (a if e == 0 else 0) if d == 2 else 0)) * weights[e]
                       for e in range(3)) for d in range(3))


def staircase_one_round_probability(
    side: int, p: Rational, *, rule: str = CLASSIC,
) -> Fraction:
    """Exact probability of this specified staircase after one full round.

For L>=4 it is tr(T^L). T has rank <=2. Its nonzero eigenvalues have
sum r=u^2*(1+v+v^2) and product -d, d=u*v*[u^2*(1+v)]^2.
The trace obeys h_0=2,h_1=r,h_j=r*h_(j-1)+d*h_(j-2).
The starting indices are algebraic traces, not probabilities on sides 0 or 1.
"""
    _classic(rule)
    side = _natural(side, "side", 4)
    p = _density(p)
    u, v = p / 2, 1 - p
    a = u * u * (1 + v)
    r, d = u * u * (1 + v + v * v), u * v * a * a
    previous, current = Fraction(2), r
    for _ in range(2, side + 1):
        previous, current = current, r * current + d * previous
    return current


def staircase_capture_lower_bound(
    side: int, p: Rational, *, rule: str = CLASSIC,
) -> Fraction:
    """Lower bound on mixed-cycle formation by round one and eventual gridlock.

floor(L/4) staircases have disjoint four-diagonal initial supports. Their
preimage events are independent under the initial product law, despite their
evolved states being dependent. Each certified staircase forces global capture.
"""
    _classic(rule)
    side = _natural(side, "side", 4)
    h = staircase_one_round_probability(side, p, rule=rule)
    return 1 - (1 - h) ** (side // 4)
