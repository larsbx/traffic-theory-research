"""Exact iid event probabilities from exhaustive counts, and an exact monotonicity certificate.

Under the iid law μ_p (each cell E w.p. p/2, N w.p. p/2, empty w.p. 1−p) on a torus with
N cells, an event with c_n of the C(N,n)·2^n configurations of n cars has probability

    P(p) = Σ_n c_n (p/2)^n (1−p)^(N−n) = Σ_n b_n · C(N,n) p^n (1−p)^(N−n),
    b_n  = c_n / (C(N,n)·2^n)   (the event's fraction among n-car configurations).

This is P in Bernstein form, so

    P′(p) = N · Σ_{n<N} (b_{n+1} − b_n) · C(N−1,n) p^n (1−p)^(N−1−n).

If b is nondecreasing, every Bernstein coefficient of P′ is ≥ 0 and P is nondecreasing on
[0, 1]. That is an exact certificate. Its converse fails in general, so a decrease in b
alone does not show that P decreases.
"""
from __future__ import annotations

from fractions import Fraction
from math import comb


def level_fractions(counts: dict, cells: int) -> list[Fraction]:
    """b_n for n = 0..cells."""
    return [Fraction(counts.get(n, 0), comb(cells, n) * 2 ** n) for n in range(cells + 1)]


def probability(counts: dict, cells: int, p: Fraction) -> Fraction:
    """P(p) exactly, for rational p."""
    p = Fraction(p)
    return sum(Fraction(c) * (p / 2) ** n * (1 - p) ** (cells - n) for n, c in counts.items())


def derivative_bernstein(counts: dict, cells: int) -> list[Fraction]:
    """Bernstein coefficients N·(b_{n+1} − b_n) of P′ (degree N−1)."""
    b = level_fractions(counts, cells)
    return [cells * (b[n + 1] - b[n]) for n in range(cells)]


def certified_nondecreasing(counts: dict, cells: int) -> bool:
    """Exact sufficient condition for P to be nondecreasing on [0, 1]: b is nondecreasing."""
    return all(c >= 0 for c in derivative_bernstein(counts, cells))
