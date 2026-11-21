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


def certify_positive_derivative(counts: dict, cells: int, max_elevations: int = 4000):
    """Exact certificate that P′ > 0 on (0, 1], even when b dips.

    P′ = N Σ_k d_k B_k^{N−1}, with d_k = b_{k+1} − b_k. Let k₀ be the first k with d_k ≠ 0.
    Factor out p^{k₀}: P′ / p^{k₀} has Bernstein coefficients
    d_k·C(N−1, k)/C(N−1−k₀, k−k₀) in degree N−1−k₀. Raise that degree until every coefficient
    is ≥ 0. Nonnegative coefficients, not all zero, prove positivity on (0, 1). The first
    coefficient d_{k₀}·C(N−1, k₀) > 0 and the last d_{N−1} > 0 (which equals P′(1)/N and is
    preserved by degree raising) make it positive at both endpoints, so P′ > 0 on (0, 1].
    Returns the number of degree raises used, or None if P is constant, if P′(1) = 0, or if
    max_elevations is not enough.
    """
    d = [c / cells for c in derivative_bernstein(counts, cells)]        # d_k
    m = cells - 1
    k0 = next((k for k, v in enumerate(d) if v != 0), None)
    if k0 is None or d[k0] < 0 or d[-1] <= 0:      # constant P, or P′ ≤ 0 near 0 or at p = 1
        return None
    c = [d[k] * comb(m, k) / comb(m - k0, k - k0) for k in range(k0, m + 1)]
    deg = m - k0
    for e in range(max_elevations + 1):
        if all(v >= 0 for v in c):
            return e
        c = [(Fraction(i, deg + 1) * c[i - 1] if i else 0) +
             (1 - Fraction(i, deg + 1)) * (c[i] if i <= deg else 0) for i in range(deg + 2)]
        deg += 1
    return None
