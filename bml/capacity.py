"""Disjoint-strip capacity obstructions for CLASSIC BML.

The deterministic certificate uses only conserved lane counts. A mixed simple
blocker cycle must spend k east vertices to cross each selected north-empty
k-column strip. Disjoint strips make these expenditures disjoint. The exact iid
bound uses separate marginal laws for strip supply and row capacity; it never
treats those two quantities as independent. See the accompanying research note
for the universal geometric and probability proofs.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import comb
from numbers import Rational
from typing import Sequence

from bml.model import CLASSIC
from bml.probability import (
    _classic, _density, _dimensions, _integer, _profiles, _rows, _strip_width,
)


@dataclass(frozen=True)
class StripCapacity:
    """Untrusted lane profiles and pairwise disjoint cyclic north-empty strips.

Each start identifies k consecutive columns, with arithmetic modulo width.
The public verifier binds all metadata to a supplied grid before accepting it.
"""

    width: int
    height: int
    k: int
    starts: tuple[int, ...]
    east_rows: tuple[int, ...]
    north_columns: tuple[int, ...]


def verify_capacity_certificate(
    rows: Sequence[Sequence[int]], certificate: StripCapacity, *, rule: str = CLASSIC,
) -> None:
    """Check a sufficient obstruction to eventual nonempty gridlock.

If B disjoint north-empty strips exceed C=sum_y floor(r_y/k), mixed cycles
are impossible in every state with the conserved profile. A full north column
must be excluded separately. A full east row would already give C>=B.
"""
    _classic(rule)
    h, w, flat = _rows(rows)
    if not isinstance(certificate, StripCapacity):
        raise ValueError("expected a StripCapacity certificate")
    if _dimensions(certificate.width, certificate.height) != (w, h):
        raise ValueError("certificate dimensions disagree with the grid")
    k = _strip_width(certificate.k, w)
    if (not isinstance(certificate.starts, tuple)
            or any(not _integer(start) or not 0 <= start < w for start in certificate.starts)):
        raise ValueError("strip starts must be a tuple of in-range integer columns")
    columns = [(int(start) + offset) % w
               for start in certificate.starts for offset in range(k)]
    if len(set(columns)) != len(columns):
        raise ValueError("selected strips must have pairwise disjoint columns")
    for profile, length, limit in (
        (certificate.east_rows, h, w), (certificate.north_columns, w, h),
    ):
        if (not isinstance(profile, tuple) or len(profile) != length
                or any(not _integer(n) or not 0 <= n <= limit for n in profile)):
            raise ValueError("lane profiles must contain one bounded integer per lane")
    east_rows, north_columns = _profiles(h, w, flat)
    if (certificate.east_rows, certificate.north_columns) != (east_rows, north_columns):
        raise ValueError("certificate lane profiles disagree with the exact input")
    if any(north_columns[x] for x in columns):
        raise ValueError("a selected strip is not north-empty")
    if h in north_columns:
        raise ValueError("a full north column must be excluded separately")
    capacity = sum(count // k for count in east_rows)
    if len(certificate.starts) <= capacity:
        raise ValueError("the number of disjoint strips must exceed row capacity")


def make_capacity_certificate(
    rows: Sequence[Sequence[int]], k: int, *, offset: int = 0, rule: str = CLASSIC,
) -> StripCapacity:
    """Use the north-empty blocks of one fixed disjoint cyclic partition.

The floor(W/k) blocks start at offset, offset+k, ..., modulo W. The leftover
columns are unused. Raises ValueError when this partition does not certify.
"""
    _classic(rule)
    h, w, flat = _rows(rows)
    k = _strip_width(k, w)
    if not _integer(offset) or not 0 <= offset < w:
        raise ValueError("partition offset must be an in-range integer column")
    east_rows, north_columns = _profiles(h, w, flat)
    starts = tuple((int(offset) + j * k) % w for j in range(w // k)
                   if not any(north_columns[(int(offset) + j * k + i) % w] for i in range(k)))
    certificate = StripCapacity(w, h, k, starts, east_rows, north_columns)
    verify_capacity_certificate(rows, certificate, rule=rule)
    return certificate


@lru_cache(maxsize=128)
def _lower_tails(
    w: int, h: int, p: Fraction, k: int,
) -> tuple[tuple[Fraction, ...], tuple[Fraction, ...], Fraction]:
    """Exact C and B lower tails, using integer polynomial coefficients.

Only coefficients of degrees less than floor(W/k) are needed. Truncation
is exact because all exponents are nonnegative. Cached results are immutable.
"""
    u = p / 2
    a, b = u.numerator, u.denominator
    blocks = w // k
    row = [0] * blocks
    for n in range(w + 1):
        j = n // k
        if j < blocks:
            row[j] += comb(w, n) * a ** n * (b - a) ** (w - n)
    coefficients = [1] + [0] * (blocks - 1)
    for _ in range(h):
        coefficients = [sum(coefficients[i] * row[j - i] for i in range(j + 1))
                        for j in range(blocks)]
    denominator = b ** (w * h)
    cumulative = 0
    capacity_below = []
    for mass in coefficients:
        cumulative += mass
        capacity_below.append(Fraction(cumulative, denominator))

    theta_numerator = (b - a) ** (h * k)
    theta_denominator = b ** (h * k)
    supply_denominator = theta_denominator ** blocks
    cumulative = 0
    strips_below = []
    for j in range(blocks):
        cumulative += (comb(blocks, j) * theta_numerator ** j
                       * (theta_denominator - theta_numerator) ** (blocks - j))
        strips_below.append(Fraction(cumulative, supply_denominator))
    full_north = 1 - Fraction((b ** h - a ** h) ** w, denominator)
    return tuple(capacity_below), tuple(strips_below), full_north


def capacity_bound_terms(
    width: int, height: int, p: Rational, k: int, threshold: int, *, rule: str = CLASSIC,
) -> tuple[Fraction, Fraction, Fraction]:
    """Return exact P(C>=threshold), P(B<threshold), and P(full N-column).

B counts north-empty blocks in the fixed partition starting at column zero;
C=sum_y floor(X_y/k), with independent X_y~Bin(W,p/2). B is binomial with
floor(W/k) trials and success probability (1-p/2)**(H*k). B and C are generally
dependent. A union bound, rather than multiplication, gives the jam bound.
"""
    _classic(rule)
    w, h = _dimensions(width, height)
    k = _strip_width(k, w)
    density = _density(p)
    if not _integer(threshold) or not 1 <= threshold <= w // k:
        raise ValueError("threshold must be an integer between 1 and floor(width/k)")
    capacity_below, strips_below, full_north = _lower_tails(w, h, density, k)
    i = int(threshold) - 1
    return 1 - capacity_below[i], strips_below[i], full_north


def capacity_upper_bound(
    width: int, height: int, p: Rational, k: int, threshold: int, *, rule: str = CLASSIC,
) -> Fraction:
    """Exact rational union bound on eventual gridlock, clamped above at one."""
    return min(Fraction(1), sum(
        capacity_bound_terms(width, height, p, k, threshold, rule=rule), Fraction()))
