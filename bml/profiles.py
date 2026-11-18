"""Prescribed-profile CLASSIC jams and limits of lane-count-only certificates.

Positive E-row and N-column counts with max(E-row)+max(N-column)<=L have an
explicit jammed representative. Therefore a sound no-gridlock certificate that
depends only on these conserved counts cannot accept such a profile. The iid
bounds below concern acceptance of that restricted class of certificates; they
are NOT upper bounds on actual gridlock probability or claims about its basins.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import comb
from numbers import Rational
from typing import Sequence

import numpy as np

from bml.model import CLASSIC, EAST, NORTH, half_step
from bml.probability import _classic, _density, _integer, _rows


def _side(side: int) -> int:
    if not _integer(side) or side < 1:
        raise ValueError("side must be a positive integer")
    return int(side)


def _profile_pair(
    east_rows: Sequence[int], north_columns: Sequence[int],
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    try:
        east, north = tuple(east_rows), tuple(north_columns)
    except TypeError as error:
        raise ValueError("expected two integer lane-count vectors") from error
    if not east or len(east) != len(north):
        raise ValueError("lane profiles must have the same positive length")
    side = len(east)
    if any(not _integer(count) for count in east + north):
        raise ValueError("lane counts must be integers, not bools or floats")
    east, north = tuple(map(int, east)), tuple(map(int, north))
    if any(not 0 <= count <= side for count in east + north):
        raise ValueError("lane counts must be between zero and the side")
    return east, north


def is_constructible_profile(
    east_rows: Sequence[int], north_columns: Sequence[int], *, rule: str = CLASSIC,
) -> bool:
    """Whether the positive-profile sufficient condition holds; not a converse."""
    _classic(rule)
    east, north = _profile_pair(east_rows, north_columns)
    return min(east) >= 1 and min(north) >= 1 and max(east) + max(north) <= len(east)


def _admissible_pair(
    east_rows: Sequence[int], north_columns: Sequence[int],
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    east, north = _profile_pair(east_rows, north_columns)
    if min(east) < 1 or min(north) < 1 or max(east) + max(north) > len(east):
        raise ValueError("construction requires positive lane counts and max east + max north <= side")
    return east, north


def construct_jam_profile(
    east_rows: Sequence[int], north_columns: Sequence[int], *, rule: str = CLASSIC,
) -> tuple[tuple[int, ...], ...]:
    """Construct a square jam with exactly the prescribed lane counts.

E occupies (y-j,y), 0<=j<r_y; N occupies (x,x-i), 1<=i<=c_x.
The positive fronts block each other. The maximum-count condition keeps the
placements disjoint, including at equality. Rows increase in the north direction.
"""
    _classic(rule)
    east, north = _admissible_pair(east_rows, north_columns)
    side = len(east)
    rows = []
    for y in range(side):
        row = []
        for x in range(side):
            is_east = (y - x) % side < east[y]
            is_north = 0 < (x - y) % side <= north[x]
            if is_east and is_north:
                raise AssertionError("admissible profile placements overlap")
            row.append(EAST if is_east else NORTH if is_north else 0)
        rows.append(tuple(row))
    return tuple(rows)


def verify_jam_profile(
    rows: Sequence[Sequence[int]], east_rows: Sequence[int], north_columns: Sequence[int],
    *, rule: str = CLASSIC,
) -> None:
    """Bind an admissible profile to an actual jammed board and both half-steps.

The verifier checks the exact E-row and N-column counts independently of the
construction formula. It checks direct occupied targets and zero actual moves
in the production E and N half-steps, not merely equality of colored snapshots.
It may accept another jam with the same admissible profile.
"""
    _classic(rule)
    east, north = _admissible_pair(east_rows, north_columns)
    h, w, flat = _rows(rows)
    if h != w or w != len(east):
        raise ValueError("the square grid dimensions disagree with the profile")
    actual_east = tuple(sum(flat[y * w + x] == EAST for x in range(w)) for y in range(h))
    actual_north = tuple(sum(flat[y * w + x] == NORTH for y in range(h)) for x in range(w))
    if (actual_east, actual_north) != (east, north):
        raise ValueError("the grid does not have the exact requested lane counts")
    for y in range(h):
        for x in range(w):
            species = flat[y * w + x]
            if species == EAST and not flat[y * w + (x + 1) % w]:
                raise ValueError("an east car has an empty target and can move")
            if species == NORTH and not flat[((y + 1) % h) * w + x]:
                raise ValueError("a north car has an empty target and can move")
    original = np.asarray(rows, dtype=np.int8)
    after_east, east_moves = half_step(original, EAST, rule=rule)
    after_north, north_moves = half_step(after_east, NORTH, rule=rule)
    if (int(east_moves) != 0 or int(north_moves) != 0
            or not np.array_equal(after_east, original) or not np.array_equal(after_north, original)):
        raise ValueError("the production half-steps do not certify zero actual movement")


def admissible_profile_count(side: int) -> int:
    """Number of positive ordered profile pairs satisfying the sufficient condition."""
    side = _side(side)
    return sum((a ** side - (a - 1) ** side) * (side - a) ** side for a in range(1, side))


def _binomial_tail(trials: int, chance: Fraction, threshold: int) -> Fraction:
    return sum((Fraction(comb(trials, count)) * chance ** count * (1 - chance) ** (trials - count)
                for count in range(max(0, threshold), trials + 1)), Fraction())


def profile_pair_overflow_probability(
    side: int, p: Rational, *, rule: str = CLASSIC,
) -> Fraction:
    """Exact initial-iid P(r_y+c_x>L) for one specified row/column pair.

Their shared cell contributes Bern(p), not two independent Bern(p/2) variables.
The remaining 2L-2 cells contribute an independent Bin(2L-2,p/2) variable.
"""
    _classic(rule)
    side, p = _side(side), _density(p)
    u = p / 2
    return ((1 - p) * _binomial_tail(2 * side - 2, u, side + 1)
            + p * _binomial_tail(2 * side - 2, u, side))


@dataclass(frozen=True)
class ProfileCertificateBounds:
    """Calculated barrier bounds, not probability bounds for the gridlock event."""

    side: int
    p: Fraction
    cutoff: int
    zero_lane_probability: Fraction
    above_cutoff_probability: Fraction
    pair_overflow_probability: Fraction
    cutoff_upper_bound: Fraction
    pair_upper_bound: Fraction

    @property
    def best_upper_bound(self) -> Fraction:
        return min(self.cutoff_upper_bound, self.pair_upper_bound)


def profile_certificate_bounds(
    side: int, p: Rational, *, rule: str = CLASSIC,
) -> ProfileCertificateBounds:
    """Upper bounds on acceptance of any sound lane-count-only no-jam certificate.

The cutoff bound controls the probability that at least one lane count lies
outside 1..floor(L/2); a sound certificate must reject when all are inside.
The pair bound separately bounds zero lanes and the event max(r)+max(c)>L,
using the exact shared-cell pair law. Independent rows and independent columns
are treated separately; dependence between the two families is handled by a
union bound. These bounds do not measure actual traffic basin probabilities.

For side one the admissible profile set is empty and both bounds safely equal
one. The endpoints p=0 and p=1 are allowed, with no conditional probabilities.
"""
    _classic(rule)
    side, p = _side(side), _density(p)
    u, cutoff = p / 2, side // 2
    zero = (1 - u) ** side
    high = _binomial_tail(side, u, cutoff + 1)
    pair = profile_pair_overflow_probability(side, p, rule=rule)
    cutoff_bound = min(Fraction(1), 2 * (1 - (1 - zero - high) ** side))
    pair_bound = min(Fraction(1), 2 * (1 - (1 - zero) ** side) + side * side * pair)
    return ProfileCertificateBounds(side, p, cutoff, zero, high, pair, cutoff_bound, pair_bound)


def profile_certificate_upper_bound(
    side: int, p: Rational, *, rule: str = CLASSIC,
) -> Fraction:
    """Best of the two finite lane-count-only certificate acceptance upper bounds."""
    return profile_certificate_bounds(side, p, rule=rule).best_upper_bound
