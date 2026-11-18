"""Exact finite iid probabilities and conserved-lane obstructions for CLASSIC BML.

The initial cells are independent with probabilities ``(1-p, p/2, p/2)`` for
empty, east, and north. No iid assumption is made about a later state. ``M``
means that a mixed occupied blocker cycle occurs at some full-round snapshot;
``J`` means eventual nonempty gridlock; ``R`` is an initially full east row or
north column. Enumeration detects mixed cycles directly and propagates their
reachability through the complete finite transition graph before checking
``M == J & ~R``. These computations do not establish an asymptotic threshold.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import comb
from numbers import Integral, Rational
from typing import Sequence

import numpy as np

from bml.capture import find_blocker_cycles, verify_cycle
from bml.certificates import _grid
from bml.exhaustive import JAM, classify_all, decode
from bml.model import CLASSIC


EVENT_NAMES = (
    "gridlock", "eventual_mixed", "initial_mixed", "initial_core",
    "full_lane", "ringless_gridlock", "ringless",
)
MAX_ENUMERATION_CELLS = 12


def _integer(value: object) -> bool:
    return isinstance(value, Integral) and not isinstance(value, (bool, np.bool_))


def _classic(rule: str) -> None:
    if rule != CLASSIC:
        raise ValueError("probability calculations require the CLASSIC update rule")


def _dimensions(width: int, height: int) -> tuple[int, int]:
    if any(not _integer(v) or v < 1 for v in (width, height)):
        raise ValueError("width and height must be positive integers")
    return int(width), int(height)


def _density(p: Rational) -> Fraction:
    if isinstance(p, (bool, np.bool_)) or not isinstance(p, Rational) or not 0 <= p <= 1:
        raise ValueError("density must be an exact rational in [0, 1], not a float or bool")
    return Fraction(int(p.numerator), int(p.denominator))


def _strip_width(k: int, width: int) -> int:
    if not _integer(k) or not 1 <= k <= width:
        raise ValueError("strip width must be an integer between 1 and the torus width")
    return int(k)


def _rows(rows: Sequence[Sequence[int]]) -> tuple[int, int, tuple[int, ...]]:
    try:
        h, w, flat = _grid(rows)
    except (TypeError, IndexError) as error:
        raise ValueError("expected a nonempty rectangular grid") from error
    if any(isinstance(cell, (bool, np.bool_)) for row in rows for cell in row):
        raise ValueError("cell values must be integer species, not bools")
    return h, w, flat


def _profiles(h: int, w: int, flat: tuple[int, ...]) -> tuple[tuple[int, ...], tuple[int, ...]]:
    east_rows = tuple(sum(flat[y * w + x] == 1 for x in range(w)) for y in range(h))
    north_columns = tuple(sum(flat[y * w + x] == 2 for y in range(h)) for x in range(w))
    return east_rows, north_columns


def has_full_lane(rows: Sequence[Sequence[int]], *, rule: str = CLASSIC) -> bool:
    """The initial event R: a full E-row or a full N-column, with species fixed."""
    _classic(rule)
    h, w, flat = _rows(rows)
    east_rows, north_columns = _profiles(h, w, flat)
    return w in east_rows or h in north_columns


@dataclass(frozen=True)
class NorthEmptyStrip:
    """Claimed conserved lane profiles and a cyclic block of N-free columns.

The metadata is untrusted until ``verify_strip_certificate`` binds it to a grid.
Columns start at ``start`` and advance modulo ``width`` for ``k`` columns.
"""

    width: int
    height: int
    start: int
    k: int
    east_rows: tuple[int, ...]
    north_columns: tuple[int, ...]


def verify_strip_certificate(
    rows: Sequence[Sequence[int]], certificate: NorthEmptyStrip, *, rule: str = CLASSIC,
) -> None:
    """Verify a sufficient obstruction to eventual gridlock.

Every row must have fewer than k east cars, the specified k consecutive columns
must contain no north cars, and no column may be full of north cars. All these
lane counts are conserved. A mixed winding cycle would need k east vertices in
one row to cross the strip; monochromatic cycles are excluded separately.
"""
    _classic(rule)
    h, w, flat = _rows(rows)
    if not isinstance(certificate, NorthEmptyStrip):
        raise ValueError("expected a NorthEmptyStrip certificate")
    if _dimensions(certificate.width, certificate.height) != (w, h):
        raise ValueError("certificate dimensions disagree with the grid")
    k = _strip_width(certificate.k, w)
    if not _integer(certificate.start) or not 0 <= certificate.start < w:
        raise ValueError("strip start must be an in-range integer column")
    for profile, length, capacity in (
        (certificate.east_rows, h, w), (certificate.north_columns, w, h),
    ):
        if (not isinstance(profile, tuple) or len(profile) != length
                or any(not _integer(n) or not 0 <= n <= capacity for n in profile)):
            raise ValueError("lane profiles must contain one bounded integer count per lane")
    east_rows, north_columns = _profiles(h, w, flat)
    if (certificate.east_rows, certificate.north_columns) != (east_rows, north_columns):
        raise ValueError("certificate lane profiles disagree with the exact input")
    if any(north_columns[(certificate.start + offset) % w] for offset in range(k)):
        raise ValueError("the claimed strip is not north-empty")
    if max(east_rows) >= k:
        raise ValueError("every east row count must be strictly less than the strip width")
    if h in north_columns:
        raise ValueError("a full north column must be excluded separately")


def make_strip_certificate(
    rows: Sequence[Sequence[int]], start: int, k: int, *, rule: str = CLASSIC,
) -> NorthEmptyStrip:
    """Build and verify a certificate, raising ValueError when its conditions fail."""
    _classic(rule)
    h, w, flat = _rows(rows)
    east_rows, north_columns = _profiles(h, w, flat)
    certificate = NorthEmptyStrip(w, h, start, k, east_rows, north_columns)
    verify_strip_certificate(rows, certificate, rule=rule)
    return certificate


def ring_probability(width: int, height: int, p: Rational, *, rule: str = CLASSIC) -> Fraction:
    """Exact initial iid P(R), including singleton dimensions.

Full east rows are mutually independent, as are full north columns. An east
full row and a north full column cannot both occur because they intersect.
"""
    _classic(rule)
    w, h = _dimensions(width, height)
    q = _density(p) / 2
    return 2 - (1 - q ** w) ** h - (1 - q ** h) ** w


def strip_bound_terms(
    width: int, height: int, p: Rational, k: int, *, rule: str = CLASSIC,
) -> tuple[Fraction, Fraction, Fraction]:
    """Unclamped union-bound terms for the initial iid law.

The terms bound (some row has at least k east cars), (none of the floor(W/k)
disjoint k-column blocks is north-empty), and (some column is full north).
Only the disjoint block events in the middle term are treated as independent.
"""
    _classic(rule)
    w, h = _dimensions(width, height)
    k = _strip_width(k, w)
    q = _density(p) / 2
    row_tail = h * sum((Fraction(comb(w, n)) * q ** n * (1 - q) ** (w - n)
                        for n in range(k, w + 1)), Fraction())
    no_empty_block = (1 - (1 - q) ** (h * k)) ** (w // k)
    full_north_column = w * q ** h
    return row_tail, no_empty_block, full_north_column


def strip_upper_bound(
    width: int, height: int, p: Rational, k: int, *, rule: str = CLASSIC,
) -> Fraction:
    """Exact rational upper bound on eventual gridlock, clamped above at 1."""
    return min(Fraction(1), sum(strip_bound_terms(width, height, p, k, rule=rule), Fraction()))


@dataclass(frozen=True)
class EventCounts:
    """Counts by occupied-site count for one named event on a finite torus.

There are binom(N,n)*2**n colored configurations with n cars. Metadata and
capacity checks establish internal consistency only: constructing this object
does not prove that its supplied counts describe the named dynamical event.
``analyze_torus`` derives its counts from the complete transition graph.
"""

    width: int
    height: int
    name: str
    by_cars: tuple[int, ...]
    rule: str = CLASSIC

    def __post_init__(self) -> None:
        _classic(self.rule)
        w, h = _dimensions(self.width, self.height)
        if not isinstance(self.name, str) or self.name not in EVENT_NAMES:
            raise ValueError("unknown probability event name")
        n = w * h
        if (not isinstance(self.by_cars, tuple) or len(self.by_cars) != n + 1
                or any(not _integer(count) or not 0 <= count <= comb(n, k) * 2 ** k
                       for k, count in enumerate(self.by_cars))):
            raise ValueError("event counts must be bounded integers for every car-count layer")
        object.__setattr__(self, "width", w)
        object.__setattr__(self, "height", h)
        object.__setattr__(self, "by_cars", tuple(int(count) for count in self.by_cars))

    @property
    def total(self) -> int:
        return sum(self.by_cars)

    @property
    def coefficients(self) -> tuple[Fraction, ...]:
        """Bernstein coefficients: conditional event probabilities given n cars."""
        n = self.width * self.height
        return tuple(Fraction(count, comb(n, k) * 2 ** k)
                     for k, count in enumerate(self.by_cars))

    @property
    def coefficients_nondecreasing(self) -> bool:
        """A sufficient finite-ensemble monotonicity test, not a threshold result."""
        coefficients = self.coefficients
        return all(left <= right for left, right in zip(coefficients, coefficients[1:]))

    def probability(self, p: Rational) -> Fraction:
        p = _density(p)
        n = self.width * self.height
        return sum((count * (p / 2) ** k * (1 - p) ** (n - k)
                    for k, count in enumerate(self.by_cars)), Fraction())

    def derivative(self, p: Rational) -> Fraction:
        """Derivative of the exact iid probability polynomial, including endpoints."""
        p = _density(p)
        n = self.width * self.height
        coefficients = self.coefficients
        return n * sum(((coefficients[k + 1] - coefficients[k]) * comb(n - 1, k)
                        * p ** k * (1 - p) ** (n - 1 - k)
                        for k in range(n)), Fraction())


@dataclass(frozen=True)
class FiniteCensus:
    """Finite counts with arithmetic consistency checks, not an authenticity token."""

    width: int
    height: int
    events: tuple[EventCounts, ...]
    strip_certified_by_k: tuple[int, ...]
    strip_certified_union: int
    rule: str = CLASSIC

    def __post_init__(self) -> None:
        _classic(self.rule)
        w, h = _dimensions(self.width, self.height)
        if (not isinstance(self.events, tuple) or len(self.events) != len(EVENT_NAMES)
                or any(not isinstance(event, EventCounts)
                       or (event.width, event.height, event.rule) != (w, h, self.rule)
                       for event in self.events)
                or tuple(event.name for event in self.events) != EVENT_NAMES):
            raise ValueError("census events must have the exact names, order, rule, and dimensions")
        size = 3 ** (w * h)
        if (not isinstance(self.strip_certified_by_k, tuple)
                or len(self.strip_certified_by_k) != w
                or any(not _integer(count) or not 0 <= count <= size
                       for count in self.strip_certified_by_k)
                or not _integer(self.strip_certified_union)):
            raise ValueError("invalid strip counts or union count")
        # Integral includes fixed-width NumPy scalars. Normalize before powers,
        # products, or sums can silently overflow in later metadata operations.
        strip_counts = tuple(int(count) for count in self.strip_certified_by_k)
        strip_union = int(self.strip_certified_union)
        if not max(strip_counts) <= strip_union <= min(size, sum(strip_counts)):
            raise ValueError("invalid strip counts or union count")
        object.__setattr__(self, "width", w)
        object.__setattr__(self, "height", h)
        object.__setattr__(self, "strip_certified_by_k", strip_counts)
        object.__setattr__(self, "strip_certified_union", strip_union)
        j, m, m0, core, r, jr, rfree = (event.by_cars for event in self.events)
        for k in range(w * h + 1):
            capacity = comb(w * h, k) * 2 ** k
            if not (m[k] == jr[k] <= j[k] and m0[k] <= m[k] and m0[k] <= core[k]
                    and core[k] <= capacity and r[k] + rfree[k] == capacity
                    and j[k] - m[k] <= r[k] and m[k] <= rfree[k]):
                raise ValueError("inconsistent event counts; these do not verify the dynamics")
        if self.strip_certified_union > size - self.event("gridlock").total:
            raise ValueError("strip certificates cannot include gridlocked states")

    @property
    def states(self) -> int:
        return 3 ** (self.width * self.height)

    def event(self, name: str) -> EventCounts:
        if not isinstance(name, str) or name not in EVENT_NAMES:
            raise ValueError("unknown probability event name")
        return self.events[EVENT_NAMES.index(name)]


def eventually_reaches(successors: np.ndarray, targets: np.ndarray) -> np.ndarray:
    """Exact reachability in a complete finite functional graph, without a cutoff.

Inputs are one-dimensional arrays: integer successor indices and boolean target
flags of equal nonzero length. Pointer doubling covers at least every possible
distinct state on each orbit; a target may already hold at time zero.
"""
    if (not isinstance(successors, np.ndarray) or successors.ndim != 1
            or not np.issubdtype(successors.dtype, np.integer) or not len(successors)
            or np.any(successors < 0) or np.any(successors >= len(successors))
            or not isinstance(targets, np.ndarray) or targets.ndim != 1
            or targets.dtype != np.dtype(bool) or len(targets) != len(successors)):
        raise ValueError("expected a complete integer successor map and matching boolean targets")
    reached, power = targets.copy(), successors.copy()
    for _ in range((len(successors) - 1).bit_length()):
        reached = reached | reached[power]
        power = power[power]
    return reached


def analyze_torus(width: int, height: int, *, rule: str = CLASSIC) -> FiniteCensus:
    """Enumerate every CLASSIC configuration on a torus of at most twelve sites.

J is reachability of nonempty fixed points and is compared with the existing
final-phase classifier. M is independently obtained from direct mixed-cycle
detection followed by graph reachability. The identity M=J intersect R^c and
every strip-width obstruction are then checked pointwise, not assumed in the
event definitions. This finite census does not prove their universal versions.
"""
    _classic(rule)
    w, h = _dimensions(width, height)
    if w * h > MAX_ENUMERATION_CELLS:
        raise ValueError("exact enumeration is limited to twelve cells")
    size = 3 ** (w * h)
    codes = np.arange(size, dtype=np.int64)
    states = decode(codes, h, w)
    classification = classify_all(h, w, rule=rule)
    cars = np.count_nonzero(states, axis=(1, 2))
    east_rows = (states == 1).sum(axis=2)
    north_columns = (states == 2).sum(axis=1)
    r = (east_rows == w).any(axis=1) | (north_columns == h).any(axis=1)
    j0 = (classification.f == codes) & (cars > 0)
    j = eventually_reaches(classification.f, j0)
    if not np.array_equal(j, classification.cls == JAM):
        raise AssertionError("fixed-point reachability disagrees with the final-phase classifier")
    if (not np.array_equal(east_rows, east_rows[classification.f])
            or not np.array_equal(north_columns, north_columns[classification.f])):
        raise AssertionError("the transition map failed conserved lane counts")
    m0 = np.zeros(size, dtype=bool)
    core = np.zeros(size, dtype=bool)
    for code, state in enumerate(states):
        rows = state.tolist()
        cycles = find_blocker_cycles(rows, rule=rule)
        core[code] = bool(cycles)
        for cycle in cycles:
            if cycle.mixed:
                verify_cycle(rows, cycle, require_mixed=True, rule=rule)
                m0[code] = True
    m = eventually_reaches(classification.f, m0)
    if not np.array_equal(m, j & ~r):
        raise AssertionError("independently propagated M disagrees with J intersect R-complement")
    if np.any(m0 & ~m0[classification.f]):
        raise AssertionError("an initial mixed blocker cycle failed to persist")
    strip_counts = []
    certified_union = np.zeros(size, dtype=bool)
    zeros = north_columns == 0
    no_full_north = (north_columns < h).all(axis=1)
    for k in range(1, w + 1):
        starts = np.ones_like(zeros)
        for offset in range(k):
            starts &= np.roll(zeros, -offset, axis=1)
        certified = starts.any(axis=1) & (east_rows.max(axis=1) < k) & no_full_north
        if np.any(certified & j):
            raise AssertionError(f"a width-{k} north-empty strip certificate reaches gridlock")
        certified_union |= certified
        strip_counts.append(int(certified.sum()))
    masks = (j, m, m0, core, r, j & ~r, ~r)
    events = tuple(
        EventCounts(w, h, name, tuple(int(count) for count in
                    np.bincount(cars[mask], minlength=w * h + 1)))
        for name, mask in zip(EVENT_NAMES, masks)
    )
    return FiniteCensus(w, h, events, tuple(strip_counts), int(certified_union.sum()))
