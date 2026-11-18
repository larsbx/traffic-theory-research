"""Tagged fixation and exact initial-iid Palm probabilities for CLASSIC BML.

Z counts identities that never move on the exact recurrent labeled cycle, and
S is the event Z>0. The census obtains Z from the independent labeled replayer,
checks it again using recurrent identity positions, compares J with production
classification, and only then checks S=J union R. No later state is assumed iid.

Supplied orbit verification additionally checks every identity edge and every
production colored transition. The exhaustive census instead uses the trusted,
source-bound independent replayer and the complete production basin classifier.
Neither count-table construction nor bounded enumeration proves a universal or
asymptotic statement.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import comb
from numbers import Rational
from typing import Sequence

import numpy as np

from bml.capture import _validate_labeled_orbit
from bml.certificates import LabeledOrbit, trace_labeled
from bml.exhaustive import FREE, JAM, MIXED, classify_all, decode
from bml.model import CLASSIC, step
from bml.probability import (
    MAX_ENUMERATION_CELLS, EventCounts, _classic, _density, _dimensions,
    _integer, _profiles, _rows,
)


FIXATION_EVENTS = ("any_stopped", "gridlock", "full_lane", "partial_fixation")


def _positive_density(p: Rational) -> Fraction:
    p = _density(p)
    if p == 0:
        raise ValueError("Palm probabilities require p>0; conditioning on occupancy is undefined at p=0")
    return p


def _step_budget(max_steps: int) -> int:
    if not _integer(max_steps) or max_steps < 1:
        raise ValueError("the labeled recurrence budget must be a positive integer")
    return int(max_steps)


@dataclass(frozen=True)
class FixationTrace:
    """A computed orbit summary, not an authenticity token when constructed by hand."""

    width: int
    height: int
    car_count: int
    transient: int
    period: int
    transitions: int
    recurrent_moves: tuple[tuple[int, int], ...]
    stopped_labels: tuple[int, ...]
    full_lane: bool

    @property
    def stopped_count(self) -> int:
        return len(self.stopped_labels)

    @property
    def any_stopped(self) -> bool:
        return bool(self.stopped_labels)

    @property
    def gridlock(self) -> bool:
        return self.car_count > 0 and all(moves == 0 for _, moves in self.recurrent_moves)

    @property
    def free(self) -> bool:
        return all(moves == self.period for _, moves in self.recurrent_moves)

    @property
    def partial_fixation(self) -> bool:
        return 0 < self.stopped_count < self.car_count

    @property
    def speeds(self) -> tuple[tuple[int, Fraction], ...]:
        return tuple((label, Fraction(moves, self.period)) for label, moves in self.recurrent_moves)


def _summarize_generated_orbit(
    rows: Sequence[Sequence[int]], orbit: LabeledOrbit,
) -> FixationTrace:
    """Summarize a trusted generated recurrence with two independent Z readings.

This fast census path binds the exact input and checks recurrent movement data
against constant identity positions. For an externally supplied orbit use
``verify_fixation``, which also validates every identity and production edge.
"""
    h, w, flat = _rows(rows)
    if not isinstance(orbit, LabeledOrbit):
        raise ValueError("expected a labeled orbit")
    expected_species = tuple((i, species) for i, species in enumerate(flat) if species)
    expected_initial = tuple(i if species else -1 for i, species in enumerate(flat))
    if (not _integer(orbit.width) or not _integer(orbit.height)
            or (orbit.width, orbit.height) != (w, h)
            or not isinstance(orbit.species, tuple)
            or any(not isinstance(pair, tuple) or len(pair) != 2
                   or any(not _integer(v) for v in pair) for pair in orbit.species)
            or orbit.species != expected_species):
        raise ValueError("independent orbit dimensions or species disagree with the input")
    if (not isinstance(orbit.states, tuple) or not orbit.states
            or not isinstance(orbit.moved, tuple) or len(orbit.moved) != len(orbit.states)
            or not _integer(orbit.cycle_start) or not 0 <= orbit.cycle_start < len(orbit.states)
            or any(not isinstance(state, tuple) or len(state) != h * w for state in orbit.states)
            or orbit.states[0] != expected_initial):
        raise ValueError("independent orbit does not give the exact input and a recurrent labeled cycle")
    movements = {label: 0 for label, _ in expected_species}
    for edge in orbit.moved[orbit.cycle_start:]:
        if (not isinstance(edge, tuple)
                or any(not _integer(label) or label not in movements for label in edge)
                or len(set(edge)) != len(edge)):
            raise ValueError("recurrent moved identities must be distinct input identities")
        for label in edge:
            movements[label] += 1
    stopped_from_moves = tuple(label for label, moves in movements.items() if moves == 0)
    first = orbit.states[orbit.cycle_start]
    stopped_from_positions = tuple(sorted(
        label for cell, label in enumerate(first) if label >= 0
        and all(state[cell] == label for state in orbit.states[orbit.cycle_start + 1:])
    ))
    if stopped_from_moves != stopped_from_positions:
        raise ValueError("reported recurrent movement disagrees with constant identity positions")
    east_rows, north_columns = _profiles(h, w, flat)
    return FixationTrace(
        w, h, len(expected_species), int(orbit.cycle_start), int(orbit.period), len(orbit.moved),
        tuple(movements.items()), stopped_from_moves, w in east_rows or h in north_columns,
    )


def verify_fixation(
    rows: Sequence[Sequence[int]], orbit: LabeledOrbit, *, rule: str = CLASSIC,
) -> FixationTrace:
    """Verify a supplied exact labeled recurrence and derive its fixation events.

Every state must contain precisely the original identities. Every moved label
must take its own one-cell successor; unchanged labels stay put. Every colored
edge, including the closing edge, must match the CLASSIC production kernel.
"""
    _classic(rule)
    h, w, flat = _rows(rows)
    _validate_labeled_orbit(orbit, h, w, flat)
    for index in range(len(orbit.states)):
        following = index + 1 if index + 1 < len(orbit.states) else orbit.cycle_start
        actual, moves = step(np.asarray(orbit.rows(index), dtype=np.int8), rule=rule)
        expected = np.asarray(orbit.rows(following), dtype=np.int8)
        if not np.array_equal(actual, expected) or int(moves) != len(orbit.moved[index]):
            raise ValueError("the supplied labeled edge disagrees with CLASSIC production dynamics")
    return _summarize_generated_orbit(rows, orbit)


def trace_fixation(
    rows: Sequence[Sequence[int]], *, max_steps: int = 10000, rule: str = CLASSIC,
) -> FixationTrace:
    """Find and verify exact labeled recurrence; reject an unresolved cutoff."""
    _classic(rule)
    _rows(rows)
    orbit = trace_labeled(rows, max_steps=_step_budget(max_steps))
    return verify_fixation(rows, orbit, rule=rule)


def ring_palm_probability(
    width: int, height: int, p: Rational, *, rule: str = CLASSIC,
) -> Fraction:
    """Exact P(R | the origin is occupied), averaged over the two species.

The conditioning is on the initial iid law, not on a later traffic snapshot.
Singleton dimensions are allowed; p=0 is rejected even though a limit exists.
"""
    _classic(rule)
    w, h = _dimensions(width, height)
    u = _positive_density(p) / 2
    return (2 - (1 - u ** (w - 1) / 2) * (1 - u ** w) ** (h - 1)
            - (1 - u ** (h - 1) / 2) * (1 - u ** h) ** (w - 1))


@dataclass(frozen=True)
class PalmProbabilities:
    """Exact results from a supplied table; their dynamical meaning needs evidence."""

    p: Fraction
    f: Fraction  # E[Z] / (p*area)
    q: Fraction  # P(J)
    q_car: Fraction  # E[N * 1_J] / (p*area)
    delta: Fraction  # f - q_car, contributed by partially fixed states
    r_car: Fraction  # E[N * 1_R] / (p*area)
    score_rhs: Fraction  # q + (1-p)*q'/area
    covariance_lhs: Fraction  # (q_car-q)^2
    covariance_rhs: Fraction  # (1-p)*q*(1-q)/(p*area)


@dataclass(frozen=True)
class FixationCounts:
    """Exact histogram H[n][z] and independent J/R count tables.

H[n][z] counts states with n cars and z recurrently stopped identities. Each row
must partition all binom(area,n)*2**n colored configurations. Validation checks
arithmetic capacities and necessary event relations only; it does not certify
that an arbitrary supplied histogram describes CLASSIC dynamics.
"""

    width: int
    height: int
    stopped_histogram: tuple[tuple[int, ...], ...]
    gridlock_by_cars: tuple[int, ...]
    full_lane_by_cars: tuple[int, ...]
    rule: str = CLASSIC

    def __post_init__(self) -> None:
        _classic(self.rule)
        w, h = _dimensions(self.width, self.height)
        area = w * h
        capacities = tuple(comb(area, n) * 2 ** n for n in range(area + 1))
        if not isinstance(self.stopped_histogram, tuple) or len(self.stopped_histogram) != area + 1:
            raise ValueError("expected one stopped-count histogram row per car-count layer")
        histogram = []
        for n, row in enumerate(self.stopped_histogram):
            if (not isinstance(row, tuple) or len(row) != n + 1
                    or any(not _integer(count) for count in row)):
                raise ValueError("histogram entries must be integer counts for z=0,...,n")
            row = tuple(int(count) for count in row)
            if any(count < 0 or count > capacities[n] for count in row) or sum(row) != capacities[n]:
                raise ValueError("each histogram row must partition its complete colored-state layer")
            histogram.append(row)
        normalized = []
        for table in (self.gridlock_by_cars, self.full_lane_by_cars):
            if (not isinstance(table, tuple) or len(table) != area + 1
                    or any(not _integer(count) for count in table)):
                raise ValueError("J and R tables must contain one integer count per car-count layer")
            table = tuple(int(count) for count in table)
            if any(not 0 <= count <= capacity for count, capacity in zip(table, capacities)):
                raise ValueError("J or R counts exceed their colored-state layer")
            normalized.append(table)
        jam, ring = normalized
        for n, row in enumerate(histogram):
            stopped = sum(row[1:])
            partial = sum(row[1:n])  # Directly 0<Z<N, not inferred from R.
            if jam[n] != (row[n] if n else 0):
                raise ValueError("nonempty all-stopped counts must agree with the independent J table")
            if not partial <= ring[n] <= stopped:
                raise ValueError("supplied counts cannot satisfy S=J union R")
        object.__setattr__(self, "width", w)
        object.__setattr__(self, "height", h)
        object.__setattr__(self, "stopped_histogram", tuple(histogram))
        object.__setattr__(self, "gridlock_by_cars", jam)
        object.__setattr__(self, "full_lane_by_cars", ring)

    @property
    def states(self) -> int:
        return 3 ** (self.width * self.height)

    @property
    def any_stopped_by_cars(self) -> tuple[int, ...]:
        return tuple(sum(row[1:]) for row in self.stopped_histogram)

    @property
    def partial_fixation_by_cars(self) -> tuple[int, ...]:
        return tuple(sum(row[1:n]) for n, row in enumerate(self.stopped_histogram))

    @property
    def stopped_tags_by_cars(self) -> tuple[int, ...]:
        return tuple(sum(z * count for z, count in enumerate(row)) for row in self.stopped_histogram)

    @property
    def gridlock_event(self) -> EventCounts:
        return EventCounts(self.width, self.height, "gridlock", self.gridlock_by_cars, self.rule)

    def _initial_expectation(self, weights: tuple[int, ...], p: Fraction) -> Fraction:
        area = self.width * self.height
        return sum((weight * (p / 2) ** n * (1 - p) ** (area - n)
                    for n, weight in enumerate(weights)), Fraction())

    def event_probability(self, name: str, p: Rational) -> Fraction:
        if not isinstance(name, str) or name not in FIXATION_EVENTS:
            raise ValueError("unknown fixation event name")
        p = _density(p)
        tables = (self.any_stopped_by_cars, self.gridlock_by_cars,
                  self.full_lane_by_cars, self.partial_fixation_by_cars)
        return self._initial_expectation(tables[FIXATION_EVENTS.index(name)], p)

    def palm(self, p: Rational) -> PalmProbabilities:
        """Exact initial-law Palm quantities, defined only for 0<p<=1.

The identities use translation invariance and species-averaged occupancy
conditioning when these tables come from the complete finite torus census.
The score identity and covariance calculation use the initial Bin(area,p) law.
"""
        p = _positive_density(p)
        area = self.width * self.height
        denominator = p * area
        q = self.gridlock_event.probability(p)
        f = self._initial_expectation(self.stopped_tags_by_cars, p) / denominator
        q_car = self._initial_expectation(tuple(n * count for n, count in
                                             enumerate(self.gridlock_by_cars)), p) / denominator
        r_car = self._initial_expectation(tuple(n * count for n, count in
                                             enumerate(self.full_lane_by_cars)), p) / denominator
        return PalmProbabilities(
            p, f, q, q_car, f - q_car, r_car,
            q + (1 - p) * self.gridlock_event.derivative(p) / area,
            (q_car - q) ** 2, (1 - p) * q * (1 - q) / denominator,
        )


@dataclass(frozen=True)
class FixationCensus:
    """Computed counts plus finite replay statistics; not a universal certificate."""

    counts: FixationCounts
    tagged_edges: int
    max_labeled_period: int
    max_transient: int
    outside_ring_intermediate: int

    def __post_init__(self) -> None:
        if not isinstance(self.counts, FixationCounts):
            raise ValueError("expected validated fixation count metadata")
        names = ("tagged_edges", "max_labeled_period", "max_transient", "outside_ring_intermediate")
        if any(not _integer(getattr(self, name)) or getattr(self, name) < 0 for name in names):
            raise ValueError("replay statistics must be nonnegative integers")
        for name in names:
            object.__setattr__(self, name, int(getattr(self, name)))
        if (self.tagged_edges < self.counts.states or self.max_labeled_period < 1
                or self.outside_ring_intermediate > self.counts.states):
            raise ValueError("replay statistics are inconsistent with the census domain")


def analyze_fixation(
    width: int, height: int, *, max_steps: int = 10000, rule: str = CLASSIC,
) -> FixationCensus:
    """Independently replay every labeled orbit on a torus of at most 12 cells.

An exhausted recurrence budget raises ValueError: it is never classified as a
final event. S, Z and partial fixation come directly from recurrent identities.
J and FREE are reconstructed from recurrent movement before comparison with
the existing production classifier. S=J union R is then checked pointwise.
"""
    _classic(rule)
    w, h = _dimensions(width, height)
    budget = _step_budget(max_steps)
    area = w * h
    if area > MAX_ENUMERATION_CELLS:
        raise ValueError("exact fixation enumeration is limited to twelve cells")
    states = decode(np.arange(3 ** area, dtype=np.int64), h, w)
    classification = classify_all(h, w, rule=rule)
    histogram = [[0] * (n + 1) for n in range(area + 1)]
    jam = [0] * (area + 1)
    ring = [0] * (area + 1)
    tagged_edges = max_period = max_transient = outside_intermediate = 0
    for code, state in enumerate(states):
        rows = state.tolist()
        orbit = trace_labeled(rows, max_steps=budget)
        result = _summarize_generated_orbit(rows, orbit)
        if result.gridlock != (classification.cls[code] == JAM):
            raise AssertionError(f"state {code}: labeled J disagrees with production classification")
        if result.free != (classification.cls[code] == FREE):
            raise AssertionError(f"state {code}: labeled FREE disagrees with production classification")
        if result.any_stopped != (result.gridlock or result.full_lane):
            raise AssertionError(f"state {code}: independently derived S disagrees with J union R")
        if not result.full_lane and classification.cls[code] == MIXED:
            if any(moves <= 0 for _, moves in result.recurrent_moves):
                raise AssertionError("an outside-R intermediate orbit has a stopped identity")
            outside_intermediate += 1
        n, z = result.car_count, result.stopped_count
        histogram[n][z] += 1
        jam[n] += int(result.gridlock)
        ring[n] += int(result.full_lane)
        tagged_edges += result.transitions
        max_period = max(max_period, result.period)
        max_transient = max(max_transient, result.transient)
    counts = FixationCounts(w, h, tuple(tuple(row) for row in histogram), tuple(jam), tuple(ring), rule)
    return FixationCensus(counts, tagged_edges, max_period, max_transient, outside_intermediate)
