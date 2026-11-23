"""Occupied direct paths, maximal frozen cores, and exact late-time bounds.

``steps`` always counts directed edges: zero steps tests the occupied root,
and ``steps=area`` tests area+1 occupied vertices. Following the car's own
direction at every occupied site gives a functional graph. Pruning everything
that leads to a hole leaves its maximal forward-closed occupied set, the frozen
core. Shorter path masks may contain cars that continue moving forever.

The census uses initial iid weights only. Its time average is over the exact
terminal cycle, never an observed finite prefix. Population-law upper bounds
are conditional on an independently established late-time input; evaluating
their arithmetic does not establish that input or a positive-density theorem.
"""
from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from math import comb
from numbers import Rational
from typing import Sequence

import numpy as np

from bml.certificates import trace_labeled
from bml.exhaustive import FREE, JAM, classify_all, decode
from bml.fixation import _step_budget, _summarize_generated_orbit
from bml.model import CLASSIC, EAST, NORTH
from bml.probability import (
    MAX_ENUMERATION_CELLS, _classic, _density, _dimensions, _integer, _rows,
)


Mask = tuple[tuple[bool, ...], ...]


def _steps(steps: int) -> int:
    if not _integer(steps) or steps < 0:
        raise ValueError("path steps must be a nonnegative integer edge count")
    return int(steps)


def _nonnegative_rational(value: Rational) -> Fraction:
    if (isinstance(value, (bool, np.bool_)) or not isinstance(value, Rational)
            or value < 0):
        raise ValueError("the supplied bound must be an exact nonnegative rational")
    return Fraction(int(value.numerator), int(value.denominator))


def _successors(height: int, width: int, flat: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(
        (i // width) * width + (i % width + 1) % width if species == EAST
        else ((i // width + 1) % height) * width + i % width
        for i, species in enumerate(flat)
    )


def _mask(flat: Sequence[bool], width: int) -> Mask:
    return tuple(tuple(bool(v) for v in flat[i:i + width])
                 for i in range(0, len(flat), width))


def direct_path_mask(
    rows: Sequence[Sequence[int]], steps: int, *, rule: str = CLASSIC,
) -> Mask:
    """Roots whose static direct path has ``steps`` edges and no empty vertex.

Repeated vertices are allowed. The recurrence stabilizes on a finite board,
so even a very large edge count terminates after at most area pruning rounds.
This is a property of this snapshot, not a claim that the path moves with cars.
"""
    _classic(rule)
    h, w, flat = _rows(rows)
    steps = _steps(steps)
    occupied = tuple(bool(cell) for cell in flat)
    successors = _successors(h, w, flat)
    current = occupied
    for _ in range(min(steps, h * w)):
        following = tuple(occupied[i] and current[target]
                          for i, target in enumerate(successors))
        if following == current:
            break
        current = following
    return _mask(current, w)


def direct_path_count(
    rows: Sequence[Sequence[int]], steps: int, *, rule: str = CLASSIC,
) -> int:
    """Number of roots in ``direct_path_mask``; steps counts edges."""
    return sum(sum(row) for row in direct_path_mask(rows, steps, rule=rule))


def scalar_path_mask(
    rows: Sequence[Sequence[int]], steps: int, *, rule: str = CLASSIC,
) -> Mask:
    """Independent scalar oracle: walk each root until a hole or a repetition.

This does not call the mask recurrence, successor-table helper, or core pruner.
The seen set is only an exact shortcut after an occupied vertex repeats.
"""
    _classic(rule)
    h, w, flat = _rows(rows)
    steps = _steps(steps)
    answer = []
    for origin in range(h * w):
        x, y = origin % w, origin // w
        seen = set()
        remaining = steps
        while True:
            species = flat[y * w + x]
            if not species:
                answer.append(False)
                break
            if remaining == 0 or (x, y) in seen:
                answer.append(True)
                break
            seen.add((x, y))
            if species == EAST:
                x = (x + 1) % w
            else:
                y = (y + 1) % h
            remaining -= 1
    return _mask(answer, w)


def maximal_frozen_core(
    rows: Sequence[Sequence[int]], *, rule: str = CLASSIC,
) -> Mask:
    """Maximal occupied forward-closed set, including feeders into its cycles.

Reverse-graph pruning starts from all holes and removes every occupied vertex
that eventually reaches one. The remaining car identities stay put under
CLASSIC. Later dynamics can add new sites to the core.
"""
    _classic(rule)
    h, w, flat = _rows(rows)
    predecessors: list[list[int]] = [[] for _ in flat]
    for cell, target in enumerate(_successors(h, w, flat)):
        if flat[cell]:
            predecessors[target].append(cell)
    alive = [bool(cell) for cell in flat]
    removed = deque(i for i, occupied in enumerate(alive) if not occupied)
    while removed:
        target = removed.popleft()
        for source in predecessors[target]:
            if alive[source]:
                alive[source] = False
                removed.append(source)
    return _mask(alive, w)


def core_count(rows: Sequence[Sequence[int]], *, rule: str = CLASSIC) -> int:
    return sum(sum(row) for row in maximal_frozen_core(rows, rule=rule))


def population_event_upper_bound(
    area: int, p: Rational, weighted_event_budget: Rational, *, minimum_population: int = 1,
) -> Fraction:
    """Sharp population-law relaxation given E[N 1_J] <= the supplied budget.

N has the initial Binomial(area,p) law and J requires N>=minimum_population.
The exact minimum runs over all integer cutoffs and the eligible population
tail. It is sharp among abstract events with these two constraints; it is not
asserted sharp for BML. A budget above area is allowed as a loose valid bound.
"""
    if not _integer(area) or area < 1:
        raise ValueError("area must be a positive integer")
    area = int(area)
    if not _integer(minimum_population) or not 1 <= minimum_population <= area:
        raise ValueError("minimum population must be an integer between one and area")
    minimum_population = int(minimum_population)
    p = _density(p)
    budget = _nonnegative_rational(weighted_event_budget)
    masses = tuple(Fraction(comb(area, n)) * p ** n * (1 - p) ** (area - n)
                   for n in range(area + 1))
    best = sum(masses[minimum_population:], Fraction())
    prefix_probability = prefix_population = Fraction()
    for cutoff in range(minimum_population, area + 1):
        best = min(best, prefix_probability + (budget - prefix_population) / cutoff)
        prefix_probability += masses[cutoff]
        prefix_population += cutoff * masses[cutoff]
    return best


def path_mass_gridlock_upper_bound(
    width: int, height: int, p: Rational, late_path_mass_bound: Rational, *, rule: str = CLASSIC,
) -> Fraction:
    """Conditional bound using an ESTABLISHED late-time root-path mass bound.

The input bounds a late-time liminf or limiting Cesaro mean of
E[C_d(S_t)]/(width*height), under the initial iid law, where C_d counts occupied
direct-path roots. The denominator includes every site, including holes. It
may instead bound E[|K_infinity|]/(width*height), the eventual core per site.
The separate normalized observable E[|K_infinity|/N; N>0] has a per-car
denominator. Any fixed finite path length d is valid here, since every occupied
root in a final jam has every such path.

A finite-prefix estimate, an initial snapshot value, or a single-time sample
does NOT supply this hypothesis. This function checks exact arithmetic only;
calling it does not certify the supplied research assumption. It uses the
necessary CLASSIC jam population N>=min(width,height).
"""
    _classic(rule)
    w, h = _dimensions(width, height)
    bound = _nonnegative_rational(late_path_mass_bound)
    return population_event_upper_bound(w * h, p, w * h * bound,
                                        minimum_population=min(w, h))


def _terminal_averages(successors, observations):
    """Exact functional-graph cycle means; transient observations are excluded."""
    size = len(successors)
    representative = [-1] * size
    distance = [0] * size
    cycle_means = {}
    max_period = 0
    for start in range(size):
        if representative[start] >= 0:
            continue
        path, positions = [], {}
        node = start
        while representative[node] < 0 and node not in positions:
            positions[node] = len(path)
            path.append(node)
            node = int(successors[node])
        if representative[node] >= 0:
            prefix = path
            root = representative[node]
            depth = distance[node]
        else:
            cut = positions[node]
            prefix, cycle = path[:cut], path[cut:]
            root = min(cycle)
            cycle_means[root] = tuple(Fraction(sum(values[i] for i in cycle), len(cycle))
                                     for values in observations)
            max_period = max(max_period, len(cycle))
            for cell in cycle:
                representative[cell] = root
            depth = 0
        for cell in reversed(prefix):
            depth += 1
            representative[cell], distance[cell] = root, depth
    means = tuple(tuple(cycle_means[root][j] for root in representative)
                  for j in range(len(observations)))
    return means, len(cycle_means), max_period, max(distance)


@dataclass(frozen=True)
class PathCoreProbabilities:
    p: Fraction
    initial_path_mass: Fraction
    one_round_path_mass: Fraction
    recurrent_path_mass: Fraction
    initial_core_mass: Fraction
    final_core_mass: Fraction
    normalized_final_core_mass: Fraction  # E[K_infinity/N], with empty value zero
    gridlock_probability: Fraction
    gridlock_root_mass: Fraction  # E[N 1_J]/area, not q or the Palm probability
    full_lane_nonjam_probability: Fraction
    path_population_upper_bound: Fraction
    core_population_upper_bound: Fraction


@dataclass(frozen=True)
class PathCoreCounts:
    """Population-layer sums; internal consistency does not authenticate dynamics.

Path and core tables count roots over initial states, while J and R-minus-J tables
count initial states. Recurrent path entries can be fractional because each
initial state receives the mean on its own terminal cycle.
"""

    width: int
    height: int
    steps: int
    initial_path_by_cars: tuple[int, ...]
    one_round_path_by_cars: tuple[int, ...]
    recurrent_path_by_cars: tuple[Fraction, ...]
    initial_core_by_cars: tuple[int, ...]
    final_core_by_cars: tuple[int, ...]
    gridlock_by_cars: tuple[int, ...]
    full_lane_nonjam_by_cars: tuple[int, ...]
    rule: str = CLASSIC

    def __post_init__(self):
        _classic(self.rule)
        w, h = _dimensions(self.width, self.height)
        object.__setattr__(self, "width", w)
        object.__setattr__(self, "height", h)
        object.__setattr__(self, "steps", _steps(self.steps))
        area = w * h
        root_tables = ("initial_path_by_cars", "one_round_path_by_cars",
                       "recurrent_path_by_cars", "initial_core_by_cars", "final_core_by_cars")
        for name in root_tables + ("gridlock_by_cars", "full_lane_nonjam_by_cars"):
            table = getattr(self, name)
            if not isinstance(table, tuple) or len(table) != area + 1:
                raise ValueError("tables require one entry per initial population layer")
            if name == "recurrent_path_by_cars":
                table = tuple(_nonnegative_rational(value) for value in table)
            else:
                if any(not _integer(value) or value < 0 for value in table):
                    raise ValueError("count tables require nonnegative integers")
                table = tuple(int(value) for value in table)
            for n, value in enumerate(table):
                capacity = comb(area, n) * 2 ** n * (n if name in root_tables else 1)
                if value > capacity:
                    raise ValueError("a count exceeds its population-layer capacity")
            object.__setattr__(self, name, table)
        for n in range(area + 1):
            initial, final = self.initial_core_by_cars[n], self.final_core_by_cars[n]
            jam, ring_nonjam = self.gridlock_by_cars[n], self.full_lane_nonjam_by_cars[n]
            if n < min(w, h) and jam:
                raise ValueError("gridlock requires the minimum torus population")
            if (not initial <= self.initial_path_by_cars[n]
                    or not initial <= final <= self.recurrent_path_by_cars[n]
                    or not n * jam <= final <= n * (jam + ring_nonjam)):
                raise ValueError("core, path, gridlock and partial-fixation tables disagree")
            if jam + ring_nonjam > comb(area, n) * 2 ** n:
                raise ValueError("disjoint event counts exceed the initial-state layer")

    @property
    def states(self) -> int:
        return 3 ** (self.width * self.height)

    def evaluate(self, p: Rational) -> PathCoreProbabilities:
        """Integrate supplied tables against exact INITIAL iid weights."""
        p = _density(p)
        area = self.width * self.height
        weights = tuple((p / 2) ** n * (1 - p) ** (area - n) for n in range(area + 1))

        def mass(table):
            return sum((value * weight for value, weight in zip(table, weights)), Fraction())

        initial_path = mass(self.initial_path_by_cars) / area
        one_round_path = mass(self.one_round_path_by_cars) / area
        recurrent_path = mass(self.recurrent_path_by_cars) / area
        initial_core = mass(self.initial_core_by_cars) / area
        final_core = mass(self.final_core_by_cars) / area
        normalized = sum((Fraction(self.final_core_by_cars[n], n) * weights[n]
                          for n in range(1, area + 1)), Fraction())
        q = mass(self.gridlock_by_cars)
        q_root = mass(tuple(n * count for n, count in enumerate(self.gridlock_by_cars))) / area
        return PathCoreProbabilities(
            p, initial_path, one_round_path, recurrent_path, initial_core, final_core,
            normalized, q, q_root, mass(self.full_lane_nonjam_by_cars),
            path_mass_gridlock_upper_bound(self.width, self.height, p, recurrent_path),
            path_mass_gridlock_upper_bound(self.width, self.height, p, final_core),
        )

    def path_polynomial(self, time: str) -> tuple[Fraction, ...]:
        """Ascending p-coefficients for initial, one_round, or recurrent path mass."""
        if time not in ("initial", "one_round", "recurrent"):
            raise ValueError("path time must be initial, one_round or recurrent")
        table = getattr(self, f"{time}_path_by_cars")
        area = self.width * self.height
        coefficients = [Fraction()] * (area + 1)
        for n, count in enumerate(table):
            scale = Fraction(count, area * 2 ** n)
            for k in range(area - n + 1):
                coefficients[n + k] += scale * comb(area - n, k) * (-1) ** k
        return tuple(coefficients)


@dataclass(frozen=True)
class PathCoreCensus:
    counts: PathCoreCounts
    colored_cycles: int
    max_colored_period: int
    max_colored_transient: int
    tagged_edges: int
    max_labeled_period: int
    max_labeled_transient: int
    core_growth_states: int
    recurrent_path_without_core_states: int
    recurrent_path_nonjam_ringless_states: int


def analyze_path_core(
    width: int, height: int, *, steps: int, max_steps: int = 10000, rule: str = CLASSIC,
) -> PathCoreCensus:
    """Exhaust the finite domain and independently check geometry and identities.

Each state receives its exact terminal-cycle path mean. The independent scalar
identity replayer checks every colored edge, the absence of movements of core
tags, the final core's exact stopped-label set, and the terminal-cycle average.
No exhausted recurrence budget is assigned an eventual classification.
"""
    _classic(rule)
    w, h = _dimensions(width, height)
    steps, budget, area = _steps(steps), _step_budget(max_steps), w * h
    if area > MAX_ENUMERATION_CELLS:
        raise ValueError("exact path-core enumeration is limited to twelve cells")
    size = 3 ** area
    states = decode(np.arange(size, dtype=np.int64), h, w)
    classification = classify_all(h, w, rule=rule)
    paths = np.empty((size, area), dtype=bool)
    cores = np.empty((size, area), dtype=bool)
    for code, state in enumerate(states):
        rows = state.tolist()
        path = direct_path_mask(rows, steps)
        core = maximal_frozen_core(rows)
        population = int(np.count_nonzero(state))
        if path != scalar_path_mask(rows, steps):
            raise AssertionError(f"state {code}: direct-path recurrence disagrees with scalar walk")
        if (core != direct_path_mask(rows, area) or core != scalar_path_mask(rows, area)
                or core != direct_path_mask(rows, population)):
            raise AssertionError(f"state {code}: pruned core disagrees with long occupied paths")
        paths[code], cores[code] = np.asarray(path).ravel(), np.asarray(core).ravel()
    following = classification.f.astype(np.int64)
    if np.any(cores & ~cores[following]):
        raise AssertionError("the frozen core shrinks under a CLASSIC round")
    flat = states.reshape(size, area)
    if np.any(cores & (flat != flat[following])):
        raise AssertionError("a core site changes species under a CLASSIC round")
    path_counts = tuple(int(n) for n in paths.sum(axis=1))
    core_counts = tuple(int(n) for n in cores.sum(axis=1))
    path_origins = tuple(int(n) for n in paths[:, 0])
    (means, cycles, max_period, max_transient) = _terminal_averages(
        following, (path_counts, path_origins, core_counts))
    cycle_path, cycle_origin, cycle_core = means
    tables = {name: [Fraction() if name == "recurrent_path_by_cars" else 0] * (area + 1)
              for name in ("initial_path_by_cars", "one_round_path_by_cars",
                           "recurrent_path_by_cars", "initial_core_by_cars",
                           "final_core_by_cars", "gridlock_by_cars", "full_lane_nonjam_by_cars")}
    origin_initial = [0] * (area + 1)
    origin_one_round = [0] * (area + 1)
    origin_recurrent = [Fraction()] * (area + 1)
    tagged_edges = max_labeled_period = max_labeled_transient = growth = 0
    short_without_core = ringless_short_nonjam = 0
    powers = tuple(3 ** i for i in range(area))
    for code, state in enumerate(states):
        rows = state.tolist()
        orbit = trace_labeled(rows, max_steps=budget)
        summary = _summarize_generated_orbit(rows, orbit)
        if summary.gridlock != (classification.cls[code] == JAM):
            raise AssertionError(f"state {code}: independent labeled and production gridlock disagree")
        if summary.free != (classification.cls[code] == FREE):
            raise AssertionError(f"state {code}: independent labeled and production free flow disagree")
        colors = dict(orbit.species)
        orbit_codes = tuple(sum(colors[label] * power for label, power in zip(labels, powers)
                                if label >= 0) for labels in orbit.states)
        for index, (labels, snapshot) in enumerate(zip(orbit.states, orbit_codes)):
            next_index = index + 1 if index + 1 < len(orbit.states) else orbit.cycle_start
            if int(following[snapshot]) != orbit_codes[next_index]:
                raise AssertionError(f"state {code}: independent colored edge disagrees with production")
            core_tags = {label for label, keep in zip(labels, cores[snapshot]) if keep}
            if core_tags.intersection(orbit.moved[index]):
                raise AssertionError(f"state {code}: a frozen-core identity moved")
        terminal = orbit_codes[orbit.cycle_start]
        final_tags = tuple(sorted(label for label, keep in
                                 zip(orbit.states[orbit.cycle_start], cores[terminal]) if keep))
        if final_tags != summary.stopped_labels or cycle_core[code] != len(final_tags):
            raise AssertionError(f"state {code}: final core disagrees with stopped original identities")
        if bool(final_tags) != (summary.gridlock or summary.full_lane):
            raise AssertionError(f"state {code}: final core event disagrees with gridlock or a full lane")
        recurrent_codes = orbit_codes[orbit.cycle_start:]
        if cycle_path[code] != Fraction(sum(path_counts[i] for i in recurrent_codes), orbit.period):
            raise AssertionError(f"state {code}: colored and labeled terminal-cycle path means disagree")
        if cycle_origin[code] != Fraction(sum(path_origins[i] for i in recurrent_codes), orbit.period):
            raise AssertionError(f"state {code}: colored and labeled terminal-cycle root means disagree")
        n, final_size = summary.car_count, len(final_tags)
        values = (path_counts[code], path_counts[following[code]], cycle_path[code],
                  core_counts[code], final_size, int(summary.gridlock),
                  int(summary.full_lane and not summary.gridlock))
        for name, value in zip(tables, values):
            tables[name][n] += value
        origin_initial[n] += path_origins[code]
        origin_one_round[n] += path_origins[following[code]]
        origin_recurrent[n] += cycle_origin[code]
        tagged_edges += len(orbit.moved)
        max_labeled_period = max(max_labeled_period, orbit.period)
        max_labeled_transient = max(max_labeled_transient, orbit.cycle_start)
        growth += int(final_size > core_counts[code])
        short_without_core += int(cycle_path[code] > 0 and not final_size)
        ringless_short_nonjam += int(cycle_path[code] > 0 and not summary.gridlock and not summary.full_lane)
    # Complete population layers are translation invariant under the initial law.
    for origin_table, name in ((origin_initial, "initial_path_by_cars"),
                               (origin_one_round, "one_round_path_by_cars"),
                               (origin_recurrent, "recurrent_path_by_cars")):
        if any(area * root != total for root, total in zip(origin_table, tables[name])):
            raise AssertionError("a fixed-origin law disagrees with the spatially averaged root count")
    counts = PathCoreCounts(w, h, steps, **{name: tuple(table) for name, table in tables.items()})
    return PathCoreCensus(counts, cycles, max_period, max_transient, tagged_edges,
                          max_labeled_period, max_labeled_transient, growth,
                          short_without_core, ringless_short_nonjam)
