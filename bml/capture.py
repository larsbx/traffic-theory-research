"""Persistent blocker certificates and formation/capture observations for CLASSIC BML.

Cells are row-major integer indices; north increases y, as in ``bml.model``.
The cycle checker is a static certificate verifier. Capture verification replays
car identities independently, then compares each edge with the production kernel.
The event tracer reports exact recurrence or an explicitly unresolved cutoff.
No frequency estimate or critical-density claim is made by this module.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from numbers import Integral
from typing import Sequence

import numpy as np

from bml.certificates import LabeledOrbit, _ahead, _grid, trace_labeled
from bml.model import CLASSIC, is_fixed, step


def _classic(rule: str) -> None:
    if rule != CLASSIC:
        raise ValueError("capture certificates require the CLASSIC update rule")


def _integer(value: object) -> bool:
    return isinstance(value, Integral) and not isinstance(value, (bool, np.bool_))


@dataclass(frozen=True)
class BlockerCycle:
    """A simple occupied cycle, with claimed source directions and winding."""

    height: int
    width: int
    cells: tuple[int, ...]
    directions: tuple[int, ...]
    winding: tuple[int, int]  # (east turns around width, north turns around height)

    @property
    def mixed(self) -> bool:
        """A claim until ``verify_cycle`` checks the certificate against a grid."""
        return self.winding[0] > 0 and self.winding[1] > 0


def verify_cycle(
    rows: Sequence[Sequence[int]],
    certificate: BlockerCycle,
    *,
    require_mixed: bool = False,
    rule: str = CLASSIC,
) -> None:
    """Reject malformed, stale, or geometrically invalid blocker certificates.

The final edge must return to the first cell, with no repeated vertex in the
listed cycle. Mixed cycles additionally cover every row and every column.
"""
    _classic(rule)
    h, w, flat = _grid(rows)
    if not isinstance(certificate, BlockerCycle):
        raise ValueError("expected a BlockerCycle certificate")
    if (not _integer(certificate.height) or not _integer(certificate.width)
            or (certificate.height, certificate.width) != (h, w)):
        raise ValueError("certificate dimensions disagree with the grid")
    cells, directions = certificate.cells, certificate.directions
    if (not isinstance(cells, tuple) or not cells
            or any(not _integer(i) or not 0 <= i < h * w for i in cells)
            or len(set(cells)) != len(cells)):
        raise ValueError("cycle cells must be nonempty, distinct, in-range integers")
    if (not isinstance(directions, tuple) or len(directions) != len(cells)
            or any(not _integer(d) or d not in (1, 2) for d in directions)):
        raise ValueError("cycle directions must specify one species per cell")
    for offset, (cell, direction) in enumerate(zip(cells, directions)):
        if flat[cell] != direction:
            raise ValueError("certificate direction disagrees with the occupied source")
        if _ahead(cell, direction, h, w) != cells[(offset + 1) % len(cells)]:
            raise ValueError("cycle edge does not point to the next occupied blocker")
    east, north = directions.count(1), directions.count(2)
    if east % w or north % h:
        raise ValueError("cycle displacement does not close on the torus")
    winding = certificate.winding
    if (not isinstance(winding, tuple) or len(winding) != 2
            or any(not _integer(v) or v < 0 for v in winding)
            or tuple(winding) != (east // w, north // h)):
        raise ValueError("claimed winding disagrees with the cycle displacement")
    if require_mixed:
        if not certificate.mixed:
            raise ValueError("a monochromatic core does not certify global capture")
        if ({i // w for i in cells} != set(range(h))
                or {i % w for i in cells} != set(range(w))):
            raise ValueError("a mixed capture cycle must cover every row and column")


def find_blocker_cycles(
    rows: Sequence[Sequence[int]], *, rule: str = CLASSIC,
) -> tuple[BlockerCycle, ...]:
    """Find all simple occupied-target cycles, including monochromatic cores.

Each cycle is rotated to start at its least cell index and is returned once.
The scan is linear in the number of sites; chains ending at holes are discarded.
"""
    _classic(rule)
    h, w, flat = _grid(rows)
    done: set[int] = set()
    cycles = []
    for start, species in enumerate(flat):
        if not species or start in done:
            continue
        positions: dict[int, int] = {}
        path = []
        current = start
        while flat[current] and current not in done:
            if current in positions:
                cells = path[positions[current]:]
                first = cells.index(min(cells))
                cells = tuple(cells[first:] + cells[:first])
                directions = tuple(flat[i] for i in cells)
                cycles.append(BlockerCycle(
                    h, w, cells, directions,
                    (directions.count(1) // w, directions.count(2) // h),
                ))
                break
            positions[current] = len(path)
            path.append(current)
            current = _ahead(current, flat[current], h, w)
        done.update(path)
    return tuple(sorted(cycles, key=lambda cycle: cycle.cells))


@dataclass(frozen=True)
class CaptureCheck:
    certificate: BlockerCycle
    move_budget: int
    rounds_to_gridlock: int
    total_moves: int
    rank_history: tuple[int, ...]
    final_rows: tuple[tuple[int, ...], ...]


def _validate_labeled_orbit(
    orbit: LabeledOrbit, h: int, w: int, flat: tuple[int, ...],
) -> list[dict[int, int]]:
    """Bind the replay to the input and validate every individual identity edge.

Color equality and a summed rank cannot detect same-species identity swaps.
The independent replayer is therefore checked at the identity level too.
"""
    if not isinstance(orbit, LabeledOrbit):
        raise ValueError("expected an independent labeled orbit")
    if (not _integer(orbit.height) or not _integer(orbit.width)
            or (orbit.height, orbit.width) != (h, w)):
        raise ValueError("independent replay dimensions disagree with the exact input")
    expected_species = tuple((i, species) for i, species in enumerate(flat) if species)
    expected_initial = tuple(i if species else -1 for i, species in enumerate(flat))
    if (not isinstance(orbit.species, tuple)
            or any(not isinstance(pair, tuple) or len(pair) != 2
                   or any(not _integer(value) for value in pair) for pair in orbit.species)
            or orbit.species != expected_species):
        raise ValueError("independent replay species disagree with the exact input")
    if (not isinstance(orbit.states, tuple) or not orbit.states
            or not isinstance(orbit.moved, tuple) or len(orbit.moved) != len(orbit.states)
            or not _integer(orbit.cycle_start) or not 0 <= orbit.cycle_start < len(orbit.states)):
        raise ValueError("malformed independent orbit states, edges, or cycle index")
    if orbit.states[0] != expected_initial:
        raise ValueError("independent replay initial identities disagree with the exact input")
    expected_labels = [label for label, _ in expected_species]
    expected_set = set(expected_labels)
    positions = []
    for state in orbit.states:
        if (not isinstance(state, tuple) or len(state) != h * w
                or any(not _integer(label) or label < -1 for label in state)
                or sorted(label for label in state if label >= 0) != expected_labels):
            raise ValueError("every replay state must contain the complete, distinct input identities")
        positions.append({label: cell for cell, label in enumerate(state) if label >= 0})
    if tuple(value for row in orbit.rows(0) for value in row) != flat:
        raise ValueError("independent replay colors disagree with the exact input")
    for index, moved in enumerate(orbit.moved):
        if (not isinstance(moved, tuple)
                or any(not _integer(label) or label not in expected_set for label in moved)
                or len(set(moved)) != len(moved)):
            raise ValueError("reported moved identities must be distinct input identities")
        following = index + 1 if index + 1 < len(positions) else orbit.cycle_start
        changed = {label for label in expected_labels
                   if positions[index][label] != positions[following][label]}
        if set(moved) != changed:
            raise ValueError("reported moved identities disagree with individual position changes")
        for label, species in expected_species:
            source = positions[index][label]
            expected = _ahead(source, species, h, w) if label in changed else source
            if positions[following][label] != expected:
                raise ValueError("a car identity did not take its own one-cell successor")
    return positions


def verify_capture(
    rows: Sequence[Sequence[int]], certificate: BlockerCycle, *, rule: str = CLASSIC,
) -> CaptureCheck:
    """Replay and verify a mixed cycle's persistence and finite global capture.

For n_E east and n_N north cars, M=n_E*(W-1)+n_N*(H-1) bounds both
remaining moves and full rounds to gridlock. A tighter integer rank assigns each
car a permanent obstacle on its invariant lane. Every actual move lowers its
forward cyclic distance to that obstacle by exactly one.

This function checks one finite witness; the general argument is in the research
note. It does not turn bounded replay into an unrestricted refinement theorem.
"""
    verify_cycle(rows, certificate, require_mixed=True, rule=rule)
    h, w, flat = _grid(rows)
    move_budget = flat.count(1) * (w - 1) + flat.count(2) * (h - 1)
    orbit = trace_labeled(rows, max_steps=move_budget + 1)
    positions_by_state = _validate_labeled_orbit(orbit, h, w, flat)
    core = set(certificate.cells)
    goals: dict[int, int] = {}
    for label, species in orbit.species:
        if label in core:
            goals[label] = label
            continue
        if species == 1:
            candidates = [cell for cell in core if cell // w == label // w]
            goals[label] = min(candidates, key=lambda cell: (cell % w - label % w) % w)
        else:
            candidates = [cell for cell in core if cell % w == label % w]
            goals[label] = min(candidates, key=lambda cell: (cell // w - label // w) % h)

    ranks = []
    for index, state in enumerate(orbit.states):
        if any(state[cell] != cell for cell in core):
            raise ValueError("a certified core car changed identity or position")
        positions = positions_by_state[index]
        rank = 0
        for label, species in orbit.species:
            position, goal = positions[label], goals[label]
            if species == 1:
                if position // w != goal // w:
                    raise ValueError("an east car left its row")
                rank += (goal % w - position % w) % w
            else:
                if position % w != goal % w:
                    raise ValueError("a north car left its column")
                rank += (goal // w - position // w) % h
        ranks.append(rank)
        following = index + 1 if index + 1 < len(orbit.states) else orbit.cycle_start
        actual, moved = step(np.array(orbit.rows(index), dtype=np.int8), rule)
        if actual.tolist() != orbit.rows(following) or int(moved) != len(orbit.moved[index]):
            raise ValueError("production dynamics disagree with independent labeled replay")
    for index, moved in enumerate(orbit.moved):
        following = index + 1 if index + 1 < len(ranks) else orbit.cycle_start
        if ranks[index] - ranks[following] != len(moved):
            raise ValueError("the obstacle rank did not decrease by the exact move count")
    if orbit.period != 1 or orbit.moved[orbit.cycle_start]:
        raise ValueError("the certified trajectory did not reach global gridlock")
    total_moves = sum(len(moved) for moved in orbit.moved)
    if not (total_moves <= ranks[0] <= move_budget and orbit.cycle_start <= move_budget):
        raise ValueError("capture exceeded its certified movement or time bound")
    return CaptureCheck(
        certificate, move_budget, orbit.cycle_start, total_moves, tuple(ranks),
        tuple(tuple(row) for row in orbit.rows(orbit.cycle_start)),
    )


@dataclass(frozen=True)
class CaptureTrace:
    """Full-round observations; a cutoff is never called an asymptotic phase."""

    outcome: str  # gridlock, free, intermediate, or unresolved
    rounds_observed: int
    first_core_round: int | None
    first_mixed_round: int | None
    gridlock_round: int | None
    cycle_start: int | None
    period: int | None
    cycle_move_count: int | None
    car_count: int

    @property
    def mean_velocity(self) -> Fraction | None:
        if self.period is None or self.cycle_move_count is None:
            return None
        if self.car_count == 0:
            return Fraction(1)  # repository's empty-state FREE convention
        return Fraction(self.cycle_move_count, self.car_count * self.period)


def trace_capture(
    rows: Sequence[Sequence[int]], *, max_steps: int = 10000, rule: str = CLASSIC,
) -> CaptureTrace:
    """Observe core formation, mixed winding, and complete capture separately.

Recurrence of the complete colored state, together with deterministic CLASSIC
updates, certifies its future occupancy cycle. Identity persistence is checked
separately by ``verify_capture``. A state reached exactly at the budget is still
inspected for a fixed point or a previously seen state before returning unresolved.
"""
    _classic(rule)
    if not _integer(max_steps) or max_steps < 0:
        raise ValueError("max_steps must be a nonnegative integer")
    h, w, flat = _grid(rows)
    car_count = sum(value != 0 for value in flat)
    current = np.array(flat, dtype=np.int8).reshape(h, w)
    seen: dict[tuple[int, ...], int] = {}
    moves: list[int] = []
    first_core = first_mixed = None
    for time in range(max_steps + 1):
        cycles = find_blocker_cycles(current)
        if cycles and first_core is None:
            first_core = time
        if any(cycle.mixed for cycle in cycles) and first_mixed is None:
            first_mixed = time
        if is_fixed(current):
            return CaptureTrace(
                "gridlock" if car_count else "free", time, first_core, first_mixed,
                time if car_count else None, time, 1, 0, car_count,
            )
        key = tuple(int(value) for value in current.flat)
        if key in seen:
            cycle_start = seen[key]
            period = time - cycle_start
            cycle_moves = sum(moves[cycle_start:])
            outcome = "free" if cycle_moves == car_count * period else "intermediate"
            return CaptureTrace(
                outcome, time, first_core, first_mixed, None, cycle_start,
                period, cycle_moves, car_count,
            )
        if time == max_steps:
            return CaptureTrace(
                "unresolved", time, first_core, first_mixed, None,
                None, None, None, car_count,
            )
        seen[key] = time
        current, moved = step(current, rule)
        moves.append(int(moved))
    raise AssertionError("unreachable")
