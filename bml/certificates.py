"""Small, labeled orbit certificates, independent of the NumPy update kernel.

Recurrence includes car identities, not only the three-valued occupancy grid.
Consequently a car moving on the recurrent cycle moves infinitely often.
This checker is intended for explicit small witnesses, not large enumeration.
"""
from __future__ import annotations

from dataclasses import dataclass
from numbers import Integral
from typing import Sequence


def _grid(rows: Sequence[Sequence[int]]) -> tuple[int, int, tuple[int, ...]]:
    h = len(rows)
    w = len(rows[0]) if h else 0
    if not h or not w or any(len(row) != w for row in rows):
        raise ValueError("expected a nonempty rectangular grid")
    raw = tuple(cell for row in rows for cell in row)
    if any(not isinstance(cell, Integral) or cell not in (0, 1, 2) for cell in raw):
        raise ValueError("cell values must be 0, 1 or 2")
    flat = tuple(int(cell) for cell in raw)
    return h, w, flat


def _ahead(i: int, species: int, h: int, w: int) -> int:
    y, x = divmod(i, w)
    return y * w + (x + 1) % w if species == 1 else ((y + 1) % h) * w + x


@dataclass(frozen=True)
class LabeledOrbit:
    height: int
    width: int
    species: tuple[tuple[int, int], ...]
    states: tuple[tuple[int, ...], ...]
    moved: tuple[tuple[int, ...], ...]
    cycle_start: int

    @property
    def period(self) -> int:
        return len(self.states) - self.cycle_start

    def rows(self, index: int) -> list[list[int]]:
        colors = dict(self.species)
        flat = [0 if label == -1 else colors[label] for label in self.states[index]]
        return [flat[i:i + self.width] for i in range(0, len(flat), self.width)]

    def cycle_moves(self, label: int) -> int:
        return sum(label in moved for moved in self.moved[self.cycle_start:])


def trace_labeled(
    rows: Sequence[Sequence[int]],
    labels: Sequence[int] | None = None,
    *,
    max_steps: int = 10000,
) -> LabeledOrbit:
    """Follow identities until a labeled state repeats; fail on budget exhaustion.

Default labels are initial row-major cell indices. A supplied labeling uses -1
for every hole and a distinct nonnegative identity for each occupied cell.
Movement eligibility is computed from the complete pre-half-step snapshot.
"""
    h, w, flat = _grid(rows)
    current = tuple(labels) if labels is not None else tuple(
        i if species else -1 for i, species in enumerate(flat)
    )
    if any(not isinstance(label, Integral) for label in current):
        raise ValueError("car identities must be integers")
    if len(current) != len(flat) or any((label == -1) != (sp == 0)
                                      for label, sp in zip(current, flat)):
        raise ValueError("labels and occupied cells disagree")
    occupied = [label for label in current if label != -1]
    if any(label < 0 for label in occupied) or len(set(occupied)) != len(occupied):
        raise ValueError("car identities must be distinct and nonnegative")
    colors = {label: sp for label, sp in zip(current, flat) if label != -1}
    seen: dict[tuple[int, ...], int] = {}
    states, movements = [], []
    while current not in seen:
        if len(states) >= max_steps:
            raise ValueError("labeled orbit did not recur within the step budget")
        seen[current] = len(states)
        states.append(current)
        moved = []
        for species in (1, 2):
            eligible = []
            for source, label in enumerate(current):
                if label == -1 or colors[label] != species:
                    continue
                target = _ahead(source, species, h, w)
                if current[target] == -1:
                    eligible.append((source, target, label))
            following = list(current)
            for source, _, _ in eligible:
                following[source] = -1
            for _, target, label in eligible:
                following[target] = label
                moved.append(label)
            current = tuple(following)
        movements.append(tuple(moved))
    return LabeledOrbit(h, w, tuple(sorted(colors.items())), tuple(states),
                        tuple(movements), seen[current])


def has_blocker_cycle(rows: Sequence[Sequence[int]]) -> bool:
    """Whether the initial occupied-target pointer graph contains a cycle.

An edge leaves a car in its own direction, and stops if it reaches a hole.
This tests the simple blocking loops used in G1, not eventual gridlock.
"""
    h, w, flat = _grid(rows)
    for start, species in enumerate(flat):
        if not species:
            continue
        seen: set[int] = set()
        cell = start
        while flat[cell] and cell not in seen:
            seen.add(cell)
            cell = _ahead(cell, flat[cell], h, w)
        if cell in seen:
            return True
    return False
