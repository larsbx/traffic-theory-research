"""Guarded finite-time barriers for CLASSIC direct-blocker paths.

Probability formulas use independent initial cells only. A guarded corner is
forced at time T for every exterior completion; the finite-time formation
bound does not estimate the probability of eventual gridlock.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from numbers import Rational
from typing import Sequence

import numpy as np

from bml.formation import _natural, diagonal_formation_upper_bound
from bml.model import CLASSIC, EAST, EMPTY, NORTH, half_step
from bml.probability import _classic, _density, _dimensions, _integer, _rows


def guarded_barrier_probability(rounds: int, p: Rational, *, rule: str = CLASSIC) -> Fraction:
    """Initial-law weight of the probe: 6T specified cars and one hole.

    The conditional interpretation requires an injective footprint disjoint
    from all initial sites already exposed by the adaptive path exploration.
    At T=0 the probe consists only of the next cell being empty.
    """
    _classic(rule)
    rounds, p = _natural(rounds, "rounds"), _density(p)
    return (1 - p) * (p / 2) ** (6 * rounds)


def guarded_barrier_formation_upper_bound(
    side: int, p: Rational, rounds: int = 0, *, rule: str = CLASSIC,
) -> Fraction:
    """Upper bound on a mixed direct cycle formed by round T on an L×L torus.

    Stride 4T+1 and K=max(0,floor((L-3T-1)/(4T+1))) keep the probe's
    initial footprint fresh before the first diagonal wrap. Persistence of
    mixed cycles identifies formation by T with presence at T.
    """
    _classic(rule)
    side, rounds, p = _natural(side, "side", 1), _natural(rounds, "rounds"), _density(p)
    if side == 1 or p == 0:
        return Fraction()
    trials = max(0, (side - 3 * rounds - 1) // (4 * rounds + 1))
    stop = guarded_barrier_probability(rounds, p)
    return min(Fraction(1), side * p / 2 * (1 - stop) ** trials)


def combined_barrier_formation_upper_bound(
    side: int, p: Rational, rounds: int = 0, *, rule: str = CLASSIC,
) -> Fraction:
    """The better of the guarded-corner and existing empty-diagonal bounds."""
    return min(guarded_barrier_formation_upper_bound(side, p, rounds, rule=rule),
               diagonal_formation_upper_bound(side, p, rounds, rule=rule))


@dataclass(frozen=True)
class BarrierPattern:
    """A lifted corner and its prescribed initial cells on a rectangular torus.

    X=x0+east_length and Y=y0+north_length. At time T, the top E wall
    ends at (X−1,Y), the right N wall ends at (X,Y−1), and (X,Y) is empty.
    The initial main N run extends to Y+T−1, with a hole at Y+T and N
    guards in the preceding column at heights Y+1,...,Y+T.
    """

    width: int
    height: int
    rounds: int
    x0: int
    y0: int
    east_length: int
    north_length: int

    def __post_init__(self) -> None:
        w, h = _dimensions(self.width, self.height)
        t = _natural(self.rounds, "rounds")
        a, b = _natural(self.east_length, "east_length"), _natural(self.north_length, "north_length")
        if not _integer(self.x0) or not _integer(self.y0):
            raise ValueError("the lifted origin must have integer coordinates")
        if a >= w or b + t >= h or (t > 0 and w < 2):
            raise ValueError("the barrier footprint must project without overlapping or wrapping its runs")
        for name, value in (("width", w), ("height", h), ("rounds", t),
                            ("x0", int(self.x0)), ("y0", int(self.y0)),
                            ("east_length", a), ("north_length", b)):
            object.__setattr__(self, name, value)

    @property
    def corner(self) -> tuple[int, int]:
        return self.x0 + self.east_length, self.y0 + self.north_length

    @property
    def lifted_initial_cells(self) -> tuple[tuple[int, int, int], ...]:
        x, y = self.corner
        return (tuple((a, y, EAST) for a in range(self.x0, x))
                + tuple((x, b, NORTH) for b in range(self.y0, y + self.rounds))
                + ((x, y + self.rounds, EMPTY),)
                + tuple((x - 1, b, NORTH) for b in range(y + 1, y + self.rounds + 1)))

    @property
    def initial_cells(self) -> tuple[tuple[int, int, int], ...]:
        return tuple((x % self.width, y % self.height, c) for x, y, c in self.lifted_initial_cells)

    @property
    def target_cells(self) -> tuple[tuple[int, int, int], ...]:
        x, y = self.corner
        lifted = (tuple((a, y, EAST) for a in range(self.x0, x))
                  + tuple((x, b, NORTH) for b in range(self.y0, y)) + ((x, y, EMPTY),))
        return tuple((a % self.width, b % self.height, c) for a, b, c in lifted)


def guarded_barrier_pattern(
    width: int, height: int, rounds: int, *, x0: int = 0, y0: int = 0,
    east_length: int | None = None, north_length: int | None = None,
) -> BarrierPattern:
    """Default both legs to 2T, the geometry used by the probability bound."""
    rounds = _natural(rounds, "rounds")
    return BarrierPattern(width, height, rounds, x0, y0,
                          2 * rounds if east_length is None else east_length,
                          2 * rounds if north_length is None else north_length)


def _pattern(value: BarrierPattern) -> BarrierPattern:
    if not isinstance(value, BarrierPattern):
        raise ValueError("expected a BarrierPattern")
    return BarrierPattern(value.width, value.height, value.rounds, value.x0, value.y0,
                          value.east_length, value.north_length)


def guarded_barrier_board(
    pattern: BarrierPattern, *, exterior: Sequence[Sequence[int]] | None = None,
    rule: str = CLASSIC,
) -> tuple[tuple[int, ...], ...]:
    """Overlay the explicit initial footprint without changing the exterior input."""
    _classic(rule)
    pattern = _pattern(pattern)
    if exterior is None:
        flat = [EMPTY] * (pattern.width * pattern.height)
    else:
        h, w, cells = _rows(exterior)
        if (w, h) != (pattern.width, pattern.height):
            raise ValueError("exterior dimensions disagree with the barrier")
        flat = list(cells)
    for x, y, color in pattern.initial_cells:
        flat[y * pattern.width + x] = color
    return tuple(tuple(flat[y * pattern.width:(y + 1) * pattern.width]) for y in range(pattern.height))


def _scalar_phase(cells: tuple[int, ...], w: int, h: int, species: int) -> tuple[tuple[int, ...], int]:
    """Snapshot scalar oracle, independent of the production roll/mask update."""
    moves = []
    for source, color in enumerate(cells):
        if color == species:
            y, x = divmod(source, w)
            target = y * w + (x + 1) % w if species == EAST else ((y + 1) % h) * w + x
            if cells[target] == EMPTY:
                moves.append((source, target))
    after = list(cells)
    for source, target in moves:
        after[source], after[target] = EMPTY, species
    return tuple(after), len(moves)


@dataclass(frozen=True)
class BarrierVerification:
    """A bounded replay through T; no terminal-orbit classification is inferred."""

    pattern: BarrierPattern
    states: tuple[tuple[int, ...], ...]
    east_states: tuple[tuple[int, ...], ...]
    phase_moves: tuple[tuple[int, int], ...]


def verify_guarded_barrier(
    rows: Sequence[Sequence[int]], pattern: BarrierPattern, *, rule: str = CLASSIC,
) -> BarrierVerification:
    """Bind the pattern to this board, compare both phases, and check the target."""
    _classic(rule)
    pattern = _pattern(pattern)
    h, w, current = _rows(rows)
    if (w, h) != (pattern.width, pattern.height):
        raise ValueError("board dimensions disagree with the barrier")
    if any(current[y * w + x] != c for x, y, c in pattern.initial_cells):
        raise ValueError("the initial board does not contain the prescribed barrier")
    production = np.array(current, dtype=np.int8).reshape(h, w)
    states, east_states, phase_moves = [current], [], []
    for _ in range(pattern.rounds):
        totals = []
        for species in (EAST, NORTH):
            current, expected = _scalar_phase(current, w, h, species)
            production, actual = half_step(production, species, rule=rule)
            if (not _integer(actual) or int(actual) != expected
                    or not np.array_equal(production, np.array(current).reshape(h, w))):
                raise ValueError("production phase disagrees with independent scalar replay")
            totals.append(expected)
            if species == EAST:
                east_states.append(current)
        phase_moves.append(tuple(totals))
        states.append(current)
    if any(current[y * w + x] != c for x, y, c in pattern.target_cells):
        raise ValueError("the target walls and hole were not present at the certified time")
    return BarrierVerification(pattern, tuple(states), tuple(east_states), tuple(phase_moves))
