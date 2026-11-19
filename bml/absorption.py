"""Certified finite-cutoff bounds for eventual nonempty CLASSIC gridlock.

The executable contract matches ``BML.Absorption.probe``: inspect the terminal
state; report ``hit`` if it is a nonempty fixed state, ``safe`` if that non-hit
state repeats an earlier prefix state, and ``unresolved`` otherwise. A safe
cycle can be intermediate rather than full-speed. Every probability weight is
attached to the original complete board, never to an allegedly iid later state.

The Lean theorems prove the abstract contract and actual Lean CLASSIC instance.
Finite replay checks correspondence with this Python implementation; they do
not prove unrestricted source refinement or a positive critical density.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import comb
from numbers import Integral
from typing import Iterable, Sequence

import numpy as np

from bml.model import CLASSIC, step


HIT, SAFE, UNRESOLVED = 0, 1, 2
VERDICTS = ("hit", "safe", "unresolved")
MAX_CENSUS_CELLS = 12
CENSUS_CHUNK = 1 << 15


def _integer(value: object) -> bool:
    return isinstance(value, Integral) and not isinstance(value, (bool, np.bool_))


def _dimensions(width: int, height: int) -> tuple[int, int]:
    if any(not _integer(n) or n < 1 for n in (width, height)):
        raise ValueError("width and height must be positive integers")
    return int(width), int(height)


def _cutoff(value: int) -> int:
    if not _integer(value) or value < 0:
        raise ValueError("cutoff must be a nonnegative integer")
    return int(value)


def _classic(rule: str) -> None:
    if not isinstance(rule, str) or rule != CLASSIC:
        raise ValueError("absorption certificates require the CLASSIC rule")


def _density(p: Fraction) -> Fraction:
    if not isinstance(p, Fraction) or not 0 <= p <= 1:
        raise ValueError("density must be an exact Fraction in [0, 1]")
    return p


def _rows(rows: Sequence[Sequence[int]]) -> np.ndarray:
    try:
        board = np.asarray(rows, dtype=object)
    except (TypeError, ValueError) as exc:
        raise ValueError("expected a nonempty rectangular board") from exc
    if board.ndim != 2 or not all(board.shape):
        raise ValueError("expected a nonempty rectangular board")
    if any(not _integer(x) or x not in (0, 1, 2) for x in board.flat):
        raise ValueError("board species must be integer 0, 1 or 2")
    return board.astype(np.int8, copy=True)


def _code(width: int, height: int, value: int) -> int:
    if not _integer(value) or not 0 <= value < 3 ** (width * height):
        raise ValueError("state code must be an integer in the complete board range")
    return int(value)


def encode_board(rows: Sequence[Sequence[int]]) -> int:
    """Row-major ternary encoding using Python integers, including large boards."""
    board = _rows(rows)
    result = 0
    for cell in reversed(tuple(board.flat)):
        result = 3 * result + int(cell)
    return result


def decode_board(width: int, height: int, code: int) -> np.ndarray:
    """Decode without fixed-width integer arithmetic or truncating high digits."""
    width, height = _dimensions(width, height)
    remaining = _code(width, height, code)
    flat = np.empty(width * height, dtype=np.int8)
    for i in range(len(flat)):
        remaining, digit = divmod(remaining, 3)
        flat[i] = digit
    return flat.reshape(height, width)


def _jam(board: np.ndarray) -> bool:
    following, _ = step(board, CLASSIC)
    return bool(np.any(board) and np.array_equal(board, following))


@dataclass(frozen=True)
class TraceCertificate:
    """A claim about a complete finite trace; construction alone is not proof.

``states`` includes the initial board and every board through ``cutoff``.
The codes use Python integers. A safe certificate supplies a strictly earlier
index whose board equals the terminal board. The verifier binds dimensions
externally and replays every edge rather than trusting these fields.
"""

    width: int
    height: int
    cutoff: int
    states: tuple[int, ...]
    verdict: str
    repeat_index: int | None
    rule: str = CLASSIC

    @property
    def initial_code(self) -> int:
        return self.states[0]

    @property
    def terminal_code(self) -> int:
        return self.states[-1]


def verify_certificate(
    width: int, height: int, certificate: TraceCertificate, *, rule: str = CLASSIC,
) -> None:
    """Replay and validate the entire bounded trace against the actual kernel."""
    _classic(rule)
    width, height = _dimensions(width, height)
    if not isinstance(certificate, TraceCertificate):
        raise ValueError("expected a TraceCertificate")
    _classic(certificate.rule)
    declared = _dimensions(certificate.width, certificate.height)
    if declared != (width, height):
        raise ValueError("certificate dimensions disagree with the requested torus")
    cutoff = _cutoff(certificate.cutoff)
    if not isinstance(certificate.states, tuple) or len(certificate.states) != cutoff + 1:
        raise ValueError("trace must contain exactly cutoff + 1 complete states")
    codes = tuple(_code(width, height, c) for c in certificate.states)
    if certificate.verdict not in VERDICTS:
        raise ValueError("unknown absorption verdict")

    current = decode_board(width, height, codes[0])
    for index, expected in enumerate(codes[1:], start=1):
        following, _ = step(current, CLASSIC)
        if encode_board(following) != expected:
            raise ValueError(f"trace edge {index - 1}->{index} disagrees with CLASSIC")
        current = following

    hit = _jam(current)
    repeated = codes[-1] in codes[:-1]
    verdict = "hit" if hit else "safe" if repeated else "unresolved"
    if certificate.verdict != verdict:
        raise ValueError("claimed verdict disagrees with nonempty jam/recurrence checks")
    if verdict == "safe":
        repeat = certificate.repeat_index
        if (not _integer(repeat) or not 0 <= repeat < cutoff
                or codes[int(repeat)] != codes[-1]):
            raise ValueError("safe verdict requires a valid strictly earlier recurrence index")
    elif certificate.repeat_index is not None:
        raise ValueError("only a safe verdict may carry a recurrence index")


def make_certificate(
    rows: Sequence[Sequence[int]], cutoff: int, *, rule: str = CLASSIC,
) -> TraceCertificate:
    """Produce and verify an actual CLASSIC trace at the requested exact cutoff."""
    _classic(rule)
    cutoff = _cutoff(cutoff)
    current = _rows(rows)
    height, width = current.shape
    codes = [encode_board(current)]
    for _ in range(cutoff):
        current, _ = step(current, CLASSIC)
        codes.append(encode_board(current))
    hit = _jam(current)
    repeat = next((i for i, c in enumerate(codes[:-1]) if c == codes[-1]), None)
    verdict = "hit" if hit else "safe" if repeat is not None else "unresolved"
    certificate = TraceCertificate(width, height, cutoff, tuple(codes), verdict,
                                   repeat if verdict == "safe" else None)
    verify_certificate(width, height, certificate)
    return certificate


def certificate_from_code(
    width: int, height: int, code: int, cutoff: int, *, rule: str = CLASSIC,
) -> TraceCertificate:
    _classic(rule)
    return make_certificate(decode_board(width, height, code), cutoff, rule=rule)


@dataclass(frozen=True)
class ProbabilityBounds:
    """Exact arithmetic output, not an authenticity token for arbitrary metadata."""

    width: int
    height: int
    density: Fraction
    lower: Fraction
    upper: Fraction
    unresolved: Fraction
    hit_mass: Fraction
    safe_mass: Fraction
    covered_mass: Fraction
    omitted_mass: Fraction
    observed_unresolved_mass: Fraction
    certificates: int


def _bounds(
    width: int, height: int, p: Fraction, hit: Fraction, safe: Fraction,
    covered: Fraction, count: int,
) -> ProbabilityBounds:
    if not 0 <= hit + safe <= covered <= 1:
        raise ValueError("inconsistent initial probability masses")
    return ProbabilityBounds(width, height, p, hit, 1 - safe, 1 - hit - safe,
                             hit, safe, covered, 1 - covered,
                             covered - hit - safe, count)


def partial_probability_bounds(
    width: int, height: int, certificates: Iterable[TraceCertificate], p: Fraction,
    *, rule: str = CLASSIC,
) -> ProbabilityBounds:
    """Certified interval under the complete initial iid law, even for partial input.

Every omitted initial board contributes its entire probability to uncertainty.
Supplied unresolved traces likewise remain uncertain; they are never counted
as safe. Distinct cutoffs are allowed, but duplicate initial boards are rejected.
"""
    _classic(rule)
    width, height = _dimensions(width, height)
    p = _density(p)
    cells = width * height
    seen: set[int] = set()
    covered = hit = safe = Fraction()
    for certificate in certificates:
        verify_certificate(width, height, certificate, rule=rule)
        initial = int(certificate.initial_code)
        if initial in seen:
            raise ValueError("duplicate initial board would double-count its probability")
        seen.add(initial)
        cars = int(np.count_nonzero(decode_board(width, height, initial)))
        weight = (p / 2) ** cars * (1 - p) ** (cells - cars)
        covered += weight
        if certificate.verdict == "hit":
            hit += weight
        elif certificate.verdict == "safe":
            safe += weight
    return _bounds(width, height, p, hit, safe, covered, len(seen))


@dataclass(frozen=True)
class CutoffSnapshot:
    """Complete-census data; arbitrary object construction does not verify dynamics.

``terminal_codes[i]`` and ``verdicts[i]`` belong to INITIAL code i. ``by_cars``
has rows hit/safe/unresolved, weighted by the INITIAL occupied-site count.
The census producer derives the arrays from the actual transition map.
"""

    width: int
    height: int
    cutoff: int
    terminal_codes: np.ndarray
    verdicts: np.ndarray
    by_cars: tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]

    @property
    def counts(self) -> tuple[int, int, int]:
        return tuple(sum(row) for row in self.by_cars)

    def probability_bounds(self, p: Fraction) -> ProbabilityBounds:
        """Integrate the supplied finite census; this does not authenticate it."""
        width, height = _dimensions(self.width, self.height)
        p = _density(p)
        cells = width * height
        if (not isinstance(self.by_cars, tuple) or len(self.by_cars) != 3
                or any(not isinstance(row, tuple) or len(row) != cells + 1
                       or any(not _integer(n) or n < 0 for n in row)
                       for row in self.by_cars)):
            raise ValueError("expected nonnegative integer counts for each initial car layer")
        if any(sum(row[n] for row in self.by_cars) != comb(cells, n) * 2 ** n
               for n in range(cells + 1)):
            raise ValueError("complete-census counts do not partition the initial state space")
        weights = tuple((p / 2) ** n * (1 - p) ** (cells - n)
                        for n in range(cells + 1))
        masses = tuple(sum((int(n) * weight for n, weight in zip(row, weights)), Fraction())
                       for row in self.by_cars)
        return _bounds(width, height, p, masses[HIT], masses[SAFE],
                       sum(masses, Fraction()), 3 ** cells)


@dataclass(frozen=True)
class CutoffCensus:
    """Complete transition/cutoff outputs, with no claim of an asymptotic theorem."""

    width: int
    height: int
    successors: np.ndarray
    initial_car_counts: np.ndarray
    snapshots: tuple[CutoffSnapshot, ...]
    rule: str = CLASSIC

    @property
    def states(self) -> int:
        return 3 ** (self.width * self.height)

    def snapshot(self, cutoff: int) -> CutoffSnapshot:
        cutoff = _cutoff(cutoff)
        for result in self.snapshots:
            if result.cutoff == cutoff:
                return result
        raise KeyError(cutoff)


def complete_cutoff_census(
    width: int, height: int, cutoffs: Sequence[int], *,
    max_cells: int = 9, rule: str = CLASSIC,
) -> CutoffCensus:
    """Build the actual complete CLASSIC map, then evaluate finite initial traces.

The existing unbounded orbit classifier is not used as an oracle. Integer
arrays are safe here because exhaustive enumeration is explicitly limited to
at most 12 cells; individual trace certificates have no such encoding limit.
Memory grows with the largest cutoff and the complete state-space size.
"""
    _classic(rule)
    width, height = _dimensions(width, height)
    if (not _integer(max_cells) or not 1 <= max_cells <= MAX_CENSUS_CELLS
            or width * height > max_cells):
        raise ValueError("complete census requires cells <= max_cells <= 12")
    try:
        requested = tuple(_cutoff(t) for t in cutoffs)
    except TypeError as exc:
        raise ValueError("cutoffs must be a nonempty sequence of distinct integers") from exc
    if not requested or len(set(requested)) != len(requested):
        raise ValueError("cutoffs must be a nonempty sequence of distinct integers")
    requested = tuple(sorted(requested))
    wanted = set(requested)
    cells, size = width * height, 3 ** (width * height)
    powers = 3 ** np.arange(cells, dtype=np.int64)
    successors = np.empty(size, dtype=np.int64)
    cars = np.empty(size, dtype=np.int16)
    for lo in range(0, size, CENSUS_CHUNK):
        codes = np.arange(lo, min(lo + CENSUS_CHUNK, size), dtype=np.int64)
        boards = ((codes[:, None] // powers) % 3).astype(np.int8).reshape(-1, height, width)
        following, _ = step(boards, CLASSIC)
        successors[lo:lo + len(codes)] = following.reshape(len(codes), cells).astype(np.int64) @ powers
        cars[lo:lo + len(codes)] = np.count_nonzero(boards, axis=(1, 2))

    initial = np.arange(size, dtype=np.int64)
    targets = (cars > 0) & (successors == initial)
    current = initial
    history: list[np.ndarray] = []
    snapshots = []
    for t in range(requested[-1] + 1):
        if t in wanted:
            hit = targets[current]
            repeated = np.zeros(size, dtype=bool)
            for previous in history:
                repeated |= current == previous
            verdicts = np.where(hit, HIT, np.where(repeated, SAFE, UNRESOLVED)).astype(np.uint8)
            by_cars = tuple(tuple(int(n) for n in np.bincount(cars[verdicts == verdict],
                                                           minlength=cells + 1))
                            for verdict in (HIT, SAFE, UNRESOLVED))
            terminal = current.copy()
            terminal.flags.writeable = False
            verdicts.flags.writeable = False
            snapshots.append(CutoffSnapshot(width, height, t, terminal, verdicts, by_cars))
        history.append(current)
        if t < requested[-1]:
            current = successors[current]
    successors.flags.writeable = False
    cars.flags.writeable = False
    return CutoffCensus(width, height, successors, cars, tuple(snapshots))
