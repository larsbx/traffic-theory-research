"""Finite gridlock-delay certificates for the CLASSIC east-then-north kernel.

A guarded queue forces its initial rear E car to move for the first time in
round T, for every assignment outside the pattern. Round zero is the first
update. Thus the state at time T is not gridlocked. Exact probability bounds
use only the initial iid law (1-p,p/2,p/2), and concern gridlock by a finite
time; they do not bound eventual gridlock or assert a critical density.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import comb
from numbers import Rational
from typing import Sequence

import numpy as np

from bml.model import CLASSIC, EAST, NORTH, half_step
from bml.probability import _classic, _density, _dimensions, _integer, _rows


def _parameters(width: int, height: int, delay: int) -> tuple[int, int, int]:
    width, height = _dimensions(width, height)
    if width < 2 or height < 2:
        raise ValueError("guarded queues require width and height at least two")
    if not _integer(delay) or not 0 <= delay <= width - 2:
        raise ValueError("delay must be an integer between zero and width-2")
    return width, height, int(delay)


@dataclass(frozen=True)
class GuardedQueueCertificate:
    """Untrusted pattern location; verification binds it to the supplied board.

The main row prescribes E at start_x,...,start_x+delay and a hole at
start_x+delay+1. The row below prescribes E at offsets 1,...,delay.
All coordinates wrap. At delay zero the guard is empty.
"""

    width: int
    height: int
    start_x: int
    row: int
    delay: int


def _certificate(value: GuardedQueueCertificate) -> GuardedQueueCertificate:
    if not isinstance(value, GuardedQueueCertificate):
        raise ValueError("expected a GuardedQueueCertificate")
    w, h, delay = _parameters(value.width, value.height, value.delay)
    if (not _integer(value.start_x) or not 0 <= value.start_x < w
            or not _integer(value.row) or not 0 <= value.row < h):
        raise ValueError("the pattern origin must be an in-range integer coordinate")
    return GuardedQueueCertificate(w, h, int(value.start_x), int(value.row), delay)


def _pattern(certificate: GuardedQueueCertificate) -> dict[int, int]:
    w, h, x, y, delay = (certificate.width, certificate.height,
                         certificate.start_x, certificate.row, certificate.delay)
    fixed = {y * w + (x + i) % w: EAST for i in range(delay + 1)}
    fixed[y * w + (x + delay + 1) % w] = 0
    fixed.update({((y - 1) % h) * w + (x + i) % w: EAST
                  for i in range(1, delay + 1)})
    return fixed


def construct_guarded_queue(
    width: int, height: int, delay: int, *, start_x: int = 0, row: int = 0,
    exterior: Sequence[Sequence[int]] | None = None, rule: str = CLASSIC,
) -> tuple[tuple[int, ...], ...]:
    """Overlay the pattern on a supplied exterior, or on an otherwise empty grid.

Only prescribed pattern cells are overwritten. The input is never mutated.
This creates a representative; the arbitrary-exterior theorem is separate
from constructing or checking one finite board.
"""
    _classic(rule)
    cert = _certificate(GuardedQueueCertificate(width, height, start_x, row, delay))
    if exterior is None:
        flat = [0] * (cert.width * cert.height)
    else:
        h, w, values = _rows(exterior)
        if (w, h) != (cert.width, cert.height):
            raise ValueError("exterior dimensions disagree with the certificate")
        flat = list(values)
    for cell, species in _pattern(cert).items():
        flat[cell] = species
    return tuple(tuple(flat[y * cert.width:(y + 1) * cert.width])
                 for y in range(cert.height))


def _ahead(cell: int, species: int, width: int, height: int) -> int:
    y, x = divmod(cell, width)
    return y * width + (x + 1) % width if species == EAST else ((y + 1) % height) * width + x


def _tagged_half_step(
    current: tuple[int, ...], colors: dict[int, int], width: int, height: int, species: int,
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Scalar snapshot update, independent of the production NumPy kernel."""
    eligible = [(cell, _ahead(cell, species, width, height), label)
                for cell, label in enumerate(current)
                if label >= 0 and colors[label] == species
                and current[_ahead(cell, species, width, height)] == -1]
    following = list(current)
    for source, target, label in eligible:
        following[source], following[target] = -1, label
    return tuple(following), tuple(label for _, _, label in eligible)


def _check_tagged_phase(
    before: tuple[int, ...], after: tuple[int, ...], moved: tuple[int, ...],
    colors: dict[int, int], width: int, height: int, species: int,
) -> None:
    """Check complete identity transport, including same-species label swaps."""
    if (not isinstance(after, tuple) or len(after) != width * height
            or any(not _integer(label) or label < -1 for label in after)
            or not isinstance(moved, tuple)
            or any(not _integer(label) for label in moved)):
        raise ValueError("malformed tagged phase")
    occupied = [label for label in after if label >= 0]
    if len(occupied) != len(colors) or set(occupied) != set(colors):
        raise ValueError("tagged phase changed the complete identity set")
    positions = {label: cell for cell, label in enumerate(after) if label >= 0}
    expected = set()
    for cell, label in enumerate(before):
        if label < 0:
            continue
        target = _ahead(cell, colors[label], width, height)
        moving = colors[label] == species and before[target] == -1
        if positions[label] != (target if moving else cell):
            raise ValueError("tagged phase has an invalid individual trajectory")
        if moving:
            expected.add(label)
    if len(moved) != len(set(moved)) or set(moved) != expected:
        raise ValueError("reported moved identities disagree with actual trajectories")


@dataclass(frozen=True)
class GuardedQueueVerification:
    """Computed bounded replay, not a claim of recurrence or a terminal basin."""

    certificate: GuardedQueueCertificate
    rear_label: int
    species: tuple[tuple[int, int], ...]
    states: tuple[tuple[int, ...], ...]
    east_moved: tuple[tuple[int, ...], ...]
    north_moved: tuple[tuple[int, ...], ...]

    @property
    def first_rear_move(self) -> int:
        return next(t for t, moved in enumerate(self.east_moved) if self.rear_label in moved)


def verify_guarded_queue(
    rows: Sequence[Sequence[int]], certificate: GuardedQueueCertificate, *, rule: str = CLASSIC,
) -> GuardedQueueVerification:
    """Check the exact initial pattern and replay rounds 0,...,T with car identities.

Initial labels are occupied row-major cell indices. Every identity transition,
both colored half-steps and both production movement counts are checked. The
rear tag must first move in round T. No orbit cutoff is classified as terminal.
"""
    _classic(rule)
    cert = _certificate(certificate)
    h, w, flat = _rows(rows)
    if (w, h) != (cert.width, cert.height):
        raise ValueError("certificate dimensions disagree with the exact input")
    if any(flat[cell] != species for cell, species in _pattern(cert).items()):
        raise ValueError("the exact initial board does not contain the guarded queue")
    colors = {cell: species for cell, species in enumerate(flat) if species}
    current = tuple(cell if species else -1 for cell, species in enumerate(flat))
    production = np.array(flat, dtype=np.int8).reshape(h, w)
    rear = cert.row * w + cert.start_x
    states, east_moved, north_moved = [current], [], []
    for t in range(cert.delay + 1):
        for species, record in ((EAST, east_moved), (NORTH, north_moved)):
            following, moved = _tagged_half_step(current, colors, w, h, species)
            _check_tagged_phase(current, following, moved, colors, w, h, species)
            production, count = half_step(production, species, rule=rule)
            colored = np.array([0 if label == -1 else colors[label] for label in following],
                               dtype=np.int8).reshape(h, w)
            if (not _integer(count) or int(count) != len(moved)
                    or not np.array_equal(production, colored)):
                raise ValueError("production half-step disagrees with independent tagged replay")
            if species == EAST and (rear in moved) != (t == cert.delay):
                raise ValueError("the rear car did not first move in the prescribed round")
            record.append(moved)
            current = following
        states.append(current)
    return GuardedQueueVerification(cert, rear, tuple(sorted(colors.items())), tuple(states),
                                    tuple(east_moved), tuple(north_moved))


@dataclass(frozen=True)
class GuardedQueueBounds:
    """Exact initial-pattern avoidance, giving upper bounds on gridlock by T.

The event is nonempty gridlock at time T, equivalently gridlock reached by T,
because CLASSIC jams are absorbing. The exact bound uses all cyclic starts
on floor(H/2) disjoint row pairs. It is not the exact gridlock probability.
"""

    width: int
    height: int
    delay: int
    p: Fraction
    row_pairs: int
    pattern_probability: Fraction
    cyclic_placement_counts: tuple[int, ...]
    cyclic_avoidance_probability: Fraction
    early_gridlock_upper_bound: Fraction
    simple_upper_bound: Fraction


def guarded_queue_bounds(
    width: int, height: int, delay: int, p: Rational, *, rule: str = CLASSIC,
) -> GuardedQueueBounds:
    """Exact rational finite-time bounds for W,H>=2 and 0<=T<=W-2.

Write s=T+2 and w=(1-p)*(p/2)**(2*T+1). Overlapping length-s main windows
are incompatible; disjoint windows have disjoint pattern supports. Therefore
one row pair has exact avoidance Q=sum_k (-1)^k a_k*w**k, where a_0=1 and
a_k=W/k * binom(W-k*(s-1)-1,k-1) counts k cyclic disjoint windows. The bounds
are Q**floor(H/2) and (1-w)**(W*floor(H/2)). These pairs, not all cyclic
vertical placements, are independent. The uniform formula is retained when
T=0 even though its empty guard permits a separate all-row improvement.
At p=0 and p=1 the pattern has zero mass and both bounds equal one.
"""
    _classic(rule)
    width, height, delay = _parameters(width, height, delay)
    p = _density(p)
    length = delay + 2
    counts = [1]
    for k in range(1, width // length + 1):
        numerator = width * comb(width - k * (length - 1) - 1, k - 1)
        count, remainder = divmod(numerator, k)
        if remainder:
            raise AssertionError("cyclic placement count is not integral")
        counts.append(count)
    mass = (1 - p) * (p / 2) ** (2 * delay + 1)
    avoidance = sum(((-1) ** k * count * mass ** k for k, count in enumerate(counts)), Fraction())
    pairs = height // 2
    exact, simple = avoidance ** pairs, (1 - mass) ** (width * pairs)
    if not 0 <= exact <= simple <= 1:
        raise AssertionError("cyclic avoidance bounds left their probability range")
    return GuardedQueueBounds(width, height, delay, p, pairs, mass, tuple(counts),
                              avoidance, exact, simple)
