"""Relaxation obstructions and exact initial-law bounds for CLASSIC BML.

The HBK defects below are the unnormalized quantities in Eqs. (8) and (11)
of Hertzberg Rabinovich, Biham and Katzav, arXiv:2601.01180v2. They recognize
the free-flow zero set but are not pointwise Lyapunov functions of this kernel.
The probability bound concerns independent initial cells only; no evolved
configuration is assigned a product law. See the accompanying research note.
"""
from __future__ import annotations

from fractions import Fraction
from numbers import Rational
from typing import Sequence

import numpy as np

from bml.formation import _natural
from bml.model import CLASSIC, EAST, NORTH
from bml.probability import _classic, _density, _rows


def hbk_defects(
    rows: Sequence[Sequence[int]], *, next_species: int = EAST,
) -> tuple[int, int]:
    """Return the integer pair (d_parallel, d_perp) on a square.

    Counter-diagonal n is x+y mod L. d_parallel counts adjacent E/E pairs
    along rows and N/N pairs along columns. At a full-round boundary,
    next_species=EAST and d_perp is sum_n min(e_n,n_n)+min(e_n,n_(n+1)).
    Immediately after the east phase, next_species=NORTH instead uses
    min(n_n,e_(n+1)) for the second term. The phase is part of the definition.
    No normalization by an asserted iid expectation is performed.
    """
    side, width, flat = _rows(rows)
    if side != width or side < 2:
        raise ValueError("HBK defects require a square of side at least two")
    next_species = _natural(next_species, "next_species", 1)
    if next_species not in (EAST, NORTH):
        raise ValueError("next_species must be EAST or NORTH")
    east_counts, north_counts = [0] * side, [0] * side
    parallel = 0
    for y in range(side):
        for x in range(side):
            cell = flat[y * side + x]
            diagonal = (x + y) % side
            if cell == EAST:
                east_counts[diagonal] += 1
                parallel += flat[y * side + (x + 1) % side] == EAST
            elif cell == NORTH:
                north_counts[diagonal] += 1
                parallel += flat[((y + 1) % side) * side + x] == NORTH
    active, other = ((east_counts, north_counts) if next_species == EAST
                     else (north_counts, east_counts))
    perpendicular = sum(
        min(east_counts[n], north_counts[n])
        + min(active[n], other[(n + 1) % side])
        for n in range(side)
    )
    return int(parallel), perpendicular


def hbk_increase_fixture(side: int) -> np.ndarray:
    """Four cars whose actual CLASSIC round gives defects (0,1) -> (0,2).

    E is at (1,0),(0,1); N is at (0,0),(2,0). This works for every
    side >= 4, so global density can be arbitrarily small.
    """
    side = _natural(side, "side", 4)
    rows = np.zeros((side, side), dtype=np.int8)
    rows[0, 1] = rows[1, 0] = EAST
    rows[0, 0] = rows[0, 2] = NORTH
    return rows


def horizontal_run_fixture(
    side: int, rounds: int, *, start_x: int = 0, row: int = 0,
) -> np.ndarray:
    """An initial T+2 east run, with empty exterior and optional wraparound.

    The universal delay proof allows every exterior assignment; this is only
    an executable representative. The distinct-site probability application
    requires 0 <= T <= side-2.
    """
    side, rounds = _run_parameters(side, rounds)
    start_x = _natural(start_x, "start_x")
    row = _natural(row, "row")
    if start_x >= side or row >= side:
        raise ValueError("the run origin must lie inside the square")
    rows = np.zeros((side, side), dtype=np.int8)
    for offset in range(rounds + 2):
        rows[row, (start_x + offset) % side] = EAST
    return rows


def _run_parameters(side: int, rounds: int) -> tuple[int, int]:
    side = _natural(side, "side", 2)
    rounds = _natural(rounds, "rounds")
    if rounds + 2 > side:
        raise ValueError("the distinct-site run bound requires rounds+2 <= side")
    return side, rounds


def free_by_round_upper_bound(
    side: int, p: Rational, rounds: int, *, rule: str = CLASSIC,
) -> Fraction:
    """Upper bound on permanent full movement from round T onward.

    Each of K=L*floor(L/(T+2)) disjoint initial horizontal blocks forces a
    blocked rear car in round T if all T+2 sites contain E. Under initial
    iid law (1-p,p/2,p/2), these events are independent. Consequently the
    bound is (1-(p/2)^(T+2))^K. It also bounds full movement in round T.

    This is a lower obstruction on relaxation time, not a bound on eventual
    gridlock probability. Its nontrivial domain is 0 <= T <= L-2.
    """
    _classic(rule)
    side, rounds = _run_parameters(side, rounds)
    p = _density(p)
    length = rounds + 2
    disjoint_blocks = side * (side // length)
    return (1 - (p / 2) ** length) ** disjoint_blocks


def vacant_cut_fixture() -> tuple[np.ndarray, tuple[tuple[int, int], ...]]:
    """An empty east/south winding cycle followed by an actual mixed jam.

    Coordinates in the immutable cycle are (x,y); south decreases y. The
    returned board is a fresh array. The cycle is not a valid invariant
    certificate of all-time avoidance: one CLASSIC round fills a mixed core.
    """
    rows = np.array([
        [0, 0, 0, 1],
        [0, 1, 2, 2],
        [0, 1, 0, 0],
        [2, 2, 0, 1],
    ], dtype=np.int8)
    cycle = ((0, 0), (1, 0), (2, 0), (2, 3),
             (2, 2), (3, 2), (0, 2), (0, 1))
    return rows, cycle
