"""BML dynamics on the W×H torus.

A configuration is an int8 array ``s[y, x]`` of shape (H, W) over {EMPTY, EAST, NORTH}.
One time step = an EAST half-step followed by a NORTH half-step (+y). Two update rules:

- CLASSIC (Biham–Middleton–Levine 1992; Angel–Holroyd–Martin 2005): a car moves iff the
  cell ahead is empty at the start of the half-step. A full ring of cars is frozen.
- TRAIN (Austin–Benjamini 2006): a maximal line of same-species cars moves together iff
  the cell ahead of its head is empty; a full ring of them rotates.

All functions are pure: inputs are never mutated.
"""
from __future__ import annotations

import numpy as np

EMPTY, EAST, NORTH = 0, 1, 2
CLASSIC, TRAIN = "classic", "train"
AXIS = {EAST: -1, NORTH: -2}  # +x is the last axis, +y the one before; works on batches too


def movers_mask(s: np.ndarray, species: int, rule: str) -> np.ndarray:
    ax = AXIS[species]
    mine = s == species
    movers = mine & (np.roll(s, -1, axis=ax) == EMPTY)
    if rule == TRAIN:
        for _ in range(s.shape[ax] - 1):      # propagate backwards along lines of cars
            movers = movers | (mine & np.roll(movers, -1, axis=ax))
        movers = movers | (mine & mine.all(axis=ax, keepdims=True))   # full ring rotates
    return movers


def half_step(s: np.ndarray, species: int, rule: str = CLASSIC) -> tuple[np.ndarray, np.ndarray | int]:
    """Move every unblocked car of ``species`` one cell; return (new state, #moved)."""
    ax = AXIS[species]
    movers = movers_mask(s, species, rule)
    out = np.where(movers, EMPTY, s)
    out = np.where(np.roll(movers, 1, axis=ax), species, out).astype(np.int8)
    return out, movers.sum(axis=(-2, -1))


def step(s: np.ndarray, rule: str = CLASSIC) -> tuple[np.ndarray, np.ndarray | int]:
    """One full BML step (EAST then NORTH); return (new state, total #moves)."""
    a, m1 = half_step(s, EAST, rule)
    b, m2 = half_step(a, NORTH, rule)
    return b, m1 + m2


def counts(s: np.ndarray) -> tuple[int, int]:
    return int((s == EAST).sum()), int((s == NORTH).sum())


def is_fixed(s: np.ndarray) -> bool:
    """Gridlock test (Lemma G0): every EAST car has its east cell occupied and every NORTH
    car its north cell occupied."""
    blocked_e = (s != EAST) | (np.roll(s, -1, axis=-1) != EMPTY)
    blocked_n = (s != NORTH) | (np.roll(s, -1, axis=-2) != EMPTY)
    return bool(blocked_e.all() and blocked_n.all())


def blocker(s: np.ndarray, cell: tuple[int, int]) -> tuple[int, int]:
    """The cell in front of the car at ``cell`` (east for EAST cars, north for NORTH)."""
    h, w = s.shape
    y, x = cell
    return (y, (x + 1) % w) if s[y, x] == EAST else ((y + 1) % h, x)


def blocker_cycle(s: np.ndarray) -> list[tuple[int, int]]:
    """For a gridlocked ``s`` with cars: follow blockers from some car until a cell repeats;
    return the cycle (a closed east/north lattice loop of cars)."""
    start = tuple(int(v) for v in np.argwhere(s != EMPTY)[0])
    seen: dict[tuple[int, int], int] = {}
    path, c = [], start
    while c not in seen:
        seen[c] = len(path)
        path.append(c)
        c = blocker(s, c)
        assert s[c] != EMPTY, "not a gridlock"
    return path[seen[c]:]
