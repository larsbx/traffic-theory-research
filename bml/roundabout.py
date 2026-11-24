"""Roundabout BML: BML on the W×H torus with every intersection replaced by a roundabout.

Each intersection (x, y) is a counter-clockwise ring of four quadrant cells. Straight-through
traffic uses three of them (see docs/research/2026-11-24-roundabout-bml.md):

    a[y, x]  south-west quadrant, EAST cars only    (private)
    c[y, x]  south-east quadrant, both species      (shared)
    b[y, x]  north-east quadrant, NORTH cars only   (private)

Routes:  EAST   a(x,y) → c(x,y) → a(x+1,y) → …      (row ring of length 2W)
         NORTH  c(x,y) → b(x,y) → c(x,y+1) → …      (column ring of length 2H)

There are no signal phases: one step moves every car whose next cell is empty at the start
of the step (the CLASSIC vacancy rule), all at once. The only merge is into c(x,y), from
a(x,y) (circulating) and b(x,y-1) (entering); ``priority`` names the species that wins it.
Yield-on-entry is ``priority=EAST``.

All functions are pure and accept batches: arrays have shape (..., H, W).
"""
from __future__ import annotations

from math import gcd, lcm
from typing import NamedTuple

import numpy as np

from bml.model import EMPTY, EAST, NORTH

X, Y = -1, -2          # array axes of +x and +y
CELLS_PER_ROUNDABOUT = 3


class State(NamedTuple):
    a: np.ndarray      # bool:  EAST car in the EAST-private cell
    c: np.ndarray      # int8:  EMPTY / EAST / NORTH in the shared cell
    b: np.ndarray      # bool:  NORTH car in the NORTH-private cell


def empty(h: int, w: int) -> State:
    return State(np.zeros((h, w), bool), np.zeros((h, w), np.int8), np.zeros((h, w), bool))


def counts(s: State) -> tuple[np.ndarray | int, np.ndarray | int]:
    """(#EAST, #NORTH) cars, per batch element."""
    return (s.a.sum(axis=(Y, X)) + (s.c == EAST).sum(axis=(Y, X)),
            s.b.sum(axis=(Y, X)) + (s.c == NORTH).sum(axis=(Y, X)))


def movers(s: State, priority: int = EAST) -> State:
    """Masks, indexed by source cell, of the cars that move in the next step."""
    vacant = s.c == EMPTY
    entering = np.roll(s.b, 1, axis=Y)                 # NORTH car at b(x, y-1), seen from c(x, y)
    east_wins = priority == EAST
    from_a = s.a & vacant & (~entering | east_wins)
    into_c = entering & vacant & (~s.a | (not east_wins))
    from_c = ((s.c == EAST) & ~np.roll(s.a, -1, axis=X)) | ((s.c == NORTH) & ~s.b)
    return State(from_a, from_c, np.roll(into_c, -1, axis=Y))


def step(s: State, priority: int = EAST) -> tuple[State, np.ndarray | int]:
    """One synchronous step; return (new state, #moves)."""
    m = movers(s, priority)
    out_e, out_n = m.c & (s.c == EAST), m.c & (s.c == NORTH)
    into_c = np.roll(m.b, 1, axis=Y)
    c = np.where(m.c, EMPTY, s.c)
    c = np.where(m.a, EAST, np.where(into_c, NORTH, c)).astype(np.int8)
    new = State((s.a & ~m.a) | np.roll(out_e, 1, axis=X), c, (s.b & ~m.b) | out_n)
    return new, sum(mask.sum(axis=(Y, X)) for mask in m)


def is_fixed(s: State) -> np.ndarray | bool:
    """Lemma RB-0: no car can move ⟺ every car's next cell on its route is occupied."""
    full = s.c != EMPTY
    blocked = ((~s.a | full) & (~s.b | np.roll(full, -1, axis=Y))
               & ((s.c != EAST) | np.roll(s.a, -1, axis=X)) & ((s.c != NORTH) | s.b))
    return blocked.all(axis=(Y, X))


def period(h: int, w: int) -> int:
    """Every free configuration returns to itself after this many steps."""
    return 2 * lcm(h, w)


def is_free(s: State, priority: int = EAST) -> np.ndarray | bool:
    """Dynamic definition: every car moves at every step, forever. Checking one period
    suffices, because a configuration whose cars all moved for 2·lcm(W,H) steps has returned."""
    h, w = s.c.shape[-2:]
    n = sum(counts(s))
    ok = np.ones_like(n, dtype=bool)
    for _ in range(period(h, w)):
        s, moved = step(s, priority)
        ok = ok & (moved == n)
    return ok


# ---- Lemma RB-R: the static criterion -------------------------------------------------
def classes(s: State) -> tuple[np.ndarray, np.ndarray]:
    """Occupied phase classes mod 2·gcd(W,H), as two boolean arrays of shape (..., 2g):
    κ_E = p + 2y for an EAST car at row position p (a(x,y) ↦ 2x, c(x,y) ↦ 2x+1) and
    κ_N = r + 2x for a NORTH car at column position r (c(x,y) ↦ 2y, b(x,y) ↦ 2y+1).
    Both advance by 1 per free step."""
    h, w = s.c.shape[-2:]
    y, x = np.indices((h, w))
    m = 2 * gcd(h, w)
    on = lambda cars, shift: np.stack(   # noqa: E731
        [(cars & ((2 * (x + y) + shift) % m == k)).any(axis=(Y, X)) for k in range(m)], axis=-1)
    return on(s.a, 0) | on(s.c == EAST, 1), on(s.c == NORTH, 0) | on(s.b, 1)


def is_free_static(s: State) -> np.ndarray | bool:
    """Lemma RB-R: free ⟺ (i) no car directly behind a car of its own species and
    (ii) κ_N − κ_E ∉ {0, −1, −2} mod 2·gcd(W,H) for every EAST/NORTH pair."""
    e, n = s.c == EAST, s.c == NORTH
    tailgating = (s.a & e) | (e & np.roll(s.a, -1, axis=X)) | (n & s.b) | (s.b & np.roll(n, -1, axis=Y))
    east, north = classes(s)
    clash = east & (north | np.roll(north, 1, axis=-1) | np.roll(north, 2, axis=-1))
    return ~tailgating.any(axis=(Y, X)) & ~clash.any(axis=-1)


# ---- Theorem RB-F: free-flow capacity and species frontier ----------------------------
def free_feasible(h: int, w: int, n_e: int, n_n: int) -> bool:
    """Theorem RB-F: a free configuration with n_e EAST and n_n NORTH cars exists
    ⟺ ⌈n_e/m⌉ + ⌈n_n/m⌉ ≤ g, where g = gcd(W,H) and m = WH/g."""
    g = gcd(h, w)
    m = h * w // g
    return -(-n_e // m) + -(-n_n // m) <= g


def max_free(h: int, w: int) -> int:
    """Free-flow capacity: one car per roundabout, for every W and H."""
    return h * w


def free_with(h: int, w: int, n_e: int, n_n: int) -> State:
    """RB-F construction: EAST cars on a-cells of the diagonals (x+y) mod g ∈ [0, i), NORTH
    cars on b-cells of the next j diagonals starting at i−1; surplus cars are removed."""
    assert free_feasible(h, w, n_e, n_n)
    g = gcd(h, w)
    m = h * w // g
    i = -(-n_e // m)
    y, x = np.indices((h, w))
    east = (x + y) % g < i
    north = (x + y + 1 - i) % g < -(-n_n // m)
    return State(_keep(east, n_e), np.zeros((h, w), np.int8), _keep(north, n_n))


def _keep(mask: np.ndarray, n: int) -> np.ndarray:
    """The first n True cells of ``mask`` in row-major order."""
    return mask & (np.cumsum(mask).reshape(mask.shape) <= n)


# ---- Theorem RB-G: gridlock ------------------------------------------------------------
def min_gridlock(h: int, w: int) -> int:
    """Least car count of a gridlock: a blocker cycle winds round the torus, two cells a block."""
    return 2 * min(h, w)


def gridlock_with(h: int, w: int, n: int) -> State:
    """A gridlock with exactly n cars, 2·min(W,H) ≤ n ≤ 3WH: a full ring of the shorter
    species, then cars queued behind it, each blocked by an earlier one."""
    assert min_gridlock(h, w) <= n <= CELLS_PER_ROUNDABOUT * h * w
    if h < w:                                  # mirror image of the w ≤ h construction
        return transpose(gridlock_with(w, h, n))
    order = [("a", 0, x) for x in range(w)] + [("c", 0, x) for x in range(w)]       # full row 0
    order += [(k, y, x) for x in range(w)                                       # columns, downwards
              for y in range(h - 1, 0, -1) for k in ("b", "c")] + [("b", 0, x) for x in range(w)]
    order += [("a", y, x) for y in range(1, h) for x in range(w)]                   # rows behind them
    s = empty(h, w)
    for k, y, x in order[:n]:
        getattr(s, k)[y, x] = {"a": True, "b": True, "c": EAST if y == 0 else NORTH}[k]
    return s


def transpose(s: State) -> State:
    """The mirror x ↔ y: swaps species and the yield rule. b(x,y) precedes c(x,y+1) as
    a(x,y) precedes c(x,y), hence the shift."""
    swap = np.select([s.c == EAST, s.c == NORTH], [NORTH, EAST], EMPTY).astype(np.int8)
    return State(np.roll(s.b.swapaxes(Y, X), 1, axis=X), swap.swapaxes(Y, X),
                 np.roll(s.a.swapaxes(Y, X), -1, axis=Y))


# ---- exhaustive enumeration -----------------------------------------------------------
def all_states(h: int, w: int) -> State:
    """Every configuration of the h×w board, as one batch of 12**(h·w) states."""
    digits = np.arange(12 ** (h * w))[:, None] // 12 ** np.arange(h * w) % 12
    grid = digits.reshape(-1, h, w)
    return State(grid % 2 == 1, (grid // 2 % 3).astype(np.int8), grid // 6 == 1)


def free_levels(h: int, w: int, priority: int = EAST) -> list[State]:
    """Every free configuration of the h×w board, grouped by car count, found from the
    dynamics alone. Freeness is hereditary (removing a car blocks nobody), so growing each
    n-car free configuration by one car in a later slot reaches every (n+1)-car one once."""
    n = h * w
    assert 4 * n < 63, "configurations are packed into int64 bitmasks"
    slots = np.arange(4 * n)                       # layers: a, c=EAST, c=NORTH, b
    rival = np.where(slots // n == 2, slots - n, slots)

    def unpack(codes: np.ndarray) -> State:
        layer = (codes[:, None] >> slots & 1).astype(bool).reshape(-1, 4, h, w)
        return State(layer[:, 0], (layer[:, 1] * EAST + layer[:, 2] * NORTH).astype(np.int8), layer[:, 3])

    level, levels = np.zeros(1, np.int64), []
    while level.size:
        levels.append(unpack(level))
        taken = (level[:, None] >> slots & 1).astype(bool)
        later = slots > np.where(taken, slots, -1).max(axis=1, keepdims=True)
        grown = (level[:, None] | 1 << slots)[later & ~taken[:, rival]]
        chunks = [grown[i:i + 2 ** 17] for i in range(0, grown.size, 2 ** 17)]
        level = np.concatenate([c[is_free(unpack(c), priority)] for c in chunks] or [grown])
    return levels
