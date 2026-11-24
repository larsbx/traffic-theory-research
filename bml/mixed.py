"""Mixed BML: a W×H torus on which a chosen set R of intersections are roundabouts and the
rest keep the BML signal (docs/research/2026-11-24-mixed-roundabout-grid.md).

``ring[y, x]`` is True on R. A state reuses ``bml.roundabout.State``: c is the junction cell of
every intersection (the BML cell of a signal, the shared quadrant of a roundabout); a and b are
the private quadrants and stay empty off R.

Routes:  EAST   c(x,y) → [a(x+1,y) if (x+1,y) ∈ R] → c(x+1,y)
         NORTH  c(x,y) → [b(x,y)   if (x,y)   ∈ R] → c(x,y+1)

One tick moves every car whose next cell is empty at the start of the tick and which is not
held by a signal: a signal junction admits EAST cars at even ticks and NORTH cars at odd ticks.
Roundabouts have no signal; their merge goes to ``priority``. With R = ∅, ticks 2t and 2t+1
are the two half-steps of ``bml.model.step``; with R everything, each tick is
``bml.roundabout.step``.

All functions are pure. ``step`` and the predicates accept batches (..., H, W) of states.
"""
from __future__ import annotations

from fractions import Fraction
from math import comb

import numpy as np

from bml.model import EMPTY, EAST, NORTH
from bml.roundabout import X, Y, State, counts, empty, grow_free


def cells(ring: np.ndarray) -> int:
    return ring.size + 2 * int(ring.sum())


def valid(s: State, ring: np.ndarray) -> np.ndarray | bool:
    """Private quadrants exist only at roundabouts."""
    return ~((s.a | s.b) & ~ring).any(axis=(Y, X))


def _entries(s: State, ring: np.ndarray, tick: int, priority: int) -> State:
    """Masks, indexed by target cell, of the cells entered in this tick. For c the mask is the
    entering species (EMPTY if none)."""
    vacant = s.c == EMPTY
    east_behind = np.roll(s.c == EAST, 1, axis=X)                       # EAST car in c(x-1, y)
    north_behind = np.where(np.roll(ring, 1, axis=Y), np.roll(s.b, 1, axis=Y),
                            np.roll(s.c == NORTH, 1, axis=Y))           # NORTH car about to reach c
    east_in = vacant & np.where(ring, s.a & ((priority == EAST) | ~north_behind), east_behind & (tick % 2 == 0))
    north_in = vacant & north_behind & np.where(ring, (priority == NORTH) | ~s.a, tick % 2 == 1)
    into_c = np.select([east_in, north_in], [EAST, NORTH], EMPTY).astype(np.int8)
    return State(ring & east_behind & ~s.a, into_c, ring & (s.c == NORTH) & ~s.b)


def step(s: State, ring: np.ndarray, tick: int, priority: int = EAST) -> tuple[State, np.ndarray | int]:
    """One tick; return (new state, #moves)."""
    into = _entries(s, ring, tick, priority)
    east_out = np.roll(into.a | ((into.c == EAST) & ~ring), -1, axis=X)       # leaves c(x,y) eastwards
    north_on = np.roll(into.c == NORTH, -1, axis=Y)                           # c(x,y+1) is entered
    left_c = ((s.c == EAST) & east_out) | into.b | ((s.c == NORTH) & ~ring & north_on)
    c = np.where(into.c != EMPTY, into.c, np.where(left_c, EMPTY, s.c)).astype(np.int8)
    new = State((s.a & ~(into.c == EAST)) | into.a, c, (s.b & ~north_on) | into.b)
    moved = into.a.sum(axis=(Y, X)) + (into.c != EMPTY).sum(axis=(Y, X)) + into.b.sum(axis=(Y, X))
    return new, moved


def is_fixed(s: State, ring: np.ndarray) -> np.ndarray | bool:
    """Lemma MX-0: no car ever moves ⟺ every car's next cell on its route is occupied."""
    full = s.c != EMPTY
    east_next = np.roll(np.where(ring, s.a, full), -1, axis=X)
    north_next = np.where(ring, s.b, np.roll(full, -1, axis=Y))
    stuck = ((~s.a | full) & (~s.b | np.roll(full, -1, axis=Y))
             & ((s.c != EAST) | east_next) & ((s.c != NORTH) | north_next))
    return stuck.all(axis=(Y, X))



def held(s: State, ring: np.ndarray, tick: int) -> np.ndarray | int:
    """Number of cars whose next cell is a signal junction showing them red in this tick."""
    east = (s.c == EAST) & ~np.roll(ring, -1, axis=X) & (tick % 2 == 1)
    north = np.where(ring, s.b, s.c == NORTH) & ~np.roll(ring, -1, axis=Y) & (tick % 2 == 0)
    return (east | north).sum(axis=(Y, X))


def is_free(s: State, ring: np.ndarray, priority: int = EAST) -> np.ndarray | bool:
    """Free: from tick 0 on, no car is ever delayed by another car; a car waits only for its
    signal. An undelayed car is on its periodic timetable once it has passed a signal, within
    one lap of its street, and the timetable has period 2·lcm(W,H). So 4·lcm(W,H) + 2 ticks
    decide freeness."""
    h, w = ring.shape
    n = sum(counts(s))
    ok = np.ones_like(n, dtype=bool)
    for tick in range(4 * np.lcm(h, w) + 2):
        waiting = held(s, ring, tick)
        s, moved = step(s, ring, tick, priority)
        ok = ok & (moved == n - waiting)
    return ok


def free_levels(ring: np.ndarray, priority: int = EAST) -> list[State]:
    """Every free configuration on the placement ``ring``, grouped by car count."""
    junction = np.ones_like(ring)
    return grow_free(*ring.shape, lambda s: is_free(s, ring, priority), np.stack([ring, junction, junction, ring]))


# ---- Proposition MX-F: junction time budget --------------------------------------------
def junction_load(s: State, ring: np.ndarray) -> np.ndarray:
    """MX-F: the share of time junction (x,y) is spoken for in free flow, as exact fractions.
    A visit holds the junction for 1 tick, or 2 if the car must wait there for a signal, and
    is followed by an empty tick. EAST cars wait iff the next junction east is a signal;
    NORTH cars iff this junction and the next one north are both signals. Free ⟹ load ≤ 1."""
    h, w = ring.shape
    east = s.a.sum(axis=X) + (s.c == EAST).sum(axis=X)            # per row
    north = s.b.sum(axis=Y) + (s.c == NORTH).sum(axis=Y)          # per column
    wait_e = ~np.roll(ring, -1, axis=X)
    wait_n = ~ring & ~np.roll(ring, -1, axis=Y)
    return np.array([[Fraction(int(east[y]) * (2 + int(wait_e[y, x])), 2 * w)
                      + Fraction(int(north[x]) * (2 + int(wait_n[y, x])), 2 * h)
                      for x in range(w)] for y in range(h)], dtype=object)


# ---- Theorem MX-G: gridlock as a function of R -----------------------------------------
def min_gridlock(ring: np.ndarray) -> int:
    """MX-G: the least gridlock is the straight street with the fewest roundabouts."""
    h, w = ring.shape
    return int(min(w + ring.sum(axis=X).min(), h + ring.sum(axis=Y).min()))


def successor(ring: np.ndarray, cell: tuple[str, int, int], species: int) -> tuple[str, int, int] | None:
    """The next cell on the route of a ``species`` car in ``cell`` = (layer, y, x), or None if
    that species never occupies the cell."""
    h, w = ring.shape
    k, y, x = cell
    if k == "a":
        return ("c", y, x) if species == EAST else None
    if k == "b":
        return ("c", (y + 1) % h, x) if species == NORTH else None
    if species == EAST:
        return ("a" if ring[y, (x + 1) % w] else "c", y, (x + 1) % w)
    return ("b", y, x) if ring[y, x] else ("c", (y + 1) % h, x)


def all_cells(ring: np.ndarray) -> list[tuple[str, int, int]]:
    h, w = ring.shape
    return [(k, y, x) for y in range(h) for x in range(w) for k in "acb" if k == "c" or ring[y, x]]


def girth(ring: np.ndarray) -> int:
    """Length of the shortest directed cycle of the blocker graph (cells, with an edge to the
    successor under either species), by breadth-first search from every cell. Independent of
    the formula in ``min_gridlock``."""
    nodes = all_cells(ring)
    succ = {v: [t for sp in (EAST, NORTH) if (t := successor(ring, v, sp))] for v in nodes}
    best = len(nodes)
    for root in nodes:
        dist, frontier = {root: 0}, [root]
        while frontier:
            nxt = []
            for v in frontier:
                for t in succ[v]:
                    if t == root:
                        best = min(best, dist[v] + 1)
                    elif t not in dist:
                        dist[t] = dist[v] + 1
                        nxt.append(t)
            frontier = nxt
    return best


def gridlock_with(ring: np.ndarray, n: int) -> State:
    """A gridlock with exactly n cars, min_gridlock(R) ≤ n ≤ WH + 2|R|: fill the cheapest
    straight street, then repeatedly queue a car behind an occupied cell."""
    h, w = ring.shape
    assert min_gridlock(ring) <= n <= cells(ring)
    rows, cols = w + ring.sum(axis=X), h + ring.sum(axis=Y)
    if rows.min() <= cols.min():
        y = int(rows.argmin())
        placed = {(k, y, x): EAST for x in range(w) for k in "ac" if k == "c" or ring[y, x]}
    else:
        x = int(cols.argmin())
        placed = {(k, y, x): NORTH for y in range(h) for k in "cb" if k == "c" or ring[y, x]}
    queue = [(v, sp) for v in all_cells(ring) for sp in (EAST, NORTH)]
    while len(placed) < n:
        v, sp = next((v, sp) for v, sp in queue if v not in placed and successor(ring, v, sp) in placed)
        placed[v] = sp
    s = empty(h, w)
    for (k, y, x), sp in placed.items():
        getattr(s, k)[y, x] = sp if k == "c" else True
    return s


# ---- Corollaries MX-E, MX-P: dependence on the number of roundabouts -------------------
def best_min_gridlock(h: int, w: int, k: int) -> int:
    """Largest least-gridlock over all placements of k roundabouts."""
    return min(w + k // h, h + k // w)


def worst_min_gridlock(h: int, w: int, k: int) -> int:
    """Smallest least-gridlock over all placements of k roundabouts."""
    return min(w + max(0, k - w * (h - 1)), h + max(0, k - h * (w - 1)))


def balanced(h: int, w: int, k: int) -> np.ndarray:
    """A placement attaining ``best_min_gridlock``: the k roundabouts are laid row after row,
    each row continuing cyclically at the column where the previous one stopped, so every row
    holds ⌊k/H⌋ or ⌈k/H⌉ and every column ⌊k/W⌋ or ⌈k/W⌉."""
    assert 0 <= k <= h * w
    ring = np.zeros((h, w), bool)
    start = 0
    for y in range(h):
        r = k // h + (y < k % h)
        ring[y, (start + np.arange(r)) % w] = True
        start += r
    return ring


def random_min_gridlock_tail(h: int, w: int, rho: Fraction, j: int) -> Fraction:
    """MX-P, for H ≥ 2W and each intersection a roundabout independently with probability ρ:
    P(least gridlock ≥ W + j) = P(Bin(W, ρ) ≥ j)^H, exactly."""
    assert h >= 2 * w
    return sum((comb(w, i) * rho ** i * (1 - rho) ** (w - i) for i in range(j, w + 1)), Fraction()) ** h
