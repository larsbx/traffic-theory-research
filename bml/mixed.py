"""Mixed BML: a W×H torus on which a chosen set R of intersections are roundabouts and the
rest keep the BML signal (docs/research/2026-11-24-mixed-roundabout-grid.md).

``ring[y, x]`` is True on R. c is the junction cell of every intersection (the BML cell of a
signal, the shared quadrant of a roundabout); a and b are the private quadrants and stay empty
off R. A state is a ``bml.roundabout.State`` (a, c, b), or a ``Linked`` state (a, c, b, e, n)
which adds one private link cell per street segment: e(x,y) east of c(x,y) and n(x,y) north of
it, after b(x,y).

Routes:  EAST   c(x,y) → [e(x,y)] → [a(x+1,y) if (x+1,y) ∈ R] → c(x+1,y)
         NORTH  c(x,y) → [b(x,y) if (x,y) ∈ R] → [n(x,y)] → c(x,y+1)

One tick moves every car whose next cell is empty at the start of the tick and which is not
held by a signal: a signal junction admits EAST cars at even ticks and NORTH cars at odd ticks.
Roundabouts have no signal; their merge goes to ``priority``. Without links and with R = ∅,
ticks 2t and 2t+1 are the two half-steps of ``bml.model.step``; with R everything, each tick
is ``bml.roundabout.step``.

All functions are pure. ``step`` and the predicates accept batches (..., H, W) of states.
"""
from __future__ import annotations

from fractions import Fraction
from math import comb, lcm
from typing import NamedTuple

import numpy as np

from bml.model import EMPTY, EAST, NORTH
from bml.roundabout import X, Y, State, _junction, grow_free


class Linked(NamedTuple):
    a: np.ndarray      # bool:  EAST car in the roundabout's EAST-private quadrant
    c: np.ndarray      # int8:  EMPTY / EAST / NORTH in the junction cell
    b: np.ndarray      # bool:  NORTH car in the roundabout's NORTH-private quadrant
    e: np.ndarray      # bool:  EAST car on the link east of the junction
    n: np.ndarray      # bool:  NORTH car on the link north of the junction


def linked(s) -> bool:
    return len(s) == 5


def empty(h: int, w: int, link: bool = False):
    off = lambda: np.zeros((h, w), bool)   # noqa: E731
    return Linked(off(), np.zeros((h, w), np.int8), off(), off(), off()) if link else \
        State(off(), np.zeros((h, w), np.int8), off())


def counts(s) -> tuple[np.ndarray | int, np.ndarray | int]:
    """(#EAST, #NORTH) cars, per batch element."""
    total = lambda *layers: sum(v.sum(axis=(Y, X)) for v in layers)   # noqa: E731
    return (total(s.a, s.c == EAST, *([s.e] if linked(s) else [])),
            total(s.b, s.c == NORTH, *([s.n] if linked(s) else [])))


def cells(ring: np.ndarray, link: bool = False) -> int:
    return (1 + 2 * link) * ring.size + 2 * int(ring.sum())


def valid(s, ring: np.ndarray) -> np.ndarray | bool:
    """Private quadrants exist only at roundabouts."""
    return ~((s.a | s.b) & ~ring).any(axis=(Y, X))


class _Chain(NamedTuple):
    """One species' cells between consecutive junctions, all indexed by the target junction v:
    stage 0 is the junction behind v (always present), the others the private cells before v."""
    occupied: list[np.ndarray]
    exists: list[np.ndarray | bool]
    axis: int


def _chains(s, ring: np.ndarray) -> tuple[_Chain, _Chain]:
    link, none = np.full_like(ring, linked(s)), np.zeros_like(s.a)
    back = lambda v, axis: np.roll(v, 1, axis=axis)   # noqa: E731
    east = _Chain([back(s.c == EAST, X), back(s.e, X) if linked(s) else none, s.a],
                  [np.ones_like(ring), link, ring], X)
    north = _Chain([back(s.c == NORTH, Y), back(s.b, Y), back(s.n, Y) if linked(s) else none],
                   [np.ones_like(ring), back(ring, Y), link], Y)
    return east, north


def _front(chain: _Chain) -> tuple[list[np.ndarray], np.ndarray]:
    """For each private stage, whether a car is directly behind it; and whether a car is
    directly behind the junction."""
    feeder, behind = chain.occupied[0], []
    for occ, ex in zip(chain.occupied[1:], chain.exists[1:]):
        behind.append(ex & feeder)
        feeder = np.where(ex, occ, feeder)
    return behind, feeder


def _advance(chain: _Chain, into_junction: np.ndarray) -> tuple[np.ndarray, list[np.ndarray], np.ndarray | int]:
    """Given the junction entries of this species, move the chain one tick. Returns the mask
    of cars leaving the junction behind (indexed by that junction), the new private stages
    (indexed by the target junction) and the number of moves."""
    behind, _ = _front(chain)
    enters = [b & ~occ for b, occ in zip(behind, chain.occupied[1:])]
    ahead, leaves = into_junction, []
    for j in (2, 1, 0):                                   # from the junction backwards
        leaves.append(chain.exists[j] & chain.occupied[j] & ahead)
        if j:
            ahead = np.where(chain.exists[j], enters[j - 1], ahead)
    leaves.reverse()
    new = [(occ & ~out) | into for occ, out, into in zip(chain.occupied[1:], leaves[1:], enters)]
    moved = sum(v.sum(axis=(Y, X)) for v in (*enters, into_junction))
    return np.roll(leaves[0], -1, axis=chain.axis), new, moved


def step(s, ring: np.ndarray, tick: int, priority: int = EAST):
    """One tick; return (new state, #moves)."""
    east, north = _chains(s, ring)
    vacant = s.c == EMPTY
    (_, e_front), (_, n_front) = _front(east), _front(north)
    east_in = vacant & e_front & np.where(ring, (priority == EAST) | ~n_front, tick % 2 == 0)
    north_in = vacant & n_front & np.where(ring, (priority == NORTH) | ~e_front, tick % 2 == 1)
    east_out, (e_new, a_new), east_moves = _advance(east, east_in)
    north_out, (b_new, n_new), north_moves = _advance(north, north_in)
    home = lambda v: np.roll(v, -1, axis=Y)   # noqa: E731  (v's NORTH chain lives at v − ŷ)
    c = np.where((s.c == EAST) & east_out | (s.c == NORTH) & north_out, EMPTY, s.c)
    c = np.select([east_in, north_in], [EAST, NORTH], c).astype(np.int8)
    new = (a_new, c, home(b_new)) + ((np.roll(e_new, -1, axis=X), home(n_new)) if linked(s) else ())
    return type(s)(*new), east_moves + north_moves


def is_fixed(s, ring: np.ndarray) -> np.ndarray | bool:
    """Lemma MX-0: no car ever moves ⟺ every car's next cell on its route is occupied."""
    ok = True
    for chain in _chains(s, ring):
        behind, front = _front(chain)
        ok = ok & (~front | (s.c != EMPTY))
        for b, occ in zip(behind, chain.occupied[1:]):
            ok = ok & (~b | occ)
    return ok.all(axis=(Y, X))


def held(s, ring: np.ndarray, tick: int) -> np.ndarray | int:
    """Number of cars whose next cell is a signal junction showing them red in this tick."""
    (_, e_front), (_, n_front) = (_front(chain) for chain in _chains(s, ring))
    return ((e_front & (tick % 2 == 1) | n_front & (tick % 2 == 0)) & ~ring).sum(axis=(Y, X))


def laps(ring: np.ndarray, link: bool = False) -> tuple[list[int], list[int]]:
    """Ticks an undelayed car needs for one lap of each row (EAST) and each column (NORTH), on
    its periodic timetable: the number of cells from one signal to the next, rounded up to
    even, summed round the street; the number of cells if the street has no signal."""
    def lap(street: np.ndarray) -> int:
        signals = np.flatnonzero(~street)
        if signals.size == 0:
            return (2 + link) * street.size
        blocks = np.diff(np.append(signals, signals[0] + street.size))
        moves = blocks * (1 + link) + blocks - 1          # links, junctions, roundabout quadrants
        return int((moves + moves % 2).sum())
    return [lap(row) for row in ring], [lap(col) for col in ring.T]


def is_free(s, ring: np.ndarray, priority: int = EAST) -> np.ndarray | bool:
    """Free: from tick 0 on, no car is ever delayed by another car; a car waits only for its
    signal. An undelayed car is on its periodic timetable once it has passed a signal, within
    one lap, so one longest lap plus one common period of ticks decide freeness."""
    rows, cols = laps(ring, linked(s))
    n = sum(counts(s))
    ok = np.ones_like(n, dtype=bool)
    for tick in range(max(rows + cols) + 2 + lcm(2, *rows, *cols)):
        waiting = held(s, ring, tick)
        s, moved = step(s, ring, tick, priority)
        ok = ok & (moved == n - waiting)
    return ok


def free_levels(ring: np.ndarray, priority: int = EAST, link: bool = False) -> list:
    """Every free configuration on the placement ``ring``, grouped by car count."""
    every = np.ones_like(ring)
    layers = [ring, every, every, ring] + [every, every] * link
    build = (lambda v: Linked(v[:, 0], _junction(v), v[:, 3], v[:, 4], v[:, 5])) if link else None
    return grow_free(*ring.shape, lambda s: is_free(s, ring, priority), np.stack(layers), build)


# ---- Proposition MX-F: junction time budget --------------------------------------------
def junction_load(s, ring: np.ndarray) -> np.ndarray:
    """MX-F: the share of time junction (x,y) is spoken for in free flow, as exact fractions.
    A visit holds the junction for 1 tick, or 2 if the car must wait there for a signal, and
    is followed by an empty tick. With links nobody waits in a junction. Without them EAST
    cars wait iff the next junction east is a signal, NORTH cars iff this junction and the
    next one north are both signals. Free ⟹ load ≤ 1."""
    h, w = ring.shape
    east, north = (np.zeros(h, int), np.zeros(w, int))
    for layer, axis, tally in ((s.a, X, east), (s.c == EAST, X, east), (s.b, Y, north), (s.c == NORTH, Y, north),
                               *(((s.e, X, east), (s.n, Y, north)) if linked(s) else ())):
        tally += layer.sum(axis=axis)
    wait_e = ~np.roll(ring, -1, axis=X) & (not linked(s))
    wait_n = ~ring & ~np.roll(ring, -1, axis=Y) & (not linked(s))
    rows, cols = laps(ring, linked(s))
    return np.array([[Fraction(int(east[y]) * (2 + int(wait_e[y, x])), rows[y])
                      + Fraction(int(north[x]) * (2 + int(wait_n[y, x])), cols[x])
                      for x in range(w)] for y in range(h)], dtype=object)


# ---- Theorem MX-G: gridlock as a function of R -----------------------------------------
def min_gridlock(ring: np.ndarray, link: bool = False) -> int:
    """MX-G: the least gridlock is the straight street with the fewest roundabouts."""
    h, w = ring.shape
    return int(min((1 + link) * w + ring.sum(axis=X).min(), (1 + link) * h + ring.sum(axis=Y).min()))


Cell = tuple[str, int, int]


def successor(ring: np.ndarray, cell: Cell, species: int, link: bool = False) -> Cell | None:
    """The next cell on the route of a ``species`` car in ``cell`` = (layer, y, x), or None if
    that species never occupies the cell."""
    h, w = ring.shape
    k, y, x = cell
    if (k in "ae") != (species == EAST) and k != "c":
        return None
    east = ("a" if ring[y, (x + 1) % w] else "c", y, (x + 1) % w)
    north = ("c", (y + 1) % h, x)
    after_b = ("n", y, x) if link else north
    return {"a": ("c", y, x), "e": east, "b": after_b, "n": north}.get(k) or (
        (("e", y, x) if link else east) if species == EAST else (("b", y, x) if ring[y, x] else after_b))


def all_cells(ring: np.ndarray, link: bool = False) -> list[Cell]:
    h, w = ring.shape
    return [(k, y, x) for y in range(h) for x in range(w) for k in "acben"
            if k == "c" or (k in "ab" and ring[y, x]) or (k in "en" and link)]


def girth(ring: np.ndarray, link: bool = False) -> int:
    """Length of the shortest directed cycle of the blocker graph (cells, with an edge to the
    successor under either species), by breadth-first search from every cell. Independent of
    the formula in ``min_gridlock``."""
    nodes = all_cells(ring, link)
    succ = {v: [t for sp in (EAST, NORTH) if (t := successor(ring, v, sp, link))] for v in nodes}
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


def gridlock_with(ring: np.ndarray, n: int, link: bool = False):
    """A gridlock with exactly n cars, min_gridlock ≤ n ≤ cells: fill the cheapest straight
    street, then repeatedly queue a car behind an occupied cell."""
    h, w = ring.shape
    assert min_gridlock(ring, link) <= n <= cells(ring, link)
    rows, cols = ring.sum(axis=X), ring.sum(axis=Y)
    if (1 + link) * w + rows.min() <= (1 + link) * h + cols.min():
        species, start = EAST, ("c", int(rows.argmin()), 0)
    else:
        species, start = NORTH, ("c", 0, int(cols.argmin()))
    placed, v = {start: species}, successor(ring, start, species, link)
    while v != start:
        placed[v] = species
        v = successor(ring, v, species, link)
    queue = [(v, sp) for v in all_cells(ring, link) for sp in (EAST, NORTH)]
    while len(placed) < n:
        v, sp = next((v, sp) for v, sp in queue if v not in placed and successor(ring, v, sp, link) in placed)
        placed[v] = sp
    s = empty(h, w, link)
    for (k, y, x), sp in placed.items():
        getattr(s, k)[y, x] = sp if k == "c" else True
    return s


# ---- Corollaries MX-E, MX-P: dependence on the number of roundabouts -------------------
def best_min_gridlock(h: int, w: int, k: int, link: bool = False) -> int:
    """Largest least-gridlock over all placements of k roundabouts."""
    return min((1 + link) * w + k // h, (1 + link) * h + k // w)


def worst_min_gridlock(h: int, w: int, k: int, link: bool = False) -> int:
    """Smallest least-gridlock over all placements of k roundabouts."""
    return min((1 + link) * w + max(0, k - w * (h - 1)), (1 + link) * h + max(0, k - h * (w - 1)))


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
    """MX-P, for H ≥ 2W, no links, and each intersection a roundabout independently with
    probability ρ: P(least gridlock ≥ W + j) = P(Bin(W, ρ) ≥ j)^H, exactly."""
    assert h >= 2 * w
    return sum((comb(w, i) * rho ** i * (1 - rho) ** (w - i) for i in range(j, w + 1)), Fraction()) ** h
