"""When do jams form? Formation time of the first mixed blocker cycle (Monte Carlo).

A *mixed simple direct-blocker cycle* is a closed loop of cars, each blocked by the next, that
contains both species (equivalently, positive winding in both directions; see
`bml.capture.BlockerCycle.mixed`). Such a cycle never moves again and captures the torus
(`docs/research/2026-11-18-freezing-gridlock-nucleation.md`). Its first appearance T_M is the
formation time of the jam's seed. This module measures T_M empirically. It proves nothing.

Detection is vectorized over a batch:
- the blocker map sends an occupied cell to the cell ahead if that cell is occupied, and to a
  sink otherwise;
- pointer doubling sends every cell onto a cycle or into the sink;
- a mixed cycle exists iff some cycle cell holds an E car whose blocker holds an N car (a pure
  cycle is a full row or column and has no E→N turn).
"""
from __future__ import annotations

import numpy as np

from bml.model import EAST, NORTH, step


def _ahead_index(h: int, w: int) -> tuple[np.ndarray, np.ndarray]:
    y, x = np.indices((h, w))
    east = (y * w + (x + 1) % w).ravel()
    north = (((y + 1) % h) * w + x).ravel()
    return east, north


def mixed_cycle_present(batch: np.ndarray) -> np.ndarray:
    """Bool per configuration: does a mixed simple direct-blocker cycle exist now?"""
    B, h, w = batch.shape
    N = h * w
    east, north = _ahead_index(h, w)
    s = batch.reshape(B, N)
    ahead = np.where(s == EAST, east[None, :], north[None, :])
    occupied = s != 0
    target_occ = np.take_along_axis(occupied, ahead, axis=1)
    sink = N
    nxt = np.where(occupied & target_occ, ahead, sink)
    nxt = np.concatenate([nxt, np.full((B, 1), sink)], axis=1)          # sink maps to itself
    g = nxt.copy()
    for _ in range(int(np.ceil(np.log2(N + 1))) + 1):                  # g = blocker^(2^K) ≥ N
        g = np.take_along_axis(g, g, axis=1)
    on_cycle = np.zeros((B, N + 1), bool)
    np.put_along_axis(on_cycle, g, True, axis=1)                        # images are cycle cells
    on_cycle = on_cycle[:, :N] & occupied
    succ_species = np.take_along_axis(s, np.minimum(nxt[:, :N], N - 1), axis=1)
    turn = on_cycle & (s == EAST) & (succ_species == NORTH) & (nxt[:, :N] != sink)
    return turn.any(axis=1)


def sample(rng: np.random.Generator, B: int, L: int, p: float) -> np.ndarray:
    u = rng.random((B, L, L))
    return np.where(u < p / 2, EAST, np.where(u < p, NORTH, 0)).astype(np.int8)


def formation_times(L: int, p: float, B: int, horizon: int, seed: int = 0) -> np.ndarray:
    """First round t ≤ horizon at which a mixed cycle is present; −1 if none by the horizon."""
    rng = np.random.default_rng(seed)
    s = sample(rng, B, L, p)
    T = np.full(B, -1)
    alive = np.arange(B)
    for t in range(horizon + 1):
        if len(alive) == 0:
            break
        hit = mixed_cycle_present(s)
        T[alive[hit]] = t
        s, alive = s[~hit], alive[~hit]
        s = step(s)[0]
    return T


def formation_sweep(L: int, p: float, B: int, horizon: int, every: int, seed: int = 0,
                    initial: np.ndarray | None = None):
    """T_M measured every `every` rounds and at the horizon (resolution `every`), plus
    frozen-at-horizon flags. Pass `initial` (shape (B, L, L)) to replay given configurations.

    Returns (T, frozen): T[i] is the first checked round with a mixed cycle (−1 if none by the
    horizon), and frozen[i] says whether sample i is a nonempty fixed point at the horizon.
    """
    s = sample(np.random.default_rng(seed), B, L, p) if initial is None else initial.copy()
    T = np.full(len(s), -1)
    for t in range(horizon + 1):
        if t % every == 0 or t == horizon:              # always check the horizon itself
            undetected = T < 0
            if undetected.any():
                hit = mixed_cycle_present(s[undetected])
                idx = np.nonzero(undetected)[0][hit]
                T[idx] = t
        if t < horizon:
            s = step(s)[0]
    nxt, moves = step(s)
    frozen = (moves == 0) & (s != 0).any(axis=(1, 2))
    return T, frozen
