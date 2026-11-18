"""Exact classification of every configuration on a small W×H torus.

The step map f on all 3^(WH) states is a functional graph. With pointer doubling,
g = f^(2^K) sends each state onto its terminal cycle (2^K ≥ #states ≥ transient), and
mn[x] = min_{0≤i<2^K} moves(f^i x) covers that whole cycle. The terminal cycle is
  JAM   : no car ever moves (max moves on the cycle is 0; under CLASSIC a fixed point, G0),
  FREE  : every car moves at every step,
  MIXED : otherwise (positive but sub-maximal mean velocity).
The empty configuration is classified FREE (vacuously).
"""
from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from bml.model import step, EAST, NORTH, CLASSIC

JAM, FREE, MIXED = 0, 1, 2
CHUNK = 1 << 21


def decode(idx: np.ndarray, h: int, w: int) -> np.ndarray:
    pw = 3 ** np.arange(h * w, dtype=np.int64)
    return ((idx[:, None] // pw) % 3).astype(np.int8).reshape(-1, h, w)


def encode(states: np.ndarray) -> np.ndarray:
    flat = states.reshape(len(states), -1).astype(np.int64)
    return flat @ (3 ** np.arange(flat.shape[1], dtype=np.int64))


@dataclass(frozen=True)
class Classification:
    h: int
    w: int
    f: np.ndarray        # successor index
    cls: np.ndarray      # JAM / FREE / MIXED per state
    n_east: np.ndarray
    n_north: np.ndarray


def classify_all(h: int, w: int, rule: str = CLASSIC) -> Classification:
    size = 3 ** (h * w)
    f = np.empty(size, np.uint32)
    m = np.empty(size, np.uint8)
    ne = np.empty(size, np.uint8)
    nn = np.empty(size, np.uint8)
    for lo in range(0, size, CHUNK):
        s = decode(np.arange(lo, min(lo + CHUNK, size), dtype=np.int64), h, w)
        t, moves = step(s, rule)
        f[lo:lo + len(s)] = encode(t)
        m[lo:lo + len(s)] = moves
        ne[lo:lo + len(s)] = (s == EAST).sum(axis=(1, 2))
        nn[lo:lo + len(s)] = (s == NORTH).sum(axis=(1, 2))
    g, mn, mx = f.copy(), m.copy(), m.copy()
    for _ in range(int(np.ceil(np.log2(size))) + 1):
        mn, mx = np.minimum(mn, mn[g]), np.maximum(mx, mx[g])
        g = g[g]
    n = ne.astype(np.int16) + nn
    cyc_max_zero = mx[g] == 0                     # nobody moves on the terminal cycle
    cls = np.where(n == 0, FREE,
          np.where(cyc_max_zero, JAM,
          np.where(mn[g] == n, FREE, MIXED))).astype(np.uint8)
    return Classification(h, w, f, cls, ne, nn)
