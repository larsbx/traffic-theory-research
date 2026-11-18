"""Empirical (non-rigorous) jam probability vs density on L×L, i.i.d. initial data:
each cell EAST w.p. p/2, NORTH w.p. p/2, else EMPTY (the original BML measure)."""
from __future__ import annotations

import sys

import numpy as np

from bml.model import EAST, NORTH, step


def sample(rng, batch, L, p):
    u = rng.random((batch, L, L))
    return np.where(u < p / 2, EAST, np.where(u < p, NORTH, 0)).astype(np.int8)


def jam_fraction(L, p, batch=32, T=20_000, seed=0):
    s = sample(np.random.default_rng(seed), batch, L, p)
    n = (s != 0).sum(axis=(1, 2))
    for _ in range(T):
        s, m = step(s)
    _, m = step(s)
    return float((m == 0).mean()), float((m / n).mean())


if __name__ == "__main__":
    L, T = int(sys.argv[1]), int(sys.argv[2])
    for p in np.round(np.arange(0.20, 0.56, 0.025), 3):
        jam, v = jam_fraction(L, p, T=T)
        print(f"L={L} p={p:.3f} jammed={jam:.2f} mean_velocity={v:.3f}", flush=True)
