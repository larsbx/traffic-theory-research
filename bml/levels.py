"""Exact jam counts at a single car count n, beyond exhaustive sizes.

Jamming is translation-invariant, and summing #cars over n-car configurations gives n·#configs
spread evenly over the N cells. So

    jam_n = (N / n) · #{jamming n-car configurations with a car at cell 0},

which needs only a fraction n/N of the level. Each configuration is classified exactly with
Floyd cycle detection: it jams iff the cycle its orbit reaches is a fixed point. No time
horizon is involved.
"""
from __future__ import annotations

import itertools
import sys
from fractions import Fraction
from math import comb

import numpy as np

from bml.model import step


def jams(batch: np.ndarray) -> np.ndarray:
    """Exact eventual-jam flags for a batch of configurations (Floyd tortoise and hare)."""
    slow, fast = batch, step(batch)[0]
    result = np.zeros(len(batch), bool)
    alive = np.arange(len(batch))
    while len(alive):
        slow, fast = step(slow)[0], step(step(fast)[0])[0]
        met = (slow == fast).all(axis=(1, 2))
        if met.any():
            result[alive[met]] = (step(slow[met])[0] == slow[met]).all(axis=(1, 2))
            slow, fast, alive = slow[~met], fast[~met], alive[~met]
    return result


def level_jam_count(h: int, w: int, n: int, chunk: int = 4000) -> int:
    N = h * w
    species = np.array(list(itertools.product((1, 2), repeat=n)), np.int8)
    combos = list(itertools.combinations(range(1, N), n - 1))
    rooted = 0
    for i in range(0, len(combos), chunk):
        pos = np.array([(0,) + c for c in combos[i:i + chunk]])
        flat = np.zeros((len(pos), len(species), N), np.int8)
        flat[np.arange(len(pos))[:, None, None], np.arange(len(species))[None, :, None],
             pos[:, None, :]] = species[None, :, :]
        rooted += int(jams(flat.reshape(-1, h, w)).sum())
    assert (rooted * N) % n == 0
    return rooted * N // n


def level_fraction(h: int, w: int, n: int) -> Fraction:
    return Fraction(level_jam_count(h, w, n), comb(h * w, n) * 2 ** n)


if __name__ == "__main__":
    h, w, *levels = map(int, sys.argv[1:])
    for n in levels:
        j = level_jam_count(h, w, n)
        print(f"{h}x{w} n={n}: jam={j} b_n={Fraction(j, comb(h*w, n) * 2**n)}", flush=True)
