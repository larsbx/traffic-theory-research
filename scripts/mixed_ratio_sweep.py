#!/usr/bin/env python3
"""Monte Carlo: gridlock against the share of roundabouts (not a proof).

On an L×L torus each intersection is a roundabout independently with probability rho, and
each cell holds a car independently with probability p (species by coin flip where both fit).
A run is gridlocked if no car can move after T ticks. Writes the gridlocked fraction and the
mean speed over the last 200 ticks to docs/research/data/2026-11-24-mixed-ratio-sweep.json.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from bml.mixed import is_fixed, step  # noqa: E402
from bml.model import EAST, EMPTY, NORTH  # noqa: E402
from bml.roundabout import State, counts  # noqa: E402

L, RUNS, TICKS, SEED = 24, 40, 6000, 20261124
RHOS = (0.0, 0.25, 0.5, 0.75, 1.0)
DENSITIES = tuple(round(0.10 + 0.04 * i, 2) for i in range(16))
OUT = ROOT / "docs/research/data/2026-11-24-mixed-ratio-sweep.json"


def run(rho: float, p: float, rng: np.random.Generator) -> dict:
    shape = (RUNS, L, L)
    ring = rng.random(shape) < rho
    c = np.where(rng.random(shape) < p, rng.choice([EAST, NORTH], shape), EMPTY).astype(np.int8)
    s = State(ring & (rng.random(shape) < p), c, ring & (rng.random(shape) < p))
    n = np.maximum(sum(counts(s)), 1)
    late = np.zeros(RUNS)
    for tick in range(TICKS):
        s, moved = step(s, ring, tick)
        if tick >= TICKS - 200:
            late += moved / n
    return {"rho": rho, "p": p, "gridlocked": float(is_fixed(s, ring).mean()),
            "moves_per_car_per_tick": round(float(late.mean() / 200), 4),
            "cars_per_intersection": round(float((n / L ** 2).mean()), 4)}


def main() -> None:
    rng = np.random.default_rng(SEED)
    rows = [run(rho, p, rng) for rho in RHOS for p in DENSITIES]
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps({"L": L, "runs": RUNS, "ticks": TICKS, "seed": SEED, "rows": rows}, indent=1) + "\n")
    for rho in RHOS:
        print(f"rho={rho}: " + " ".join(f"{r['p']}:{r['gridlocked']:.2f}" for r in rows if r["rho"] == rho))


if __name__ == "__main__":
    main()
