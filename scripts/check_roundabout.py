#!/usr/bin/env python3
"""Replay the roundabout-BML theorems (docs/research/2026-11-24-roundabout-bml.md).

For each listed board and each yield rule, every free configuration is enumerated from the
dynamics alone (`bml.roundabout.free_levels`: hereditary growth, freeness decided by
simulating one period). The realised species counts are then compared with Theorem RB-F,
every enumerated configuration with the static criterion of Lemma RB-R, and the capacity
level with Corollary RB-P. The gridlock constructions of Theorem RB-G are replayed too.
These are finite checks of universal prose proofs; they are not proofs.
"""
from __future__ import annotations

import argparse
import json
from math import gcd
from pathlib import Path
import sys
from time import perf_counter

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from bml.model import EAST, EMPTY, NORTH  # noqa: E402
from bml.roundabout import (  # noqa: E402
    counts, free_feasible, free_levels, gridlock_with, is_fixed, is_free_static,
    max_free, min_gridlock, period, step,
)

DOMAINS = ((1, 1), (1, 4), (2, 2), (2, 3), (3, 2), (2, 4), (4, 2), (3, 3), (2, 5), (3, 4), (2, 6))   # (H, W)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def check_free(h: int, w: int, priority: int) -> dict:
    start = perf_counter()
    levels = free_levels(h, w, priority)
    pairs = sorted({pair for s in levels for pair in zip(*(k.tolist() for k in counts(s)))})
    expected = [(e, n) for e in range(h * w + 1) for n in range(h * w + 1) if free_feasible(h, w, e, n)]
    require(pairs == expected, f"{w}x{h}: species frontier differs from RB-F")
    require(len(levels) - 1 == max_free(h, w), f"{w}x{h}: capacity differs from WH")
    require(all(is_free_static(s).all() for s in levels), f"{w}x{h}: RB-R rejects a free configuration")
    top = levels[-1]
    mixed = (counts(top)[0] > 0) & (counts(top)[1] > 0)
    require(bool(mixed.any()) == (gcd(h, w) >= 2), f"{w}x{h}: mixed capacity states vs gcd")
    for _ in range(period(h, w)):
        full = top.c != EMPTY
        require(bool((full.all(axis=(-2, -1)) | ~full.any(axis=(-2, -1)))[mixed].all()), f"{w}x{h}: RB-P unison")
        top = step(top, priority)[0]
        require(bool((full != (top.c != EMPTY)).all()), f"{w}x{h}: RB-P alternation")
    return {
        "width": w, "height": h, "gcd": gcd(h, w), "priority": {EAST: "EAST", NORTH: "NORTH"}[priority],
        "free_configurations_by_cars": [int(s.c.shape[0]) for s in levels],
        "mixed_capacity_configurations": int(mixed.sum()),
        "maximal_species_pairs": [p for p in pairs if not any(q != p and q[0] >= p[0] and q[1] >= p[1] for q in pairs)],
        "seconds": round(perf_counter() - start, 3),
    }


def check_gridlock(h: int, w: int) -> dict:
    span = range(min_gridlock(h, w), 3 * h * w + 1)
    for n in span:
        s = gridlock_with(h, w, n)
        require(sum(counts(s)) == n and bool(is_fixed(s)), f"{w}x{h}: RB-G construction fails at n={n}")
    return {"width": w, "height": h, "gridlock_counts": [span[0], span[-1]]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    free = [check_free(h, w, priority) for h, w in DOMAINS for priority in (EAST, NORTH)]
    for row in free:
        print(f"roundabout {row['width']}x{row['height']} priority={row['priority']}: "
              f"{sum(row['free_configurations_by_cars'])} free configurations, "
              f"capacity {len(row['free_configurations_by_cars']) - 1}, frontier {row['maximal_species_pairs']}")
    report = {"free_flow": free, "gridlock": [check_gridlock(h, w) for h in range(1, 9) for w in range(1, 9)]}
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print("roundabout checks passed")


if __name__ == "__main__":
    main()
