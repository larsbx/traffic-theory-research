#!/usr/bin/env python3
"""Replay the mixed signal/roundabout results (docs/research/2026-11-24-mixed-roundabout-grid.md).

For every placement R on the listed boards: Theorem MX-G against the girth of the blocker
graph and against the gridlock construction at every admissible count; Corollary MX-E against
the extremes over all placements; and a census of the free-flow capacity, found from the
dynamics alone, with Proposition MX-F checked on every capacity configuration.
These are finite checks of universal prose proofs; the census itself is only finite data.
"""
from __future__ import annotations

import argparse
from itertools import product
import json
from pathlib import Path
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from bml.mixed import (  # noqa: E402
    best_min_gridlock, cells, counts, free_levels, girth, gridlock_with, is_fixed, junction_load,
    min_gridlock, worst_min_gridlock,
)

GIRTH = ((2, 2), (2, 3), (3, 2), (3, 3), (2, 4), (4, 2), (3, 4))      # (H, W)
EXTREMES = GIRTH + ((2, 5), (4, 4))
CENSUS = ((2, 2), (2, 3), (3, 2), (3, 3), (2, 4))
LINK_CENSUS = ((2, 2), (2, 3), (3, 2))


def masks(h: int, w: int):
    return (np.array(bits, bool).reshape(h, w) for bits in product((False, True), repeat=h * w))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def check_gridlock(h: int, w: int, link: bool) -> dict:
    for ring in masks(h, w):
        least, most = min_gridlock(ring, link), cells(ring, link)
        require(least == girth(ring, link), f"{w}x{h}: MX-G differs from the blocker-graph girth")
        for n in {least, (least + most) // 2, most}:
            s = gridlock_with(ring, n, link)
            require(sum(counts(s)) == n and bool(is_fixed(s, ring)), f"{w}x{h}: construction fails at n={n}")
    return {"width": w, "height": h, "link": link, "placements": 2 ** (h * w)}


def check_extremes(h: int, w: int, link: bool) -> dict:
    seen: dict[int, set[int]] = {}
    for ring in masks(h, w):
        seen.setdefault(int(ring.sum()), set()).add(min_gridlock(ring, link))
    for k, values in seen.items():
        require(max(values) == best_min_gridlock(h, w, k, link)
                and min(values) == worst_min_gridlock(h, w, k, link), f"{w}x{h}: MX-E fails at k={k}")
    return {"width": w, "height": h, "link": link,
            "least_gridlock_range_by_roundabouts": [[min(seen[k]), max(seen[k])] for k in sorted(seen)]}


def census(h: int, w: int, link: bool) -> dict:
    by_k: dict[int, list[int]] = {}
    for ring in masks(h, w):
        top = free_levels(ring, link=link)[-1]
        for layers in zip(*top):
            require(junction_load(type(top)(*layers), ring).max() <= 1, f"{w}x{h}: MX-F violated")
        by_k.setdefault(int(ring.sum()), []).append(int(sum(counts(top))[0]))
    table = [{"roundabouts": k, "placements": len(v), "min": min(v), "max": max(v),
              "mean": round(sum(v) / len(v), 3)} for k, v in sorted(by_k.items())]
    print(f"mixed {w}x{h} link={link} capacity by #roundabouts: "
          + " ".join(f"{r['min']}-{r['max']}" for r in table), flush=True)
    return {"width": w, "height": h, "link": link, "free_capacity": table}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    report = {"gridlock": [check_gridlock(h, w, link) for link in (False, True) for h, w in GIRTH],
              "extremes": [check_extremes(h, w, link) for link in (False, True) for h, w in EXTREMES],
              "capacity_census": [census(h, w, link) for link, boards in ((False, CENSUS), (True, LINK_CENSUS))
                                  for h, w in boards]}
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print("mixed-grid checks passed")


if __name__ == "__main__":
    main()
