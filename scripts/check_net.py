#!/usr/bin/env python3
"""Compare the Lean traffic-net step on mixed grids with the Python kernel `bml.mixed.step`.

`net_export` (formal/lean/NetExport.lean) prints one tick per line, computed by the generic
`BML.Net.step` on the `mixed` instance: every valid state of the boards with at most two
intersections, for every roundabout set, with and without links, on both tick parities; and
pseudo-random runs on boards up to 5×4. This is a finite replay, not a refinement proof.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import subprocess
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from bml.mixed import Linked, step  # noqa: E402
from bml.model import EAST, NORTH  # noqa: E402
from bml.roundabout import State  # noqa: E402


def decode(digits: str, h: int, w: int, link: bool):
    layer = np.array(list(digits), int).reshape(h, w, 5)      # junction, a, b, e, n
    core = (layer[..., 1] == EAST, layer[..., 0].astype(np.int8), layer[..., 2] == NORTH)
    return Linked(*core, layer[..., 3] == EAST, layer[..., 4] == NORTH) if link else State(*core)


def encode(s, h: int, w: int) -> str:
    off = np.zeros((h, w), int)
    e, n = (s.e * EAST, s.n * NORTH) if len(s) == 5 else (off, off)
    return "".join(map(str, np.stack([s.c, s.a * EAST, s.b * NORTH, e, n], axis=-1).ravel()))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--binary", type=Path, default=ROOT / "formal/lean/.lake/build/bin/net_export")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    if not args.binary.exists():
        parser.error("build the net_export target in formal/lean first")
    lines = subprocess.run([args.binary], check=True, capture_output=True, text=True).stdout.splitlines()
    boards: Counter = Counter()
    for line in lines:
        w, h, link, ring, tick, before, after = line.split()
        w, h, link = int(w), int(h), link == "1"
        mask = np.array(list(ring), int).reshape(h, w) == 1
        got = encode(step(decode(before, h, w, link), mask, int(tick))[0], h, w)
        if got != after:
            raise AssertionError(f"Lean and Python disagree: {line}\nPython: {got}")
        boards[f"{w}x{h}{'+links' if link else ''}"] += 1
    if len(lines) < 20000:
        raise AssertionError("net_export printed fewer ticks than expected")
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps({"ticks": len(lines), "by_board": dict(sorted(boards.items()))}, indent=2) + "\n")
    print(f"Lean net step equals bml.mixed.step on {len(lines)} ticks across {len(boards)} board variants")


if __name__ == "__main__":
    main()
