#!/usr/bin/env python3
"""Compare the Lean gates and original tagged transport with Python CLASSIC."""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
import subprocess
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from bml.levels import jams  # noqa: E402
from bml.model import CLASSIC, EAST, NORTH, half_step  # noqa: E402
from bml.nonmonotone import gated_witness, labelled_step  # noqa: E402


def digits(board):
    return "".join(map(str, board.flat))


def tag_field(ids, tag):
    y, x = np.argwhere(ids == tag)[0]
    return f"{x},{y}"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def check_trace(rows, board, variant, original):
    h, w = board.shape
    ids = np.full(board.shape, -1)
    ids[board != 0] = np.arange(np.count_nonzero(board))
    tag = ids[original] if original is not None else None
    require(tag is None or tag > 0, f"{w}x{h}: the original tag is missing or added")
    horizon = 2 * max(w, h) + 1
    first_jam = None
    feeder_moves = 0
    for t in range(horizon):
        mid, east_moves = half_step(board, EAST, CLASSIC)
        after, north_moves = half_step(mid, NORTH, CLASSIC)
        current_pos = next_pos = "-"
        if tag is not None:
            current_pos = tag_field(ids, tag)
            traced, next_ids, moved = labelled_step(board, ids, CLASSIC)
            require(np.array_equal(traced, after) and moved == {tag},
                    f"{w}x{h} {variant} round {t}: the lone original car must move")
            next_pos = tag_field(next_ids, tag)
            ids = next_ids
        expected = [str(w), str(h), variant, str(t), str(east_moves), str(north_moves),
                    digits(board), digits(mid), digits(after), current_pos, next_pos]
        observed = next(rows, None)
        require(observed == expected,
                f"{w}x{h} {variant} round {t}: Lean/Python row differs\n"
                f"expected {expected}\nobserved {observed}")
        if east_moves + north_moves == 0 and first_jam is None:
            first_jam = t
        feeder_moves += int(east_moves if w >= 4 else north_moves)
        board = after
    if variant == "X":
        require(first_jam is not None, f"{w}x{h}: no open-gate jam in the replay")
        lane_length = h if w >= 4 else w
        require(feeder_moves <= 2 * lane_length, f"{w}x{h}: open-gate movement budget exceeded")
    else:
        require(first_jam is None, f"{w}x{h}: closed gate jams")
    return horizon


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-side", type=int, default=10)
    parser.add_argument("--binary", type=Path, default=ROOT / "formal/lean/.lake/build/bin/gated_export")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    if args.max_side < 4:
        parser.error("--max-side must be at least 4")
    if not args.binary.is_file():
        parser.error("build the gated_export target in formal/lean first")
    run = subprocess.run([str(args.binary.resolve()), str(args.max_side)],
                         check=True, capture_output=True, text=True, timeout=120)
    rows = (line.split("\t") for line in run.stdout.splitlines())
    columns = transposed = transitions = 0
    sides = range(2, args.max_side + 1)
    for w, h in itertools.product(sides, repeat=2):
        if max(w, h) < 4:
            continue
        x, y, added = gated_witness(h, w)
        original = (0, 1) if w >= 4 else (1, 0)
        require(added == (0, 0) and x[original] == y[original] != 0 and
                np.array_equal(jams(np.stack([x, y])), [True, False]),
                f"{w}x{h}: Python witness does not have the expected orbit outcomes")
        transitions += check_trace(rows, x, "X", None)
        transitions += check_trace(rows, y, "Y", original)
        columns += int(w >= 4)
        transposed += int(w < 4)
    require(next(rows, None) is None, "unexpected extra Lean rows")
    report = {
        "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "max_side": args.max_side,
        "column_shapes": columns,
        "transposed_shapes": transposed,
        "transitions": transitions,
        "status": "passed",
    }
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS: {columns + transposed} gated shapes ({columns} column, {transposed} row), "
          f"{transitions} transitions with both phase states and original tag replay")


if __name__ == "__main__":
    main()
