#!/usr/bin/env python3
"""Compare the executable Lean kernel with both phases of the NumPy kernel.

This is exhaustive over the declared finite domain, not a universal refinement
proof between Lean and Python. The separate Lean axiom audit checks the proofs.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from bml.exhaustive import decode, encode  # noqa: E402
from bml.model import EAST, NORTH, half_step  # noqa: E402


def compare_shape(binary: Path, width: int, height: int) -> dict:
    size = 3 ** (width * height)
    result = subprocess.run([str(binary), str(width), str(height)], check=True,
                            capture_output=True, text=True, timeout=120)
    rows = list(csv.reader(io.StringIO(result.stdout)))
    if len(rows) != size or any(len(row) != 5 for row in rows):
        raise AssertionError(f"{width}x{height}: malformed or incomplete Lean replay")
    actual = np.array(rows, dtype=np.int64)
    indices = np.arange(size, dtype=np.int64)
    initial = decode(indices, height, width)
    east, east_moves = half_step(initial, EAST)
    final, north_moves = half_step(east, NORTH)
    expected = np.column_stack((indices, encode(east), encode(final), east_moves, north_moves))
    mismatches = np.flatnonzero((actual != expected).any(axis=1))
    if len(mismatches):
        i = int(mismatches[0])
        raise AssertionError(f"{width}x{height}, state {i}: Lean={actual[i].tolist()}, Python={expected[i].tolist()}")
    print(f"Lean/Python {width}x{height}: {size} states, both phases and move counts agree", flush=True)
    return {"width": width, "height": height, "states": size,
            "csv_sha256": hashlib.sha256(result.stdout.encode()).hexdigest()}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-cells", type=int, default=9)
    parser.add_argument("--binary", type=Path, default=ROOT / "formal/lean/.lake/build/bin/bml_replay")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    if not 1 <= args.max_cells <= 9:
        parser.error("--max-cells must be in 1..9")
    binary = args.binary.resolve(strict=True)
    scopes = [compare_shape(binary, width, height)
              for width in range(1, args.max_cells + 1)
              for height in range(1, args.max_cells // width + 1)]
    # The default domain includes the complete 4x2 witness; a smaller domain
    # still checks it without claiming the additional rectangle is exhaustive
    # coverage under the chosen max-cells setting.
    extra = [] if args.max_cells >= 8 else [compare_shape(binary, 4, 2)]
    source_paths = [ROOT / "formal/lean/Main.lean", ROOT / "bml/model.py"]
    source_paths += sorted((ROOT / "formal/lean/BML").glob("*.lean"))
    report = {
        "schema": "bml.lean-replay.v1",
        "status": "passed",
        "lean_toolchain": (ROOT / "formal/lean/lean-toolchain").read_text().strip(),
        "source_sha256": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in source_paths},
        "max_cells": args.max_cells,
        "rectangles": scopes,
        "exhaustive_states": sum(scope["states"] for scope in scopes),
        "additional_witness_rectangles": extra,
        "scope": "finite executable correspondence; not a universal Lean/Python refinement theorem",
    }
    print(json.dumps(report, indent=2))
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
