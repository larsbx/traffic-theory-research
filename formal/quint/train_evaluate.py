#!/usr/bin/env python3
"""Evaluate actual Quint TRAIN rows, validating the internal invariant flag.

The public TSV has ten integer columns:
width,height,input,east,north,full,eastMoves,northMoves,cycleNorthMoves,stuck.
The north half-step is independent of the east half-step; full is east then
north. This adapter only serializes inputs/outputs. It has no traffic dynamics.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
DEFAULT_CLI = str(HERE / "node_modules" / ".bin" / "quint")
MAX_EXPLICIT_CELLS = 64


class InvariantViolation(RuntimeError):
    """The interpreter rejected an actual state, even if encoded codes match."""

    def __init__(self, row: list[int]):
        self.row = row[:10]
        super().__init__(f"TRAIN invariant failed at {row[0]}x{row[1]}, code {row[2]}")


def evaluate_rows(
    width: int,
    height: int,
    indices: list[int],
    quint_cli: str = DEFAULT_CLI,
    *,
    source: Path | None = None,
    timeout: int = 600,
) -> list[list[int]]:
    """Return interpreter rows in input order, including independent N moves."""
    if width < 1 or height < 1 or width * height > MAX_EXPLICIT_CELLS:
        raise ValueError(f"positive dimensions and at most {MAX_EXPLICIT_CELLS} cells required")
    if any(type(i) is not int or not 0 <= i < 3 ** (width * height) for i in indices):
        raise ValueError("state code is outside this torus")
    if not indices:
        return []
    source = HERE / "Train.qnt" if source is None else source
    expressions = []
    for start in range(0, len(indices), 48):
        batch = indices[start : start + 48]
        if batch == list(range(batch[0], batch[0] + len(batch))):
            expressions.append(f"checkedRows({width},{height},{batch[0]},{batch[-1] + 1})")
        else:
            expressions.append("List(" + ",".join(
                f"checkedRow({width},{height},{index})" for index in batch
            ) + ")")
    process = subprocess.run(
        [quint_cli, "repl", "--quiet", "--backend=typescript", "--require", f"{source}::Train"],
        input="\n".join(expressions) + "\n", text=True, capture_output=True,
        timeout=timeout, check=False,
    )
    if process.returncode != 0 or process.stderr.strip():
        raise RuntimeError(f"Quint TRAIN evaluation failed:\n{process.stdout}\n{process.stderr}")
    remaining = process.stdout.strip()
    decoder = json.JSONDecoder()
    result: list[list[int]] = []
    chunks = 0
    while remaining:
        chunk, end = decoder.raw_decode(remaining)
        if not isinstance(chunk, list):
            raise RuntimeError(f"unexpected Quint TRAIN output: {chunk!r}")
        result.extend(chunk)
        chunks += 1
        remaining = remaining[end:].lstrip()
    if chunks != len(expressions) or len(result) != len(indices):
        raise RuntimeError("missing or extra Quint TRAIN rows/chunks")
    for index, row in zip(indices, result, strict=True):
        if not isinstance(row, list) or len(row) != 11 or any(type(x) is not int for x in row):
            raise RuntimeError(f"malformed Quint TRAIN row: {row!r}")
        if row[:3] != [width, height, index]:
            raise RuntimeError(f"out-of-order Quint TRAIN row: {row[:3]!r}")
        if row[10] not in (0, 1):
            raise RuntimeError(f"malformed TRAIN invariant flag: {row[10]!r}")
        if row[10] == 0:
            raise InvariantViolation(row)
        if any(not 0 <= code < 3 ** (width * height) for code in row[3:6]):
            raise RuntimeError("TRAIN output code outside torus")
        if any(not 0 <= count <= width * height for count in row[6:9]) or row[9] not in (0, 1):
            raise RuntimeError("invalid TRAIN count or stuck flag")
    return [row[:10] for row in result]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("width", type=int)
    parser.add_argument("height", type=int)
    parser.add_argument("--indices", type=int, nargs="+")
    parser.add_argument("--quint-cli", default=os.environ.get("QUINT_CLI", DEFAULT_CLI))
    args = parser.parse_args()
    if args.width < 1 or args.height < 1 or args.width * args.height > MAX_EXPLICIT_CELLS:
        parser.error(f"positive dimensions and at most {MAX_EXPLICIT_CELLS} cells required")
    if args.indices is None and args.width * args.height > 9:
        parser.error("full enumeration is capped at nine cells; use --indices for larger tori")
    indices = args.indices if args.indices is not None else list(range(3 ** (args.width * args.height)))
    for row in evaluate_rows(args.width, args.height, indices, args.quint_cli):
        print("\t".join(map(str, row)))


if __name__ == "__main__":
    main()
