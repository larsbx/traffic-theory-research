#!/usr/bin/env python3
"""Evaluate encoded BML transitions using the actual pinned Quint interpreter.

Usage: python formal/quint/evaluate.py WIDTH HEIGHT
CSV output (no header): index,east_state,next_state,east_moves,north_moves.
State digits are 0=empty, 1=east, 2=north; x is the fastest coordinate.
This adapter only encodes inputs and decodes output; it contains no BML dynamics.
The interpreter also returns an internal invariant flag for every evaluated
state. The adapter requires it to be true before emitting the five CSV fields.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
DEFAULT_CLI = str(HERE / "node_modules" / ".bin" / "quint")


class InvariantViolation(RuntimeError):
    """The actual Quint model reported a failed state/transition invariant."""


def evaluate_rows(
    width: int,
    height: int,
    indices: list[int],
    quint_cli: str = DEFAULT_CLI,
    *,
    source: Path | None = None,
    timeout: int = 600,
) -> list[list[int]]:
    """Return exact Quint results in the input order; reject incomplete output."""
    if width < 1 or height < 1 or width * height > 16:
        raise ValueError("adapter profile requires positive dimensions and at most 16 cells")
    if any(type(i) is not int or not 0 <= i < 3 ** (width * height) for i in indices):
        raise ValueError("state index is outside this torus")
    if not indices:
        return []
    source = HERE / "BML.qnt" if source is None else source
    expressions = []
    for start in range(0, len(indices), 96):
        batch = indices[start : start + 96]
        if batch == list(range(batch[0], batch[0] + len(batch))):
            expressions.append(f"checkedRows({width},{height},{batch[0]},{batch[-1] + 1})")
        else:
            calls = [f"checkedRow({width},{height},{i})" for i in batch]
            expressions.append("List(" + ",".join(calls) + ")")
    process = subprocess.run(
        [quint_cli, "repl", "--quiet", "--backend=typescript", "--require", f"{source}::BML"],
        input="\n".join(expressions) + "\n",
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
    )
    if process.returncode != 0 or process.stderr.strip():
        raise RuntimeError(f"Quint evaluation failed:\n{process.stdout}\n{process.stderr}")
    remaining = process.stdout.strip()
    decoder = json.JSONDecoder()
    result: list[list[int]] = []
    chunks = 0
    while remaining:
        chunk, end = decoder.raw_decode(remaining)
        if not isinstance(chunk, list):
            raise RuntimeError(f"unexpected Quint output: {chunk!r}")
        result.extend(chunk)
        chunks += 1
        remaining = remaining[end:].lstrip()
    if chunks != len(expressions) or len(result) != len(indices):
        raise RuntimeError("missing or extra Quint rows/chunks")
    for index, row in zip(indices, result, strict=True):
        if not isinstance(row, list) or len(row) != 6 or any(type(x) is not int for x in row):
            raise RuntimeError(f"malformed Quint row: {row!r}")
        if row[0] != index:
            raise RuntimeError(f"out-of-order Quint row: expected {index}, got {row[0]}")
        if row[5] not in (0, 1):
            raise RuntimeError(f"malformed Quint invariant flag: {row[5]!r}")
        if row[5] == 0:
            raise InvariantViolation(f"Quint invariant failed at {width}x{height}, state {index}")
    return [row[:5] for row in result]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("width", type=int)
    parser.add_argument("height", type=int)
    parser.add_argument("--indices", type=int, nargs="+", help="only evaluate these state indices")
    parser.add_argument("--quint-cli", default=os.environ.get("QUINT_CLI", DEFAULT_CLI))
    args = parser.parse_args()
    if args.width < 1 or args.height < 1 or args.width * args.height > 16:
        parser.error("positive dimensions and at most 16 cells are required")
    if args.indices is None and args.width * args.height > 9:
        parser.error("full enumeration is limited to 9 cells; use --indices for larger tori")
    indices = args.indices if args.indices is not None else list(range(3 ** (args.width * args.height)))
    for row in evaluate_rows(args.width, args.height, indices, args.quint_cli):
        print(",".join(map(str, row)))


if __name__ == "__main__":
    main()
