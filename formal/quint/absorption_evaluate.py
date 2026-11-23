#!/usr/bin/env python3
"""Evaluate bounded CLASSIC absorption probes in the actual Quint interpreter.

Rows are [input_code, cutoff, terminal_code, verdict, initial_population],
where verdict 0 is hit, 1 is a recurrent non-target safe certificate, and 2
is unresolved. Results are cutoff-major, preserving the supplied code order.
The model returns a sixth internal legality/transition flag. This adapter
requires it to be one before exposing the public row. No Python traffic
dynamics or orbit classification is implemented here.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
DEFAULT_CLI = str(HERE / "node_modules" / ".bin" / "quint")
QUINT_VERSION = "0.33.1"
MAX_EXPLICIT_CELLS = 16
MAX_ENUMERATED_CELLS = 6


class InvariantViolation(RuntimeError):
    """The actual Quint execution rejected an internal state or transition."""

    def __init__(self, width: int, height: int, row: list[int]):
        self.row = row[:5]
        super().__init__(
            f"Quint absorption invariant failed at {width}x{height}, "
            f"state {row[0]}, cutoff {row[1]}"
        )


def evaluate_probe_rows(
    width: int,
    height: int,
    indices: list[int],
    cutoffs: list[int],
    quint_cli: str = DEFAULT_CLI,
    *,
    source: Path | None = None,
    timeout: int = 600,
) -> list[list[int]]:
    """Return actual interpreter rows; reject malformed or incomplete evidence."""
    if (type(width) is not int or type(height) is not int or width < 1 or height < 1
            or width * height > MAX_EXPLICIT_CELLS):
        raise ValueError("positive integer dimensions and at most 16 cells are required")
    limit = 3 ** (width * height)
    if any(type(code) is not int or not 0 <= code < limit for code in indices):
        raise ValueError("state code is outside this torus")
    if any(type(cutoff) is not int or cutoff < 0 for cutoff in cutoffs):
        raise ValueError("cutoffs must be nonnegative integers")
    if not indices or not cutoffs:
        return []
    version = subprocess.check_output(
        [quint_cli, "--version"], text=True, timeout=30,
    ).strip()
    if version != QUINT_VERSION:
        raise RuntimeError(f"expected Quint {QUINT_VERSION}, got {version!r}")

    source = HERE / "Absorption.qnt" if source is None else Path(source)
    expressions = []
    expected_keys = []
    for cutoff in cutoffs:
        for start in range(0, len(indices), 48):
            batch = indices[start:start + 48]
            expected_keys.extend((code, cutoff) for code in batch)
            if batch == list(range(batch[0], batch[0] + len(batch))):
                expressions.append(
                    f"checkedRange({width},{height},{batch[0]},{batch[-1] + 1},{cutoff})"
                )
            else:
                codes = "List(" + ",".join(map(str, batch)) + ")"
                expressions.append(f"checkedIndices({width},{height},{codes},{cutoff})")

    process = subprocess.run(
        [quint_cli, "repl", "--quiet", "--backend=typescript", "--require", f"{source}::Absorption"],
        input="\n".join(expressions) + "\n", text=True, capture_output=True,
        timeout=timeout, check=False,
    )
    if process.returncode != 0 or process.stderr.strip():
        raise RuntimeError(f"Quint absorption evaluation failed:\n{process.stdout}\n{process.stderr}")
    remaining = process.stdout.strip()
    decoder = json.JSONDecoder()
    result: list[list[int]] = []
    chunks = 0
    while remaining:
        chunk, end = decoder.raw_decode(remaining)
        if not isinstance(chunk, list):
            raise RuntimeError(f"unexpected Quint absorption output: {chunk!r}")
        result.extend(chunk)
        chunks += 1
        remaining = remaining[end:].lstrip()
    if chunks != len(expressions) or len(result) != len(expected_keys):
        raise RuntimeError("missing or extra Quint absorption rows/chunks")
    for (code, cutoff), row in zip(expected_keys, result, strict=True):
        if not isinstance(row, list) or len(row) != 6 or any(type(x) is not int for x in row):
            raise RuntimeError(f"malformed Quint absorption row: {row!r}")
        if row[:2] != [code, cutoff]:
            raise RuntimeError(f"out-of-order Quint absorption row: {row[:2]!r}")
        if not 0 <= row[2] < limit or row[3] not in (0, 1, 2):
            raise RuntimeError(f"invalid Quint terminal code or verdict: {row!r}")
        if not 0 <= row[4] <= width * height:
            raise RuntimeError(f"invalid Quint initial population: {row!r}")
        if row[5] not in (0, 1):
            raise RuntimeError(f"malformed Quint absorption invariant flag: {row[5]!r}")
        if row[5] == 0:
            raise InvariantViolation(width, height, row)
    return [row[:5] for row in result]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("width", type=int)
    parser.add_argument("height", type=int)
    parser.add_argument("--indices", type=int, nargs="+")
    parser.add_argument("--cutoffs", type=int, nargs="+", required=True)
    parser.add_argument("--quint-cli", default=os.environ.get("QUINT_CLI", DEFAULT_CLI))
    args = parser.parse_args()
    if args.width < 1 or args.height < 1 or args.width * args.height > MAX_EXPLICIT_CELLS:
        parser.error("positive dimensions and at most 16 cells are required")
    if any(cutoff < 0 for cutoff in args.cutoffs):
        parser.error("cutoffs must be nonnegative")
    if args.indices is None and args.width * args.height > MAX_ENUMERATED_CELLS:
        parser.error("full enumeration is capped at six cells; use --indices for larger tori")
    indices = args.indices if args.indices is not None else list(range(3 ** (args.width * args.height)))
    for row in evaluate_probe_rows(args.width, args.height, indices, args.cutoffs, args.quint_cli):
        print("\t".join(map(str, row)))


if __name__ == "__main__":
    main()
