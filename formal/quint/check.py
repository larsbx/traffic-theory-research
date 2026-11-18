#!/usr/bin/env python3
"""Run the actual Quint model and compare both phases against NumPy BML.

The default covers every state on every positive rectangle with at most six
cells, plus a 4x2 nonmonotonicity witness. Use --max-cells 9 for the larger replay.
This is finite exhaustive correspondence, not an unbounded refinement proof.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT))

from bml.exhaustive import decode, encode  # noqa: E402
from bml.model import EAST, NORTH, half_step, is_fixed  # noqa: E402
from evaluate import DEFAULT_CLI, InvariantViolation, evaluate_rows  # noqa: E402


def python_rows(width: int, height: int, indices: list[int]) -> list[list[int]]:
    states = decode(np.array(indices, dtype=np.int64), height, width)
    east, east_moves = half_step(states, EAST)
    final, north_moves = half_step(east, NORTH)
    return np.column_stack((indices, encode(east), encode(final), east_moves, north_moves)).tolist()


def compare(width: int, height: int, actual: list[list[int]], expected: list[list[int]]) -> None:
    if len(actual) != len(expected):
        raise AssertionError(f"{width}x{height}: expected {len(expected)} rows, got {len(actual)}")
    for got, want in zip(actual, expected, strict=True):
        if got != want:
            raise AssertionError(f"{width}x{height}, state {want[0]}: Quint {got}, Python {want}")


def check_row_invariants(width: int, height: int, rows: list[list[int]]) -> None:
    original = decode(np.array([row[0] for row in rows]), height, width)
    east = decode(np.array([row[1] for row in rows]), height, width)
    final = decode(np.array([row[2] for row in rows]), height, width)
    for species in (EAST, NORTH):
        counts = (original == species).sum(axis=(1, 2))
        if not np.array_equal(counts, (east == species).sum(axis=(1, 2))):
            raise AssertionError(f"{width}x{height}: species {species} lost during east phase")
        if not np.array_equal(counts, (final == species).sum(axis=(1, 2))):
            raise AssertionError(f"{width}x{height}: species {species} lost during north phase")
    for s, row in zip(original, rows, strict=True):
        fixed = is_fixed(s)
        if fixed != (row[0] == row[2]) or fixed != (row[3] + row[4] == 0):
            raise AssertionError(f"{width}x{height}, state {row[0]}: fixed/blocking/moves disagree")
        if not (s == 0).any() and not fixed:
            raise AssertionError("full occupancy did not freeze")


def mutation_controls(quint_cli: str) -> list[str]:
    """Execute altered Quint models and require correspondence to reject them."""
    text = (HERE / "BML.qnt").read_text()
    transition_start = text.index("  pure def transition(")
    transition_end = text.index("  pure def step(", transition_start)
    wrong_order = text[:transition_start] + """  pure def transition(w: int, h: int, s: State): Transition = {
    val a = half(w, h, s, north)
    { east: a, next: half(w, h, a, east),
      eastMoves: moves(w, h, a, east), northMoves: moves(w, h, s, north) }
  }
""" + text[transition_end:]
    half_start = text.index("  pure def half(")
    half_end = text.index("  pure def moves(", half_start)
    asynchronous = text[:half_start] + """  pure def half(w: int, h: int, s: State, species: int): State =
    cells(w, h).foldl(s, (current, i) =>
      if (canMove(w, h, current, species, i))
        current.replaceAt(i, empty).replaceAt(front(w, h, species, i), species)
      else current)
""" + text[half_end:]
    # On a full 2x1 east row this preserves both encoded transition states
    # and both move counts: [1,1] -> [4,0] -> [7,-1] all encode as 4.
    # Only validation of the actual Quint lists exposes the illegal digits.
    nonternary = text[:half_start] + """  pure def half(w: int, h: int, s: State, species: int): State =
    s.replaceAt(0, s[0] + 3).replaceAt(1, s[1] - 1)
""" + text[half_end:]
    controls = [
        ("north-before-east", wrong_order, 2, 2, 5),
        ("asynchronous-phase", asynchronous, 3, 1, 1),
        ("nonternary-state-with-identical-encoding", nonternary, 2, 1, 4),
    ]
    rejected = []
    with tempfile.TemporaryDirectory(prefix="bml-quint-mutations-") as folder:
        for name, source, width, height, index in controls:
            path = Path(folder) / f"{name}.qnt"
            path.write_text(source)
            expected = python_rows(width, height, [index])
            try:
                actual = evaluate_rows(width, height, [index], quint_cli, source=path)
                compare(width, height, actual, expected)
            except (AssertionError, InvariantViolation):
                rejected.append(name)
            else:
                raise AssertionError(f"mutation survived correspondence: {name}")
    return rejected


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-cells", type=int, default=6)
    parser.add_argument("--quint-cli", default=os.environ.get("QUINT_CLI", DEFAULT_CLI))
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    if not 1 <= args.max_cells <= 9:
        parser.error("--max-cells must be between 1 and 9")
    version = subprocess.check_output([args.quint_cli, "--version"], text=True).strip()
    if version != "0.33.1":
        raise RuntimeError(f"expected pinned Quint 0.33.1, got {version!r}")
    for command in ("parse", "typecheck"):
        subprocess.run([args.quint_cli, command, str(HERE / "BML.qnt")], check=True, capture_output=True, text=True)
    subprocess.run(
        [args.quint_cli, "test", str(HERE / "BML.qnt"), "--backend=typescript", "--max-samples=1"],
        check=True,
    )
    scopes = []
    for width in range(1, args.max_cells + 1):
        for height in range(1, args.max_cells // width + 1):
            indices = list(range(3 ** (width * height)))
            actual = evaluate_rows(width, height, indices, args.quint_cli)
            compare(width, height, actual, python_rows(width, height, indices))
            check_row_invariants(width, height, actual)
            scopes.append({"width": width, "height": height, "states": len(indices)})
            print(f"Quint/Python {width}x{height}: {len(indices)} states, both phases and move counts agree", flush=True)
    witness_indices = [3858, 3860, 4340]
    witness = evaluate_rows(4, 2, witness_indices, args.quint_cli)
    compare(4, 2, witness, python_rows(4, 2, witness_indices))
    check_row_invariants(4, 2, witness)
    mutations = mutation_controls(args.quint_cli)
    report = {
        "schema": "bml.quint-replay.v1",
        "status": "passed",
        "quint_version": version,
        "backend": "typescript",
        "source_sha256": hashlib.sha256((HERE / "BML.qnt").read_bytes()).hexdigest(),
        "max_cells": args.max_cells,
        "rectangles": scopes,
        "exhaustive_states": sum(scope["states"] for scope in scopes),
        "additional_witness_rows": len(witness),
        "deterministic_quint_tests": 7,
        "internal_invariant_evaluations": sum(scope["states"] for scope in scopes) + len(witness),
        "rejected_mutations": mutations,
        "scope": "finite exhaustive correspondence only; no unbounded or probabilistic theorem",
    }
    print(json.dumps(report, indent=2))
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
