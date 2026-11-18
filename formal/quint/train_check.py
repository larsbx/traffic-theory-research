#!/usr/bin/env python3
"""Check actual Quint TRAIN semantics against NumPy TRAIN and mutant models.

Default: all 3,720 boards on every positive rectangle with area <= 6. The
optional --rows file contains ONLY these exhaustive rows, in width/height/code
order, using the ten-column train_evaluate protocol. Larger fixed cases and
all-count constructions are reported separately. This is finite replay, not an
unbounded Quint/Lean refinement theorem or an Apalache verification result.
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

from bml.model import EAST, NORTH, TRAIN, half_step  # noqa: E402
from bml.extremal import train_stuck_with  # noqa: E402
from train_evaluate import DEFAULT_CLI, InvariantViolation, evaluate_rows  # noqa: E402

SEED = 20261118
EXPECTED_TESTS = {
    "train_tests.qnt": [
        "emptyStuckTest", "eastQueueMovesTogetherTest", "northQueueMovesTogetherTest",
        "eastOppositeBlockerTest", "northOppositeBlockerTest", "eastWrapQueueTest",
        "northWrapQueueTest", "eastFullRingMovesTest", "northFullRingMovesTest",
        "oneCellEastRotatesTest", "oneCellNorthRotatesTest", "thinTorusOwnDirectionRingsTest",
        "quietPhaseIsNotStuckTest", "fixedOccupancyIsNotStuckTest", "phaseOrderMattersTest",
        "mixedStuckBoardTest", "longQueuePropagationTest", "separatePhaseMovementCountsTest",
        "allRectanglesThroughSixCellsTest",
    ],
    "train_model.qnt": [
        "ringMovementAdvancesClockTest", "emptyStepTogglesPhaseTest",
        "stuckStepTogglesPhaseTest", "bothPhasesConserveSpeciesTest",
        "quietActivePhaseTogglesTest",
    ],
}
EXPECTED_MUTATIONS = [
    "classic-replacement", "omitted-full-ring", "truncated-queue-propagation",
    "north-before-east", "illegal-digits-with-identical-encoding",
]


def encode_board(board: np.ndarray) -> int:
    """Input/output encoding only; Python integers avoid large-board overflow."""
    return sum(int(cell) * 3**i for i, cell in enumerate(board.flat))


def python_rows(width: int, height: int, indices: list[int]) -> list[list[int]]:
    states = np.array([
        [(index // 3**i) % 3 for i in range(width * height)] for index in indices
    ], dtype=np.int8).reshape((-1, height, width))
    east, east_moves = half_step(states, EAST, TRAIN)
    north, north_moves = half_step(states, NORTH, TRAIN)
    full, cycle_north_moves = half_step(east, NORTH, TRAIN)
    return [
        [width, height, index, encode_board(e), encode_board(n), encode_board(f),
         int(em), int(nm), int(cnm), int(em == 0 and nm == 0)]
        for index, e, n, f, em, nm, cnm in zip(
            indices, east, north, full, east_moves, north_moves, cycle_north_moves, strict=True
        )
    ]


def compare(actual: list[list[int]], expected: list[list[int]]) -> None:
    if len(actual) != len(expected):
        raise AssertionError(f"expected {len(expected)} TRAIN rows, got {len(actual)}")
    for got, want in zip(actual, expected, strict=True):
        if got != want:
            raise AssertionError(f"TRAIN {want[:3]}: Quint {got}, Python {want}")


def test_suites(quint_cli: str) -> dict:
    for filename in ["Train.qnt", *EXPECTED_TESTS]:
        for command in ("parse", "typecheck"):
            subprocess.run([quint_cli, command, str(HERE / filename)], check=True,
                           capture_output=True, text=True)
    inventory = {}
    with tempfile.TemporaryDirectory(prefix="train-quint-tests-") as directory:
        for filename, expected in EXPECTED_TESTS.items():
            output = Path(directory) / f"{filename}.json"
            subprocess.run([
                quint_cli, "test", str(HERE / filename), "--backend=typescript",
                "--max-samples=1", f"--seed={SEED}", f"--out={output}",
            ], check=True)
            result = json.loads(output.read_text())
            passed = result.get("passed")
            if not isinstance(passed, list) or any(type(name) is not str for name in passed):
                raise AssertionError(f"{filename}: missing structured passed-test inventory")
            if len(passed) != len(expected) or set(passed) != set(expected):
                raise AssertionError(f"{filename}: wrong passed-test inventory {passed!r}")
            if result.get("failed") != [] or result.get("ignored") != []:
                raise AssertionError(f"{filename}: failed or ignored tests")
            inventory[filename] = {"passed": passed, "count": len(passed), "failed": [], "ignored": []}
    return inventory


def replace_definition(source: str, start: str, end: str, replacement: str) -> str:
    first = source.index(start)
    last = source.index(end, first)
    return source[:first] + replacement + source[last:]


def mutation_controls(quint_cli: str) -> list[dict]:
    """Actual altered Quint models must fail the same adapter/comparator."""
    source = (HERE / "Train.qnt").read_text()
    classic = replace_definition(source, "  pure def movers(", "  pure def moves(",
        "  pure def movers(w: int, h: int, b: Board, phase: int): Set[int] =\n"
        "    initialMovers(w, h, b, phase)\n")
    no_ring = source.replace("queues.union(fullRing(w, h, b, phase))", "queues")
    truncated = source.replace("range(0, period(w, h, phase) - 1).foldl(", "range(0, 1).foldl(")
    reversed_phases = source.replace("half(w, h, half(w, h, b, east), north)",
                                     "half(w, h, half(w, h, b, north), east)")
    nonternary = replace_definition(source, "  pure def half(", "  pure def full(",
        "  pure def half(w: int, h: int, b: Board, phase: int): Board =\n"
        "    b.replaceAt(0, b[0] + 3).replaceAt(1, b[1] - 1)\n")
    controls = [
        ("classic-replacement", classic, 3, 1, 4),
        ("omitted-full-ring", no_ring, 1, 1, 1),
        ("truncated-queue-propagation", truncated, 4, 1, 13),
        ("north-before-east", reversed_phases, 2, 2, 5),
        ("illegal-digits-with-identical-encoding", nonternary, 2, 1, 4),
    ]
    rejected = []
    with tempfile.TemporaryDirectory(prefix="train-quint-mutations-") as directory:
        for name, altered, width, height, code in controls:
            if altered == source:
                raise AssertionError(f"mutation did not alter model: {name}")
            path = Path(directory) / f"{name}.qnt"
            path.write_text(altered)
            expected = python_rows(width, height, [code])
            try:
                actual = evaluate_rows(width, height, [code], quint_cli, source=path)
                compare(actual, expected)
            except InvariantViolation as exc:
                if name == "illegal-digits-with-identical-encoding" and exc.row != expected[0]:
                    raise AssertionError("illegal-digit control did not preserve all ten public fields") from exc
                rejected.append({"name": name, "reason": "internal-invariant", "width": width,
                                 "height": height, "input_code": code})
            except AssertionError:
                rejected.append({"name": name, "reason": "cross-language-mismatch", "width": width,
                                 "height": height, "input_code": code})
            else:
                raise AssertionError(f"TRAIN mutation survived acceptance: {name}")
    if [item["name"] for item in rejected] != EXPECTED_MUTATIONS:
        raise AssertionError("missing TRAIN mutation rejection")
    return rejected


def targeted_cases(quint_cli: str) -> list[dict]:
    checked = []
    for width, height in [(7, 1), (1, 7), (8, 2), (2, 8), (3, 3), (4, 3), (3, 4), (4, 4)]:
        boards = [np.zeros((height, width), dtype=np.int8),
                  np.full((height, width), EAST, dtype=np.int8),
                  np.full((height, width), NORTH, dtype=np.int8)]
        boards.append(np.fromfunction(lambda y, x: 1 + (x+y) % 2, (height, width), dtype=int).astype(np.int8))
        queue_e = np.zeros((height, width), dtype=np.int8)
        queue_e[0, :width - 1] = EAST
        boards.append(queue_e)
        queue_n = np.zeros((height, width), dtype=np.int8)
        queue_n[:height - 1, 0] = NORTH
        boards.append(queue_n)
        blocked_e = queue_e.copy()
        blocked_e[0, width - 1] = NORTH
        boards.append(blocked_e)
        blocked_n = queue_n.copy()
        blocked_n[height - 1, 0] = EAST
        boards.append(blocked_n)
        if width >= 3:
            wrap = np.zeros((height, width), dtype=np.int8)
            wrap[0, :] = EAST
            wrap[0, 1] = 0
            boards.append(wrap)
        if height >= 3:
            wrap = np.zeros((height, width), dtype=np.int8)
            wrap[:, 0] = NORTH
            wrap[1, 0] = 0
            boards.append(wrap)
        indices = sorted({encode_board(board) for board in boards})
        rows = evaluate_rows(width, height, indices, quint_cli)
        compare(rows, python_rows(width, height, indices))
        checked.append({"width": width, "height": height, "rows": rows})
    return checked


def construction_cases(quint_cli: str) -> list[dict]:
    """All integer car counts on 2..8 rectangles with area <=16 (96 boards)."""
    checked = []
    for width in range(2, 9):
        for height in range(2, 9):
            if width * height > 16:
                continue
            counts = list(range(width + height, width * height + 1))
            boards = [train_stuck_with(height, width, count) for count in counts]
            if any(int(np.count_nonzero(board)) != count for board, count in zip(boards, counts, strict=True)):
                raise AssertionError("all-count TRAIN constructor returned wrong occupancy")
            indices = [encode_board(board) for board in boards]
            rows = evaluate_rows(width, height, indices, quint_cli)
            compare(rows, python_rows(width, height, indices))
            if any(row[9] != 1 or row[6:9] != [0, 0, 0] for row in rows):
                raise AssertionError("Quint did not certify an all-count construction as stuck")
            checked.append({"width": width, "height": height, "car_counts": counts, "rows": rows})
    return checked


def source_hashes() -> dict[str, str]:
    files = ["formal/quint/Train.qnt", "formal/quint/train_tests.qnt", "formal/quint/train_model.qnt",
             "formal/quint/train_evaluate.py", "formal/quint/train_check.py", "formal/quint/package.json",
             "formal/quint/package-lock.json", "bml/model.py", "bml/extremal.py"]
    return {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in files}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-cells", type=int, default=6)
    parser.add_argument("--quint-cli", default=os.environ.get("QUINT_CLI", DEFAULT_CLI))
    parser.add_argument("--report", type=Path)
    parser.add_argument("--rows", type=Path)
    args = parser.parse_args()
    if not 1 <= args.max_cells <= 9:
        parser.error("--max-cells must be between 1 and 9")
    if args.report and args.rows and args.report.resolve() == args.rows.resolve():
        parser.error("--report and --rows must name different files")
    for output in (args.report, args.rows):
        if output:
            output.unlink(missing_ok=True)
    sources = source_hashes()
    version = subprocess.check_output([args.quint_cli, "--version"], text=True).strip()
    if version != "0.33.1":
        raise RuntimeError(f"expected Quint 0.33.1, got {version!r}")
    tests = test_suites(args.quint_cli)
    scopes = []
    exhaustive = []
    for width in range(1, args.max_cells + 1):
        for height in range(1, args.max_cells // width + 1):
            indices = list(range(3 ** (width * height)))
            rows = evaluate_rows(width, height, indices, args.quint_cli)
            compare(rows, python_rows(width, height, indices))
            exhaustive.extend(rows)
            scopes.append({"width": width, "height": height, "states": len(rows)})
            print(f"TRAIN Quint/Python {width}x{height}: {len(rows)} boards, ten fields agree", flush=True)
    targets = targeted_cases(args.quint_cli)
    constructions = construction_cases(args.quint_cli)
    mutations = mutation_controls(args.quint_cli)
    if source_hashes() != sources:
        raise RuntimeError("TRAIN acceptance sources changed during execution")
    table = ("\n".join("\t".join(map(str, row)) for row in exhaustive) + "\n").encode()
    report = {
        "schema": "train.quint-replay.v1", "status": "passed", "rule": "train",
        "quint_version": version, "backend": "typescript", "seed": SEED,
        "sources_sha256": sources, "max_cells": args.max_cells, "rectangles": scopes,
        "exhaustive_states": len(exhaustive), "exhaustive_rows_sha256": hashlib.sha256(table).hexdigest(),
        "columns": ["width", "height", "input_code", "east_code", "north_code", "full_code",
                    "east_moves", "north_moves", "cycle_north_moves", "stuck"],
        "test_suites": tests, "deterministic_quint_tests": sum(t["count"] for t in tests.values()),
        "targeted_cases": targets, "targeted_states": sum(len(case["rows"]) for case in targets),
        "construction_cases": constructions,
        "construction_states": sum(len(case["rows"]) for case in constructions),
        "rejected_mutations": mutations,
        "scope": "finite replay and internal invariants; no unbounded source refinement or Apalache claim",
    }
    if args.rows:
        args.rows.parent.mkdir(parents=True, exist_ok=True)
        args.rows.write_bytes(table)
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in {"targeted_cases", "construction_cases"}}, indent=2))


if __name__ == "__main__":
    main()
