#!/usr/bin/env python3
"""Check actual Lean CLASSIC G1 constructions with independent Python dynamics.

Every admissible exact population is checked for every positive ordered
rectangle with each side <= --max-side (default 12). This validates the actual
Lean-produced boards, not equality with Python's potentially different
construction. The finite replay is separate from the universal Lean theorem.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, replace
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import re
import subprocess
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "formal/lean"
sys.path.insert(0, str(ROOT))

from bml.model import CLASSIC, EAST, NORTH, half_step, step  # noqa: E402


COLUMNS = [
    "width", "height", "requested_count", "car_count", "east_count",
    "north_count", "row_major_digits",
]


class ConstructionError(ValueError):
    """A malformed or incorrect constructor receipt, with a stable reason."""

    def __init__(self, reason: str, message: str):
        self.reason = reason
        super().__init__(message)


def require(condition: bool, reason: str, message: str) -> None:
    if not condition:
        raise ConstructionError(reason, message)


@dataclass(frozen=True)
class Construction:
    width: int
    height: int
    requested_count: int
    car_count: int
    east_count: int
    north_count: int
    digits: str

    @property
    def key(self) -> tuple[int, int, int]:
        return self.width, self.height, self.requested_count

    def tsv(self) -> str:
        return "\t".join(map(str, (
            self.width, self.height, self.requested_count, self.car_count,
            self.east_count, self.north_count, self.digits,
        )))


def parse_rows(output: str) -> list[Construction]:
    rows = []
    for number, line in enumerate(output.splitlines(), 1):
        fields = line.split("\t")
        require(len(fields) == len(COLUMNS), "malformed-row",
                f"row {number}: expected seven tab-separated fields")
        require(all(re.fullmatch(r"[0-9]+", value) for value in fields[:6]),
                "malformed-row", f"row {number}: metadata must be natural numbers")
        rows.append(Construction(*map(int, fields[:6]), fields[6]))
    return rows


def validate_row(row: Construction) -> None:
    w, h, n = row.key
    require(w > 0 and h > 0, "dimensions", f"{row.key}: dimensions must be positive")
    require(min(w, h) <= n <= w * h, "population-range",
            f"{row.key}: requested population is outside the G1 construction range")
    require(len(row.digits) == w * h, "board-size", f"{row.key}: incorrect digit-string length")
    # Validate the raw alphabet before conversion; neither integer encoding
    # nor int8 casts may silently normalize invalid constructor output.
    require(all(digit in "012" for digit in row.digits), "invalid-digits",
            f"{row.key}: board contains a nonternary digit")
    actual_east = row.digits.count("1")
    actual_north = row.digits.count("2")
    actual_total = actual_east + actual_north
    require(row.car_count == n == actual_total, "car-count",
            f"{row.key}: requested, Lean, and independently counted populations differ")
    require((row.east_count, row.north_count) == (actual_east, actual_north),
            "species-count", f"{row.key}: Lean and independently counted species differ")
    board = np.fromiter((ord(digit) - ord("0") for digit in row.digits), dtype=np.int8).reshape(h, w)
    original = board.copy()
    east_board, east_moves = half_step(board, EAST, CLASSIC)
    final_board, north_moves = half_step(east_board, NORTH, CLASSIC)
    full_board, total_moves = step(board, CLASSIC)
    require(int(east_moves) == int(north_moves) == int(total_moves) == 0,
            "not-frozen", f"{row.key}: constructed board permits CLASSIC movement")
    require(np.array_equal(east_board, original) and np.array_equal(final_board, original)
            and np.array_equal(full_board, original) and np.array_equal(board, original),
            "not-frozen", f"{row.key}: constructed board is not unchanged by CLASSIC updates")


def expected_keys(max_side: int) -> list[tuple[int, int, int]]:
    return [(w, h, n) for w in range(1, max_side + 1) for h in range(1, max_side + 1)
            for n in range(min(w, h), w * h + 1)]


def validate_coverage(rows: list[Construction], max_side: int) -> None:
    expected = expected_keys(max_side)
    actual = [row.key for row in rows]
    require(actual == expected, "coverage",
            "constructor rows are missing, duplicated, reordered, or outside the declared domain")


def check_output(output: str, max_side: int) -> list[Construction]:
    rows = parse_rows(output)
    validate_coverage(rows, max_side)
    for row in rows:
        validate_row(row)
    return rows


def negative_controls(rows: list[Construction], max_side: int) -> list[dict[str, str]]:
    """Require specific rejection reasons for corrupted actual exporter rows."""
    require(bool(rows), "coverage", "cannot check mutation controls without actual rows")
    first = rows[0]
    occupied_index = next(i for i, digit in enumerate(first.digits) if digit != "0")
    illegal_digits = first.digits[:occupied_index] + "3" + first.digits[occupied_index + 1:]
    # This metadata keeps the total population correct while misreporting its
    # species split, so aggregate-count validation alone cannot reject it.
    if first.east_count:
        wrong_species = replace(first, east_count=first.east_count - 1, north_count=first.north_count + 1)
    else:
        wrong_species = replace(first, east_count=first.east_count + 1, north_count=first.north_count - 1)
    # A single east car on a 3x1 ring has a valid G1 population but moves. When
    # that rectangle is exported, mutate its actual constructor row. Smaller
    # requested domains use the same explicit synthetic negative control.
    base = next((row for row in rows if row.key == (3, 1, 1)), Construction(3, 1, 1, 1, 0, 1, "002"))
    moving = replace(base, car_count=1, east_count=1, north_count=0, digits="100")
    controls = [
        ("dropped-row", "coverage", lambda: validate_coverage(rows[:-1], max_side)),
        ("duplicate-row", "coverage", lambda: validate_coverage(rows + [first], max_side)),
        ("malformed-row", "malformed-row", lambda: parse_rows("\t".join(first.tsv().split("\t")[:-1]))),
        ("wrong-car-count", "car-count", lambda: validate_row(replace(first, car_count=first.car_count + 1))),
        ("wrong-species-count", "species-count", lambda: validate_row(wrong_species)),
        ("invalid-digit-preserves-occupancy", "invalid-digits", lambda: validate_row(replace(first, digits=illegal_digits))),
        ("moving-board-with-valid-count", "not-frozen", lambda: validate_row(moving)),
    ]
    rejected = []
    for name, reason, check in controls:
        try:
            check()
        except ConstructionError as error:
            require(error.reason == reason, "negative-control",
                    f"{name}: rejected for {error.reason}, expected {reason}")
            rejected.append({"name": name, "reason": reason})
        else:
            raise ConstructionError("negative-control", f"corrupted constructor receipt was accepted: {name}")
    return rejected


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def source_manifest() -> dict[str, str]:
    paths = [
        ROOT / "scripts/check_g1_constructions.py", ROOT / "bml/model.py",
        ROOT / "requirements-dev.txt", LEAN / "G1Export.lean", LEAN / "BML.lean",
        LEAN / "lakefile.toml", LEAN / "lean-toolchain",
        LEAN / "Train/Counting.lean",
    ]
    paths.extend(sorted((LEAN / "BML").glob("*.lean")))
    return {str(path.relative_to(ROOT)): sha256(path.read_bytes()) for path in sorted(paths)}


def revision() -> str | None:
    result = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True,
                            text=True, check=False)
    return result.stdout.strip() if result.returncode == 0 else None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-side", type=int, default=12)
    parser.add_argument("--binary", type=Path, default=LEAN / ".lake/build/bin/g1_export")
    parser.add_argument("--report", type=Path)
    parser.add_argument("--rows", type=Path, help="preserve the raw Lean TSV output")
    args = parser.parse_args()
    if args.max_side < 1:
        parser.error("--max-side must be positive")
    if args.report and args.rows and args.report.resolve() == args.rows.resolve():
        parser.error("--report and --rows must be distinct paths")
    sources = source_manifest()
    report = {
        "schema": "bml.g1-construction-replay.v1", "status": "running", "rule": "classic",
        "constructor": "BML.gridlockWith", "started_at": datetime.now(timezone.utc).isoformat(),
        "revision": revision(), "source_sha256": sources,
        "source_manifest_sha256": sha256(json.dumps(sources, sort_keys=True).encode()),
        "runtime": {"python": platform.python_version(), "numpy": np.__version__},
        "lean_toolchain": (LEAN / "lean-toolchain").read_text().strip(),
        "columns": COLUMNS, "min_side": 1, "max_side": args.max_side,
        "scope": (
            "Every admissible exact count on the stated finite rectangle domain. "
            "Actual Lean constructor boards are checked by independent Python CLASSIC dynamics; "
            "this is not a universal source refinement, a comparison by identity with Python's "
            "different constructor, or a TRAIN-rule result."
        ),
    }
    try:
        binary = args.binary.resolve(strict=True)
        binary_digest = sha256(binary.read_bytes())
        command = [str(binary), "--max-side", str(args.max_side)]
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                                check=False, timeout=600)
        report["exporter"] = {"argv": command, "exit_code": result.returncode,
                              "executable_sha256": binary_digest}
        if args.rows:
            args.rows.parent.mkdir(parents=True, exist_ok=True)
            args.rows.write_text(result.stdout)
        require(result.returncode == 0 and not result.stderr.strip(), "exporter",
                f"Lean constructor exporter failed: {result.stderr.strip()}")
        rows = check_output(result.stdout, args.max_side)
        report["rows_sha256"] = sha256(result.stdout.encode())
        report["construction_cases"] = len(rows)
        report["rectangles"] = [
            {"width": w, "height": h, "counts_from": min(w, h), "counts_through": w*h,
             "construction_cases": w*h - min(w, h) + 1}
            for w in range(1, args.max_side + 1) for h in range(1, args.max_side + 1)
        ]
        report["rejected_mutations"] = negative_controls(rows, args.max_side)
        require(source_manifest() == sources, "source-drift", "construction sources changed during acceptance")
        require(sha256(binary.read_bytes()) == binary_digest, "source-drift", "exporter changed during acceptance")
        report["status"] = "passed"
        print(f"PASS: {len(rows)} actual Lean G1 constructions on {args.max_side**2} rectangles, "
              f"every admissible exact count; {len(report['rejected_mutations'])} negative controls rejected.")
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        if isinstance(error, ConstructionError):
            report["failure_reason"] = error.reason
        print(f"FAIL: {error}", file=sys.stderr, flush=True)
    finally:
        report["finished_at"] = datetime.now(timezone.utc).isoformat()
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(report, indent=2) + "\n")
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
