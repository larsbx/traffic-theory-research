#!/usr/bin/env python3
"""Check actual Lean G2 constructor traces against Python CLASSIC dynamics.

For every positive W,H <= --max-side (default 12), every 0 <= n < W*H is
followed for 2*max(W,H)+1 full transitions. The universal never-jam theorem is
separate: this program establishes finite constructor/phase/trace agreement.
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
    "width", "height", "requested_count", "time", "car_count", "east_count",
    "north_count", "east_moves", "north_moves", "jam", "before_digits",
    "east_digits", "after_digits",
]


class TraceError(ValueError):
    def __init__(self, reason: str, message: str):
        self.reason = reason
        super().__init__(message)


def require(condition: bool, reason: str, message: str) -> None:
    if not condition:
        raise TraceError(reason, message)


@dataclass(frozen=True)
class Transition:
    width: int
    height: int
    requested_count: int
    time: int
    car_count: int
    east_count: int
    north_count: int
    east_moves: int
    north_moves: int
    jam: int
    before: str
    east: str
    after: str

    @property
    def trace_key(self) -> tuple[int, int, int]:
        return self.width, self.height, self.requested_count

    @property
    def key(self) -> tuple[int, int, int, int]:
        return (*self.trace_key, self.time)

    def tsv(self) -> str:
        return "\t".join(map(str, (
            self.width, self.height, self.requested_count, self.time, self.car_count,
            self.east_count, self.north_count, self.east_moves, self.north_moves,
            self.jam, self.before, self.east, self.after,
        )))


def horizon(width: int, height: int) -> int:
    return 2 * max(width, height) + 1


def expected_keys(max_side: int) -> list[tuple[int, int, int, int]]:
    return [(w, h, n, time) for w in range(1, max_side + 1) for h in range(1, max_side + 1)
            for n in range(w * h) for time in range(horizon(w, h))]


def parse_rows(output: str) -> list[Transition]:
    rows = []
    for number, line in enumerate(output.splitlines(), 1):
        fields = line.split("\t")
        require(len(fields) == len(COLUMNS), "malformed-row",
                f"row {number}: expected thirteen tab-separated fields")
        require(all(re.fullmatch(r"[0-9]+", field) for field in fields[:10]),
                "malformed-row", f"row {number}: metadata must be natural numbers")
        rows.append(Transition(*map(int, fields[:10]), *fields[10:]))
    return rows


def validate_coverage(rows: list[Transition], max_side: int) -> None:
    require([row.key for row in rows] == expected_keys(max_side), "coverage",
            "G2 traces are missing, duplicated, reordered, truncated, or outside the declared domain")


def validate_trace(rows: list[Transition]) -> None:
    """Validate a nonempty consecutive trace segment with actual production updates.

    The global coverage check separately requires every full trace to start at
    time zero and run for the entire declared horizon. Allowing a short segment
    here also permits focused rejection controls without replaying all rows.
    """
    require(bool(rows), "coverage", "an empty trace segment is not evidence")
    w, h, n = rows[0].trace_key
    require(w > 0 and h > 0, "dimensions", "trace dimensions must be positive")
    require(0 <= n < w * h, "population-range", f"{(w, h, n)} is not a sub-full population")
    for offset, row in enumerate(rows):
        require(row.trace_key == (w, h, n) and row.time == rows[0].time + offset,
                "continuity", "trace keys or times are not consecutive")
        require(row.car_count == n, "car-count", f"{row.key}: wrong declared population")
        for label, digits in (("before", row.before), ("east", row.east), ("after", row.after)):
            require(len(digits) == w*h, "board-size", f"{row.key}: wrong {label} digit-string length")
            require(all(digit in "012" for digit in digits), "invalid-digits",
                    f"{row.key}: nonternary {label} digit")

    # The alphabet is validated before conversion; do not allow int8 casts or
    # a base-three encoding to normalize an invalid intermediate state.
    def boards(field: str) -> np.ndarray:
        text = "".join(getattr(row, field) for row in rows)
        return (np.frombuffer(text.encode("ascii"), dtype=np.uint8) - ord("0")).reshape(len(rows), h, w)

    before, east, after = boards("before"), boards("east"), boards("after")
    actual_east = (before == EAST).sum(axis=(1, 2))
    actual_north = (before == NORTH).sum(axis=(1, 2))
    require(bool(np.all(actual_east + actual_north == n)), "car-count",
            f"{(w, h, n)}: initial-state populations differ from the requested count")
    require(np.array_equal(actual_east, [row.east_count for row in rows]) and
            np.array_equal(actual_north, [row.north_count for row in rows]), "species-count",
            f"{(w, h, n)}: Lean and independently counted species disagree")
    for label, state in (("before", before), ("east", east), ("after", after)):
        east_count = (state == EAST).sum(axis=(1, 2))
        north_count = (state == NORTH).sum(axis=(1, 2))
        require(bool(np.all(east_count + north_count == n)), "car-count",
                f"{(w, h, n)}: {label} states change population")
        require(bool(np.all(north_count == 0 if w >= 2 else east_count == 0)), "species",
                f"{(w, h, n)}: {label} contains the other species")

    expected_east, east_moves = half_step(before, EAST, CLASSIC)
    expected_after, north_moves = half_step(expected_east, NORTH, CLASSIC)
    full_after, full_moves = step(before, CLASSIC)
    require(np.array_equal(east, expected_east), "phase-mismatch",
            f"{(w, h, n)}: Lean/Python east intermediate states differ")
    require(np.array_equal(after, expected_after) and np.array_equal(after, full_after),
            "phase-mismatch", f"{(w, h, n)}: Lean/Python north/full-step states differ")
    require(np.array_equal(east_moves, [row.east_moves for row in rows]) and
            np.array_equal(north_moves, [row.north_moves for row in rows]) and
            np.array_equal(east_moves + north_moves, full_moves), "phase-mismatch",
            f"{(w, h, n)}: Lean/Python movement counts differ")

    expected_jam = (n > 0) & (full_moves == 0)
    flags = np.array([row.jam for row in rows], dtype=np.int64)
    require(bool(np.all((flags == 0) | (flags == 1))) and np.array_equal(flags, expected_jam),
            "jam-flag", f"{(w, h, n)}: operational jam flag is incorrect (empty is not jam)")
    require(not bool(np.any(expected_jam)), "jam", f"{(w, h, n)}: constructed trace reaches gridlock")

    # Preserve the particular mixed lanes of the constructor, not merely the
    # total population: east cars stay in their row, north cars in their column.
    lane_axis, lane_length = (2, w) if w >= 2 else (1, h)
    initial_lanes = np.count_nonzero(before[0], axis=lane_axis - 1)
    for label, state in (("before", before), ("east", east), ("after", after)):
        counts = np.count_nonzero(state, axis=lane_axis)
        require(bool(np.all(counts == initial_lanes)), "lane-count",
                f"{(w, h, n)}: {label} changed a lane's car count")
    if n > 0:
        require(bool(np.any((initial_lanes > 0) & (initial_lanes < lane_length))),
                "mixed-lane", f"{(w, h, n)}: positive constructor has no car-and-hole lane")
        require(bool(np.all(full_moves > 0)), "no-movement", f"{(w, h, n)}: positive trace stopped")
    else:
        require(bool(np.all(full_moves == 0)) and np.array_equal(before, after), "empty-state",
                f"{(w, h, n)}: empty constructor did not remain fixed")
    for previous, current in zip(rows, rows[1:]):
        require(current.before == previous.after, "continuity",
                f"{current.key}: transition does not continue the preceding state")


def check_output(output: str, max_side: int) -> list[Transition]:
    rows = parse_rows(output)
    validate_coverage(rows, max_side)
    start = 0
    for w in range(1, max_side + 1):
        for h in range(1, max_side + 1):
            length = horizon(w, h)
            for _ in range(w * h):
                validate_trace(rows[start:start + length])
                start += length
    require(start == len(rows), "coverage", "unconsumed construction trace rows")
    return rows


def negative_controls(rows: list[Transition], max_side: int) -> list[dict[str, str]]:
    """Require intended rejection of corrupted receipts, not unrelated exceptions."""
    first = rows[0]  # The first declared case is the empty 1x1 constructor.
    fixed_controls = {
        (3, 1, 1, 0): Transition(3, 1, 1, 0, 1, 1, 0, 1, 0, 0, "100", "010", "010"),
        (3, 1, 1, 1): Transition(3, 1, 1, 1, 1, 1, 0, 1, 0, 0, "010", "001", "001"),
        (3, 1, 1, 2): Transition(3, 1, 1, 2, 1, 1, 0, 1, 0, 0, "001", "100", "100"),
        (1, 3, 1, 0): Transition(1, 3, 1, 0, 1, 0, 1, 0, 1, 0, "200", "200", "020"),
    }
    # At the default domain these are actual exported rows. A smaller domain
    # still runs the explicit 3x1 and 1x3 negative controls stated above.
    cases = dict(fixed_controls)
    for row in rows:
        if row.key in cases:
            cases[row.key] = row
    east0, east1, east2 = (cases[(3, 1, 1, t)] for t in (0, 1, 2))
    north0 = cases[(1, 3, 1, 0)]
    suppressed_east = replace(east0, east=east0.before, after=east0.before, east_moves=0, jam=1)
    suppressed_north = replace(north0, after=north0.before, north_moves=0, jam=1)
    invalid_index = next(i for i, digit in enumerate(east0.east) if digit != "0")
    invalid_east = east0.east[:invalid_index] + "3" + east0.east[invalid_index + 1:]
    disconnected = replace(east1, before=east2.before, east=east2.east, after=east2.after,
                           east_moves=east2.east_moves, north_moves=east2.north_moves)
    controls = [
        ("missing-trace", "coverage", lambda: validate_coverage(
            [row for row in rows if row.trace_key != first.trace_key], max_side)),
        ("duplicate-transition", "coverage", lambda: validate_coverage(rows + [first], max_side)),
        ("malformed-row", "malformed-row", lambda: parse_rows("\t".join(first.tsv().split("\t")[:-1]))),
        ("wrong-car-count", "car-count", lambda: validate_trace([replace(first, car_count=1)])),
        ("wrong-species-count", "species-count", lambda: validate_trace([
            replace(east0, east_count=0, north_count=1)])),
        ("invalid-intermediate-digit", "invalid-digits", lambda: validate_trace([
            replace(east0, east=invalid_east)])),
        ("false-empty-jam", "jam-flag", lambda: validate_trace([replace(first, jam=1)])),
        ("suppressed-east-movement", "phase-mismatch", lambda: validate_trace([suppressed_east])),
        ("suppressed-north-movement", "phase-mismatch", lambda: validate_trace([suppressed_north])),
        ("disconnected-valid-transition", "continuity", lambda: validate_trace([east0, disconnected])),
    ]
    rejected = []
    for name, reason, check in controls:
        try:
            check()
        except TraceError as error:
            require(error.reason == reason, "negative-control",
                    f"{name}: rejected for {error.reason}, expected {reason}")
            rejected.append({"name": name, "reason": reason})
        else:
            raise TraceError("negative-control", f"invalid trace accepted: {name}")
    return rejected


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def source_manifest() -> dict[str, str]:
    # Audit imports umbrella BML and G1Export; include their local closure too.
    paths = [
        ROOT / "scripts/check_g2_constructions.py", ROOT / "bml/model.py",
        ROOT / "requirements-dev.txt", LEAN / "G2Export.lean", LEAN / "G2Audit.lean",
        LEAN / "BML.lean", LEAN / "Audit.lean", LEAN / "G1Export.lean", LEAN / "lakefile.toml",
        LEAN / "lake-manifest.json", LEAN / "lean-toolchain",
        LEAN / "Train/Counting.lean", LEAN / "Train/Finite.lean",
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
    parser.add_argument("--binary", type=Path, default=LEAN / ".lake/build/bin/g2_export")
    parser.add_argument("--report", type=Path)
    parser.add_argument("--rows", type=Path, help="preserve actual Lean transition rows")
    args = parser.parse_args()
    if args.max_side < 1:
        parser.error("--max-side must be positive")
    if args.report and args.rows and args.report.resolve() == args.rows.resolve():
        parser.error("--report and --rows must be distinct paths")
    sources = source_manifest()
    report = {
        "schema": "bml.g2-construction-replay.v1", "status": "running", "rule": "classic",
        "constructor": "BML.nonGridlockWith", "started_at": datetime.now(timezone.utc).isoformat(),
        "revision": revision(), "source_sha256": sources,
        "source_manifest_sha256": sha256(json.dumps(sources, sort_keys=True).encode()),
        "runtime": {"python": platform.python_version(), "numpy": np.__version__},
        "lean_toolchain": (LEAN / "lean-toolchain").read_text().strip(),
        "columns": COLUMNS, "min_side": 1, "max_side": args.max_side,
        "transitions_per_trace": "2*max(width,height)+1",
        "scope": (
            "Actual Lean constructor and kernel traces on the stated finite domain/horizon, "
            "including empty and singleton-dimension cases, compared to production Python CLASSIC "
            "phases. Finite replay is not a proof of perpetual non-gridlock, a universal source "
            "refinement, or a TRAIN-rule result. The universal G2 theorem is audited separately."
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
                f"Lean G2 exporter failed: {result.stderr.strip()}")
        rows = check_output(result.stdout, args.max_side)
        report["rows_sha256"] = sha256(result.stdout.encode())
        report["construction_cases"] = sum(w*h for w in range(1, args.max_side + 1)
                                           for h in range(1, args.max_side + 1))
        report["transition_rows"] = len(rows)
        report["empty_construction_cases"] = args.max_side**2
        report["rectangles"] = [
            {"width": w, "height": h, "counts_from": 0, "counts_through": w*h - 1,
             "construction_cases": w*h, "transitions_per_trace": horizon(w, h),
             "transition_rows": w*h*horizon(w, h)}
            for w in range(1, args.max_side + 1) for h in range(1, args.max_side + 1)
        ]
        report["rejected_mutations"] = negative_controls(rows, args.max_side)
        require(source_manifest() == sources, "source-drift", "G2 sources changed during acceptance")
        require(sha256(binary.read_bytes()) == binary_digest, "source-drift", "G2 exporter changed during acceptance")
        report["status"] = "passed"
        print(f"PASS: {report['construction_cases']} Lean G2 constructions, {len(rows)} actual "
              f"transition rows on {args.max_side**2} rectangles; "
              f"{len(report['rejected_mutations'])} negative controls rejected.")
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        if isinstance(error, TraceError):
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
