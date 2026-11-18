#!/usr/bin/env python3
"""Check actual Lean diagonal successors, phase classes, and east translates.

Every position of every positive W,H <= --max-side (default 12) is exported.
Complete cycles are reconstructed from those actual edges and compared to an
independent Python modular-arithmetic oracle. Both coset relations are checked
on every ordered pair of positions. This finite acceptance is separate from
the general theorem and does not establish the full free-flow characterization.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, replace
from datetime import datetime, timezone
import hashlib
import json
from math import gcd, lcm
from pathlib import Path
import platform
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "formal/lean"
COLUMNS = [
    "width", "height", "gcd", "lcm", "x", "y", "next_x", "next_y",
    "phase", "shift_x", "shift_y", "shift_phase",
]
Point = tuple[int, int]


class CosetError(ValueError):
    def __init__(self, reason: str, message: str):
        self.reason = reason
        super().__init__(message)


def require(condition: bool, reason: str, message: str) -> None:
    if not condition:
        raise CosetError(reason, message)


@dataclass(frozen=True)
class PositionRow:
    width: int
    height: int
    gcd: int
    lcm: int
    x: int
    y: int
    next_x: int
    next_y: int
    phase: int
    shift_x: int
    shift_y: int
    shift_phase: int

    @property
    def point(self) -> Point:
        return self.x, self.y

    @property
    def successor(self) -> Point:
        return self.next_x, self.next_y

    @property
    def shifted(self) -> Point:
        return self.shift_x, self.shift_y

    @property
    def key(self) -> tuple[int, int, int, int]:
        return self.width, self.height, self.x, self.y

    def tsv(self) -> str:
        return "\t".join(str(getattr(self, field)) for field in COLUMNS)


def parse_rows(output: str) -> list[PositionRow]:
    rows = []
    for number, line in enumerate(output.splitlines(), 1):
        fields = line.split("\t")
        require(len(fields) == len(COLUMNS), "malformed-row",
                f"row {number}: expected twelve tab-separated fields")
        require(all(re.fullmatch(r"[0-9]+", field) for field in fields),
                "malformed-row", f"row {number}: fields must be natural numbers")
        rows.append(PositionRow(*map(int, fields)))
    return rows


def validate_coverage(rows: list[PositionRow], max_side: int) -> None:
    expected = [(w, h, x, y) for w in range(1, max_side + 1)
                for h in range(1, max_side + 1) for y in range(h) for x in range(w)]
    require([row.key for row in rows] == expected, "coverage",
            "positions are missing, duplicated, reordered, truncated, or outside the declared domain")


def validate_row(row: PositionRow) -> None:
    w, h = row.width, row.height
    require(w > 0 and h > 0, "dimensions", f"{row.key}: dimensions must be positive")
    for label, (x, y) in (("position", row.point), ("successor", row.successor),
                         ("east translate", row.shifted)):
        require(0 <= x < w and 0 <= y < h, "coordinates",
                f"{row.key}: {label} is outside the torus")
    g, period = gcd(w, h), lcm(w, h)
    require(row.gcd == g, "modulus", f"{row.key}: Lean/Python gcd differs")
    require(row.lcm == period, "period", f"{row.key}: Lean/Python lcm differs")
    require(row.successor == ((row.x + 1) % w, (row.y - 1) % h), "step-mismatch",
            f"{row.key}: diagonalStep differs from independent (+1,-1) arithmetic")
    require(row.phase == (row.x + row.y) % g, "phase-class",
            f"{row.key}: phaseClass differs from independent x+y modulo gcd")
    require(row.shifted == ((row.x + 1) % w, row.y), "shift-mismatch",
            f"{row.key}: actual east translate is incorrect")
    require(row.shift_phase == sum(row.shifted) % g and
            row.shift_phase == (row.phase + 1) % g, "shift-phase",
            f"{row.key}: east translate does not have the expected class increment")


def validate_rectangle(rows: list[PositionRow]) -> dict[str, int]:
    require(bool(rows), "coverage", "an empty rectangle is not evidence")
    w, h = rows[0].width, rows[0].height
    points = [(x, y) for y in range(h) for x in range(w)]
    require([row.key for row in rows] == [(w, h, *point) for point in points],
            "coverage", f"{(w, h)}: rectangle does not contain each position exactly once")
    for row in rows:
        validate_row(row)
    observations = {row.point: row for row in rows}
    require({row.successor for row in rows} == set(points), "permutation",
            f"{(w, h)}: exported successor is not a permutation")
    g, period = gcd(w, h), lcm(w, h)
    reachable: dict[Point, set[Point]] = {}
    orbit_visits = 0
    for start in points:
        current = start
        sequence: list[Point] = []
        visited: set[Point] = set()
        while current not in visited:
            require(current in observations and len(sequence) < w*h, "orbit",
                    f"{(w, h, start)}: orbit escaped the exported finite graph")
            sequence.append(current)
            visited.add(current)
            current = observations[current].successor
        # This checks the actual final edge as well as all preceding edges.
        # A repetition at another node would be a transient, not a cycle of start.
        require(current == start, "closure", f"{(w, h, start)}: final edge does not close at start")
        require(len(sequence) == len(visited) == period, "orbit-period",
                f"{(w, h, start)}: first return period is not lcm(width,height)")
        oracle = [((start[0] + time) % w, (start[1] - time) % h) for time in range(period)]
        require(sequence == oracle, "orbit-mismatch",
                f"{(w, h, start)}: ordered Lean-exported orbit differs from independent oracle")
        reachable[start] = visited
        orbit_visits += len(sequence)

    classes = {residue: {row.point for row in rows if row.phase == residue} for residue in range(g)}
    require(all(len(group) == period for group in classes.values()), "class-size",
            f"{(w, h)}: phase classes do not all have lcm(width,height) elements")
    origin = (0, 0)
    require(reachable[origin] == classes[0], "origin-coset",
            f"{(w, h)}: origin orbit differs from the zero phase class")
    require(reachable[observations[origin].shifted] == classes[1 % g], "class-one-coset",
            f"{(w, h)}: shifted origin orbit differs from the class-one coset")

    ordered_pairs = 0
    for source in points:
        source_row = observations[source]
        for target in points:
            target_phase = observations[target].phase
            require((target in reachable[source]) == (target_phase == source_row.phase),
                    "same-class-reachability", f"{(w, h, source, target)}: coset identity fails")
            require((target in reachable[source_row.shifted]) ==
                    (target_phase == (source_row.phase + 1) % g), "shifted-class-reachability",
                    f"{(w, h, source, target)}: B3 shifted class criterion fails")
            ordered_pairs += 1
    return {"width": w, "height": h, "gcd": g, "period": period,
            "positions": len(rows), "orbit_visits": orbit_visits,
            "ordered_pairs_per_relation": ordered_pairs}


def check_output(output: str, max_side: int) -> tuple[list[PositionRow], list[dict[str, int]]]:
    rows = parse_rows(output)
    validate_coverage(rows, max_side)
    rectangles = []
    start = 0
    for w in range(1, max_side + 1):
        for h in range(1, max_side + 1):
            rectangles.append(validate_rectangle(rows[start:start + w*h]))
            start += w*h
    require(start == len(rows), "coverage", "unconsumed position rows")
    return rows, rectangles


def negative_controls(rows: list[PositionRow], max_side: int) -> list[dict[str, str]]:
    """Reject meaningful corruptions for the intended reason, not incidental errors."""
    first = rows[0]
    # For a smaller requested domain, these explicit fixtures keep both signs
    # and nontrivial phase classes covered by the negative controls. At the
    # default bound they are replaced by the actual exported observations.
    cases = {
        (3, 3, 0, 0): PositionRow(3, 3, 3, 3, 0, 0, 1, 2, 0, 1, 0, 1),
        (2, 2, 0, 0): PositionRow(2, 2, 2, 2, 0, 0, 1, 1, 0, 1, 0, 1),
    }
    for row in rows:
        if row.key in cases:
            cases[row.key] = row
    square3, square2 = cases[(3, 3, 0, 0)], cases[(2, 2, 0, 0)]
    controls = [
        ("truncated-positions", "coverage", lambda: validate_coverage(rows[:-1], max_side)),
        ("duplicate-position", "coverage", lambda: validate_coverage(rows + [first], max_side)),
        ("malformed-row", "malformed-row", lambda: parse_rows("\t".join(first.tsv().split("\t")[:-1]))),
        ("out-of-range-successor", "coordinates", lambda: validate_row(replace(first, next_x=first.width))),
        ("wrong-north-sign", "step-mismatch", lambda: validate_row(replace(square3, next_y=1))),
        ("wrong-east-sign", "step-mismatch", lambda: validate_row(replace(square3, next_x=2))),
        ("wrong-modulus", "modulus", lambda: validate_row(replace(square2, gcd=1))),
        ("zero-modulus", "modulus", lambda: validate_row(replace(first, gcd=0))),
        ("wrong-phase-class", "phase-class", lambda: validate_row(replace(square2, phase=1))),
        ("wrong-period", "period", lambda: validate_row(replace(square3, lcm=6))),
        # North translation has the same phase increment. The coordinate check
        # must still reject it in place of the actual east translation.
        ("wrong-east-translate", "shift-mismatch", lambda: validate_row(
            replace(square3, shift_x=0, shift_y=1))),
        ("wrong-shift-phase", "shift-phase", lambda: validate_row(replace(square2, shift_phase=0))),
    ]
    rejected = []
    for name, reason, check in controls:
        try:
            check()
        except CosetError as error:
            require(error.reason == reason, "negative-control",
                    f"{name}: rejected for {error.reason}, expected {reason}")
            rejected.append({"name": name, "reason": reason})
        else:
            raise CosetError("negative-control", f"invalid observation accepted: {name}")
    return rejected


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def source_manifest() -> dict[str, str]:
    # Audit imports umbrella BML and G1Export; include their local closure too.
    paths = [
        ROOT / "scripts/check_cosets.py", LEAN / "CosetExport.lean", LEAN / "CosetAudit.lean",
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
    parser.add_argument("--binary", type=Path, default=LEAN / ".lake/build/bin/coset_export")
    parser.add_argument("--report", type=Path)
    parser.add_argument("--rows", type=Path, help="preserve actual Lean position observations")
    args = parser.parse_args()
    if args.max_side < 1:
        parser.error("--max-side must be positive")
    if args.report and args.rows and args.report.resolve() == args.rows.resolve():
        parser.error("--report and --rows must be distinct paths")
    sources = source_manifest()
    report = {
        "schema": "bml.coset-replay.v1", "status": "running",
        "functions": ["BML.diagonalStep", "BML.phaseClass", "BML.eastDirection.next"],
        "started_at": datetime.now(timezone.utc).isoformat(), "revision": revision(),
        "source_sha256": sources,
        "source_manifest_sha256": sha256(json.dumps(sources, sort_keys=True).encode()),
        "runtime": {"python": platform.python_version()},
        "lean_toolchain": (LEAN / "lean-toolchain").read_text().strip(),
        "columns": COLUMNS, "min_side": 1, "max_side": args.max_side,
        "scope": (
            "Actual Lean diagonal successors, phase classes, and east translates on every "
            "position of the stated positive rectangles. All complete ordered cycles, their "
            "closing edges, and both pairwise coset relations are checked with an independent "
            "Python arithmetic oracle. Includes origin/zero residue, singleton dimensions, "
            "and coprime sides. Finite acceptance is not a universal source refinement or the "
            "full free-flow characterization. The universal coset theorem is audited separately."
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
                f"Lean coset exporter failed: {result.stderr.strip()}")
        rows, rectangles = check_output(result.stdout, args.max_side)
        report["rows_sha256"] = sha256(result.stdout.encode())
        report["position_rows"] = len(rows)
        report["complete_starting_point_orbits"] = len(rows)
        report["orbit_visits"] = sum(rectangle["orbit_visits"] for rectangle in rectangles)
        report["ordered_pairs_per_relation"] = sum(
            rectangle["ordered_pairs_per_relation"] for rectangle in rectangles)
        report["relations_checked"] = ["same-phase iff reachable", "phase-plus-one iff reachable from east translate"]
        report["rectangles"] = rectangles
        report["coprime_rectangles"] = sum(rectangle["gcd"] == 1 for rectangle in rectangles)
        report["singleton_side_rectangles"] = sum(
            rectangle["width"] == 1 or rectangle["height"] == 1 for rectangle in rectangles)
        report["rejected_mutations"] = negative_controls(rows, args.max_side)
        require(source_manifest() == sources, "source-drift", "coset sources changed during acceptance")
        require(sha256(binary.read_bytes()) == binary_digest, "source-drift", "coset exporter changed during acceptance")
        report["status"] = "passed"
        print(f"PASS: {len(rows)} actual Lean position rows and complete orbits on {len(rectangles)} "
              f"rectangles, {report['orbit_visits']} orbit visits, "
              f"{report['ordered_pairs_per_relation']} ordered pairs per coset relation; "
              f"{len(report['rejected_mutations'])} negative controls rejected.")
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        if isinstance(error, CosetError):
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
