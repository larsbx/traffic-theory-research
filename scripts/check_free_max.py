#!/usr/bin/env python3
"""Replay actual Lean Theorem F constructors through the complete lcm window.

For every ordered positive W,H <= --max-side (default 12), check every count
from zero through the independently computed free-flow capacity, inclusive.
Every east phase and successive full state is replayed by the independent
scalar CLASSIC kernel. Universal optimality is a separate Lean theorem.
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
import time

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "formal/lean"
sys.path.insert(0, str(ROOT))

# These routines use scalar snapshot updates, not production NumPy stepping,
# the capacity construction, or the eventual-free-flow classifier.
from scripts.check_freeflow import scalar_round, static_rules  # noqa: E402

COLUMNS = [
    "width", "height", "requested_count", "free_max", "lcm", "car_count",
    "east_count", "north_count", "static_free", "state_digits", "east_digits",
    "east_moves", "north_moves",
]


class FreeMaxError(ValueError):
    def __init__(self, reason: str, message: str):
        self.reason = reason
        super().__init__(message)


def require(condition: bool, reason: str, message: str) -> None:
    if not condition:
        raise FreeMaxError(reason, message)


@dataclass(frozen=True)
class Trace:
    width: int
    height: int
    requested_count: int
    free_max: int
    period: int
    car_count: int
    east_count: int
    north_count: int
    static_free: int
    state_digits: tuple[str, ...]
    east_digits: tuple[str, ...]
    east_moves: tuple[int, ...]
    north_moves: tuple[int, ...]

    @property
    def key(self) -> tuple[int, int, int]:
        return self.width, self.height, self.requested_count

    def tsv(self) -> str:
        scalars = (self.width, self.height, self.requested_count, self.free_max,
                   self.period, self.car_count, self.east_count, self.north_count,
                   self.static_free)
        vectors = (self.state_digits, self.east_digits, self.east_moves, self.north_moves)
        return "\t".join([*(str(value) for value in scalars),
                          *(",".join(map(str, values)) for values in vectors)])


def capacity(width: int, height: int) -> int:
    """The published nested-floor formula, independent of Lean's 2*g/3 form."""
    g = gcd(width, height)
    if g == 1:
        return max(height * (width // 2), width * (height // 2))
    return (width * height // g) * ((g + g // 3) // 2)


def expected_keys(max_side: int) -> list[tuple[int, int, int]]:
    return [(w, h, n) for w in range(1, max_side + 1)
            for h in range(1, max_side + 1) for n in range(capacity(w, h) + 1)]


def parse_rows(output: str) -> list[Trace]:
    rows = []
    for number, line in enumerate(output.splitlines(), 1):
        fields = line.split("\t")
        require(len(fields) == len(COLUMNS), "malformed-row",
                f"row {number}: expected thirteen tab-separated fields")
        require(all(re.fullmatch(r"[0-9]+", value) for value in fields[:9]),
                "malformed-row", f"row {number}: metadata must be natural numbers")
        require(all(re.fullmatch(r"[0-9]+(?:,[0-9]+)*", value) for value in fields[11:]),
                "malformed-row", f"row {number}: move lists must contain natural numbers")
        rows.append(Trace(*map(int, fields[:9]), tuple(fields[9].split(",")),
                          tuple(fields[10].split(",")),
                          *(tuple(map(int, value.split(","))) for value in fields[11:])))
    return rows


def validate_coverage(rows: list[Trace], max_side: int) -> None:
    require([row.key for row in rows] == expected_keys(max_side), "coverage",
            "constructor rows are missing, duplicated, reordered, truncated, or outside the domain")


def validate_shape(row: Trace) -> None:
    w, h = row.width, row.height
    require(w > 0 and h > 0, "dimensions", f"{row.key}: dimensions must be positive")
    require(row.free_max == capacity(w, h), "formula",
            f"{row.key}: Lean freeMax differs from the independent gcd/nested-floor formula")
    require(0 <= row.requested_count <= row.free_max, "population-range",
            f"{row.key}: requested count lies outside the attainable interval")
    require(row.period == lcm(w, h), "period", f"{row.key}: incorrect lcm")
    require(row.car_count == row.requested_count, "car-count",
            f"{row.key}: Lean constructor count differs from its request")
    require(row.static_free in (0, 1), "flags", f"{row.key}: StaticFree is not Boolean")
    require(len(row.state_digits) == row.period + 1 and
            all(len(values) == row.period for values in
                (row.east_digits, row.east_moves, row.north_moves)), "trace-length",
            f"{row.key}: complete lcm trace, including the final edge, is required")
    for digits in (*row.state_digits, *row.east_digits):
        require(len(digits) == w*h, "board-size", f"{row.key}: wrong digit-string length")
        require(all(digit in "012" for digit in digits), "invalid-digits",
                f"{row.key}: every snapshot must use only ternary digits")


def validate_trace(row: Trace) -> None:
    validate_shape(row)
    w, h = row.width, row.height
    states = [tuple(map(int, digits)) for digits in row.state_digits]
    east_states = [tuple(map(int, digits)) for digits in row.east_digits]
    initial = states[0]
    population = initial.count(1), initial.count(2)
    require(sum(population) == row.requested_count, "car-count",
            f"{row.key}: actual board population differs from the requested count")
    require(population == (row.east_count, row.north_count), "species-count",
            f"{row.key}: Lean and independently counted species disagree")
    rules = static_rules(initial, w, h)
    require(row.static_free == int(all(rules)), "static-mismatch",
            f"{row.key}: actual Lean StaticFree differs from the independent four rules")
    require(all(rules), "static-blocked",
            f"{row.key}: constructor violates static free flow; four rules={rules}")
    current = initial
    for t in range(row.period):
        east, after, em, nm = scalar_round(current, w, h)
        require(states[t] == current and east_states[t] == east and states[t+1] == after,
                "phase-mismatch", f"{row.key} at t={t}: exported phase differs from scalar replay")
        require((row.east_moves[t], row.north_moves[t]) == (em, nm), "movement-count",
                f"{row.key} at t={t}: separate Lean phase move counts disagree")
        for label, board in (("east", east_states[t]), ("after", states[t+1])):
            require((board.count(1), board.count(2)) == population, "conservation",
                    f"{row.key} at t={t}: {label} phase changes species counts")
        require((em, nm) == population, "blocked-round",
                f"{row.key} at t={t}: at least one car fails to move")
        current = after
    require(current == initial, "closure",
            f"{row.key}: the final lcm edge does not return to the initial configuration")


def check_output(output: str, max_side: int) -> tuple[list[Trace], list[dict[str, int]]]:
    rows = parse_rows(output)
    validate_coverage(rows, max_side)
    rectangles, offset = [], 0
    for w in range(1, max_side + 1):
        for h in range(1, max_side + 1):
            maximum = capacity(w, h)
            rectangle = rows[offset:offset + maximum + 1]
            for row in rectangle:
                validate_trace(row)
            rectangles.append({"width": w, "height": h, "gcd": gcd(w, h),
                               "free_max": maximum, "constructors": maximum + 1,
                               "period": lcm(w, h),
                               "transition_rows": (maximum + 1) * lcm(w, h)})
            offset += maximum + 1
    require(offset == len(rows), "coverage", "some constructor rows were not consumed")
    return rows, rectangles


def fixture(w: int, h: int, initial: tuple[int, ...]) -> Trace:
    """Scalar fixtures are rejection controls, never evidence of a Lean constructor."""
    require(len(initial) == w*h and all(digit in (0, 1, 2) for digit in initial),
            "fixture", "fixture must be a correctly sized ternary board")
    digits = lambda board: "".join(map(str, board))
    states, east_states, east_moves, north_moves = [digits(initial)], [], [], []
    current = initial
    for _ in range(lcm(w, h)):
        east, current, em, nm = scalar_round(current, w, h)
        states.append(digits(current))
        east_states.append(digits(east))
        east_moves.append(em)
        north_moves.append(nm)
    e, n = initial.count(1), initial.count(2)
    return Trace(w, h, e+n, capacity(w, h), lcm(w, h), e+n, e, n,
                 int(all(static_rules(initial, w, h))), tuple(states), tuple(east_states),
                 tuple(east_moves), tuple(north_moves))


def negative_controls(rows: list[Trace], max_side: int) -> list[dict[str, str]]:
    """Require each malformed witness to fail for its intended reason."""
    first = rows[0]
    east = fixture(3, 1, (1, 0, 0))
    north = fixture(1, 3, (2, 0, 0))
    validate_trace(east)
    validate_trace(north)
    blocked = {
        "east-adjacency": fixture(4, 1, (1, 1, 0, 0)),
        "north-adjacency": fixture(1, 4, (2, 2, 0, 0)),
        "equal-phase": fixture(3, 3, (1, 0, 0, 0, 0, 0, 0, 2, 0)),
        "next-phase": fixture(2, 2, (1, 0, 2, 0)),
    }
    for index, (name, row) in enumerate(blocked.items()):
        rules = static_rules(tuple(map(int, row.state_digits[0])), row.width, row.height)
        require(rules == tuple(i != index for i in range(4)) and
                row.requested_count <= capacity(row.width, row.height), "control-premise",
                f"{name}: blocked board does not isolate the intended rule at a valid population")
    reordered = rows[1:] + rows[:1] if len(rows) > 1 else []
    controls = [
        ("missing-constructor", "coverage", lambda: validate_coverage(rows[:-1], max_side)),
        ("duplicate-constructor", "coverage", lambda: validate_coverage([*rows, first], max_side)),
        ("reordered-constructors", "coverage", lambda: validate_coverage(reordered, max_side)),
        ("malformed-row", "malformed-row", lambda: parse_rows(first.tsv() + "\textra")),
        ("wrong-formula", "formula", lambda: validate_trace(replace(first, free_max=first.free_max+1))),
        ("wrong-car-count", "car-count", lambda: validate_trace(replace(first, car_count=1))),
        ("wrong-species-count", "species-count", lambda: validate_trace(
            replace(east, east_count=0, north_count=1))),
        ("nonboolean-static-flag", "flags", lambda: validate_trace(replace(first, static_free=2))),
        ("false-static-flag", "static-mismatch", lambda: validate_trace(replace(east, static_free=0))),
        ("invalid-intermediate-digit", "invalid-digits", lambda: validate_trace(
            replace(east, east_digits=("030", *east.east_digits[1:])))),
        ("incorrect-board-size", "board-size", lambda: validate_trace(
            replace(east, state_digits=("10", *east.state_digits[1:])))),
        ("wrong-lcm", "period", lambda: validate_trace(replace(east, period=east.period+1))),
        ("missing-final-state", "trace-length", lambda: validate_trace(
            replace(east, state_digits=east.state_digits[:-1]))),
        ("missing-final-east-phase", "trace-length", lambda: validate_trace(
            replace(east, east_digits=east.east_digits[:-1]))),
        ("suppressed-east-phase", "phase-mismatch", lambda: validate_trace(
            replace(east, east_digits=(east.state_digits[0], *east.east_digits[1:])))),
        ("suppressed-north-phase", "phase-mismatch", lambda: validate_trace(
            replace(north, state_digits=(north.state_digits[0], north.state_digits[0],
                                         *north.state_digits[2:])))),
        ("corrupted-closing-edge", "phase-mismatch", lambda: validate_trace(
            replace(east, state_digits=(*east.state_digits[:-1], east.state_digits[1])))),
        ("wrong-phase-move-count", "movement-count", lambda: validate_trace(
            replace(east, east_moves=(0, *east.east_moves[1:])))),
    ]
    controls.extend((f"valid-population-blocked-{name}", "static-blocked",
                     lambda row=row: validate_trace(row)) for name, row in blocked.items())
    rejected = []
    for name, reason, run in controls:
        try:
            run()
        except FreeMaxError as error:
            require(error.reason == reason, "negative-control",
                    f"{name}: rejected for {error.reason}, expected {reason}")
            rejected.append({"name": name, "reason": error.reason})
        else:
            raise FreeMaxError("negative-control", f"{name}: malformed witness was accepted")
    return rejected


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def local_lean_closure(roots: list[Path]) -> set[Path]:
    """Bind every repository Lean import reached by exporter and axiom audit."""
    pending, seen = list(roots), set()
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        for line in path.read_text().splitlines():
            match = re.match(r"\s*import\s+([^\n-]+)", line)
            if match:
                for module in match.group(1).split():
                    dependency = LEAN / (module.replace(".", "/") + ".lean")
                    if dependency.is_file():
                        pending.append(dependency)
    return seen


def source_manifest() -> dict[str, str]:
    paths = local_lean_closure([LEAN / "FreeMaxExport.lean", LEAN / "FreeMaxAudit.lean"])
    paths.update(ROOT / path for path in (
        "scripts/check_free_max.py", "scripts/check_freeflow.py",
        "tests/test_free_max_acceptance.py", "bml/__init__.py", "bml/model.py",
        "bml/exhaustive.py", "requirements-dev.txt",
    ))
    paths.update(LEAN / name for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"))
    return {str(path.relative_to(ROOT)): sha256(path.read_bytes()) for path in sorted(paths)}


def revision() -> str | None:
    result = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True,
                            text=True, check=False)
    return result.stdout.strip() if result.returncode == 0 else None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-side", type=int, default=12)
    parser.add_argument("--binary", type=Path, default=LEAN / ".lake/build/bin/free_max_export")
    parser.add_argument("--report", type=Path)
    parser.add_argument("--rows", type=Path, help="preserve actual Lean constructor/phase rows")
    args = parser.parse_args()
    if args.max_side < 1:
        parser.error("--max-side must be positive")
    if args.report and args.rows and args.report.resolve() == args.rows.resolve():
        parser.error("--report and --rows must be distinct paths")
    started = time.perf_counter()
    sources = source_manifest()
    report = {
        "schema": "bml.free-max-construction-replay.v1", "status": "running", "rule": "classic",
        "constructor": "BML.freeWith", "capacity": "BML.freeMax",
        "started_at": datetime.now(timezone.utc).isoformat(), "revision": revision(),
        "source_sha256": sources,
        "source_manifest_sha256": sha256(json.dumps(sources, sort_keys=True).encode()),
        "runtime": {"python": platform.python_version()},
        "lean_toolchain": (LEAN / "lean-toolchain").read_text().strip(),
        "columns": COLUMNS, "min_side": 1, "max_side": args.max_side,
        "transitions_per_constructor": "lcm(width,height), including the final closing edge",
        "scope": (
            "Every actual Lean freeWith constructor on every ordered positive rectangle in the "
            "declared side bound and every population 0..freeMax inclusive. Exact Lean car/species "
            "counts and StaticFree decisions, the independent gcd/nested-floor capacity formula, "
            "all four static rules, separate phase snapshots and move counts, species conservation, "
            "full movement in every round, and lcm closure are checked. Dynamics use the scalar "
            "oracle from scripts/check_freeflow.py. Finite construction acceptance is separate from "
            "the universal optimality theorem and axiom audit."
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
                f"Lean free-max exporter failed: {result.stderr.strip()}")
        rows, rectangles = check_output(result.stdout, args.max_side)
        report["rows_sha256"] = sha256(result.stdout.encode())
        report["construction_rows"] = len(rows)
        report["transition_rows"] = sum(rectangle["transition_rows"] for rectangle in rectangles)
        report["full_state_snapshots"] = report["transition_rows"] + len(rows)
        report["east_phase_snapshots"] = report["transition_rows"]
        report["rectangles"] = rectangles
        report["capacity_attaining_constructors"] = len(rectangles)
        report["singleton_side_rectangles"] = sum(
            rectangle["width"] == 1 or rectangle["height"] == 1 for rectangle in rectangles)
        report["coprime_rectangles"] = sum(rectangle["gcd"] == 1 for rectangle in rectangles)
        report["rejected_mutations"] = negative_controls(rows, args.max_side)
        require(source_manifest() == sources, "source-drift", "free-max sources changed during acceptance")
        require(sha256(binary.read_bytes()) == binary_digest, "source-drift",
                "free-max exporter changed during acceptance")
        report["revision_end"] = revision()
        require(report["revision_end"] == report["revision"], "source-drift",
                "repository revision changed during acceptance")
        report["status"] = "passed"
        print(f"PASS: {len(rows)} actual Lean constructors on {len(rectangles)} rectangles, "
              f"{report['transition_rows']} complete transitions, every attainable population; "
              f"{len(report['rejected_mutations'])} negative controls rejected.")
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        if isinstance(error, FreeMaxError):
            report["failure_reason"] = error.reason
        print(f"FAIL: {error}", file=sys.stderr, flush=True)
    finally:
        report["finished_at"] = datetime.now(timezone.utc).isoformat()
        report["elapsed_seconds"] = time.perf_counter() - started
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(report, indent=2) + "\n")
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
