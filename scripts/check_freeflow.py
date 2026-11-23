#!/usr/bin/env python3
"""Replay actual Lean CLASSIC free-flow decisions and complete lcm windows.

Every state on every positive ordered W×H torus with WH <= --max-cells is
checked (default 9). A scalar orbit-following oracle stops at the first
blocked round, or at its first repeated state, without assuming the lcm
bound or the static characterization. This is perpetual speed one FROM
TIME ZERO, not the existing classifier's eventual-free-flow label.
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

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "formal/lean"
sys.path.insert(0, str(ROOT))
from bml.exhaustive import decode, encode  # noqa: E402
from bml.model import CLASSIC, EAST, NORTH, half_step  # noqa: E402

COLUMNS = ["width", "height", "input_code", "lcm", "static_free",
           "all_move_window", "first_blocked", "state_codes", "east_codes",
           "east_moves", "north_moves", "all_move_flags"]


class FreeFlowError(ValueError):
    def __init__(self, reason: str, message: str):
        self.reason = reason
        super().__init__(message)


def require(condition: bool, reason: str, message: str) -> None:
    if not condition:
        raise FreeFlowError(reason, message)


@dataclass(frozen=True)
class Trace:
    width: int
    height: int
    input_code: int
    period: int
    static_free: int
    all_move_window: int
    first_blocked: int
    state_codes: tuple[int, ...]
    east_codes: tuple[int, ...]
    east_moves: tuple[int, ...]
    north_moves: tuple[int, ...]
    all_move_flags: tuple[int, ...]

    @property
    def key(self) -> tuple[int, int, int]:
        return self.width, self.height, self.input_code

    def tsv(self) -> str:
        scalars = (self.width, self.height, self.input_code, self.period,
                   self.static_free, self.all_move_window, self.first_blocked)
        vectors = (self.state_codes, self.east_codes, self.east_moves,
                   self.north_moves, self.all_move_flags)
        return "\t".join([*(str(value) for value in scalars),
                          *(",".join(map(str, values)) for values in vectors)])


def parse_rows(output: str) -> list[Trace]:
    rows = []
    for number, line in enumerate(output.splitlines(), 1):
        fields = line.split("\t")
        require(len(fields) == len(COLUMNS), "malformed-row",
                f"row {number}: expected twelve tab-separated fields")
        require(all(re.fullmatch(r"[0-9]+", field) for field in fields[:7]),
                "malformed-row", f"row {number}: scalars must be natural numbers")
        require(all(re.fullmatch(r"[0-9]+(?:,[0-9]+)*", field) for field in fields[7:]),
                "malformed-row", f"row {number}: lists must contain natural numbers")
        scalars = [int(field) for field in fields[:7]]
        vectors = [tuple(map(int, field.split(","))) for field in fields[7:]]
        rows.append(Trace(*scalars, *vectors))
    return rows


def domain(max_cells: int) -> list[tuple[int, int]]:
    return [(w, h) for w in range(1, max_cells + 1)
            for h in range(1, max_cells // w + 1)]


def validate_coverage(rows: list[Trace], max_cells: int) -> None:
    expected = [(w, h, code) for w, h in domain(max_cells)
                for code in range(3 ** (w*h))]
    require([row.key for row in rows] == expected, "coverage",
            "configurations are missing, duplicated, reordered, truncated, or outside the domain")


def decode_scalar(code: int, area: int) -> tuple[int, ...]:
    cells = []
    for _ in range(area):
        code, digit = divmod(code, 3)
        cells.append(digit)
    require(code == 0, "code-range", "state code exceeds the finite torus")
    return tuple(cells)


def encode_scalar(cells: tuple[int, ...]) -> int:
    code = 0
    for digit in reversed(cells):
        code = 3*code + digit
    return code


def scalar_phase(cells: tuple[int, ...], w: int, h: int,
                 species: int) -> tuple[tuple[int, ...], int]:
    """Independent snapshot implementation, with no NumPy/model helper calls."""
    movers = []
    for source, cell in enumerate(cells):
        if cell != species:
            continue
        x, y = source % w, source // w
        target = y*w + (x+1) % w if species == EAST else ((y+1) % h)*w + x
        if cells[target] == 0:
            movers.append((source, target))
    result = list(cells)
    for source, _ in movers:
        result[source] = 0
    for _, target in movers:
        result[target] = species
    return tuple(result), len(movers)


def scalar_round(cells: tuple[int, ...], w: int, h: int):
    east, em = scalar_phase(cells, w, h, EAST)
    after, nm = scalar_phase(east, w, h, NORTH)
    return east, after, em, nm


def static_rules(cells: tuple[int, ...], w: int, h: int) -> tuple[bool, ...]:
    east = [i for i, cell in enumerate(cells) if cell == EAST]
    north = [i for i, cell in enumerate(cells) if cell == NORTH]
    g = gcd(w, h)
    phase = lambda i: (i % w + i // w) % g
    return (
        all(cells[(i // w)*w + (i % w + 1) % w] != EAST for i in east),
        all(cells[((i // w + 1) % h)*w + i % w] != NORTH for i in north),
        all(phase(n) != phase(e) for e in east for n in north),
        all(phase(n) != (phase(e)+1) % g for e in east for n in north),
    )


def orbit_oracle(initial: tuple[int, ...], w: int, h: int) -> dict:
    """Follow actual states to blockage or repetition; no lcm/static shortcut."""
    seen: dict[tuple[int, ...], int] = {}
    current, time = initial, 0
    population = initial.count(EAST), initial.count(NORTH)
    while current not in seen:
        require(time < 3 ** (w*h), "oracle-orbit", "orbit exceeded its finite state space")
        seen[current] = time
        _, after, em, nm = scalar_round(current, w, h)
        if (em, nm) != population:
            return {"perpetual": False, "first_blocked": time,
                    "visited": len(seen), "cycle_start": None, "period": None}
        current, time = after, time + 1
    return {"perpetual": True, "first_blocked": None, "visited": len(seen),
            "cycle_start": seen[current], "period": time - seen[current]}


def rigid_state(initial: tuple[int, ...], w: int, h: int,
                east_time: int, north_time: int) -> tuple[int, ...]:
    result = [0] * (w*h)
    for i, cell in enumerate(initial):
        if cell == 0:
            continue
        x, y = i % w, i // w
        target = (y*w + (x+east_time) % w if cell == EAST
                  else ((y+north_time) % h)*w + x)
        require(result[target] == 0, "rigid-overlap", "rigidly translated cars overlap")
        result[target] = cell
    return tuple(result)


def validate_shape(row: Trace) -> None:
    w, h, period = row.width, row.height, row.period
    require(w > 0 and h > 0, "dimensions", f"{row.key}: dimensions must be positive")
    require(period == lcm(w, h), "period", f"{row.key}: incorrect lcm")
    require(all(flag in (0, 1) for flag in
                (row.static_free, row.all_move_window, *row.all_move_flags)),
            "flags", f"{row.key}: predicates must be Boolean")
    require(len(row.state_codes) == period + 1 and
            all(len(values) == period for values in
                (row.east_codes, row.east_moves, row.north_moves, row.all_move_flags)),
            "trace-length", f"{row.key}: incomplete first-lcm trace or closing edge")
    require(0 <= row.first_blocked <= period, "first-blocked",
            f"{row.key}: first blocked round must be in [0,lcm]")
    require(all(0 <= code < 3 ** (w*h) for code in
                (row.input_code, *row.state_codes, *row.east_codes)),
            "code-range", f"{row.key}: state code is outside the torus state space")
    require(row.state_codes[0] == row.input_code, "initial-state",
            f"{row.key}: the trace does not begin at its declared initial state")


def validate_trace(row: Trace) -> dict[str, int]:
    validate_shape(row)
    w, h, period = row.width, row.height, row.period
    initial = decode_scalar(row.input_code, w*h)
    require(row.static_free == int(all(static_rules(initial, w, h))), "static-mismatch",
            f"{row.key}: actual Lean StaticFree differs from independent four-rule evaluation")
    population = initial.count(EAST), initial.count(NORTH)
    current, prefix_moves = initial, True
    expected_flags = []
    rigid_full, rigid_east = 0, 0
    for time in range(period):
        if prefix_moves:
            require(current == rigid_state(initial, w, h, time, time), "rigid-full",
                    f"{row.key} at t={time}: a fully moving prefix is not rigid")
            rigid_full += 1
        east, after, em, nm = scalar_round(current, w, h)
        require(row.state_codes[time] == encode_scalar(current) and
                row.east_codes[time] == encode_scalar(east) and
                row.state_codes[time+1] == encode_scalar(after), "phase-mismatch",
                f"{row.key} at t={time}: exported east/then-north trace differs from scalar oracle")
        require((row.east_moves[time], row.north_moves[time]) == (em, nm),
                "movement-count", f"{row.key} at t={time}: separate phase move counts differ")
        require((after.count(EAST), after.count(NORTH)) == population, "conservation",
                f"{row.key} at t={time}: species counts changed")
        flag = int((em, nm) == population)
        require(row.all_move_flags[time] == flag, "all-move",
                f"{row.key} at t={time}: actual Lean AllMove differs from observed motion")
        if prefix_moves and em == population[0]:
            require(east == rigid_state(initial, w, h, time+1, time), "rigid-east",
                    f"{row.key} at t={time}: the east phase of a moving prefix is not rigid")
            rigid_east += 1
        expected_flags.append(flag)
        prefix_moves = prefix_moves and bool(flag)
        current = after
    expected_window = int(all(expected_flags))
    expected_first = next((i for i, flag in enumerate(expected_flags) if not flag), period)
    require(row.all_move_window == expected_window, "window",
            f"{row.key}: the full first-lcm movement window was not checked")
    require(row.first_blocked == expected_first, "first-blocked",
            f"{row.key}: incorrect earliest blocked round or lcm sentinel")
    oracle = orbit_oracle(initial, w, h)
    require(row.all_move_window == int(oracle["perpetual"]), "oracle-classification",
            f"{row.key}: finite window differs from independent from-time-zero orbit oracle")
    require(row.first_blocked == (period if oracle["perpetual"] else oracle["first_blocked"]),
            "oracle-first-blocked", f"{row.key}: first blocked round differs from orbit oracle")
    require(row.static_free == row.all_move_window, "lemma-r",
            f"{row.key}: StaticFree and the complete moving window disagree")
    if expected_window:
        require(current == initial == rigid_state(initial, w, h, period, period), "closure",
                f"{row.key}: the final lcm edge does not close the initial state")
        require(oracle["cycle_start"] == 0 and period % oracle["period"] == 0,
                "orbit-period", f"{row.key}: first-return period does not divide lcm")
        rigid_full += 1
    return {"rigid_full_snapshots": rigid_full, "rigid_east_snapshots": rigid_east,
            "oracle_visited_states": oracle["visited"], "free_from_time_zero": expected_window}


def compare_production_kernel(rows: list[Trace]) -> None:
    """Third implementation: replay the production NumPy kernel as a batch."""
    w, h, period = rows[0].width, rows[0].height, rows[0].period
    current = decode(np.asarray([row.input_code for row in rows], dtype=np.int64), h, w)
    states = np.asarray([row.state_codes for row in rows], dtype=np.int64)
    east_codes = np.asarray([row.east_codes for row in rows], dtype=np.int64)
    east_moves = np.asarray([row.east_moves for row in rows], dtype=np.int64)
    north_moves = np.asarray([row.north_moves for row in rows], dtype=np.int64)
    for time in range(period):
        east, em = half_step(current, EAST, CLASSIC)
        after, nm = half_step(east, NORTH, CLASSIC)
        require(np.array_equal(encode(current), states[:, time]) and
                np.array_equal(encode(east), east_codes[:, time]) and
                np.array_equal(encode(after), states[:, time+1]), "production-phase",
                f"{(w, h)} at t={time}: actual Lean trace differs from production NumPy kernel")
        require(np.array_equal(em, east_moves[:, time]) and
                np.array_equal(nm, north_moves[:, time]), "production-moves",
                f"{(w, h)} at t={time}: actual Lean move counts differ from production kernel")
        current = after


def check_output(output: str, max_cells: int) -> tuple[list[Trace], list[dict[str, int]]]:
    rows = parse_rows(output)
    validate_coverage(rows, max_cells)
    scope, offset = [], 0
    for w, h in domain(max_cells):
        count = 3 ** (w*h)
        rectangle = rows[offset:offset+count]
        counters = {"rigid_full_snapshots": 0, "rigid_east_snapshots": 0,
                    "oracle_visited_states": 0, "free_from_time_zero": 0}
        for row in rectangle:
            for name, value in validate_trace(row).items():
                counters[name] += value
        compare_production_kernel(rectangle)
        scope.append({"width": w, "height": h, "states": count, "period": lcm(w, h),
                      "transition_rows": count*lcm(w, h), **counters})
        offset += count
    require(offset == len(rows), "coverage", "not all exported rows were consumed")
    return rows, scope


def fixture(w: int, h: int, initial: tuple[int, ...]) -> Trace:
    """Independent fixtures let targeted controls run even with a smaller domain."""
    require(len(initial) == w*h, "fixture", "incorrect fixture dimensions")
    period = lcm(w, h)
    states, east_codes, east_moves, north_moves, flags = [encode_scalar(initial)], [], [], [], []
    population = initial.count(EAST), initial.count(NORTH)
    current = initial
    for _ in range(period):
        east, current, em, nm = scalar_round(current, w, h)
        east_codes.append(encode_scalar(east))
        states.append(encode_scalar(current))
        east_moves.append(em)
        north_moves.append(nm)
        flags.append(int((em, nm) == population))
    return Trace(w, h, states[0], period, int(all(static_rules(initial, w, h))),
                 int(all(flags)), next((i for i, flag in enumerate(flags) if not flag), period),
                 tuple(states), tuple(east_codes), tuple(east_moves), tuple(north_moves), tuple(flags))


def negative_controls(rows: list[Trace], max_cells: int) -> dict:
    observed = {row.key: row for row in rows}
    cases = {
        "last_round": fixture(2, 2, (1, 0, 2, 0)),
        "class_zero": fixture(3, 3, (1, 0, 0, 0, 0, 0, 0, 2, 0)),
        "transient": fixture(4, 1, (1, 1, 0, 0)),
        "fixed_jam": fixture(1, 1, (1,)),
    }
    cases = {label: observed.get(row.key, row) for label, row in cases.items()}
    for row in cases.values():
        validate_trace(row)
    last, zero, transient, jam = (cases[label] for label in
                                   ("last_round", "class_zero", "transient", "fixed_jam"))
    require(last.first_blocked == last.period-1 and last.all_move_flags[0] == 1,
            "control-premise", "last-round fixture does not isolate the final window round")
    zero_cells = decode_scalar(zero.input_code, 9)
    require(static_rules(zero_cells, 3, 3) == (True, True, False, True) and
            static_rules(decode_scalar(last.input_code, 4), 2, 2) == (True, True, True, False),
            "control-premise", "cross-species controls do not isolate the two phase exclusions")
    transient_initial = decode_scalar(transient.input_code, 4)
    transient_after = decode_scalar(transient.state_codes[1], 4)
    require(not orbit_oracle(transient_initial, 4, 1)["perpetual"] and
            orbit_oracle(transient_after, 4, 1)["perpetual"], "control-premise",
            "transient fixture does not distinguish eventual from perpetual free flow")
    require(len(set(jam.state_codes)) == 1 and jam.all_move_window == 0,
            "control-premise", "fixed occupancy fixture is not a blocked fixed point")
    north_first, pre_north_moves = scalar_phase(zero_cells, 3, 3, NORTH)
    reversed_after, _ = scalar_phase(north_first, 3, 3, EAST)
    require(pre_north_moves == 1 and zero.north_moves[0] == 0, "control-premise",
            "north eligibility fixture does not distinguish pre-east from post-east")
    swapped = replace(zero,
                      east_codes=(encode_scalar(north_first), *zero.east_codes[1:]),
                      state_codes=(zero.state_codes[0], encode_scalar(reversed_after),
                                   *zero.state_codes[2:]))
    checks = [
        ("truncated-domain", "coverage", lambda: validate_coverage(rows[:-1], max_cells)),
        ("duplicate-configuration", "coverage",
         lambda: validate_coverage([rows[0], *rows], max_cells)),
        ("reordered-configurations", "coverage",
         lambda: validate_coverage([rows[1], rows[0], *rows[2:]], max_cells)),
        ("malformed-row", "malformed-row", lambda: parse_rows(rows[0].tsv() + "\textra")),
        ("out-of-range-state", "code-range",
         lambda: validate_trace(replace(jam, state_codes=(3, *jam.state_codes[1:])))),
        ("nonboolean-predicate", "flags", lambda: validate_trace(replace(jam, static_free=2))),
        ("wrong-lcm", "period", lambda: validate_trace(replace(last, period=last.period+1))),
        ("truncated-phase-trace", "trace-length",
         lambda: validate_trace(replace(last, east_codes=last.east_codes[:-1]))),
        ("north-before-east", "phase-mismatch", lambda: validate_trace(swapped)),
        ("pre-east-north-eligibility", "movement-count",
         lambda: validate_trace(replace(zero, north_moves=(pre_north_moves, *zero.north_moves[1:])))),
        ("omitted-final-window-check", "window",
         lambda: validate_trace(replace(last, all_move_window=1, first_blocked=last.period))),
        ("eventual-free-as-perpetual", "window",
         lambda: validate_trace(replace(transient, all_move_window=1, first_blocked=transient.period))),
        ("omitted-class-zero", "static-mismatch", lambda: validate_trace(replace(zero, static_free=1))),
        ("omitted-class-one", "static-mismatch", lambda: validate_trace(replace(last, static_free=1))),
        ("fixed-occupancy-as-free", "window",
         lambda: validate_trace(replace(jam, all_move_window=1, first_blocked=jam.period))),
    ]
    rejected = []
    for label, reason, run in checks:
        try:
            run()
        except FreeFlowError as error:
            require(error.reason == reason, "negative-control",
                    f"{label}: rejected for {error.reason}, expected {reason}")
            rejected.append({"name": label, "rejected_as": error.reason})
        else:
            raise FreeFlowError("negative-control", f"{label}: mutation was accepted")
    return {"rejected": rejected, "boundary_cases": {
        label: {"key": row.key, "period": row.period, "first_blocked": row.first_blocked,
                "actual_Lean_row": row.key in observed} for label, row in cases.items()}}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def source_manifest() -> dict[str, str]:
    # Audit imports umbrella BML and G1Export; include their local closure too.
    paths = [
        ROOT / "scripts/check_freeflow.py", ROOT / "bml/model.py", ROOT / "bml/exhaustive.py",
        ROOT / "requirements-dev.txt", LEAN / "FreeFlowExport.lean", LEAN / "FreeFlowAudit.lean",
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
    parser.add_argument("--max-cells", type=int, default=9)
    parser.add_argument("--binary", type=Path, default=LEAN / ".lake/build/bin/freeflow_export")
    parser.add_argument("--report", type=Path)
    parser.add_argument("--rows", type=Path, help="preserve actual Lean predicate decisions and traces")
    args = parser.parse_args()
    if not 1 <= args.max_cells <= 9:
        parser.error("--max-cells must be between 1 and 9")
    if args.report and args.rows and args.report.resolve() == args.rows.resolve():
        parser.error("--report and --rows must be distinct paths")
    started = time.perf_counter()
    sources = source_manifest()
    report = {
        "schema": "bml.freeflow-replay.v1", "status": "running", "rule": CLASSIC,
        "functions": ["BML.StaticFree", "BML.AllMove", "BML.halfStep", "BML.torusStep"],
        "started_at": datetime.now(timezone.utc).isoformat(), "revision": revision(),
        "source_sha256": sources,
        "source_manifest_sha256": sha256(json.dumps(sources, sort_keys=True).encode()),
        "runtime": {"python": platform.python_version(), "numpy": np.__version__},
        "lean_toolchain": (LEAN / "lean-toolchain").read_text().strip(),
        "columns": COLUMNS, "max_cells": args.max_cells,
        "scope": (
            "Every ternary configuration on every positive ordered rectangle with width*height "
            "at most max_cells. Actual Lean StaticFree and AllMove decisions, all east phases "
            "and full rounds t<lcm, separate movement counts, earliest blockage, rigid moving "
            "prefixes, and free-flow closing edges are replayed against an independent scalar "
            "kernel and the production NumPy CLASSIC kernel. An independent orbit-following "
            "oracle checks perpetual speed one from time zero, without assuming the lcm bound "
            "or using the eventual-free-flow classifier. Finite acceptance is separate from "
            "the universal Lean theorem and its axiom audit."
        ),
    }
    try:
        binary = args.binary.resolve(strict=True)
        binary_digest = sha256(binary.read_bytes())
        command = [str(binary), "--max-cells", str(args.max_cells)]
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                                check=False, timeout=600)
        report["exporter"] = {"argv": command, "exit_code": result.returncode,
                              "executable_sha256": binary_digest}
        if args.rows:
            args.rows.parent.mkdir(parents=True, exist_ok=True)
            args.rows.write_text(result.stdout)
        require(result.returncode == 0 and not result.stderr.strip(), "exporter",
                f"Lean free-flow exporter failed: {result.stderr.strip()}")
        rows, rectangles = check_output(result.stdout, args.max_cells)
        report["rows_sha256"] = sha256(result.stdout.encode())
        report["state_rows"] = len(rows)
        report["transition_rows"] = sum(rectangle["transition_rows"] for rectangle in rectangles)
        report["full_state_snapshots"] = report["transition_rows"] + len(rows)
        for name in ("rigid_full_snapshots", "rigid_east_snapshots",
                     "oracle_visited_states", "free_from_time_zero"):
            report[name] = sum(rectangle[name] for rectangle in rectangles)
        report["rectangles"] = rectangles
        report["singleton_side_rectangles"] = sum(
            rectangle["width"] == 1 or rectangle["height"] == 1 for rectangle in rectangles)
        controls = negative_controls(rows, args.max_cells)
        report["rejected_mutations"] = controls["rejected"]
        report["boundary_cases"] = controls["boundary_cases"]
        require(source_manifest() == sources, "source-drift", "free-flow sources changed during acceptance")
        require(sha256(binary.read_bytes()) == binary_digest, "source-drift",
                "free-flow exporter changed during acceptance")
        report["revision_end"] = revision()
        require(report["revision_end"] == report["revision"], "source-drift",
                "repository revision changed during acceptance")
        report["status"] = "passed"
        print(f"PASS: {len(rows)} actual Lean initial-state rows on {len(rectangles)} rectangles, "
              f"{report['transition_rows']} full transitions, {report['free_from_time_zero']} "
              f"free from time zero; {len(report['rejected_mutations'])} negative controls rejected.")
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        if isinstance(error, FreeFlowError):
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
