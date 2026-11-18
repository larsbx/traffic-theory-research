#!/usr/bin/env python3
"""Finite TRAIN low-density flow certificates from actual Quint transitions.

Enumerates all legal N x N boards with 2*population < N for N=1..5 by occupied
position combinations and species products: 1+1+19+33+1251 = 1305 boards. The
closed functional graphs come from Quint's full-step output, not a replacement
simulator. Python TRAIN independently checks every row. Target orbit discovery
uses the existing Python kernel, then every edge and return is checked against
actual Quint. All claims here are finite; the all-size theorem belongs to Lean.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
from fractions import Fraction
import hashlib
from itertools import combinations, product
import json
from math import comb
import os
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT))

from train_evaluate import DEFAULT_CLI, evaluate_rows  # noqa: E402
from train_check import python_rows  # noqa: E402

MAX_SIDE = 5
SEED = 20261118
EXPECTED_COUNTS = [1, 1, 19, 33, 1251]
EXPECTED_TESTS = [
    "completeCycleClockTest", "wrongHalfStepClockRejectedTest", "wholeTrainQueueClockTest",
    "northReadsEastResultTest", "blockedNorthDiagonalFallsTest", "emptyGapPairCanDisappearTest",
    "fixedOccupancyIsNotFullMovementTest", "rotatingRingIsFullMovementTest",
    "emptyOrbitIsVacuouslyFullMovementTest", "rectangularLowDensityCounterexampleTest",
]
EXPECTED_CONTROLS = [
    "wrong-half-step-diagonal-clock", "independent-north-count-used-for-cycle",
    "fixed-occupancy-implies-free", "rectangular-square-theorem-overreach",
    "truncated-orbit-closure", "incomplete-square-domain",
]
# Labels, dimensions, initial ternary code, expected eventual full movement.
TARGETS = [
    ("square6-delayed-pair", 6, 6, 7, True),
    ("square7-blocked-train", 7, 7, 22, True),
    ("square8-wrapped-train", 8, 8, 7 + 3**7, True),
    ("north-phase-after-east", 5, 5, 1 + 2*3**21, True),
    ("equality-boundary-gap", 4, 4, 3**12 + 2*3**13, True),
    ("rectangular-5x7-counterexample", 5, 7, 7, False),
    ("fixed-occupancy-jam", 2, 2, 52, False),
    ("fixed-occupancy-rotating-ring", 1, 1, 1, True),
]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def counts(code: int, size: int) -> tuple[int, int]:
    require(type(code) is int and code >= 0, "illegal board code")
    east = north = 0
    for _ in range(size):
        digit = code % 3
        east += digit == 1
        north += digit == 2
        code //= 3
    require(code == 0, "board code exceeds dimensions")
    return east, north


def low_density_codes(side: int) -> list[int]:
    """Generate the sparse domain directly; never scan all 3^(side*side) boards."""
    require(type(side) is int and side > 0, "side must be positive")
    weights = [3**i for i in range(side * side)]
    result = []
    for occupied in range((side - 1) // 2 + 1):
        for positions in combinations(range(side * side), occupied):
            for species in product((1, 2), repeat=occupied):
                result.append(sum(cell * weights[position] for position, cell in zip(positions, species, strict=True)))
    result.sort()
    expected = sum(comb(side*side, occupied) * 2**occupied for occupied in range((side-1)//2 + 1))
    require(len(result) == len(set(result)) == expected, "sparse domain has duplicates or omissions")
    return result


def validate_row(row: list[int], width: int, height: int) -> None:
    require(isinstance(row, list) and len(row) == 10 and
            all(type(value) is int and value >= 0 for value in row), "malformed flow row")
    require(row[:2] == [width, height], "wrong row dimensions")
    east, north = counts(row[2], width*height)
    for output in row[3:6]:
        require(counts(output, width*height) == (east, north), "flow row lost a species")
    require(row[6] <= east and row[7] <= north and row[8] <= north, "invalid movement count")
    require(row[9] == int(row[6] == row[7] == 0), "incorrect stuck bit")


def full_movement(row: list[int]) -> bool:
    east, north = counts(row[2], row[0]*row[1])
    # northMoves at column7 is an independent input phase; column8 is the
    # north movement AFTER east and is the count relevant to a full cycle.
    return row[6] == east and row[8] == north


def analyze_graph(side: int, rows: list[list[int]]) -> dict:
    expected = low_density_codes(side)
    require([row[2] for row in rows] == expected, "incomplete or reordered closed square domain")
    table = {row[2]: row for row in rows}
    for row in rows:
        validate_row(row, side, side)
        require(2*sum(counts(row[2], side*side)) < side, "board violates strict square density bound")
        require(row[5] in table, "successor escapes the supposedly closed square domain")
    # Each assigned node carries its canonical cycle root and distance to it.
    assigned: dict[int, tuple[int, int]] = {}
    cycles: dict[int, list[int]] = {}
    for start in expected:
        if start in assigned:
            continue
        positions: dict[int, int] = {}
        path = []
        current = start
        while current not in assigned and current not in positions:
            positions[current] = len(path)
            path.append(current)
            current = table[current][5]
        if current in positions:
            offset = positions[current]
            cycle = path[offset:]
            root = min(cycle)
            first = cycle.index(root)
            cycle = cycle[first:] + cycle[:first]
            require(all(full_movement(table[code]) for code in cycle),
                    f"terminal cycle is not full movement on square{side}: {cycle}")
            cycles[root] = cycle
            for code in cycle:
                assigned[code] = (root, 0)
            prefix = path[:offset]
        else:
            prefix = path
        for code in reversed(prefix):
            root, distance = assigned[table[code][5]]
            assigned[code] = (root, distance + 1)
    require(len(assigned) == len(rows), "not every square board was classified")
    for code, (root, distance) in assigned.items():
        successor_root, successor_distance = assigned[table[code][5]]
        require(root == successor_root and successor_distance == max(0, distance-1),
                "invalid graph distance certificate")
    return {
        "side": side, "max_population": (side-1)//2, "states": len(rows), "closed": True,
        "cycle_count": len(cycles), "cycle_states": sum(map(len, cycles.values())),
        "maximum_transient": max(distance for _, distance in assigned.values()),
        "all_terminal_cycles_full_movement": True,
        "cycles": [{"root": root, "codes": cycle, "period": len(cycle),
                    "population": sum(counts(root, side*side)),
                    "full_step_mover_totals": [table[code][6] + table[code][8] for code in cycle]}
                   for root, cycle in sorted(cycles.items())],
        "distance_certificate": [[code, *assigned[code]] for code in expected],
    }


def corrected_support(side: int, code: int, time: int) -> list[int]:
    support = set()
    for i in range(side*side):
        if code % 3:
            support.add((i % side + i // side - time) % side)
        code //= 3
    return sorted(support)


def orbit_certificate(label: str, width: int, height: int, rows: list[list[int]], transient: int) -> dict:
    population = sum(counts(rows[0][2], width*height))
    flags = [full_movement(row) for row in rows]
    cycle = rows[transient:]
    moved = sum(row[6] + row[8] for row in cycle)
    velocity = Fraction(moved, population * len(cycle)) if population else Fraction(1)
    eventual = all(flags[transient:])
    tail = max((i+1 for i, flag in enumerate(flags) if not flag), default=0) if eventual else None
    result = {
        "label": label, "width": width, "height": height, "initial_code": rows[0][2],
        "population": population, "rows": rows, "transient_length": transient,
        "period": len(cycle), "repeated_code": rows[-1][5],
        "full_movement_by_step": flags, "eventually_full_movement": eventual,
        "first_permanent_full_movement_step": tail,
        "cycle_total_moves": moved,
        "cycle_velocity_numerator": velocity.numerator, "cycle_velocity_denominator": velocity.denominator,
        "satisfies_square_hypothesis": width == height and 2*population < width,
        "satisfies_2m_lt_min_rectangle_bound": 2*population < min(width, height),
    }
    if width == height:
        result["corrected_diagonal_supports"] = [
            corrected_support(width, row[2], time) for time, row in enumerate(rows)
        ]
    return result


def validate_certificate(certificate: dict) -> None:
    width, height = certificate["width"], certificate["height"]
    rows = certificate["rows"]
    require(rows and type(width) is int and type(height) is int and width > 0 and height > 0,
            "empty or zero-dimensional orbit certificate")
    for row in rows:
        validate_row(row, width, height)
    codes = [row[2] for row in rows]
    require(len(codes) == len(set(codes)), "orbit repeats before its stated return")
    require(certificate["initial_code"] == codes[0], "wrong initial orbit code")
    transient = certificate["transient_length"]
    require(type(transient) is int and 0 <= transient < len(rows), "invalid transient length")
    require(certificate["period"] == len(rows)-transient, "invalid orbit period")
    require(all(row[5] == codes[i+1] for i, row in enumerate(rows[:-1])), "missing orbit edge")
    require(rows[-1][5] == codes[transient] == certificate["repeated_code"], "orbit does not close")
    expected = orbit_certificate(certificate["label"], width, height, rows, transient)
    for field in expected:
        require(certificate.get(field) == expected[field], f"incorrect orbit certificate field: {field}")


def discover_and_replay_targets(quint_cli: str, square_tables: dict[int, dict]) -> list[dict]:
    certificates = []
    for label, width, height, initial, expected_flow in TARGETS:
        seen = {}
        codes = []
        current = initial
        # Discovery uses the existing Python kernel, never hand-written traffic.
        # No discovery edge is accepted until Quint replays it below.
        for _ in range(20_000):
            if current in seen:
                break
            seen[current] = len(codes)
            codes.append(current)
            current = python_rows(width, height, [current])[0][5]
        else:
            raise AssertionError(f"target orbit exceeds discovery budget: {label}")
        cached = square_tables.get(width) if width == height else None
        if cached is not None and all(code in cached for code in codes):
            actual = [cached[code] for code in codes]
        else:
            actual = evaluate_rows(width, height, codes, quint_cli)
        require(actual == python_rows(width, height, codes), f"target Quint/Python mismatch: {label}")
        certificate = orbit_certificate(label, width, height, actual, seen[current])
        validate_certificate(certificate)
        require(certificate["eventually_full_movement"] == expected_flow, f"wrong target outcome: {label}")
        certificates.append(certificate)
    return certificates


def run_quint_tests(quint_cli: str) -> dict:
    path = HERE / "train_flow_tests.qnt"
    for command in ("parse", "typecheck"):
        subprocess.run([quint_cli, command, str(path)], check=True, capture_output=True, text=True)
    with tempfile.TemporaryDirectory(prefix="train-flow-tests-") as directory:
        output = Path(directory) / "tests.json"
        subprocess.run([quint_cli, "test", str(path), "--backend=typescript", "--max-samples=1",
                        f"--seed={SEED}", f"--out={output}"], check=True)
        result = json.loads(output.read_text())
    passed = result.get("passed")
    require(isinstance(passed, list) and all(type(name) is str for name in passed), "missing flow test inventory")
    require(len(passed) == len(EXPECTED_TESTS) and set(passed) == set(EXPECTED_TESTS), "wrong flow test inventory")
    require(result.get("failed") == [] and result.get("ignored") == [], "failed or ignored flow tests")
    return {"module": path.name, "passed": passed, "count": len(passed), "failed": [], "ignored": []}


def wrong_clock_control(quint_cli: str) -> dict:
    source = (HERE / "train_flow_tests.qnt").read_text()
    altered = source.replace("diagonal(n, i) + n - time % n", "diagonal(n, i) + n - (2*time) % n")
    require(altered != source, "clock mutation did not alter the specification")
    with tempfile.TemporaryDirectory(prefix="train-flow-clock-") as directory:
        folder = Path(directory)
        (folder / "Train.qnt").write_bytes((HERE / "Train.qnt").read_bytes())
        mutant = folder / "train_flow_tests.qnt"
        mutant.write_text(altered)
        output = folder / "result.json"
        result = subprocess.run([
            quint_cli, "test", str(mutant), "--backend=typescript", "--max-samples=1",
            f"--seed={SEED}", f"--out={output}",
        ], text=True, capture_output=True, check=False)
        require(output.exists(), "clock mutant failed without a structured test result")
        inventory = json.loads(output.read_text())
        require(result.returncode != 0 and "completeCycleClockTest" in inventory.get("failed", []),
                "wrong half-step clock survived its actual Quint test")
        require(inventory.get("ignored") == [], "clock mutant skipped tests")
    return {"name": EXPECTED_CONTROLS[0], "reason": "actual-Quint-test-failure",
            "failed_tests": inventory["failed"], "mutant_source_sha256": hashlib.sha256(altered.encode()).hexdigest()}


def adversarial_controls(quint_cli: str, certificates: list[dict], square_rows: dict[int, list]) -> list[dict]:
    rejected = [wrong_clock_control(quint_cli)]
    by_label = {certificate["label"]: certificate for certificate in certificates}

    def reject(name: str, altered: dict) -> None:
        try:
            validate_certificate(altered)
        except AssertionError as exc:
            rejected.append({"name": name, "reason": "certificate-rejected", "detail": str(exc)})
        else:
            raise AssertionError(f"adversarial orbit certificate survived: {name}")

    wrong_count = deepcopy(by_label["north-phase-after-east"])
    wrong_count["full_movement_by_step"] = [
        row[6]+row[7] == wrong_count["population"] for row in wrong_count["rows"]
    ]
    require(wrong_count["full_movement_by_step"] != by_label["north-phase-after-east"]["full_movement_by_step"],
            "north phase-count mutation is vacuous")
    reject(EXPECTED_CONTROLS[1], wrong_count)
    fixed_free = deepcopy(by_label["fixed-occupancy-jam"])
    fixed_free["full_movement_by_step"] = [True]
    fixed_free["eventually_full_movement"] = True
    reject(EXPECTED_CONTROLS[2], fixed_free)
    rectangle_free = deepcopy(by_label["rectangular-5x7-counterexample"])
    rectangle_free["eventually_full_movement"] = True
    reject(EXPECTED_CONTROLS[3], rectangle_free)
    truncated = deepcopy(by_label["rectangular-5x7-counterexample"])
    truncated["rows"] = truncated["rows"][:-1]
    truncated["period"] -= 1
    reject(EXPECTED_CONTROLS[4], truncated)
    try:
        analyze_graph(3, square_rows[3][:-1])
    except AssertionError as exc:
        rejected.append({"name": EXPECTED_CONTROLS[5], "reason": "incomplete-domain-rejected", "detail": str(exc)})
    else:
        raise AssertionError("missing square-domain row was accepted")
    require([item["name"] for item in rejected] == EXPECTED_CONTROLS, "missing flow adversarial control")
    return rejected


def source_hashes() -> dict[str, str]:
    paths = ["formal/quint/Train.qnt", "formal/quint/train_evaluate.py", "formal/quint/train_check.py",
             "formal/quint/train_flow_tests.qnt", "formal/quint/train_flow_check.py",
             "formal/quint/package.json", "formal/quint/package-lock.json", "bml/model.py"]
    return {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in paths}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rows", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--quint-cli", default=os.environ.get("QUINT_CLI", DEFAULT_CLI))
    args = parser.parse_args()
    require(args.rows.resolve() != args.report.resolve(), "table and report must be different files")
    args.rows.unlink(missing_ok=True)
    args.report.unlink(missing_ok=True)
    sources = source_hashes()
    version = subprocess.check_output([args.quint_cli, "--version"], text=True).strip()
    require(version == "0.33.1", f"expected Quint0.33.1, got {version!r}")
    tests = run_quint_tests(args.quint_cli)
    all_rows = []
    square_rows = {}
    graphs = []
    for side in range(1, MAX_SIDE+1):
        codes = low_density_codes(side)
        require(len(codes) == EXPECTED_COUNTS[side-1], "wrong low-density square count")
        rows = evaluate_rows(side, side, codes, args.quint_cli)
        require(rows == python_rows(side, side, codes), f"Quint/Python low-density mismatch on square{side}")
        graph = analyze_graph(side, rows)
        graphs.append(graph)
        square_rows[side] = rows
        all_rows.extend(rows)
        print(f"TRAIN flow {side}x{side}: {len(rows)} boards, {graph['cycle_count']} full-movement cycles, "
              f"maximum transient {graph['maximum_transient']}", flush=True)
    require(len(all_rows) == 1305, "wrong exhaustive low-density table length")
    tables = {side: {row[2]: row for row in rows} for side, rows in square_rows.items()}
    targets = discover_and_replay_targets(args.quint_cli, tables)
    controls = adversarial_controls(args.quint_cli, targets, square_rows)
    require(source_hashes() == sources, "flow acceptance sources changed during execution")
    table = ("\n".join("\t".join(map(str, row)) for row in all_rows) + "\n").encode()
    report = {
        "schema": "train.flow.quint.v1", "status": "passed", "rule": "train",
        "quint_version": version, "backend": "typescript", "seed": SEED,
        "sources_sha256": sources,
        "columns": ["width", "height", "input_code", "east_code", "north_code", "full_code",
                    "east_moves", "north_moves", "cycle_north_moves", "stuck"],
        "domain": {"min_side": 1, "max_side": MAX_SIDE, "condition": "2*population < side",
                   "state_counts": EXPECTED_COUNTS, "total_states": len(all_rows),
                   "generation": "occupied-position combinations times species products; ordered by side then code"},
        "rows_sha256": hashlib.sha256(table).hexdigest(), "graphs": graphs,
        "quint_tests": tests, "target_orbits": targets,
        "target_orbit_rows": sum(len(target["rows"]) for target in targets),
        "rejected_controls": controls,
        "diagonal_clock": "(x+y-completed_full_cycles) mod square_side",
        "scope": "closed finite graphs and explicit repeated orbits; no all-size Quint or source-refinement theorem",
    }
    args.rows.parent.mkdir(parents=True, exist_ok=True)
    args.rows.write_bytes(table)
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "exhaustive_boards": len(all_rows),
                      "rows_sha256": report["rows_sha256"], "quint_tests": tests,
                      "target_orbit_rows": report["target_orbit_rows"], "rejected_controls": controls}, indent=2))


if __name__ == "__main__":
    main()
