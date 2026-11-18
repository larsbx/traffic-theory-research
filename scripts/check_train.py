#!/usr/bin/env python3
"""Build/audit TRAIN proofs and compare actual Lean, Quint, and Python evaluators.

Writes a source-bound acceptance report even when a stage fails. The finite
replay checks are kept separate from the unrestricted Lean threshold and
sparse-square eventual-movement theorems.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
from itertools import combinations, product
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "formal/lean"
QUINT = ROOT / "formal/quint"
COVERAGE = json.loads((ROOT / "formal/train-coverage.json").read_text())
sys.path.insert(0, str(QUINT))
sys.path.insert(0, str(ROOT))

from bml.extremal import train_stuck_with  # noqa: E402
from train_check import encode_board, python_rows  # noqa: E402
from train_flow_check import validate_certificate as validate_flow_certificate  # noqa: E402


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def source_manifest() -> dict[str, str]:
    paths = []
    for path in ROOT.rglob("*"):
        relative = path.relative_to(ROOT)
        if not path.is_file() or any(part in {
            ".git", ".lake", "node_modules", "artifacts", ".artifacts",
            "__pycache__", ".pytest_cache", ".hypothesis",
        } for part in relative.parts):
            continue
        if relative.parts[0] in {"bml", "formal", "scripts", "tests", ".github"} or str(relative) in {
            "requirements.txt", "requirements-dev.txt", "pyproject.toml", "README.md",
        }:
            paths.append(path)
    return {str(p.relative_to(ROOT)): sha256(p.read_bytes()) for p in sorted(paths)}


def revision() -> str | None:
    top = subprocess.run(["git", "rev-parse", "--show-toplevel"], cwd=ROOT,
                         text=True, capture_output=True, check=False)
    if top.returncode or Path(top.stdout.strip()).resolve() != ROOT:
        return None
    return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()


def parse_rows(path: Path, fields: int = 10) -> list[list[int]]:
    rows = []
    for number, line in enumerate(path.read_text().splitlines(), 1):
        parts = line.split("\t")
        require(len(parts) == fields and all(re.fullmatch(r"[0-9]+", p) for p in parts),
                f"{path.name}:{number}: expected {fields} natural-number fields")
        rows.append(list(map(int, parts)))
    return rows


def digit_counts(code: int, size: int) -> Counter:
    counts: Counter = Counter()
    for _ in range(size):
        counts[code % 3] += 1
        code //= 3
    require(code == 0, "board code exceeds its grid")
    return counts


def validate_row(row: list[int]) -> None:
    require(len(row) == 10 and all(type(x) is int and x >= 0 for x in row), "malformed TRAIN row")
    w, h, code, east, north, full, em, nm, cnm, stuck = row
    require(w > 0 and h > 0, "zero-dimensional board")
    counts = digit_counts(code, w*h)
    for after in (east, north, full):
        require(digit_counts(after, w*h) == counts, f"species conservation failed: {row}")
    require(em <= counts[1] and nm <= counts[2] and cnm <= counts[2], f"invalid mover count: {row}")
    require(stuck in (0, 1) and stuck == int(em == nm == 0), f"wrong stuck flag: {row}")
    require(stuck == int(em + cnm == 0), f"successive-phase stuck mismatch: {row}")
    require(not stuck or code == east == north == full, f"stuck occupancy changed: {row}")


def audit_result(output: str) -> dict:
    theorems = {}
    summary = None
    for line in output.splitlines():
        fields = line.split("\t")
        if fields[0] == "AUDIT_THEOREM":
            require(len(fields) == 3 and fields[1] not in theorems, "malformed or duplicate audit theorem")
            theorems[fields[1]] = fields[2].split(",") if fields[2] else []
        elif fields[0] == "AUDIT_SUMMARY":
            require(summary is None, "duplicate audit summary")
            summary = {"declarations": int(fields[1]), "theorem_declarations": int(fields[2])}
    require(summary is not None and len(theorems) == summary["theorem_declarations"], "incomplete proof audit")
    required = COVERAGE["required_theorems"]
    require(len(required) == len(set(required)), "duplicate required theorem")
    require(set(required) <= theorems.keys(), f"missing required theorems: {set(required) - theorems.keys()}")
    axioms = sorted({a for dependencies in theorems.values() for a in dependencies})
    require(set(axioms) <= set(COVERAGE["allowed_axioms"]), "disallowed proof axiom")
    return {**summary, "required_theorems": len(required), "actual_axioms": axioms, "theorems": theorems}


def validate_quint_report(report: dict, sources: dict, rows_path: Path) -> None:
    require(report.get("schema") == "train.quint-replay.v1" and report.get("status") == "passed",
            "Quint acceptance did not pass")
    require(report.get("rule") == "train" and report.get("quint_version") == COVERAGE["quint_version"],
            "Quint ran the wrong rule/version")
    spec = COVERAGE["quint"]
    require(report.get("backend") == spec["backend"] and report.get("seed") == spec["seed"],
            "wrong Quint backend/seed")
    require(report.get("sources_sha256") and all(sources.get(p) == digest
            for p, digest in report["sources_sha256"].items()), "Quint sources differ from gate sources")
    require(report.get("exhaustive_rows_sha256") == sha256(rows_path.read_bytes()), "stale Quint rows")
    require(report.get("columns") == COVERAGE["finite_comparison"]["columns"], "Quint protocol changed")
    suites = report.get("test_suites", {})
    require(set(suites) == set(spec["test_suites"]), "wrong Quint test modules")
    for module, expected in spec["test_suites"].items():
        result = suites[module]
        passed = result.get("passed", [])
        require(len(passed) == len(expected) == result.get("count") and set(passed) == set(expected),
                f"wrong Quint test inventory: {module}")
        require(result.get("failed") == [] and result.get("ignored") == [], f"unpassed tests: {module}")
    require(report.get("deterministic_quint_tests") == sum(map(len, spec["test_suites"].values())),
            "wrong Quint test count")
    mutations = report.get("rejected_mutations", [])
    require([m.get("name") for m in mutations] == spec["required_mutations"], "missing mutation rejection")
    require(all(m.get("reason") in {"cross-language-mismatch", "internal-invariant"} for m in mutations),
            "mutation rejected for an unrelated reason")
    require(mutations[-1]["reason"] == "internal-invariant", "illegal digits were not checked internally")


def compare_exhaustive(lean_rows: list, quint_rows: list, quint_report: dict) -> dict:
    spec = COVERAGE["finite_comparison"]
    rectangles = [(w, h) for w in range(1, spec["max_cells"] + 1)
                  for h in range(1, spec["max_cells"] // w + 1)]
    keys = [[w, h, code] for w, h in rectangles for code in range(3**(w*h))]
    require(len(rectangles) == spec["rectangles"] and len(keys) == spec["boards"], "wrong coverage totals")
    require([row[:3] for row in lean_rows] == keys, "Lean replay incomplete, duplicated, or reordered")
    require([row[:3] for row in quint_rows] == keys, "Quint replay incomplete, duplicated, or reordered")
    require(quint_report.get("max_cells") == spec["max_cells"] and
            quint_report.get("exhaustive_states") == len(keys), "wrong Quint exhaustive scope")
    expected_rectangles = [{"width": w, "height": h, "states": 3**(w*h)} for w, h in rectangles]
    require(quint_report.get("rectangles") == expected_rectangles, "wrong Quint rectangle inventory")
    expected = [row for w, h in rectangles for row in python_rows(w, h, list(range(3**(w*h))))]
    for index, (lean, quint, python) in enumerate(zip(lean_rows, quint_rows, expected, strict=True), 1):
        require(lean == quint == python, f"three-language mismatch at row {index}: {lean}, {quint}, {python}")
        validate_row(lean)
    table = {tuple(row[:3]): row for row in lean_rows}
    require(table[(1, 1, 1)][5:] == [1, 1, 0, 0, 0], "moving singleton mistaken for a jam")
    require(table[(3, 1, 4)][3] == 12 and table[(3, 1, 4)][6] == 2, "queue did not move together")
    require(table[(3, 1, 13)][3] == 13 and table[(3, 1, 13)][6] == 3, "full ring did not rotate")
    return {"status": "passed", "rectangles": rectangles, "boards": len(keys), "fields_per_board": 10,
            "scope": "all positive rectangles with area <=6; exact finite agreement of actual evaluators"}


def compare_constructions(rows: list) -> dict:
    spec = COVERAGE["construction"]
    keys = [[w, h, n] for w in range(spec["min_side"], spec["max_side"] + 1)
            for h in range(spec["min_side"], spec["max_side"] + 1) for n in range(w+h, w*h+1)]
    require(len(keys) == spec["lean_python_boards"] and [row[:3] for row in rows] == keys,
            "construction coverage is incomplete, duplicated, or reordered")
    for row in rows:
        w, h, n, population, code = row[:5]
        board = train_stuck_with(h, w, n)
        expected_code = encode_board(board)
        actual = [w, h, *row[4:]]
        require(population == n == int((board != 0).sum()), f"wrong constructed population: {row[:5]}")
        require(code == expected_code, f"Lean/Python constructor differs: {row[:5]}")
        require(actual == python_rows(w, h, [code])[0], f"constructor dynamics differ: {row[:5]}")
        require(actual[6:] == [0, 0, 0, 1], f"construction is not movement-stuck: {row[:5]}")
        validate_row(actual)
    return {"status": "passed", "boards": len(keys), "min_side": spec["min_side"],
            "max_side": spec["max_side"], "all_populations": "W+H through W*H inclusive"}


def compare_sparse_flow(lean_rows: list, quint_rows: list, flow_report: dict,
                        sources: dict, quint_path: Path) -> dict:
    """Check every sparse row and independently verify the finite graph certificate."""
    spec = COVERAGE["low_density_flow"]
    require(flow_report.get("schema") == "train.flow.quint.v1" and
            flow_report.get("status") == "passed" and flow_report.get("rule") == "train",
            "Quint flow acceptance did not pass")
    require(flow_report.get("quint_version") == COVERAGE["quint_version"] and
            flow_report.get("backend") == COVERAGE["quint"]["backend"] and
            flow_report.get("seed") == COVERAGE["quint"]["seed"], "wrong flow evaluator settings")
    expected_sources = {
        "formal/quint/Train.qnt", "formal/quint/train_evaluate.py", "formal/quint/train_check.py",
        "formal/quint/train_flow_tests.qnt", "formal/quint/train_flow_check.py",
        "formal/quint/package.json", "formal/quint/package-lock.json", "bml/model.py",
    }
    hashes = flow_report.get("sources_sha256", {})
    require(set(hashes) == expected_sources and all(sources.get(p) == digest for p, digest in hashes.items()),
            "flow evidence is not bound to the checked sources")
    require(flow_report.get("columns") == COVERAGE["finite_comparison"]["columns"] and
            flow_report.get("rows_sha256") == sha256(quint_path.read_bytes()), "stale or malformed flow table")
    domain = flow_report.get("domain", {})
    require(all(domain.get(k) == spec[k] for k in ("min_side", "max_side", "condition", "state_counts")) and
            domain.get("total_states") == spec["boards"], "wrong sparse flow domain")
    keys, per_side = [], {}
    for n in range(spec["min_side"], spec["max_side"]+1):
        codes = sorted(sum(sp*3**p for p, sp in zip(positions, species, strict=True))
                       for occupied in range((n-1)//2+1)
                       for positions in combinations(range(n*n), occupied)
                       for species in product((1, 2), repeat=occupied))
        require(len(codes) == len(set(codes)) == spec["state_counts"][n-spec["min_side"]],
                "incorrect sparse domain enumeration")
        per_side[n] = codes
        keys.extend([n, n, code] for code in codes)
    require(len(keys) == spec["boards"] and [r[:3] for r in lean_rows] == keys and
            [r[:3] for r in quint_rows] == keys, "missing, duplicated, or reordered sparse flow rows")
    expected = [r for n, codes in per_side.items() for r in python_rows(n, n, codes)]
    for lean, quint, python in zip(lean_rows, quint_rows, expected, strict=True):
        require(lean == quint == python, f"sparse three-language mismatch: {lean[:3]}")
        validate_row(lean)
    graphs = flow_report.get("graphs", [])
    require([g.get("side") for g in graphs] == list(per_side), "missing sparse functional graph")
    summaries = []
    for graph in graphs:
        n = graph["side"]
        table = {r[2]: r for r in lean_rows if r[0] == n}
        require(graph.get("states") == len(table) and graph.get("closed") is True and
                graph.get("max_population") == (n-1)//2, "incorrect graph domain")
        require(all(r[5] in table for r in table.values()), "sparse graph is not closed")
        cycles = graph.get("cycles", [])
        roots, cycle_members = {}, set()
        for cycle in cycles:
            codes, root = cycle["codes"], cycle["root"]
            require(codes and root == min(codes) == codes[0] and root not in roots,
                    "noncanonical or duplicate terminal cycle")
            require(len(codes) == len(set(codes)) == cycle["period"] and
                    not cycle_members.intersection(codes), "overlapping or repeated cycle")
            require(all(code in table and table[code][5] == successor
                        for code, successor in zip(codes, codes[1:]+codes[:1], strict=True)),
                    "cycle certificate disagrees with actual successors")
            population = sum(digit_counts(root, n*n)[sp] for sp in (1, 2))
            totals = [table[code][6]+table[code][8] for code in codes]
            require(cycle["population"] == population and cycle["full_step_mover_totals"] == totals and
                    all(total == population for total in totals), "terminal cycle has blocked cars")
            roots[root] = set(codes)
            cycle_members.update(codes)
        certificate = graph.get("distance_certificate", [])
        require(all(isinstance(c, list) and len(c) == 3 and all(type(x) is int and x >= 0 for x in c)
                    for c in certificate) and [c[0] for c in certificate] == per_side[n],
                "incomplete graph distance certificate")
        distances = {code: (root, distance) for code, root, distance in certificate}
        for code, (root, distance) in distances.items():
            require(root in roots, "distance certificate names an unknown cycle")
            successor_root, successor_distance = distances[table[code][5]]
            require(root == successor_root and successor_distance == max(0, distance-1) and
                    (distance != 0 or code in roots[root]), "invalid distance to a terminal cycle")
        maximum = max(distance for _, distance in distances.values())
        require(graph.get("maximum_transient") == maximum and graph.get("cycle_count") == len(roots) and
                graph.get("cycle_states") == len(cycle_members) and
                graph.get("all_terminal_cycles_full_movement") is True, "incorrect graph summary")
        summaries.append({key: graph[key] for key in (
            "side", "states", "cycle_count", "cycle_states", "maximum_transient")})
    tests, expected_tests = flow_report.get("quint_tests", {}), spec["quint_test_suite"]
    passed = tests.get("passed", [])
    require(tests.get("module") == expected_tests["module"] and
            len(passed) == tests.get("count") == len(expected_tests["tests"]) and
            set(passed) == set(expected_tests["tests"]) and tests.get("failed") == tests.get("ignored") == [],
            "missing or failed Quint flow test")
    controls = flow_report.get("rejected_controls", [])
    require([c.get("name") for c in controls] == spec["required_controls"], "missing flow negative controls")
    require(controls[0].get("reason") == "actual-Quint-test-failure" and
            "completeCycleClockTest" in controls[0].get("failed_tests", []), "wrong clock mutation survived")
    require(all(c.get("reason") == "certificate-rejected" for c in controls[1:5]) and
            controls[-1].get("reason") == "incomplete-domain-rejected", "wrong negative-control failures")
    return {"status": "passed", "boards": len(keys), "graphs": summaries,
            "quint_tests": tests, "rejected_controls": controls,
            "scope": "complete finite low-density square graphs through side 5; all terminal cycles have full movement"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, default=ROOT / ".artifacts/train-acceptance.json")
    args = parser.parse_args()
    report_path = args.report.resolve()
    artifacts = report_path.parent
    artifacts.mkdir(parents=True, exist_ok=True)
    before = source_manifest()
    report = {"schema": "train.formal.acceptance.v1", "rule": "train", "status": "running",
              "started_at": datetime.now(timezone.utc).isoformat(), "revision": revision(),
              "source_sha256": before,
              "source_manifest_sha256": sha256(json.dumps(before, sort_keys=True).encode()), "steps": []}
    lake = os.environ.get("TRAIN_LAKE", "lake")
    cli = QUINT / "node_modules/.bin/quint"
    executable = LEAN / ".lake/build/bin/train_replay"

    def run(label: str, command: list[str], cwd: Path, output_name: str | None = None) -> str:
        print(f"Checking {label} ...", flush=True)
        start = time.monotonic()
        result = subprocess.run(command, cwd=cwd, text=True, capture_output=True, check=False, timeout=900)
        output = artifacts / (output_name or f"train-{label}.log")
        output.write_text(result.stdout)
        (artifacts / f"train-{label}.stderr.log").write_text(result.stderr)
        report["steps"].append({"name": label, "argv": command, "cwd": str(cwd.relative_to(ROOT)),
                                "exit_code": result.returncode, "seconds": round(time.monotonic()-start, 3)})
        require(result.returncode == 0, f"{label} failed; see {output.name} and stderr log")
        return result.stdout

    try:
        lean_version = run("lean-version", [lake, "env", "lean", "--version"], LEAN).strip()
        quint_version = run("quint-version", [str(cli), "--version"], QUINT).strip()
        node_version = run("node-version", ["node", "--version"], ROOT).strip()
        require(f"version {COVERAGE['lean_version']}," in lean_version, "incorrect Lean version")
        require(quint_version == COVERAGE["quint_version"], "incorrect Quint version")
        report["versions"] = {"lean": lean_version, "quint": quint_version, "node": node_version}
        run("lean-build", [lake, "build", "Train", "train_replay"], LEAN)
        report["lean_audit"] = audit_result(run("lean-audit", [lake, "env", "lean", "TrainAudit.lean"], LEAN))
        lean_path, quint_path = artifacts / "train-lean.tsv", artifacts / "train-quint.tsv"
        quint_report_path = artifacts / "train-quint-replay.json"
        require(report_path != quint_report_path, "acceptance and replay reports must have different paths")
        run("lean-replay", [str(executable), "--max-cells", str(COVERAGE["finite_comparison"]["max_cells"])],
            LEAN, lean_path.name)
        run("quint-replay", [sys.executable, "formal/quint/train_check.py", "--max-cells",
            str(COVERAGE["finite_comparison"]["max_cells"]), "--rows", str(quint_path),
            "--report", str(quint_report_path)], ROOT)
        quint_report = json.loads(quint_report_path.read_text())
        validate_quint_report(quint_report, before, quint_path)
        report["finite_comparison"] = compare_exhaustive(parse_rows(lean_path), parse_rows(quint_path), quint_report)
        report["quint_tests"] = quint_report["test_suites"]
        report["rejected_mutations"] = quint_report["rejected_mutations"]
        constructions_path = artifacts / "train-constructions.tsv"
        run("lean-constructions", [str(executable), "--construct", str(COVERAGE["construction"]["max_side"])],
            LEAN, constructions_path.name)
        construction_rows = parse_rows(constructions_path, 12)
        report["constructions"] = compare_constructions(construction_rows)
        all_constructions = {(r[0], r[1], r[2]): [r[0], r[1], *r[4:]] for r in construction_rows}
        q_construction_keys = []
        for case in quint_report["construction_cases"]:
            w, h = case["width"], case["height"]
            counts, rows = case["car_counts"], case["rows"]
            require(counts == list(range(w+h, w*h+1)) and len(counts) == len(rows), "wrong Quint construction counts")
            for n, row in zip(counts, rows, strict=True):
                require(row == all_constructions.get((w, h, n)), "Quint/Lean constructor mismatch")
                q_construction_keys.append((w, h, n))
        expected_q_keys = [tuple(key) for key in all_constructions
                           if key[0]*key[1] <= COVERAGE["construction"]["quint_max_area"]]
        require(q_construction_keys == expected_q_keys and len(q_construction_keys) ==
                quint_report["construction_states"] == COVERAGE["construction"]["quint_boards"],
                "missing Quint construction coverage")
        report["constructions"]["quint_boards"] = len(q_construction_keys)
        targeted_count = 0
        require([[c["width"], c["height"]] for c in quint_report["targeted_cases"]] ==
                COVERAGE["finite_comparison"]["larger_targeted_dimensions"], "wrong larger target rectangles")
        for case in quint_report["targeted_cases"]:
            w, h, rows = case["width"], case["height"], case["rows"]
            require([r[2] for r in rows] == sorted({r[2] for r in rows}), "duplicate or unordered larger target cases")
            output_name = f"train-targeted-{w}x{h}.tsv"
            run(f"targeted-{w}x{h}", [str(executable), str(w), str(h), *[str(r[2]) for r in rows]],
                LEAN, output_name)
            actual = parse_rows(artifacts / output_name)
            require(actual == rows == python_rows(w, h, [r[2] for r in rows]), "larger targeted replay mismatch")
            for row in actual:
                validate_row(row)
            targeted_count += len(rows)
        require(targeted_count == quint_report["targeted_states"] ==
                COVERAGE["finite_comparison"]["larger_targeted_boards"], "wrong targeted-case count")
        report["larger_targeted_boards"] = targeted_count
        flow_lean_path = artifacts / "train-flow-lean.tsv"
        flow_quint_path = artifacts / "train-flow-quint.tsv"
        flow_report_path = artifacts / "train-flow-quint.json"
        require(report_path != flow_report_path, "acceptance and flow reports must have different paths")
        run("lean-low-density", [str(executable), "--low-density",
            str(COVERAGE["low_density_flow"]["max_side"])], LEAN, flow_lean_path.name)
        run("quint-low-density", [sys.executable, "formal/quint/train_flow_check.py",
            "--rows", str(flow_quint_path), "--report", str(flow_report_path)], ROOT)
        flow_report = json.loads(flow_report_path.read_text())
        report["low_density_flow"] = compare_sparse_flow(parse_rows(flow_lean_path),
            parse_rows(flow_quint_path), flow_report, before, flow_quint_path)
        target_orbits = flow_report.get("target_orbits", [])
        target_spec = COVERAGE["low_density_flow"]["target_orbits"]
        require([{key: case.get(key) for key in expected}
                 for case, expected in zip(target_orbits, target_spec, strict=True)] == target_spec,
                "wrong flow orbit inventory")
        flow_target_paths, orbit_summaries = [], []
        for index, case in enumerate(target_orbits):
            validate_flow_certificate(case)
            w, h, rows = case["width"], case["height"], case["rows"]
            output_name = f"train-flow-orbit-{index}-{w}x{h}.tsv"
            run(f"flow-orbit-{index}", [str(executable), str(w), str(h), *[str(r[2]) for r in rows]],
                LEAN, output_name)
            path = artifacts / output_name
            actual = parse_rows(path)
            require(actual == rows == python_rows(w, h, [r[2] for r in rows]),
                    f"three-language orbit mismatch: {case['label']}")
            for row in actual:
                validate_row(row)
            flow_target_paths.append(path)
            orbit_summaries.append({key: case[key] for key in (
                "label", "width", "height", "initial_code", "population", "transient_length", "period",
                "eventually_full_movement", "cycle_velocity_numerator", "cycle_velocity_denominator")})
        require(sum(len(c["rows"]) for c in target_orbits) == flow_report.get("target_orbit_rows") ==
                COVERAGE["low_density_flow"]["target_orbit_rows"], "wrong flow target coverage")
        rectangle = next(c for c in target_orbits if c["label"] == "rectangular-5x7-counterexample")
        require(rectangle["transient_length"] == 1 and rectangle["period"] == 15 and
                rectangle["repeated_code"] == 1459 and rectangle["cycle_total_moves"] == 29 and
                rectangle["cycle_velocity_numerator"] == 29 and rectangle["cycle_velocity_denominator"] == 30 and
                rectangle["satisfies_2m_lt_min_rectangle_bound"] is True and
                rectangle["eventually_full_movement"] is False, "lost the rectangular counterexample")
        report["low_density_flow"]["target_orbit_rows"] = flow_report["target_orbit_rows"]
        report["low_density_flow"]["target_orbits"] = orbit_summaries
        require(source_manifest() == before, "project sources changed during acceptance")
        report["artifact_sha256"] = {p.name: sha256(p.read_bytes()) for p in
            [lean_path, quint_path, quint_report_path, constructions_path,
             flow_lean_path, flow_quint_path, flow_report_path, *flow_target_paths]}
        report["status"] = "passed"
    except Exception as exc:
        report["status"] = "failed"
        report["error"] = f"{type(exc).__name__}: {exc}"
        print(report["error"], file=sys.stderr)
    finally:
        report["finished_at"] = datetime.now(timezone.utc).isoformat()
        report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(f"TRAIN acceptance {report['status']}: {report_path}")
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
