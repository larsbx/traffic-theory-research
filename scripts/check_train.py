#!/usr/bin/env python3
"""Build/audit TRAIN proofs and compare actual Lean, Quint, and Python evaluators.

Writes a source-bound acceptance report even when a stage fails. The finite
replay checks are kept separate from the unrestricted Lean threshold theorem.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
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
        require(source_manifest() == before, "project sources changed during acceptance")
        report["artifact_sha256"] = {p.name: sha256(p.read_bytes()) for p in
            [lean_path, quint_path, quint_report_path, constructions_path]}
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
