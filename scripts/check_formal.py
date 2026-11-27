#!/usr/bin/env python3
"""Run the version-pinned formal gate and record source-bound evidence."""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "formal/lean"
QUINT = ROOT / "formal/quint"
COVERAGE = json.loads((ROOT / "formal/coverage.json").read_text())
R2_APP_SOURCES = {
    "app/data/presets.json",
    "app/scripts/r2-certificates.mjs",
    "app/scripts/r2-progress.mjs",
    "app/scripts/r2-service.mjs",
    "app/src/presets.js",
    "app/src/raster.js",
    "app/src/realflow.js",
    "app/src/rng.js",
    "app/src/sim.js",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def source_manifest() -> dict[str, str]:
    paths = []
    for path in ROOT.rglob("*"):
        relative = path.relative_to(ROOT)
        if not path.is_file() or any(
            part in {".git", ".lake", "node_modules", "artifacts", ".artifacts", "__pycache__"}
            for part in relative.parts
        ):
            continue
        if (relative.parts[0] in {"formal", "scripts", ".github"}
                or relative.as_posix() in R2_APP_SOURCES
                or relative == Path("README.md")):
            paths.append(path)
    return {str(p.relative_to(ROOT)): sha256(p.read_bytes()) for p in sorted(paths)}


def revision() -> str | None:
    result = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"], cwd=ROOT,
        text=True, capture_output=True, check=False,
    )
    if result.returncode or Path(result.stdout.strip()).resolve() != ROOT:
        return None
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=ROOT,
        text=True, capture_output=True, check=False,
    )
    return result.stdout.strip() if result.returncode == 0 else None


def parse_rows(path: Path) -> list[tuple[int, ...]]:
    rows = []
    for number, line in enumerate(path.read_text().splitlines(), 1):
        parts = line.split("\t")
        require(len(parts) == 10, f"{path.name}:{number}: expected ten fields")
        require(all(re.fullmatch(r"\d+", x) for x in parts), f"{path.name}:{number}: noninteger")
        rows.append(tuple(map(int, parts)))
    return rows


def digit_counts(code: int, size: int) -> Counter:
    result: Counter = Counter()
    for _ in range(size):
        result[code % 3] += 1
        code //= 3
    require(code == 0, "board code exceeds the stated grid")
    return result


def compare_rows(lean_path: Path, quint_path: Path) -> dict:
    lean_rows = parse_rows(lean_path)
    quint_rows = parse_rows(quint_path)
    spec = COVERAGE["finite_comparison"]
    expected_keys = [
        (w, h, code, phase)
        for w, h in spec["dimensions"]
        for code in range(3 ** (w * h))
        for phase in (1, 2)
    ]
    require(len(expected_keys) == spec["phase_cases"], "coverage row count is inconsistent")
    require(len(expected_keys) // 2 == spec["boards"], "coverage board count is inconsistent")
    require([r[:4] for r in lean_rows] == expected_keys, "Lean export has missing/duplicate/reordered cases")
    require([r[:4] for r in quint_rows] == expected_keys, "Quint export has missing/duplicate/reordered cases")
    for index, (lean_row, quint_row) in enumerate(zip(lean_rows, quint_rows), 1):
        require(lean_row == quint_row, f"Lean/Quint mismatch at row {index}: {lean_row} != {quint_row}")
        w, h, before, phase, after, next_phase, frozen, valid, decoded, tiles = lean_row
        require(0 <= after < 3 ** (w * h), f"invalid output code at row {index}")
        require(next_phase == 3 - phase, f"phase failed to alternate at row {index}")
        require(frozen in (0, 1) and valid == frozen, f"frozen/Wang mismatch at row {index}")
        require(decoded == before and tiles == 21, f"tile recoding failure at row {index}")
        require(digit_counts(before, w*h) == digit_counts(after, w*h), f"species lost at row {index}")
        require(not frozen or before == after, f"frozen board moved at row {index}")

    table = {row[:4]: row for row in lean_rows}
    controls = {
        "east_wraparound": ((3, 2, 9, 1), 1),
        "north_wraparound": ((3, 2, 54, 2), 2),
        "simultaneous_queue_no_cascade": ((3, 2, 4, 1), 10),
        "quiet_east_half_step": ((3, 2, 2, 1), 2),
        "north_moves_after_quiet_east": ((3, 2, 2, 2), 54),
        "east_blocked_by_north": ((3, 2, 7, 1), 7),
        "north_releases_east_target": ((3, 2, 7, 2), 163),
        "east_moves_after_release": ((3, 2, 163, 1), 165),
    }
    for name, (key, expected) in controls.items():
        require(table[key][4] == expected, f"semantic control failed: {name}")
    require(table[(3, 2, 2, 1)][6] == 0, "quiet half-step was mistaken for complete freezing")
    require(table[(1, 1, 1, 1)][6] == 1, "singleton occupied torus must be frozen")
    return {
        "dimensions": spec["dimensions"],
        "boards": spec["boards"],
        "phase_cases": len(lean_rows),
        "semantic_controls": list(controls) + ["quiet_is_not_frozen", "singleton_frozen"],
        "lean_sha256": sha256(lean_path.read_bytes()),
        "quint_sha256": sha256(quint_path.read_bytes()),
        "status": "passed",
        "scope": "exhaustive finite board/phase agreement; no unbounded refinement claim",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifacts", type=Path, default=ROOT / "formal/artifacts")
    args = parser.parse_args()
    artifacts = args.artifacts.resolve()
    artifacts.mkdir(parents=True, exist_ok=True)
    lake = os.environ.get("TRAFFIC_LAKE", "lake")
    require(shutil.which(lake) is not None, "lake is unavailable; install the pinned Lean toolchain")
    require(shutil.which("node") is not None, "node is unavailable")
    cli = QUINT / "node_modules/@informalsystems/quint/dist/src/cli.js"
    require(cli.is_file(), "Quint is unavailable; run npm ci --ignore-scripts in formal/quint")
    before_sources = source_manifest()
    report = {
        "schema": "traffic.formal.acceptance.v1",
        "started_at": datetime.now(timezone.utc).isoformat(),
        "revision": revision(),
        "source_sha256": before_sources,
        "source_manifest_sha256": sha256(json.dumps(before_sources, sort_keys=True).encode()),
        "status": "running",
        "steps": [],
    }

    def run(label: str, command: list[str], cwd: Path, output_name: str | None = None) -> str:
        print(f"Checking {label} ...", flush=True)
        start = time.monotonic()
        result = subprocess.run(command, cwd=cwd, text=True, capture_output=True, check=False, timeout=600)
        stdout_path = artifacts / (output_name or f"{label}.log")
        stdout_path.write_text(result.stdout)
        (artifacts / f"{label}.stderr.log").write_text(result.stderr)
        report["steps"].append({
            "name": label, "argv": command, "cwd": str(cwd.relative_to(ROOT)),
            "exit_code": result.returncode, "seconds": round(time.monotonic() - start, 3),
        })
        require(result.returncode == 0, f"{label} failed; see {stdout_path} and its stderr log")
        return result.stdout.strip()

    try:
        lean_version = run("lean-version", [lake, "env", "lean", "--version"], LEAN)
        quint_version = run("quint-version", ["node", str(cli), "--version"], QUINT)
        node_version = run("node-version", ["node", "--version"], ROOT)
        require(f"version {COVERAGE['lean_version']}," in lean_version, f"wrong Lean version: {lean_version}")
        require(quint_version == COVERAGE["quint_version"], f"wrong Quint version: {quint_version}")
        report["versions"] = {"lean": lean_version, "quint": quint_version, "node": node_version}
        run("lean-build", [lake, "build", "Traffic", "traffic_export", "r2_check"], LEAN)
        audit = run("lean-axiom-audit", [lake, "env", "lean", "TrafficAudit.lean"], LEAN)
        audited = {}
        summary = None
        for line in audit.splitlines():
            parts = line.split("\t")
            if parts[0] == "AUDIT_THEOREM":
                audited[parts[1]] = parts[2].split(",") if len(parts) > 2 and parts[2] else []
            elif parts[0] == "AUDIT_SUMMARY":
                summary = {"declarations": int(parts[1]), "theorem_declarations": int(parts[2])}
        require(summary is not None and len(audited) == summary["theorem_declarations"], "incomplete Lean audit")
        missing = set(COVERAGE["required_theorems"]) - audited.keys()
        require(not missing, f"required theorems missing from compiled inventory: {sorted(missing)}")
        actual_axioms = sorted({a for axioms in audited.values() for a in axioms})
        require(set(actual_axioms) <= set(COVERAGE["allowed_axioms"]), "unexpected theorem axiom")
        report["lean_audit"] = {
            **summary, "required_theorems": len(COVERAGE["required_theorems"]),
            "actual_axioms": actual_axioms, "theorems": audited,
        }
        run("quint-typecheck", ["npm", "run", "typecheck"], QUINT)
        report["quint_tests"] = {}
        for kind, suite in COVERAGE["quint"]["test_suites"].items():
            expected = suite["required_tests"]
            expected_count = COVERAGE["quint"][f"{kind}_tests"]
            require(len(set(expected)) == len(expected) == expected_count,
                    f"inconsistent {kind} test inventory in coverage.json")
            result_path = artifacts / f"quint-{kind}-tests.json"
            result_path.unlink(missing_ok=True)
            run(f"quint-{kind}-tests", [
                "node", str(cli), "test", suite["module"],
                f"--backend={COVERAGE['quint']['backend']}", "--max-samples=1",
                f"--seed={COVERAGE['quint']['simulation_seed']}", f"--out={result_path}",
            ], QUINT)
            result = json.loads(result_path.read_text())
            passed = result.get("passed")
            require(isinstance(passed, list) and all(isinstance(name, str) for name in passed),
                    f"{kind} suite did not emit a passed-test inventory")
            require(len(passed) == expected_count and set(passed) == set(expected),
                    f"{kind} suite executed a different test inventory: {passed}")
            require(result.get("failed") == [] and result.get("ignored") == [],
                    f"{kind} suite has failed or ignored tests")
            report["quint_tests"][kind] = {
                "module": suite["module"], "passed": passed,
                "count": len(passed), "failed": [], "ignored": [],
                "result_sha256": sha256(result_path.read_bytes()),
            }
        run("quint-simulation", ["npm", "run", "simulate"], QUINT)
        run("lean-export", [str(LEAN / ".lake/build/bin/traffic_export")], LEAN, "lean.tsv")
        run("quint-export", ["node", str(QUINT / "export.cjs")], ROOT, "quint.tsv")
        report["cross_language"] = compare_rows(artifacts / "lean.tsv", artifacts / "quint.tsv")
        r2_audit = run("r2-axiom-audit", [lake, "env", "lean", "R2Audit.lean"], LEAN)
        r2 = run("r2-correspondence", [
            "node", "app/scripts/r2-certificates.mjs", "--check-lean",
            str(LEAN / ".lake/build/bin/r2_check"), str(artifacts),
        ], ROOT)
        report["r2"] = {
            **json.loads(r2),
            "axiom_audit": r2_audit,
            "map_certificates_sha256": sha256((artifacts / "r2-map-certificates.json").read_bytes()),
            "lean_cases_sha256": sha256((artifacts / "r2-lean-cases.json").read_bytes()),
            "scope": "CLASSIC structural traps, conditional progress, and finite simulator correspondence",
        }
        progress = run("r2-progress", [
            "node", "app/scripts/r2-progress.mjs", str(LEAN / ".lake/build/bin/r2_check"),
        ], ROOT)
        report["r2"]["progress"] = json.loads(progress)
        service = run("r2-service", [
            "node", "app/scripts/r2-service.mjs", str(LEAN / ".lake/build/bin/r2_check"), str(artifacts),
        ], ROOT)
        report["r2"]["service"] = {
            **json.loads(service),
            "cases_sha256": sha256((artifacts / "r2-service-cases.json").read_bytes()),
        }
        require(source_manifest() == before_sources, "sources changed during acceptance")
        report["status"] = "passed"
        report["not_claimed"] = COVERAGE["not_claimed"]
        print(
            f"PASS: Lean build/audit, Quint checks, and {COVERAGE['finite_comparison']['phase_cases']} "
            "exhaustive cross-language phase cases. R2 rank, trap, progress, and service checks passed.",
            flush=True,
        )
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        print(f"FAIL: {error}", file=sys.stderr, flush=True)
    finally:
        report["finished_at"] = datetime.now(timezone.utc).isoformat()
        (artifacts / "acceptance.json").write_text(json.dumps(report, indent=2) + "\n")
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
