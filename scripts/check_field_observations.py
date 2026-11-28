#!/usr/bin/env python3
"""Check exact observation evidence offline, optionally including pinned NGSIM CSVs.

This gate downloads nothing. Without --parts its receipt covers synthetic
controls only. With --parts it also checks every pair in the pinned capture,
while retaining one shared-sample corpus rather than copying samples per cut.
The native checker is supplied explicitly and bound by SHA-256; compilation
and the Lean axiom audit are separate formal gates.
"""

from __future__ import annotations

import argparse
import copy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
FIELD = ROOT / "data/lankershim-field-replay"
LEAN = ROOT / "formal/lean"
RECEIPT_SCHEMA = "gridlock-field-observation-receipt-v1"
SOURCE_FILES = (
    "data/lankershim-field-replay/observation_events.py",
    "data/lankershim-field-replay/test_observation_events.py",
    "data/lankershim-field-replay/replay.py",
    "data/lankershim-field-replay/test_replay.py",
    "data/lankershim-field-replay/result.json",
    "data/lankershim-field-replay/fetch.sh",
    "data/lankershim-field-replay/README.md",
    "formal/lean/lakefile.toml",
    "formal/lean/lean-toolchain",
    "scripts/check_field_observations.py",
)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def hash_file(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as file:
        for chunk in iter(lambda: file.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def source_manifest():
    paths = {ROOT / relative for relative in SOURCE_FILES}
    paths.update(path for path in LEAN.rglob("*.lean")
                 if ".lake" not in path.relative_to(LEAN).parts)
    package_manifest = LEAN / "lake-manifest.json"
    if package_manifest.is_file():
        paths.add(package_manifest)
    require(all(path.is_file() for path in paths), "missing observation gate source")
    return {path.relative_to(ROOT).as_posix(): hash_file(path) for path in sorted(paths)}


def revision():
    result = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT,
                            capture_output=True, text=True, check=False)
    return result.stdout.strip() if result.returncode == 0 else None


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def json_result(result, name):
    require(result.returncode == 0, f"{name} failed: {result.stderr.strip() or result.stdout.strip()}")
    try:
        value = json.loads(result.stdout)
    except json.JSONDecodeError as error:
        raise RuntimeError(f"{name} did not emit one JSON result") from error
    require(isinstance(value, dict), f"{name} emitted a non-object result")
    return value


class Gate:
    def __init__(self, executable, artifacts, parts):
        self.executable = Path(executable).resolve()
        self.artifacts = Path(artifacts).resolve()
        self.parts = [Path(part).resolve() for part in parts] if parts else []
        self.artifacts.mkdir(parents=True, exist_ok=True)
        self.produced = set()
        self.initial_sources = source_manifest()
        require(self.executable.is_file(), f"missing native checker: {self.executable}")
        self.executable_hash = hash_file(self.executable)
        self.initial_inputs = {str(part): hash_file(part) for part in self.parts}
        self.receipt = {
            "schema": RECEIPT_SCHEMA, "started_at_utc": utc_now(), "status": "running",
            "repository_revision": revision(), "python_version": sys.version.split()[0],
            "sources_sha256": self.initial_sources,
            "executable": {"path": str(self.executable), "sha256": self.executable_hash,
                           "build": "supplied executable; compilation and axiom audit are separate gates"},
            "tests": {"status": "not_run"}, "synthetic": {"status": "not_run"},
            "negative_controls": [],
            "observed": {"status": "not_run", "reason": "no pinned CSV paths supplied"},
            "commands": [],
            "scope": {
                "exact_recorded_decimal_decisions": True,
                "physical_stop_line_registered": False,
                "controller_clock_aligned": False,
                "vacancy_or_exit_inferred_from_missing_rows": False,
            },
        }

    def output(self, name):
        return self.artifacts / name

    def register(self, *paths):
        for path in paths:
            require(Path(path).is_file(), f"expected artifact was not produced: {path}")
            self.produced.add(Path(path))

    def run_command(self, name, command, cwd=ROOT, timeout=300):
        start = time.monotonic()
        result = subprocess.run([str(argument) for argument in command], cwd=cwd,
                                capture_output=True, text=True, check=False, timeout=timeout)
        log = self.output(name + ".log")
        log.write_text(result.stdout + ("\n" if result.stdout and result.stderr else "") + result.stderr,
                       encoding="utf-8")
        self.register(log)
        self.receipt["commands"].append({
            "name": name, "argv": [str(argument) for argument in command], "cwd": str(cwd),
            "exit_code": result.returncode, "duration_seconds": round(time.monotonic() - start, 6),
            "log": log.name,
        })
        return result

    def check_native(self, name, path, expected):
        result = self.run_command(name, [self.executable, "--field", path])
        actual = json_result(result, name)
        for key, value in expected.items():
            require(actual.get(key) == value,
                    f"{name} {key}: expected {value!r}, got {actual.get(key)!r}")
        require(actual.get("ok", True) is not False, f"{name} reported failure")
        result_path = self.output(name + ".json")
        write_json(result_path, actual)
        self.register(result_path)
        return actual

    def run_tests(self):
        result = self.run_command("python-tests", [sys.executable, "-m", "unittest", "-v",
            "test_replay", "test_observation_events"], cwd=FIELD, timeout=120)
        require(result.returncode == 0, "observation Python tests failed; see python-tests.log")
        output = result.stdout + result.stderr
        count = re.search(r"Ran ([0-9]+) tests? in", output)
        require(count is not None and int(count.group(1)) > 0, "Python test inventory was empty")
        require("(test_replay." in output and "(test_observation_events." in output,
                "both existing replay and observation adapter tests must execute")
        substitution = "test_source_commitment_survives_renaming_but_not_byte_substitution"
        require(re.search(re.escape(substitution) + r".*\.\.\. ok", output) is not None,
                "source-substitution rejection test did not pass")
        self.receipt["tests"] = {
            "status": "passed", "tests": int(count.group(1)),
            "modules": ["test_replay", "test_observation_events"],
            "source_substitution_rejection": {"test": substitution, "status": "passed"},
        }

    def run_fixture(self):
        path = self.output("fixture-cases.json")
        generated = self.run_command("generate-fixture", [sys.executable,
            FIELD / "observation_events.py", "--fixture-cases", path])
        generation = json_result(generated, "fixture generator")
        require(generation.get("kind") == "synthetic_control", "fixture was not labeled synthetic")
        self.register(path)
        corpus = json.loads(path.read_text())
        require(all(source.get("kind") == "synthetic_control" for source in corpus["sources"]),
                "synthetic corpus contains a source labeled as field data")
        expected = {
            "samples": len(corpus["samples"]), "pairs": len(corpus["pairs"]),
            "cuts": len(corpus["cuts"]),
            "decisions": len(corpus["pairs"]) * len(corpus["cuts"]),
            "firstCrossings": corpus["expectedFirstCrossings"],
            "adjacentPairs": sum(pair["expected"][0]["adjacent"] for pair in corpus["pairs"]),
            "gapPairs": sum(not pair["expected"][0]["adjacent"] for pair in corpus["pairs"]),
            "laneChanges": sum(pair["expected"][0]["changedLane"] for pair in corpus["pairs"]),
            "phaseClaims": 0, "modelTransitionClaims": 0,
        }
        actual = self.check_native("fixture-native", path, expected)
        self.receipt["synthetic"] = {"status": "passed", "counts": actual, "corpus": path.name}
        return corpus

    def run_negative_controls(self, fixture):
        def wrong_classification(case):
            result = case["pairs"][0]["expected"][2]
            result["crossing"] = not result["crossing"]

        def wrong_count(case):
            case["expectedFirstCrossings"][0] += 1

        def zero_denominator(case):
            case["samples"][0]["y"]["den"] = "0"

        def out_of_range_pair(case):
            case["pairs"][0]["after"] = len(case["samples"])

        mutations = (
            ("wrong-classification", wrong_classification),
            ("wrong-crossing-count", wrong_count),
            ("zero-denominator", zero_denominator),
            ("out-of-range-pair", out_of_range_pair),
        )
        for name, mutate in mutations:
            case = copy.deepcopy(fixture)
            mutate(case)
            path = self.output("rejected-" + name + ".json")
            write_json(path, case)
            self.register(path)
            result = self.run_command("reject-" + name, [self.executable, "--field", path])
            require(result.returncode != 0, f"native checker accepted {name}")
            require(result.returncode > 0, f"native checker crashed instead of rejecting {name}")
            require(bool(result.stderr.strip() or result.stdout.strip()),
                    f"native checker rejected {name} without a diagnostic")
            self.receipt["negative_controls"].append({
                "name": name, "status": "rejected", "exit_code": result.returncode,
                "diagnostic": result.stderr.strip() or result.stdout.strip(), "corpus": path.name,
            })

    def run_track_inventory_controls(self, fixture):
        # These are synthetic records exercising the recorded-track decoder's
        # inventory branch. No CSV provenance or observed traffic is claimed.
        packet = copy.deepcopy(fixture)
        packet["sources"] = [copy.deepcopy(fixture["sources"][0])]
        packet["sources"][0]["kind"] = "recorded_trajectory_capture"
        packet["sources"][0]["description"] = "Synthetic recorded-track inventory control"
        packet["samples"] = copy.deepcopy(fixture["samples"][:2])
        third = copy.deepcopy(packet["samples"][1])
        third["frame"] += 1
        third["timeMs"] += 100
        third["y"] = {"num": "351", "den": "1"}
        third["decimalLexemes"]["local_y"] = "351"
        third["provenance"]["csvRow"] += 1
        packet["samples"].append(third)
        no_cross = {"identity": True, "adjacent": True, "forwardBracket": False,
                    "crossing": False, "changedLane": False, "gapCandidate": False,
                    "slowBefore": False}
        packet["pairs"] = [copy.deepcopy(fixture["pairs"][0]),
                           {"before": 1, "after": 2, "expected": [no_cross.copy() for _ in range(3)]}]
        packet["expectedFirstCrossings"] = [0, 0, 1]
        path = self.output("synthetic-track-inventory.json")
        write_json(path, packet)
        self.register(path)
        result = self.check_native("synthetic-track-inventory", path,
            {"samples": 3, "pairs": 2, "cuts": 3, "decisions": 6, "firstCrossings": [0, 0, 1],
             "phaseClaims": 0, "modelTransitionClaims": 0})
        self.receipt["synthetic_track_inventory"] = {
            "kind": "synthetic_control", "status": "passed", "counts": result,
            "scope": "Constructed track; recorded-kind wire branch only, no real-data assertion",
        }
        for name, expected_message in (
                ("duplicate-pair", "duplicate recorded pair"),
                ("omitted-pair", "inventory is incomplete"),
                ("duplicate-time", "duplicate or unordered sample")):
            corrupted = copy.deepcopy(packet)
            if name == "duplicate-pair":
                corrupted["pairs"].append(copy.deepcopy(corrupted["pairs"][0]))
            elif name == "omitted-pair":
                corrupted["pairs"].pop()
            else:
                corrupted["samples"][2]["timeMs"] = corrupted["samples"][1]["timeMs"]
            path = self.output("rejected-" + name + ".json")
            write_json(path, corrupted)
            self.register(path)
            rejected = self.run_command("reject-" + name, [self.executable, "--field", path])
            require(rejected.returncode > 0 and expected_message in rejected.stderr,
                    f"native inventory control {name} did not reject for its intended reason")
            self.receipt["negative_controls"].append({
                "name": name, "status": "rejected", "exit_code": rejected.returncode,
                "diagnostic": rejected.stderr.strip(), "corpus": path.name,
            })

    def run_observed(self):
        if not self.parts:
            return
        self.receipt["observed"] = {"status": "running", "inputs_sha256": self.initial_inputs}
        cases, report, events = (self.output(name) for name in ("real-cases.json", "report.json", "events.jsonl"))
        result = self.run_command("generate-observed", [sys.executable,
            FIELD / "observation_events.py", *self.parts,
            "--manifest", FIELD / "result.json", "--cases", cases,
            "--report", report, "--events", events])
        summary = json_result(result, "pinned observation adapter")
        require(summary.get("pinned_baseline_matched") is True, "pinned field baseline was not matched")
        require(json.loads(report.read_text()) == summary, "adapter report and stdout disagree")
        self.register(cases, report, events)
        baseline = json.loads((FIELD / "result.json").read_text())
        require({item["sha256"] for item in summary["inputs"]} ==
                {item["sha256"] for item in baseline["inputs"]}, "observed source commitment mismatch")
        require({item["sha256"] for item in summary["inputs"]} == set(self.initial_inputs.values()),
                "adapter processed different CSV bytes than the gate committed")
        cut_order = ["330", "340", "350"]
        expected = {
            "samples": summary["rows"], "pairs": summary["pairs"], "cuts": len(cut_order),
            "decisions": summary["pairs"] * len(cut_order),
            "firstCrossings": [summary["screenlines"][cut]["total"] for cut in cut_order],
            "adjacentPairs": summary["adjacent_frame_time_pairs"],
            "gapPairs": summary["unknown_intervening_trajectory_pairs"],
            "laneChanges": summary["pairs_with_changed_lane_code"],
            "phaseClaims": 0, "modelTransitionClaims": 0,
        }
        actual = self.check_native("observed-native", cases, expected)
        require(summary["evidence_events_sha256"] == hash_file(events), "evidence-event digest mismatch")
        self.receipt["observed"] = {
            "status": "passed", "inputs": summary["inputs"], "inputs_sha256": self.initial_inputs,
            "sources": summary["sources"], "counts": actual, "cut_order_ft": cut_order,
            "pinned_baseline_matched": True,
            "adjacent_frame_time_pairs": summary["adjacent_frame_time_pairs"],
            "unknown_intervening_trajectory_pairs": summary["unknown_intervening_trajectory_pairs"],
            "pairs_with_changed_lane_code": summary["pairs_with_changed_lane_code"],
            "evidence_events": summary["evidence_events"],
            "corpus": cases.name, "report": report.name, "events": events.name,
        }

    def stable_inputs(self):
        require(source_manifest() == self.initial_sources,
                "source files changed while the observation gate was running")
        require(hash_file(self.executable) == self.executable_hash,
                "native checker changed while the observation gate was running")
        require({str(path): hash_file(path) for path in self.parts} == self.initial_inputs,
                "CSV inputs changed while the observation gate was running")

    def run(self):
        try:
            self.run_tests()
            fixture = self.run_fixture()
            self.run_negative_controls(fixture)
            self.run_track_inventory_controls(fixture)
            self.run_observed()
            self.stable_inputs()
            self.receipt["status"] = "passed"
        except Exception as error:
            self.receipt["status"] = "failed"
            self.receipt["error"] = f"{type(error).__name__}: {error}"
            if self.receipt["observed"]["status"] == "running":
                self.receipt["observed"]["status"] = "failed"
            raise
        finally:
            self.receipt["finished_at_utc"] = utc_now()
            self.receipt["outputs"] = {
                path.relative_to(self.artifacts).as_posix(): {"sha256": hash_file(path), "bytes": path.stat().st_size}
                for path in sorted(self.produced)}
            write_json(self.output("receipt.json"), self.receipt)
        return self.receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-executable", type=Path, required=True)
    parser.add_argument("--artifacts", type=Path, required=True)
    parser.add_argument("--parts", nargs=3, type=Path, metavar=("PART0", "PART1", "PART2"))
    args = parser.parse_args()
    gate = None
    try:
        gate = Gate(args.lean_executable, args.artifacts, args.parts)
        receipt = gate.run()
    except Exception as error:
        if gate is None:
            # An invalid executable or missing source must not leave an old
            # passed receipt looking like the result of this invocation.
            write_json(Path(args.artifacts).resolve() / "receipt.json", {
                "schema": RECEIPT_SCHEMA, "status": "failed", "phase": "initialization",
                "finished_at_utc": utc_now(), "error": f"{type(error).__name__}: {error}",
                "synthetic": {"status": "not_run"}, "observed": {"status": "not_run"},
            })
        print(f"field observation gate failed: {error}", file=sys.stderr)
        return 1
    print(json.dumps({
        "status": receipt["status"], "tests": receipt["tests"]["tests"],
        "synthetic": receipt["synthetic"]["counts"],
        "negative_controls": len(receipt["negative_controls"]),
        "observed": receipt["observed"].get("counts", {"status": "not_run"}),
        "receipt": str(Path(args.artifacts).resolve() / "receipt.json"),
    }))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
