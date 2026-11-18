#!/usr/bin/env python3
"""Check exact finite-cutoff absorption bounds against actual Lean and Quint.

The default evaluates every initial board of every positive rectangle with at
most six cells at six complete-round cutoffs. Additional 3x3 cases are exactly
the 72 states still unresolved at cutoff 16, replayed at cutoffs 16 and 32.
Probability weights always belong to initial boards. This gate proves no
size-uniform decay estimate and claims no unrestricted source refinement.
"""
from __future__ import annotations

import argparse
from dataclasses import replace
from fractions import Fraction
import hashlib
import json
from math import comb
from pathlib import Path
import platform
import subprocess
import sys
from time import perf_counter

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "formal/lean"
QUINT = ROOT / "formal/quint"
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(QUINT))

from bml.absorption import (  # noqa: E402
    HIT, SAFE, UNRESOLVED, certificate_from_code, complete_cutoff_census,
    partial_probability_bounds, verify_certificate,
)
from bml.exhaustive import JAM, MIXED, classify_all  # noqa: E402

CUTOFFS = (0, 1, 2, 4, 8, 16)
DENSITIES = tuple(map(Fraction, ("0", "1/10", "1/5", "1/2", "2/3", "9/10", "1")))


def source_hashes() -> dict[str, str]:
    paths = {
        "bml/absorption.py", "bml/obstructions.py", "bml/model.py", "bml/exhaustive.py",
        "scripts/check_absorption.py", "tests/test_absorption.py", "tests/test_obstructions.py",
        "formal/quint/Absorption.qnt", "formal/quint/absorption_evaluate.py",
        "formal/quint/BML.qnt", "formal/quint/package.json", "formal/quint/package-lock.json",
        "formal/lean/lakefile.toml", "formal/lean/lake-manifest.json", "formal/lean/lean-toolchain",
        ".github/workflows/finite-bml.yml", "requirements-dev.txt",
    }
    paths.update(str(path.relative_to(ROOT)) for path in LEAN.rglob("*.lean")
                 if ".lake" not in path.parts)
    return {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in sorted(paths)}


def command(args: list[str], *, cwd: Path = ROOT, timeout: int = 300) -> str:
    result = subprocess.run(args, cwd=cwd, capture_output=True, text=True,
                            timeout=timeout, check=False)
    if result.returncode:
        raise RuntimeError(f"Command failed: {args!r}\n{result.stdout}\n{result.stderr}")
    return result.stdout


def expected_rows(census, cutoffs, indices=None):
    indices = list(range(census.states)) if indices is None else indices
    return [[code, cutoff, int(census.snapshot(cutoff).terminal_codes[code]),
             int(census.snapshot(cutoff).verdicts[code]), int(census.initial_car_counts[code])]
            for cutoff in cutoffs for code in indices]


def compare_rows(actual, expected, label: str) -> None:
    if len(actual) != len(expected):
        raise AssertionError(f"{label}: missing or extra output rows")
    for row, want in zip(actual, expected, strict=True):
        if (not isinstance(row, list) or len(row) != 5
                or any(type(value) is not int for value in row)):
            raise AssertionError(f"{label}: malformed output row")
        if row != want:
            raise AssertionError(f"{label}: output differs: got {row}, expected {want}")


def lean_rows(binary: Path, width: int, height: int, cutoffs, indices=None):
    args = [str(binary), str(width), str(height), ",".join(map(str, cutoffs))]
    if indices is not None:
        args.extend(map(str, indices))
    output = command(args)
    try:
        return [list(map(int, line.split(","))) for line in output.splitlines()]
    except ValueError as error:
        raise AssertionError("Lean emitted a malformed integer protocol") from error


def check_probabilities(census) -> dict:
    """Independent complete-graph oracle and integer-denominator integration."""
    oracle = classify_all(census.height, census.width)
    if not np.array_equal(census.successors, oracle.f):
        raise AssertionError("independent producers disagree on the full transition map")
    cells = census.width * census.height
    if not np.array_equal(census.initial_car_counts, oracle.n_east + oracle.n_north):
        raise AssertionError("initial population counts disagree with the graph oracle")
    for snapshot in census.snapshots:
        if not np.all(np.isin(snapshot.verdicts, (HIT, SAFE, UNRESOLVED))):
            raise AssertionError("unknown verdict in a complete census")
        hit, safe = snapshot.verdicts == HIT, snapshot.verdicts == SAFE
        if np.any(hit & (oracle.cls != JAM)) or np.any(safe & (oracle.cls == JAM)):
            raise AssertionError("a certified verdict contradicts the full graph oracle")
        for verdict in (HIT, SAFE, UNRESOLVED):
            coefficients = np.bincount(
                census.initial_car_counts[snapshot.verdicts == verdict], minlength=cells + 1)
            if not np.array_equal(coefficients, snapshot.by_cars[verdict]):
                raise AssertionError("population coefficients disagree with verified verdicts")
    oracle_counts = np.bincount(census.initial_car_counts[oracle.cls == JAM],
                               minlength=cells + 1)
    curves = []
    for p in DENSITIES:
        a, d = p.numerator, p.denominator
        denominator = (2 * d) ** cells
        weights = [a**n * (2 * (d-a))**(cells-n) for n in range(cells + 1)]
        normalization = sum(comb(cells, n) * 2**n * weight
                            for n, weight in enumerate(weights))
        if normalization != denominator:
            raise AssertionError("integer initial-iid weights do not normalize")
        truth = Fraction(sum(int(c) * weight for c, weight in zip(oracle_counts, weights)),
                         denominator)
        previous_lower, previous_upper = Fraction(), Fraction(1)
        for snapshot in census.snapshots:
            bounds = snapshot.probability_bounds(p)
            numerators = [sum(count * weight for count, weight in zip(row, weights))
                          for row in snapshot.by_cars]
            if sum(numerators) != denominator:
                raise AssertionError("verdict masses fail to partition initial probability")
            if (bounds.lower != Fraction(numerators[HIT], denominator)
                    or bounds.unresolved != Fraction(numerators[UNRESOLVED], denominator)
                    or bounds.upper != 1 - Fraction(numerators[SAFE], denominator)):
                raise AssertionError("rational bounds disagree with initial integer weights")
            if not previous_lower <= bounds.lower <= truth <= bounds.upper <= previous_upper:
                raise AssertionError("intervals are unsound or fail to refine monotonically")
            previous_lower, previous_upper = bounds.lower, bounds.upper
            curves.append({"p": str(p), "cutoff": snapshot.cutoff,
                           "lower": str(bounds.lower), "upper": str(bounds.upper),
                           "unresolved": str(bounds.unresolved), "oracle": str(truth)})
    return {"width": census.width, "height": census.height, "states": census.states,
            "population_coefficients_checked": True,
            "cutoffs": [s.cutoff for s in census.snapshots],
            "verdict_counts": [list(s.counts) for s in census.snapshots],
            "safe_intermediate_states_at_last_cutoff": int(np.count_nonzero(
                (census.snapshots[-1].verdicts == SAFE) & (oracle.cls == MIXED))),
            "exact_initial_iid_bounds": curves}


def rejection_controls() -> list[str]:
    empty = certificate_from_code(2, 2, 0, 1)
    short = certificate_from_code(2, 2, 1, 0)
    late = certificate_from_code(4, 2, 3858, 1)
    moving = certificate_from_code(4, 2, 3860, 2)
    controls = [
        ("empty-as-jam", 2, 2, replace(empty, verdict="hit", repeat_index=None), "verdict"),
        ("cutoff-without-recurrence", 2, 2, replace(short, verdict="safe", repeat_index=0), "verdict"),
        ("late-jam-treated-as-safe", 4, 2, replace(late, verdict="safe", repeat_index=0), "verdict"),
        ("forged-transition", 4, 2, replace(moving, states=(3860, 4340, 4340)), "edge"),
        ("wrong-recurrence-index", 4, 2, replace(moving, repeat_index=1), "recurrence"),
        ("wrong-phase-count", 4, 2, replace(moving, cutoff=1), "cutoff"),
        ("wrong-dimensions", 2, 4, moving, "dimensions"),
        ("TRAIN-rule-substitution", 4, 2, replace(moving, rule="train"), "CLASSIC"),
    ]
    rejected = []
    for name, width, height, certificate, expected_message in controls:
        try:
            verify_certificate(width, height, certificate)
        except ValueError as error:
            if expected_message not in str(error):
                raise AssertionError(f"{name}: failed for the wrong reason: {error}") from error
            rejected.append(name)
        else:
            raise AssertionError(f"negative control accepted: {name}")
    try:
        partial_probability_bounds(2, 2, [empty, empty], Fraction(1, 2))
    except ValueError as error:
        if "duplicate" not in str(error):
            raise
        rejected.append("duplicate-initial-probability")
    else:
        raise AssertionError("duplicate initial state was counted twice")
    census = complete_cutoff_census(2, 2, (1,))
    wrong_populations = census.initial_car_counts.copy()
    wrong_populations[1] = 0
    wrong_coefficients = [list(row) for row in census.snapshots[0].by_cars]
    wrong_coefficients[SAFE][0] -= 1
    wrong_coefficients[HIT][0] += 1
    wrong_snapshot = replace(census.snapshots[0],
                             by_cars=tuple(tuple(row) for row in wrong_coefficients))
    for name, altered, expected_message in [
        ("wrong-initial-population", replace(census, initial_car_counts=wrong_populations),
         "initial population"),
        ("wrong-population-coefficients", replace(census, snapshots=(wrong_snapshot,)),
         "population coefficients"),
    ]:
        try:
            check_probabilities(altered)
        except AssertionError as error:
            if expected_message not in str(error):
                raise AssertionError(f"{name}: failed for the wrong reason: {error}") from error
            rejected.append(name)
        else:
            raise AssertionError(f"probability aggregation mutation survived: {name}")
    partial = partial_probability_bounds(2, 2, [empty], Fraction(1, 2))
    if partial.upper != Fraction(15, 16) or partial.omitted_mass != Fraction(15, 16):
        raise AssertionError("omitted initial probability was silently discarded")
    protocol = [[0, 0, 0, 2, 0], [1, 0, 1, 0, 1]]
    for name, altered in [
        ("missing-output-row", protocol[:1]),
        ("duplicate-output-row", [protocol[0], protocol[0]]),
        ("wrong-output-verdict", [protocol[0], [1, 0, 1, 1, 1]]),
    ]:
        try:
            compare_rows(altered, protocol, name)
        except AssertionError:
            rejected.append(name)
        else:
            raise AssertionError(f"protocol mutation survived: {name}")
    return rejected


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--backend", choices=("both", "lean", "quint", "python"), default="both")
    parser.add_argument("--max-cells", type=int, default=6)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--quint-cli", default=str(QUINT / "node_modules/.bin/quint"))
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    if not 1 <= args.max_cells <= 6:
        parser.error("--max-cells must be in 1..6")
    before = source_hashes()
    started = perf_counter()
    use_lean, use_quint = args.backend in ("both", "lean"), args.backend in ("both", "quint")
    tools = {"python": platform.python_version(), "numpy": np.__version__}
    audits = {}
    binary = LEAN / ".lake/build/bin/absorption_export"
    binary_before = None
    if use_lean:
        tools["lean"] = command([args.lake, "env", "lean", "--version"], cwd=LEAN).strip()
        command([args.lake, "build", "BML", "absorption_export"], cwd=LEAN)
        for audit in ("Audit.lean", "AbsorptionAudit.lean"):
            audits[audit] = command([args.lake, "env", "lean", audit], cwd=LEAN).strip()
        binary_before = hashlib.sha256(binary.read_bytes()).hexdigest()
        print("Lean build and both axiom audits passed", flush=True)
    if use_quint:
        from absorption_evaluate import evaluate_probe_rows
        tools["quint"] = command([args.quint_cli, "--version"]).strip()
        if tools["quint"] != "0.33.1":
            raise AssertionError("expected pinned Quint 0.33.1")
        for action in ("parse", "typecheck"):
            command([args.quint_cli, action, str(QUINT / "Absorption.qnt")])
        audits["Quint tests"] = command([args.quint_cli, "test", str(QUINT / "Absorption.qnt"),
                                        "--backend=typescript", "--max-samples=1"])
        print("Actual Quint parse, typecheck and deterministic tests passed", flush=True)

    scopes = []
    replay_rows = 0
    for width in range(1, args.max_cells + 1):
        for height in range(1, args.max_cells // width + 1):
            census = complete_cutoff_census(width, height, CUTOFFS)
            expected = expected_rows(census, CUTOFFS)
            if use_lean:
                compare_rows(lean_rows(binary, width, height, CUTOFFS), expected, "Lean")
            if use_quint:
                compare_rows(evaluate_probe_rows(width, height, list(range(census.states)),
                                                list(CUTOFFS), args.quint_cli), expected, "Quint")
            scope = check_probabilities(census)
            replay_rows += len(expected)
            scopes.append(scope)
            print(f"Absorption {width}x{height}: {census.states} states, {len(expected)} cutoff rows", flush=True)

    large = complete_cutoff_census(3, 3, CUTOFFS + (32,))
    pending = np.flatnonzero(large.snapshot(16).verdicts == UNRESOLVED).tolist()
    if len(pending) != 72 or large.snapshot(32).counts[UNRESOLVED] != 0:
        raise AssertionError("the explicit incomplete-cutoff control changed")
    expected = expected_rows(large, (16, 32), pending)
    if use_lean:
        compare_rows(lean_rows(binary, 3, 3, (16, 32), pending), expected, "Lean unresolved cases")
    if use_quint:
        compare_rows(evaluate_probe_rows(3, 3, pending, [16, 32], args.quint_cli),
                     expected, "Quint unresolved cases")
    large_report = check_probabilities(large)
    exact = large.snapshot(32).probability_bounds(Fraction(1, 2))
    if exact.lower != Fraction(12613, 131072) or exact.lower != exact.upper:
        raise AssertionError("exact closed 3x3 interval changed")
    witness_rows = 0
    for width, height, code, cutoffs in [(4, 2, 3858, (0, 1, 3)),
                                      (4, 2, 3860, (0, 1, 2, 8)),
                                      (4, 4, 18626220, (0, 1, 2))]:
        expected = []
        for cutoff in cutoffs:
            certificate = certificate_from_code(width, height, code, cutoff)
            population = sum(int(d) != 0 for d in np.base_repr(code, base=3))
            verdict = ("hit", "safe", "unresolved").index(certificate.verdict)
            expected.append([code, cutoff, certificate.terminal_code, verdict, population])
        if use_lean:
            compare_rows(lean_rows(binary, width, height, cutoffs, [code]), expected, "Lean witness")
        if use_quint:
            compare_rows(evaluate_probe_rows(width, height, [code], list(cutoffs), args.quint_cli),
                         expected, "Quint witness")
        witness_rows += len(expected)
    rejected = rejection_controls()
    after = source_hashes()
    if before != after:
        raise AssertionError("sources changed during acceptance")
    if binary_before is not None and hashlib.sha256(binary.read_bytes()).hexdigest() != binary_before:
        raise AssertionError("Lean executable changed during acceptance")
    report = {
        "schema": "bml.absorption-acceptance.v1", "status": "passed", "backend": args.backend,
        "tools": tools, "audits": audits, "max_cells": args.max_cells,
        "lean_audited": use_lean, "quint_evaluated": use_quint,
        "exhaustive_initial_states": sum(s["states"] for s in scopes),
        "exhaustive_cutoff_rows": replay_rows, "cutoffs": list(CUTOFFS),
        "rectangles": scopes, "python_complete_3x3_census": large_report,
        "additional_3x3_initial_states": len(pending), "additional_3x3_cutoff_rows": len(pending)*2,
        "additional_witness_rows": witness_rows,
        "rejected_controls": rejected,
        "lean_binary_sha256": binary_before,
        "source_sha256_before": before, "source_sha256_after": after,
        "seconds": round(perf_counter() - started, 6),
        "scope": ("finite actual implementation evaluation"
                  + (" plus separately audited universal Lean soundness" if use_lean else "")),
        "not_established": ["unrestricted source refinement", "iid laws on evolved cells",
                            "uniform late-time defect or unresolved-mass decay",
                            "positive or sharp critical density"],
    }
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed {replay_rows} exhaustive cutoff rows, {len(pending)*2} targeted 3x3 rows, "
          f"{witness_rows} witness rows; rejected {len(rejected)} controls.", flush=True)


if __name__ == "__main__":
    main()
