#!/usr/bin/env python3
"""Reproduce disjoint-strip capacity certificates and exact initial-iid bounds.

Every state of the listed tori is checked against the complete eventual-basin
classifier. For each width and canonical partition, the three exact marginal
laws are independently integrated from the enumerated initial configurations.
The public certificate verifier and strict-improvement examples are separate
controls; the census is not counted as calls to that verifier.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, replace
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import platform
import sys
from time import perf_counter

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from bml.capacity import (  # noqa: E402
    capacity_bound_terms, capacity_upper_bound,
    make_capacity_certificate, verify_capacity_certificate,
)
from bml.exhaustive import JAM, classify_all, decode  # noqa: E402
from bml.model import TRAIN, step  # noqa: E402
from bml.probability import make_strip_certificate, strip_upper_bound  # noqa: E402


DOMAINS = ((2, 2), (3, 2), (2, 3), (4, 2), (2, 4), (3, 3), (4, 3))
DENSITIES = (Fraction(0), Fraction(1, 7), Fraction(1, 2), Fraction(2, 3), Fraction(1))
SOURCE_PATHS = (
    "bml/capacity.py", "bml/probability.py", "bml/certificates.py",
    "bml/exhaustive.py", "bml/model.py", "tests/test_capacity.py",
    "scripts/check_capacity.py", "requirements-dev.txt",
)


def integrated(counts: np.ndarray, p: Fraction, cells: int) -> Fraction:
    return sum((int(count) * (p / 2) ** n * (1 - p) ** (cells - n)
                for n, count in enumerate(counts)), Fraction())


def check_shape(width: int, height: int) -> dict:
    start = perf_counter()
    cells = width * height
    size = 3 ** cells
    states = decode(np.arange(size), height, width)
    classification = classify_all(height, width)
    jam = classification.cls == JAM
    cars = (states != 0).sum(axis=(1, 2))
    east_rows = (states == 1).sum(axis=2)
    north_columns = (states == 2).sum(axis=1)
    full_north = (north_columns == height).any(axis=1)

    def coefficients(mask: np.ndarray) -> np.ndarray:
        return np.bincount(cars[mask], minlength=cells + 1)

    jam_counts = coefficients(jam)
    full_north_counts = coefficients(full_north)
    capacity_union = np.zeros(size, dtype=bool)
    single_union = np.zeros(size, dtype=bool)
    widths = []
    marginal_checks = 0
    for k in range(1, width + 1):
        capacity = (east_rows // k).sum(axis=1)
        offset_counts = []
        for offset in range(width):
            supply = np.zeros(size, dtype=int)
            for j in range(width // k):
                columns = [(offset + j * k + i) % width for i in range(k)]
                supply += (north_columns[:, columns] == 0).all(axis=1)
            certified = (supply > capacity) & ~full_north
            if np.any(certified & jam):
                raise AssertionError(f"{width}x{height}: capacity certificate admitted a jam basin")
            capacity_union |= certified
            # The first block starts at this offset, so cycling offsets covers
            # every single strip of this width, including those that wrap.
            single_columns = [(offset + i) % width for i in range(k)]
            single_union |= ((north_columns[:, single_columns] == 0).all(axis=1)
                             & (east_rows.max(axis=1) < k) & ~full_north)
            offset_counts.append(int(certified.sum()))
            if offset == 0:
                canonical_supply = supply.copy()
        evaluations = []
        for threshold in range(1, width // k + 1):
            term_counts = (
                coefficients(capacity >= threshold),
                coefficients(canonical_supply < threshold), full_north_counts,
            )
            for p in DENSITIES:
                direct = tuple(integrated(counts, p, cells) for counts in term_counts)
                terms = capacity_bound_terms(width, height, p, k, threshold)
                if terms != direct:
                    raise AssertionError("exact marginal law disagrees with direct initial-state weights")
                bound = capacity_upper_bound(width, height, p, k, threshold)
                if integrated(jam_counts, p, cells) > bound:
                    raise AssertionError("the finite eventual gridlock probability exceeds the bound")
                marginal_checks += 3
                evaluations.append({
                    "threshold": threshold, "p": str(p),
                    "capacity_tail": str(terms[0]), "strip_supply_lower_tail": str(terms[1]),
                    "full_north_column": str(terms[2]), "gridlock_upper_bound": str(bound),
                })
        widths.append({"k": k, "certified_by_offset": offset_counts, "iid_checks": evaluations})
    if np.any(single_union & ~capacity_union):
        raise AssertionError("disjoint-strip certificates lost a single-strip certificate")
    result = {
        "width": width, "height": height, "states": size,
        "partition_predicate_checks": size * width * width,
        "exact_marginal_checks": marginal_checks,
        "capacity_certified_union": int(capacity_union.sum()),
        "single_strip_certified_union": int(single_union.sum()),
        "additional_certified_states": int((capacity_union & ~single_union).sum()),
        "widths": widths, "seconds": round(perf_counter() - start, 6),
    }
    print(f"CLASSIC capacity {width}x{height}: {size} states; "
          f"certified={result['capacity_certified_union']}; "
          f"additional={result['additional_certified_states']}", flush=True)
    return result


def reject(operation, label: str) -> str:
    try:
        operation()
    except ValueError:
        return "rejected"
    raise AssertionError(f"negative control accepted: {label}")


def controls() -> dict:
    rows = [[0] * 8 for _ in range(8)]
    for y in range(8):
        rows[y][0] = 1
    rows[0][1] = 1
    for x, ys in ((2, (0, 1)), (3, (2, 3)), (6, (4, 5)), (7, (6, 7))):
        for y in ys:
            rows[y][x] = 2
    certificate = make_capacity_certificate(rows, 2)
    if certificate.starts != (0, 4) or sum(n // 2 for n in certificate.east_rows) != 1:
        raise AssertionError("the strict deterministic capacity example changed")
    single_rejections = 0
    dual = [[{0: 0, 1: 2, 2: 1}[rows[x][y]] for x in range(8)] for y in range(8)]
    for board in (rows, dual):
        for k in range(1, 9):
            for start in range(8):
                reject(lambda: make_strip_certificate(board, start, k), "single-strip insufficiency")
                single_rejections += 1
    state = np.array(rows, dtype=np.int8)
    for _ in range(24):
        verify_capacity_certificate(state.tolist(), certificate)
        state, _ = step(state)
    negative = {
        "overlapping_strips": reject(
            lambda: verify_capacity_certificate(rows, replace(certificate, starts=(0, 0))), "overlap"),
        "stale_profile": reject(
            lambda: verify_capacity_certificate(rows, replace(certificate, east_rows=(1,) * 8)), "profile"),
        "capacity_equality": reject(
            lambda: verify_capacity_certificate(rows, replace(certificate, starts=(0,))), "equality"),
        "full_north_column": reject(
            lambda: make_capacity_certificate([[2, 0], [2, 0]], 1), "full north"),
        "TRAIN_rule": reject(
            lambda: capacity_upper_bound(2, 2, Fraction(1, 2), 1, 1, rule=TRAIN), "TRAIN"),
    }
    return {"strict_example_rows": rows, "certificate": asdict(certificate),
            "single_strip_rejections_in_both_orientations": single_rejections,
            "successive_profile_rechecks": 24, "negative_controls": negative}


def improvement(side: int, p: Fraction, expected: tuple[int, int]) -> dict:
    candidates = [(capacity_upper_bound(side, side, p, k, threshold), k, threshold)
                  for k in range(1, side + 1) for threshold in range(1, side // k + 1)]
    best = min(candidates)
    one = min(item for item in candidates if item[2] == 1)
    old = min((strip_upper_bound(side, side, p, k), k) for k in range(1, side + 1))
    if not best[0] < one[0] < old[0] or best[1:] != expected:
        raise AssertionError("the exact optimized improvement changed")
    return {
        "side": side, "p": str(p), "all_k_and_thresholds_checked": len(candidates),
        "capacity": {"k": best[1], "threshold": best[2], "exact": str(best[0]), "decimal": float(best[0])},
        "threshold_one": {"k": one[1], "exact": str(one[0]), "decimal": float(one[0])},
        "original_strip": {"k": old[1], "exact": str(old[0]), "decimal": float(old[0])},
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    source_before = {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in SOURCE_PATHS}
    scopes = [check_shape(width, height) for width, height in DOMAINS]
    report = {
        "schema": "bml.capacity-replay.v1", "status": "passed", "rule": "classic",
        "runtime": {"python": platform.python_version(), "numpy": np.__version__},
        "source_sha256": source_before,
        "rectangles": scopes, "exhaustive_states": sum(row["states"] for row in scopes),
        "partition_predicate_checks": sum(row["partition_predicate_checks"] for row in scopes),
        "exact_marginal_checks": sum(row["exact_marginal_checks"] for row in scopes),
        "additional_certified_states": sum(row["additional_certified_states"] for row in scopes),
        "controls": controls(),
        "optimized_examples": [improvement(8, Fraction(1, 40), (1, 5)),
                               improvement(12, Fraction(1, 18), (2, 2))],
        "scope": (
            "Complete finite basin and marginal-law checks on the seven listed domains. "
            "Public certificate controls are separate from vectorized census predicates. "
            "Universal geometry and asymptotic statements have separate prose proofs; "
            "no unrestricted source refinement, Lean capacity theorem, or fixed positive "
            "critical-density result is claimed."
        ),
    }
    source_after = {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in SOURCE_PATHS}
    if source_before != source_after:
        raise AssertionError("source files changed during capacity validation")
    print(json.dumps({key: report[key] for key in (
        "schema", "status", "exhaustive_states", "partition_predicate_checks",
        "exact_marginal_checks", "additional_certified_states",
    )}, sort_keys=True))
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
