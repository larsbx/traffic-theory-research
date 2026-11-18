#!/usr/bin/env python3
"""Exhaust every 4x4 initial state for the specified one-round capture event.

This is a one-step event census, not a 4x4 eventual-basin census. Counts and
exact product-law weights are compared with the transfer formula. Every state
also checks the local initial predicate against the actual two-phase kernel.
"""
from __future__ import annotations

import argparse
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

from bml.exhaustive import decode  # noqa: E402
from bml.formation import (  # noqa: E402
    geometric_formation_upper_bound, mixed_formation_upper_bound,
    staircase_capture_lower_bound, staircase_one_round_probability,
)
from bml.model import step  # noqa: E402

SOURCE_PATHS = (
    "bml/formation.py", "bml/model.py", "bml/exhaustive.py", "bml/probability.py",
    "scripts/check_formation.py", "tests/test_formation.py", "requirements-dev.txt",
    "formal/lean/BML/Formation.lean", "formal/lean/BML.lean", "formal/lean/Audit.lean",
    "docs/research/2026-11-18-fixed-density-formation.md",
)
EXPECTED_BEFORE = [0, 0, 0, 0, 0, 0, 0, 0, 1, 16, 112, 448, 1120, 1792, 1792, 1024, 256]
EXPECTED_AFTER = [0, 0, 0, 0, 0, 0, 0, 0, 81, 792, 3272, 7568, 10800, 9792, 5536, 1792, 256]


def hashes():
    return {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in SOURCE_PATHS}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    started = perf_counter()
    before_hashes = hashes()
    side, size, chunk = 4, 3 ** 16, 1 << 18
    y = np.arange(side)
    before, after = np.zeros(17, dtype=np.int64), np.zeros(17, dtype=np.int64)
    east_at_origin = north_at_origin = 0
    first_new = None
    for lo in range(0, size, chunk):
        states = decode(np.arange(lo, min(lo + chunk, size), dtype=np.int64), side, side)
        evolved, _ = step(states)
        cars = np.count_nonzero(states, axis=(1, 2))
        initial = (states[:, y, y] == 1).all(axis=1) & (states[:, y, (y + 1) % side] == 2).all(axis=1)
        target = (evolved[:, y, y] == 1).all(axis=1) & (evolved[:, y, (y + 1) % side] == 2).all(axis=1)
        a, b, c = states[:, y, (y - 1) % side], states[:, y, y], states[:, y, (y + 1) % side]
        d, q = states[:, (y - 1) % side, (y + 1) % side], states[:, y, (y + 2) % side]
        east = ((b == 1) & (c != 0)) | ((b == 0) & (a == 1))
        north = (c == 2) | ((d == 2) & (((c == 0) & (b != 1)) | ((c == 1) & (q == 0))))
        if not np.array_equal(target, (east & north).all(axis=1)):
            raise AssertionError("the local initial predicate disagrees with the actual full round")
        if np.any(initial & ~target):
            raise AssertionError("a specified mixed cycle did not persist")
        rings = (states == 1).all(axis=2).any(axis=1) | (states == 2).all(axis=1).any(axis=1)
        if np.any(rings & target):
            raise AssertionError("the mixed cycle appeared despite an initially full monochromatic lane")
        before += np.bincount(cars[initial], minlength=17)
        after += np.bincount(cars[target], minlength=17)
        east_at_origin += int((evolved[:, 0, 0] == 1).sum())
        north_at_origin += int((evolved[:, 0, 0] == 2).sum())
        if first_new is None and np.any(target & ~initial):
            i = int(np.flatnonzero(target & ~initial)[0])
            first_new = {"code": lo + i, "initial_rows": states[i].tolist(), "after_rows": evolved[i].tolist()}
        if lo % (chunk * 32) == 0:
            print(f"CLASSIC one-round staircase: {lo:,}/{size:,} states", flush=True)
    if before.tolist() != EXPECTED_BEFORE or after.tolist() != EXPECTED_AFTER:
        raise AssertionError("pinned exact event counts changed")
    if east_at_origin != size // 3 or north_at_origin != size // 3:
        raise AssertionError("the evolved one-site marginals changed under the uniform initial law")
    if before.sum() == after.sum():
        raise AssertionError("the evolved-iid negative control was not rejected")

    evaluations = []
    for p in (Fraction(0), Fraction(1, 5), Fraction(1, 2), Fraction(2, 3), Fraction(9, 10), Fraction(1)):
        weights = [(p / 2) ** n * (1 - p) ** (16 - n) for n in range(17)]
        initial = sum(int(count) * weight for count, weight in zip(before, weights))
        evolved = sum(int(count) * weight for count, weight in zip(after, weights))
        if initial != (p / 2) ** 8 or evolved != staircase_one_round_probability(4, p):
            raise AssertionError("initial-law integration disagrees with the exact transfer trace")
        evaluations.append({"p": str(p), "initial_specified_cycle": str(initial),
                            "one_round_specified_cycle": str(evolved),
                            "probability_ratio": str(evolved / initial) if initial else None})
    bounds = []
    for side in (4, 8, 16):
        for p in (Fraction(1, 5), Fraction(1, 2), Fraction(9, 10)):
            bounds.append({"side": side, "p": str(p),
                           "one_round_capture_lower": str(staircase_capture_lower_bound(side, p)),
                           "initial_any_mixed_upper": str(mixed_formation_upper_bound(side, p)),
                           "round_one_any_mixed_upper": str(mixed_formation_upper_bound(side, p, 1)),
                           "round_one_geometric_upper": str(geometric_formation_upper_bound(side, p, 1))})
    after_hashes = hashes()
    if before_hashes != after_hashes:
        raise AssertionError("sources changed during the census")
    report = {
        "scope": "one prescribed winding staircase, one CLASSIC full round, all 4x4 initial states",
        "states": size, "pointwise_preimage_checks": size, "rule": "classic east then north",
        "counts_by_cars_initial": before.tolist(), "counts_by_cars_one_round": after.tolist(),
        "initial_count": int(before.sum()), "one_round_count": int(after.sum()),
        "evolved_uniform_one_site_species_counts": [east_at_origin, north_at_origin],
        "exact_iid_evaluations": evaluations, "finite_bounds": bounds,
        "new_specified_cycle_witness": first_new,
        "negative_control_evolved_iid": "rejected: 6561 initial versus 39889 one-round target states",
        "runtime": {"python": platform.python_version(), "numpy": np.__version__},
        "source_sha256_before": before_hashes, "source_sha256_after": after_hashes,
        "seconds": round(perf_counter() - started, 6),
        "not_established": ["a positive nonjamming interval", "eventual-basin enumeration on 4x4",
                            "a positive or sharp critical density", "asymptotic probability proofs in Lean"],
    }
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Verified {size:,} states: initial={before.sum()}, one-round={after.sum()}; all exact weights match.")


if __name__ == "__main__":
    main()
