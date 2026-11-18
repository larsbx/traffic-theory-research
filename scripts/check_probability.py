#!/usr/bin/env python3
"""Reproduce exact finite iid basin counts and conserved-lane probability bounds.

The seven advertised domains are complete. Mixed-cycle targets are detected
directly before reachability is propagated through each functional graph.
Every k-column strip predicate is checked against the eventual gridlock mask;
individual public certificate-verifier controls are recorded separately.
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
from unittest.mock import patch

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from bml import probability  # noqa: E402
from bml.capture import find_blocker_cycles, trace_capture  # noqa: E402
from bml.certificates import trace_labeled  # noqa: E402
from bml.model import TRAIN  # noqa: E402
from bml.probability import (  # noqa: E402
    EventCounts, NorthEmptyStrip, analyze_torus, has_full_lane, make_strip_certificate,
    ring_probability, strip_upper_bound, verify_strip_certificate,
)


# Ordered (width, height); north increases row index and east moves first.
DOMAINS = ((2, 2), (3, 2), (2, 3), (4, 2), (2, 4), (3, 3), (4, 3))
DENSITIES = (Fraction(0), Fraction(1, 7), Fraction(1, 2), Fraction(2, 3), Fraction(1))
SOURCE_PATHS = (
    "bml/probability.py", "bml/capture.py", "bml/certificates.py", "bml/exhaustive.py",
    "bml/model.py", "tests/test_probability.py", "scripts/check_probability.py",
    "requirements-dev.txt",
)


def source_hashes() -> dict[str, str]:
    return {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in SOURCE_PATHS}


def check_shape(width: int, height: int) -> tuple[dict, probability.FiniteCensus]:
    start = perf_counter()
    census = analyze_torus(width, height)
    j = census.event("gridlock")
    m = census.event("eventual_mixed")
    r = census.event("full_lane")
    evaluations = []
    for p in DENSITIES:
        pj, pm, pr = j.probability(p), m.probability(p), r.probability(p)
        ring = ring_probability(width, height, p)
        strip_bounds = [strip_upper_bound(width, height, p, k) for k in range(1, width + 1)]
        if pr != ring or not 0 <= pj - pm <= ring or any(pj > bound for bound in strip_bounds):
            raise AssertionError(f"{width}x{height}: exact iid bound or ring probability failed at {p}")
        if pm != census.event("ringless_gridlock").probability(p):
            raise AssertionError("mixed and ringless-gridlock probability identity failed")
        if p == Fraction(2, 3) and any(
            event.probability(p) != Fraction(event.total, census.states) for event in census.events
        ):
            raise AssertionError("the uniform ternary law disagrees with exact counts")
        evaluations.append({
            "p": str(p), "gridlock": str(pj), "eventual_mixed": str(pm),
            "full_lane_exact": str(pr), "gridlock_minus_mixed": str(pj - pm),
            "clamped_strip_upper_bounds_by_k": [str(bound) for bound in strip_bounds],
        })
    scope = {
        "width": width, "height": height, "states": census.states,
        "pointwise_identity_checks": census.states,
        "vectorized_strip_predicate_checks": width * census.states,
        "strip_certified_by_k": list(census.strip_certified_by_k),
        "strip_certified_union": census.strip_certified_union,
        "events": {
            event.name: {
                "total": event.total, "counts_by_cars": list(event.by_cars),
                "bernstein_coefficients": [str(coefficient) for coefficient in event.coefficients],
                "bernstein_coefficients_nondecreasing": event.coefficients_nondecreasing,
            }
            for event in census.events
        },
        "exact_iid_evaluations": evaluations,
        "seconds": round(perf_counter() - start, 6),
    }
    print(f"CLASSIC iid {width}x{height}: {census.states} states; J={j.total}, M={m.total}, "
          f"R={r.total}; strip union={census.strip_certified_union}", flush=True)
    return scope, census


def expect_rejection(operation, error_type, label: str) -> str:
    try:
        operation()
    except error_type:
        return "rejected"
    raise AssertionError(f"negative control was accepted: {label}")


def check_controls(square3: probability.FiniteCensus) -> dict:
    before = [[1, 2, 2, 1], [2, 1, 1, 0], [1, 0, 2, 1], [2, 1, 1, 0]]
    after = [[1, 2, 2, 1], [2, 1, 1, 0], [1, 2, 2, 1], [2, 1, 1, 0]]
    jam, flowing = trace_capture(before), trace_capture(after)
    if has_full_lane(before) or has_full_lane(after):
        raise AssertionError("the nonmonotonicity witness is not outside R")
    if (jam.first_mixed_round, jam.gridlock_round) != (2, 3):
        raise AssertionError("the lower-occupancy witness no longer captures")
    if (flowing.outcome, flowing.first_core_round, flowing.cycle_start,
            flowing.period, flowing.cycle_move_count) != ("intermediate", None, 2, 8, 28):
        raise AssertionError("the added-car witness no longer has its exact moving cycle")
    tagged_before, tagged_after = trace_labeled(before), trace_labeled(after)
    if ((tagged_before.cycle_start, tagged_before.period) != (3, 1)
            or tagged_before.moved[-1] != ()
            or (tagged_after.cycle_start, tagged_after.period) != (2, 16)
            or any(tagged_after.cycle_moves(label) != 4 for label, _ in tagged_after.species)
            or any(find_blocker_cycles(tagged_after.rows(index)) for index in range(len(tagged_after.states)))):
        raise AssertionError("independent labeled replay disagrees with the witness")
    mixed = square3.event("eventual_mixed")
    initial = square3.event("initial_mixed")
    if (mixed.derivative(1) != Fraction(-279, 256)
            or mixed.probability(Fraction(99, 100)) <= mixed.probability(1)
            or initial.total != 573 or mixed.total != 3492
            or not square3.event("gridlock").coefficients_nondecreasing):
        raise AssertionError("a pinned finite iid probability fact changed")

    # These exercise the public certificate checker individually. They are not
    # counted as 565,785 calls to it: the complete census uses equivalent lane
    # predicates in vectorized form and tests them against every eventual basin.
    strip_rows = [[0, 0, 2, 0], [1, 0, 0, 0]]
    certificate = make_strip_certificate(strip_rows, 3, 3)
    verify_strip_certificate(strip_rows, certificate)
    negative = {
        "strip_stale_lane_profile": expect_rejection(
            lambda: verify_strip_certificate(strip_rows, replace(certificate, east_rows=(0, 2))),
            ValueError, "stale lane profile"),
        "strip_omitted_full_north_exclusion": expect_rejection(
            lambda: verify_strip_certificate([[2, 0], [2, 0]], NorthEmptyStrip(2, 2, 1, 1, (0, 0), (2, 0))),
            ValueError, "full north column"),
        "incorrect_event_name": expect_rejection(
            lambda: EventCounts(2, 2, "Gridlock", (0, 0, 4, 8, 16)),
            ValueError, "incorrect event name"),
        "bool_count": expect_rejection(
            lambda: EventCounts(2, 2, "gridlock", (False, 0, 4, 8, 16)),
            ValueError, "bool count"),
        "TRAIN_rule": expect_rejection(
            lambda: ring_probability(2, 2, Fraction(1, 2), rule=TRAIN),
            ValueError, "TRAIN rule"),
    }
    real_reachability = probability.eventually_reaches
    calls = 0

    def initial_only_mixed(successors, targets):
        nonlocal calls
        calls += 1
        return real_reachability(successors, targets) if calls == 1 else targets.copy()

    with patch.object(probability, "eventually_reaches", side_effect=initial_only_mixed):
        negative["initial_mixed_substituted_for_eventual"] = expect_rejection(
            lambda: analyze_torus(3, 2), AssertionError, "initial-only mixed event")
    with patch.object(probability, "find_blocker_cycles", return_value=()):
        negative["direct_mixed_targets_deleted"] = expect_rejection(
            lambda: analyze_torus(2, 2), AssertionError, "deleted mixed targets")
    return {
        "outside_R_nonmonotonicity": {
            "before_rows": before, "after_rows": after, "added_north_at_xy": [1, 2],
            "before": asdict(jam), "after": asdict(flowing),
            "independent_labeled_after_transient": tagged_after.cycle_start,
            "independent_labeled_after_period": tagged_after.period,
            "moves_per_identity_per_labeled_period": 4,
        },
        "square3_mixed_probability_derivative_at_one": str(mixed.derivative(1)),
        "square3_initial_mixed_uniform_probability": str(initial.probability(Fraction(2, 3))),
        "square3_eventual_mixed_uniform_probability": str(mixed.probability(Fraction(2, 3))),
        "individual_strip_verifier_controls": {"accepted": 1, "rejected": 2},
        "negative_controls": negative,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    started = perf_counter()
    before_hashes = source_hashes()
    scopes = []
    square3 = None
    for width, height in DOMAINS:
        scope, census = check_shape(width, height)
        scopes.append(scope)
        if (width, height) == (3, 3):
            square3 = census
    if square3 is None:
        raise AssertionError("the pinned square domain is missing")
    controls = check_controls(square3)
    after_hashes = source_hashes()
    if before_hashes != after_hashes:
        raise AssertionError("source files changed during the probability census")
    states = sum(scope["states"] for scope in scopes)
    if states != 565785:
        raise AssertionError("the advertised enumeration domain changed")
    report = {
        "schema": "bml.probability-census.v1", "status": "passed", "rule": "classic",
        "initial_iid_law": {"empty": "1-p", "east": "p/2", "north": "p/2"},
        "runtime": {"python": platform.python_version(), "numpy": np.__version__,
                    "seconds": round(perf_counter() - started, 6)},
        "source_sha256_before": before_hashes, "source_sha256_after": after_hashes,
        "rectangles": scopes, "exhaustive_states": states,
        "pointwise_M_equals_J_intersect_R_complement_checks": states,
        "vectorized_strip_predicate_checks": sum(scope["vectorized_strip_predicate_checks"] for scope in scopes),
        "controls": controls,
        "scope": (
            "Exact finite initial-iid probabilities. J is fixed-point reachability checked against "
            "the production final-phase classifier; M is direct mixed-cycle detection followed "
            "by independent target reachability, not defined from J and R. Conserved lane counts, "
            "M == J & ~R, and all strip widths are checked pointwise on the listed domains. "
            "The all-width census checks vectorized strip predicates; individual public strip "
            "certificate-verifier controls are reported separately. Supplied count tables receive "
            "arithmetic consistency checks, not automatic authentication as dynamical evidence. "
            "This is not an asymptotic critical-density or sharp-threshold proof, an evolved-iid "
            "assumption, or a TRAIN-rule result."
        ),
    }
    print(json.dumps({key: report[key] for key in (
        "schema", "status", "exhaustive_states", "vectorized_strip_predicate_checks",
    )}, sort_keys=True))
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
