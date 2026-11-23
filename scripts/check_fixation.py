#!/usr/bin/env python3
"""Reproduce the finite CLASSIC tagged-fixation and initial-iid Palm census.

Every initial state on the seven listed tori is followed to exact labeled
recurrence. No timeout is given a final classification. Individual supplied
orbit-verifier controls are reported separately from the trusted-source census.
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

from bml import fixation  # noqa: E402
from bml.certificates import LabeledOrbit, trace_labeled  # noqa: E402
from bml.fixation import (  # noqa: E402
    analyze_fixation, ring_palm_probability, trace_fixation, verify_fixation,
)
from bml.model import TRAIN  # noqa: E402
from bml.probability import ring_probability  # noqa: E402


DOMAINS = ((2, 2), (3, 2), (2, 3), (4, 2), (2, 4), (3, 3), (4, 3))
DENSITIES = (Fraction(1, 7), Fraction(1, 2), Fraction(2, 3), Fraction(1))
SOURCE_PATHS = (
    "bml/fixation.py", "bml/certificates.py", "bml/capture.py", "bml/model.py",
    "bml/exhaustive.py", "bml/probability.py", "tests/test_fixation.py",
    "scripts/check_fixation.py", "requirements-dev.txt",
)


def source_hashes() -> dict[str, str]:
    return {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in SOURCE_PATHS}


def check_shape(width: int, height: int) -> tuple[dict, fixation.FixationCounts]:
    started = perf_counter()
    census = analyze_fixation(width, height)
    counts = census.counts
    tables = {
        "any_stopped": counts.any_stopped_by_cars,
        "gridlock": counts.gridlock_by_cars,
        "full_lane": counts.full_lane_by_cars,
        "partial_fixation": counts.partial_fixation_by_cars,
    }
    evaluations = []
    for p in DENSITIES:
        palm = counts.palm(p)
        ring = counts.event_probability("full_lane", p)
        if (palm.q_car != palm.score_rhs or palm.f != palm.q_car + palm.delta
                or not 0 <= palm.delta <= palm.r_car <= min(1, ring / p)
                or not 0 <= palm.f <= 1 or not 0 <= palm.q_car <= 1
                or palm.covariance_lhs > palm.covariance_rhs):
            raise AssertionError(f"{width}x{height}: a Palm identity or covariance/ring bound failed at {p}")
        if ring != ring_probability(width, height, p) or palm.r_car != ring_palm_probability(width, height, p):
            raise AssertionError("the exact iid full-lane formulas disagree with independent counts")
        if p == Fraction(2, 3):
            if any(counts.event_probability(name, p) != Fraction(sum(table), counts.states)
                   for name, table in tables.items()):
                raise AssertionError("uniform initial ternary weights disagree with the exact census")
        if p == 1 and (palm.f, palm.q, palm.q_car, palm.delta) != (1, 1, 1, 0):
            raise AssertionError("the fully occupied Palm boundary changed")
        evaluations.append({
            **{name: str(value) for name, value in asdict(palm).items()},
            "full_lane_probability": str(ring),
            "full_lane_probability_divided_by_p_clamped": str(min(1, ring / p)),
        })
    scope = {
        "width": width, "height": height, "states": counts.states,
        "events": {name: {"total": sum(table), "counts_by_cars": list(table)}
                   for name, table in tables.items()},
        "stopped_histogram_by_n_then_z": [list(row) for row in counts.stopped_histogram],
        "stopped_tags_by_cars": list(counts.stopped_tags_by_cars),
        "total_stopped_tags_over_initial_states": sum(counts.stopped_tags_by_cars),
        "independent_labeled_edges": census.tagged_edges,
        "max_labeled_period": census.max_labeled_period,
        "max_transient": census.max_transient,
        "outside_ring_intermediate_states_all_tags_positive": census.outside_ring_intermediate,
        "pointwise_S_equals_J_union_R_checks": counts.states,
        "stopped_set_move_position_agreement_checks": counts.states,
        "unresolved_orbits": 0,
        "exact_initial_iid_palm_evaluations": evaluations,
        "seconds": round(perf_counter() - started, 6),
    }
    print(f"CLASSIC fixation {width}x{height}: {counts.states} states; "
          f"S={sum(counts.any_stopped_by_cars)}, J={sum(counts.gridlock_by_cars)}, "
          f"R={sum(counts.full_lane_by_cars)}, partial={sum(counts.partial_fixation_by_cars)}; "
          f"{census.tagged_edges} labeled edges", flush=True)
    return scope, counts


def expect_rejection(operation, error_type, label: str) -> str:
    try:
        operation()
    except error_type:
        return "rejected"
    raise AssertionError(f"negative control accepted: {label}")


def check_controls(square2: fixation.FixationCounts) -> dict:
    rows_by_name = {
        "partial_fixation": [[1, 1], [1, 0]],
        "balanced_partial": [[1, 1, 1], [1, 0, 0], [2, 0, 0], [2, 2, 2]],
        "outside_ring_intermediate": [[1, 2, 2, 1], [2, 1, 1, 0]],
        "outside_ring_slow_car": [[1, 1, 1, 2], [2, 2, 2, 1], [0, 0, 0, 0]],
        "joint_empty_species_lanes": [[1, 1, 2], [2, 0, 1], [2, 0, 0]],
        "east_blocker_changes_species": [[1, 1, 0], [1, 1, 1], [0, 2, 0]],
        "north_target_empty_between_rounds": [[2, 2, 0], [2, 2, 1], [0, 2, 0]],
    }
    summaries = {name: trace_fixation(rows) for name, rows in rows_by_name.items()}
    expected_z = {
        "partial_fixation": 2, "balanced_partial": 7,
        "outside_ring_intermediate": 0, "outside_ring_slow_car": 0,
        "joint_empty_species_lanes": 6, "east_blocker_changes_species": 6,
        "north_target_empty_between_rounds": 6,
    }
    if any(summaries[name].stopped_count != z for name, z in expected_z.items()):
        raise AssertionError("a pinned independent fixation control changed")
    if (not summaries["partial_fixation"].partial_fixation
            or summaries["outside_ring_intermediate"].full_lane
            or min(speed for _, speed in summaries["outside_ring_slow_car"].speeds) != Fraction(1, 9)):
        raise AssertionError("partial fixation and outside-ring motion controls disagree")
    north = trace_labeled(rows_by_name["north_target_empty_between_rounds"])
    if north.states[1][3] != -1 or any(0 in edge for edge in north.moved):
        raise AssertionError("the phase-aware north blocker control changed")

    missing_car_rows = [[1, 1, 2], [2, 0, 1], [2, 1, 0]]
    missing_car_orbit = trace_labeled([[1, 1, 2], [2, 0, 1], [2, 0, 0]])
    train_orbit = LabeledOrbit(1, 3, ((0, 1), (1, 1)),
                               ((0, 1, -1), (-1, 0, 1), (1, -1, 0)),
                               ((0, 1), (0, 1), (0, 1)), 0)
    negative = {
        "missing_input_identity": expect_rejection(
            lambda: verify_fixation(missing_car_rows, missing_car_orbit), ValueError, "missing identity"),
        "train_style_following_under_classic": expect_rejection(
            lambda: verify_fixation([[1, 1, 0]], train_orbit), ValueError, "TRAIN following"),
        "unresolved_cutoff": expect_rejection(
            lambda: trace_fixation([[1, 0, 0]], max_steps=2), ValueError, "unresolved cutoff"),
        "zero_density_Palm": expect_rejection(lambda: square2.palm(0), ValueError, "zero density"),
        "TRAIN_rule": expect_rejection(
            lambda: analyze_fixation(2, 2, rule=TRAIN), ValueError, "TRAIN rule"),
        "bool_histogram_count": expect_rejection(
            lambda: replace(square2, stopped_histogram=((True,),) + square2.stopped_histogram[1:]),
            ValueError, "bool count"),
    }
    # This mutation leaves S=true and J=false, but falsely adds a stopped tag.
    # The independent constant-position check must catch the corrupted Z.
    rows = [[1, 1, 1], [1, 1, 0]]
    original_replayer = fixation.trace_labeled
    original = original_replayer(rows)
    mutant = replace(original, moved=tuple(tuple(label for label in edge if label != 3)
                                           for edge in original.moved))

    def replay_mutant(candidate, **kwargs):
        return mutant if candidate == rows else original_replayer(candidate, **kwargs)

    with patch.object(fixation, "trace_labeled", side_effect=replay_mutant):
        negative["erased_movement_without_changing_S_or_J"] = expect_rejection(
            lambda: analyze_fixation(3, 2), ValueError, "corrupted stopped-tag count")
    palm = square2.palm(Fraction(1, 2))
    if (palm.f, palm.q, palm.q_car, palm.delta) != (
        Fraction(11, 32), Fraction(3, 16), Fraction(9, 32), Fraction(1, 16),
    ):
        raise AssertionError("the pinned distinction between event and Palm probabilities changed")
    singleton = analyze_fixation(1, 1).counts
    if singleton.palm(Fraction(1, 2)).f != 1 or singleton.gridlock_by_cars != (0, 2):
        raise AssertionError("singleton or empty boundaries changed")
    return {
        "explicit_orbits": {name: {"rows": rows_by_name[name], **asdict(summary)}
                            for name, summary in summaries.items()},
        "supplied_orbit_verifier_controls_accepted": len(summaries),
        "supplied_orbit_verifier_controls_rejected": 2,
        "negative_controls": negative,
        "square2_at_half_density": {name: str(value) for name, value in asdict(palm).items()},
        "singleton_control_states": 3,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    started = perf_counter()
    hashes_before = source_hashes()
    scopes = []
    square2 = None
    for width, height in DOMAINS:
        scope, counts = check_shape(width, height)
        scopes.append(scope)
        if (width, height) == (2, 2):
            square2 = counts
    if square2 is None:
        raise AssertionError("the pinned square domain is missing")
    controls = check_controls(square2)
    hashes_after = source_hashes()
    if hashes_before != hashes_after:
        raise AssertionError("source files changed during the fixation census")
    states = sum(scope["states"] for scope in scopes)
    if states != 565785:
        raise AssertionError("the advertised seven-domain census changed")
    report = {
        "schema": "bml.fixation-census.v1", "status": "passed", "rule": "classic",
        "initial_iid_law": {"empty": "1-p", "east": "p/2", "north": "p/2"},
        "Palm_condition": "origin occupied, species averaged; exact rational 0<p<=1",
        "labeled_recurrence_budget_per_orbit": 10000,
        "runtime": {"python": platform.python_version(), "numpy": np.__version__,
                    "seconds": round(perf_counter() - started, 6)},
        "source_sha256_before": hashes_before, "source_sha256_after": hashes_after,
        "rectangles": scopes, "exhaustive_states": states,
        "independent_labeled_edges": sum(scope["independent_labeled_edges"] for scope in scopes),
        "pointwise_S_equals_J_union_R_checks": states,
        "stopped_set_move_position_agreement_checks": states,
        "unresolved_orbits": 0,
        "event_totals": {name: sum(scope["events"][name]["total"] for scope in scopes)
                         for name in fixation.FIXATION_EVENTS},
        "outside_ring_intermediate_states_all_tags_positive": sum(
            scope["outside_ring_intermediate_states_all_tags_positive"] for scope in scopes),
        "controls": controls,
        "scope": (
            "Complete finite census on the seven listed tori. The trusted independent Python "
            "replayer supplies full labeled recurrence; Z is independently read from zero "
            "recurrent moves and constant recurrent identity positions, which must agree. "
            "J and FREE are reconstructed from movements and compared with the production "
            "functional-graph classifier. S=J union R is checked pointwise, not used to define S. "
            "Partial fixation is directly 0<Z<N. Explicit supplied-orbit controls additionally "
            "check all identity edges and production colored transitions; that slower verifier "
            "is not claimed for every census edge. Count metadata is internally checked, not "
            "authenticated as dynamics by construction. Palm weights use only the initial iid "
            "law. Exact finite calculations do not prove the universal fixation theorem, an "
            "asymptotic critical density, sharpness, a positive limiting speed, or TRAIN semantics."
        ),
    }
    print(json.dumps({key: report[key] for key in (
        "schema", "status", "exhaustive_states", "independent_labeled_edges", "event_totals",
    )}, sort_keys=True))
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
