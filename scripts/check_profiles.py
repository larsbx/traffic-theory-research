#!/usr/bin/env python3
"""Reproduce prescribed-profile jams and exact certificate-acceptance bounds.

The profile census calls the public verifier on every constructed witness and
independently replays its tagged fixed point. The separate initial-state census
checks the sufficient-condition failure probability and the shared-cell pair
law. These are not measurements or bounds of eventual gridlock probability.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
from itertools import product
import json
from math import comb
from pathlib import Path
import platform
import sys
from time import perf_counter

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from bml.certificates import trace_labeled  # noqa: E402
from bml.model import TRAIN  # noqa: E402
from bml.profiles import (  # noqa: E402
    admissible_profile_count, construct_jam_profile, is_constructible_profile,
    profile_certificate_bounds, profile_pair_overflow_probability,
    verify_jam_profile,
)


PROFILE_DOMAINS = ((2, 1), (3, 15), (4, 386), (5, 16090))
INITIAL_SIDES = (1, 2, 3)
DENSITIES = (Fraction(0), Fraction(1, 5), Fraction(1, 2), Fraction(2, 3), Fraction(1))
SOURCE_PATHS = (
    "bml/__init__.py", "bml/profiles.py", "bml/probability.py", "bml/capture.py",
    "bml/certificates.py", "bml/exhaustive.py", "bml/model.py",
    "tests/test_profiles.py", "scripts/check_profiles.py", "requirements-dev.txt",
)


def source_hashes() -> dict[str, str]:
    return {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
            for path in SOURCE_PATHS}


def check_witness(east: tuple[int, ...], north: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    rows = construct_jam_profile(east, north)
    verify_jam_profile(rows, east, north)
    orbit = trace_labeled(rows, max_steps=1)
    if (orbit.cycle_start != 0 or orbit.period != 1 or orbit.moved != ((),)
            or tuple(map(tuple, orbit.rows(0))) != rows):
        raise AssertionError("the independent tagged replay did not certify a zero-move fixed point")
    if not is_constructible_profile(east, north):
        raise AssertionError("an enumerated admissible profile was rejected")
    return rows


def check_profile_side(side: int, expected: int) -> dict:
    start = perf_counter()
    count = 0
    for east in product(range(1, side), repeat=side):
        for north in product(range(1, side - max(east) + 1), repeat=side):
            check_witness(east, north)
            count += 1
    if count != expected or count != admissible_profile_count(side):
        raise AssertionError("the exhaustive ordered profile count changed")
    print(f"CLASSIC profiles L={side}: {count} exact jam witnesses", flush=True)
    return {
        "side": side, "ordered_profile_pairs": count,
        "public_actual_kernel_verifier_calls": count,
        "independent_tagged_fixed_point_checks": count,
        "seconds": round(perf_counter() - start, 6),
    }


def integrate(counts: list[int], p: Fraction, cells: int) -> Fraction:
    return sum((count * (p / 2) ** n * (1 - p) ** (cells - n)
                for n, count in enumerate(counts)), Fraction())


def binomial_mass(trials: int, chance: Fraction, value: int) -> Fraction:
    if not 0 <= value <= trials:
        return Fraction()
    return comb(trials, value) * chance ** value * (1 - chance) ** (trials - value)


def check_initial_side(side: int) -> dict:
    start = perf_counter()
    cells = side * side
    all_counts = [0] * (cells + 1)
    failure_counts = [0] * (cells + 1)
    pair_counts = [[0] * (cells + 1) for _ in range(2 * side + 1)]
    for flat in product(range(3), repeat=cells):
        east = tuple(sum(flat[y * side + x] == 1 for x in range(side)) for y in range(side))
        north = tuple(sum(flat[y * side + x] == 2 for y in range(side)) for x in range(side))
        cars = sum(east) + sum(north)
        admissible = min(east) >= 1 and min(north) >= 1 and max(east) + max(north) <= side
        if admissible != is_constructible_profile(east, north):
            raise AssertionError("the initial-state profile predicate disagrees with direct counting")
        all_counts[cars] += 1
        failure_counts[cars] += int(not admissible)
        pair_counts[east[0] + north[0]][cars] += 1
    if all_counts != [comb(cells, n) * 2 ** n for n in range(cells + 1)]:
        raise AssertionError("the initial-state census is incomplete")

    evaluations = []
    pair_mass_checks = 0
    for p in DENSITIES:
        bounds = profile_certificate_bounds(side, p)
        actual_failure = integrate(failure_counts, p, cells)
        if not (0 <= actual_failure <= bounds.cutoff_upper_bound <= 1
                and actual_failure <= bounds.pair_upper_bound <= 1):
            raise AssertionError("a certificate barrier bound is below the exact failure probability")
        actual_pair = [integrate(counts, p, cells) for counts in pair_counts]
        expected_pair = [
            (1 - p) * binomial_mass(2 * side - 2, p / 2, value)
            + p * binomial_mass(2 * side - 2, p / 2, value - 1)
            for value in range(2 * side + 1)
        ]
        if actual_pair != expected_pair or sum(actual_pair) != 1:
            raise AssertionError("the complete shared-cell pair law disagrees with initial-state weights")
        pair_mass_checks += len(actual_pair)
        overflow = sum(actual_pair[side + 1:], Fraction())
        if (overflow != bounds.pair_overflow_probability
                or overflow != profile_pair_overflow_probability(side, p)):
            raise AssertionError("the exact shared-cell pair overflow is incorrect")
        evaluations.append({
            "p": str(p), "inadmissible_profile_probability": str(actual_failure),
            "cutoff_upper_bound": str(bounds.cutoff_upper_bound),
            "pair_upper_bound": str(bounds.pair_upper_bound),
            "best_upper_bound": str(bounds.best_upper_bound),
            "pair_overflow_probability": str(overflow),
            "specified_pair_distribution": list(map(str, actual_pair)),
        })
    states = sum(all_counts)
    print(f"CLASSIC profile law L={side}: {states} initial states", flush=True)
    return {
        "side": side, "initial_states": states,
        "admissible_initial_states": states - sum(failure_counts),
        "inadmissible_counts_by_cars": failure_counts,
        "specified_pair_counts_by_value_then_cars": pair_counts,
        "exact_density_evaluations": evaluations,
        "individual_pair_mass_checks": pair_mass_checks,
        "seconds": round(perf_counter() - start, 6),
    }


def reject(operation, label: str) -> str:
    try:
        operation()
    except ValueError:
        return "rejected"
    raise AssertionError(f"negative control accepted: {label}")


def check_controls() -> dict:
    free_rows = ((2, 1, 0), (1, 0, 2), (0, 2, 1))
    free_orbit = trace_labeled(free_rows, max_steps=10)
    if free_orbit.cycle_start != 0 or not all(len(moved) == 6 for moved in free_orbit.moved):
        raise AssertionError("the same-profile moving control changed")
    nonuniform = construct_jam_profile((1, 2, 3, 1), (1, 1, 1, 1))
    negative = {
        "same_profile_moving_board": reject(
            lambda: verify_jam_profile(free_rows, (1, 1, 1), (1, 1, 1)), "moving board"),
        "stale_exact_profile": reject(
            lambda: verify_jam_profile(nonuniform, (3, 2, 1, 1), (1, 1, 1, 1)), "stale profile"),
        "boolean_profile": reject(
            lambda: construct_jam_profile((1, True), (1, 1)), "boolean profile"),
        "malformed_profile": reject(
            lambda: construct_jam_profile(None, (1, 1)), "malformed profile"),
        "zero_lane": reject(
            lambda: construct_jam_profile((0, 1), (1, 1)), "positivity"),
        "excess_maximum_sum": reject(
            lambda: construct_jam_profile((2, 2, 2), (2, 2, 2)), "maximum sum"),
        "TRAIN_constructor": reject(
            lambda: construct_jam_profile((1, 1), (1, 1), rule=TRAIN), "TRAIN constructor"),
        "TRAIN_probability": reject(
            lambda: profile_certificate_bounds(2, Fraction(1, 2), rule=TRAIN), "TRAIN probability"),
        "floating_density": reject(
            lambda: profile_certificate_bounds(3, 0.5), "floating density"),
    }
    correct = profile_pair_overflow_probability(3, Fraction(1, 2))
    false_independence = sum((binomial_mass(6, Fraction(1, 4), n) for n in range(4, 7)), Fraction())
    if correct != Fraction(7, 256) or false_independence != Fraction(77, 2048) or correct == false_independence:
        raise AssertionError("the negative control did not distinguish the false independent shared-cell model")
    bounds = profile_certificate_bounds(64, Fraction(1, 2))
    if not (bounds.pair_upper_bound < Fraction(1, 100000)
            and bounds.cutoff_upper_bound > Fraction(1, 10000)):
        raise AssertionError("the strict finite pair-bound improvement changed")
    return {
        "negative_API_controls": negative,
        "same_profile_moving_board": {
            "rows": free_rows, "labeled_period": free_orbit.period,
            "moves_per_full_round": [len(moved) for moved in free_orbit.moved],
        },
        "false_independence_control": {
            "side": 3, "p": "1/2", "correct_shared_cell_tail": str(correct),
            "incorrect_Bin_2L_tail": str(false_independence), "status": "distinguished",
        },
        "strict_finite_bound_comparison": {
            "side": 64, "p": "1/2", "cutoff_exact": str(bounds.cutoff_upper_bound),
            "pair_exact": str(bounds.pair_upper_bound),
            "cutoff_decimal": float(bounds.cutoff_upper_bound),
            "pair_decimal": float(bounds.pair_upper_bound),
            "pair_lt_1_over_100000_and_cutoff_gt_1_over_10000": True,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    started = perf_counter()
    before = source_hashes()
    profile_scopes = [check_profile_side(side, count) for side, count in PROFILE_DOMAINS]
    targeted = []
    for side in (8, 16, 31):
        for east_cap in (1, side // 2, side - 1):
            east = tuple(1 + y % east_cap for y in range(side))
            north = tuple(1 + x % (side - east_cap) for x in range(side))
            rows = check_witness(east, north)
            targeted.append({
                "side": side, "east_cap": east_cap,
                "east_rows": east, "north_columns": north,
                "grid_sha256": hashlib.sha256(json.dumps(rows, separators=(",", ":")).encode()).hexdigest(),
            })
    initial_scopes = [check_initial_side(side) for side in INITIAL_SIDES]
    controls = check_controls()
    after = source_hashes()
    if before != after:
        raise AssertionError("source files changed during the profile validation")
    profile_total = sum(scope["ordered_profile_pairs"] for scope in profile_scopes)
    initial_total = sum(scope["initial_states"] for scope in initial_scopes)
    if profile_total != 16492 or initial_total != 19767 or len(targeted) != 9:
        raise AssertionError("the advertised exhaustive and targeted scopes changed")
    report = {
        "schema": "bml.profiles-replay.v1", "status": "passed", "rule": "classic",
        "runtime": {"python": platform.python_version(), "numpy": np.__version__,
                    "seconds": round(perf_counter() - started, 6)},
        "source_sha256_before": before, "source_sha256_after": after,
        "exhaustive_profile_domains": profile_scopes,
        "exhaustive_ordered_profile_pairs": profile_total,
        "targeted_larger_profiles": targeted,
        "targeted_larger_profile_count": len(targeted),
        "public_actual_kernel_verifier_calls": profile_total + len(targeted),
        "independent_tagged_fixed_point_checks": profile_total + len(targeted),
        "initial_state_domains": initial_scopes,
        "exhaustive_initial_states": initial_total,
        "exact_density_evaluations": len(INITIAL_SIDES) * len(DENSITIES),
        "individual_shared_pair_mass_checks": sum(scope["individual_pair_mass_checks"] for scope in initial_scopes),
        "controls": controls,
        "scope": (
            "Every admissible positive ordered profile pair on sides 2 through 5 is constructed, "
            "bound to exact numerical lane counts by the public production-half-step verifier, "
            "and independently replayed as a zero-move labeled fixed point. Nine larger profiles "
            "are targeted checks, not exhaustive domains. Complete initial-state spaces on sides "
            "1 through 3 check the initial-iid sufficient-condition failure probability and the "
            "shared-cell pair law at five exact densities. The probability upper bounds concern "
            "acceptance of universally sound lane-count-only nonjamming certificates, not actual "
            "eventual gridlock probability. Universal construction and asymptotic claims have "
            "separate Lean/prose proofs; no fixed positive critical density is established."
        ),
    }
    print(json.dumps({key: report[key] for key in (
        "schema", "status", "exhaustive_ordered_profile_pairs", "targeted_larger_profile_count",
        "exhaustive_initial_states", "exact_density_evaluations", "individual_shared_pair_mass_checks",
    )}, sort_keys=True))
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
