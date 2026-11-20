#!/usr/bin/env python3
"""Reproduce exact finite path/core evidence and conditional population envelopes.

All 81 and 19,683 initial states on 2x2 and 3x3 are checked. Cycle averages are
computed over exact recurrence, then weighted by the INITIAL iid law. Neither
a finite prefix nor the small-board census supplies an asymptotic path bound.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, replace
from fractions import Fraction
import hashlib
import json
from math import comb
from pathlib import Path
import platform
import subprocess
import sys
from time import perf_counter
from unittest.mock import patch

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from bml import path_core  # noqa: E402
from bml.certificates import trace_labeled  # noqa: E402
from bml.model import EAST, NORTH, TRAIN, step  # noqa: E402
from bml.path_core import (  # noqa: E402
    analyze_path_core, core_count, direct_path_count, direct_path_mask,
    maximal_frozen_core, path_mass_gridlock_upper_bound, population_event_upper_bound,
    scalar_path_mask,
)
from bml.probability import has_full_lane, ring_probability  # noqa: E402


DOMAINS = ((2, 2, 1), (3, 3, 2))  # width, height, directed edge count
DENSITIES = (Fraction(0), Fraction(1, 5), Fraction(1, 2), Fraction(2, 3), Fraction(1))
SOURCE_PATHS = (
    "bml/path_core.py", "bml/fixation.py", "bml/certificates.py", "bml/capture.py",
    "bml/probability.py", "bml/exhaustive.py", "bml/model.py", "tests/test_path_core.py",
    "scripts/check_path_core.py", "requirements-dev.txt", "formal/lean/BML/PathCore.lean",
    "formal/lean/BML/Fixation.lean", "formal/lean/BML.lean", "formal/lean/Audit.lean",
    "docs/research/2026-11-19-maximal-core-and-path-mass.md",
)


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def hashes():
    return {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in SOURCE_PATHS}


def check_shape(width, height, steps):
    started = perf_counter()
    census = analyze_path_core(width, height, steps=steps)
    counts = census.counts
    area = width * height
    expected = {
        (2, 2): (81, 49, 177, 0, 28, (0, 0, 8, 40, 64), (0, 0, 4, 8, 16)),
        (3, 3): (19683, 2644, 162141, 5121, 9387,
                 (0, 0, 0, 18, 252, 1530, 7200, 21780, 16614, 4608),
                 (0, 0, 0, 6, 36, 180, 798, 2538, 1881, 512)),
    }[width, height]
    actual = (counts.states, census.colored_cycles, census.tagged_edges,
              census.core_growth_states, census.recurrent_path_nonjam_ringless_states,
              counts.final_core_by_cars, counts.gridlock_by_cars)
    require(actual == expected, "a pinned complete finite path/core census changed")
    values = []
    for p in DENSITIES:
        value = counts.evaluate(p)
        q, core, normalized = value.gridlock_probability, value.final_core_mass, value.normalized_final_core_mass
        require(value.initial_path_mass == p ** (steps + 1), "the initial iid path fixture changed")
        require(value.initial_core_mass <= core <= value.recurrent_path_mass,
                "initial/final core or recurrent path mass inequalities failed")
        require(value.gridlock_root_mass <= core <= normalized,
                "per-site and per-car core normalization inequalities failed")
        require(0 <= normalized - q <= value.full_lane_nonjam_probability <= ring_probability(width, height, p),
                "the normalized final-core error is not covered by the full-lane event")
        require(q <= value.core_population_upper_bound <= value.path_population_upper_bound <= 1,
                "an exact late-time population envelope fails to bound gridlock")
        if p in (0, 1):
            require(q == core == normalized == value.recurrent_path_mass == p,
                    "empty/full density endpoint failed")
        if p == Fraction(2, 3):
            require(q == Fraction(sum(counts.gridlock_by_cars), counts.states),
                    "uniform ternary initial weights disagree with the state census")
        values.append({name: str(number) for name, number in asdict(value).items()})
    if (width, height) == (3, 3):
        require(counts.path_polynomial("initial") == (0, 0, 0, 1, 0, 0, 0, 0, 0, 0),
                "the initial three-vertex path polynomial changed")
        require(counts.path_polynomial("one_round") == (
            0, 0, 0, Fraction(3, 2), Fraction(-9, 16), Fraction(9, 32),
            Fraction(-5, 16), Fraction(3, 32), 0, 0),
            "the exact one-round pushforward polynomial changed")
        half = counts.evaluate(Fraction(1, 2))
        require(half.normalized_final_core_mass == Fraction(476101, 3670016)
                and half.normalized_final_core_mass - half.gridlock_probability == Fraction(122937, 3670016),
                "the normalized final-core control changed")
    scope = {
        "width": width, "height": height, "path_edges": steps, "path_vertices": steps + 1,
        "all_initial_states": counts.states,
        "counts_by_initial_population": {name: [str(x) if isinstance(x, Fraction) else x for x in table]
            for name, table in asdict(counts).items() if name.endswith("_by_cars")},
        "geometry_checks": {
            "path_recurrence_vs_independent_scalar_walk": counts.states,
            "pruned_core_vs_area_edge_path_recurrence": counts.states,
            "pruned_core_vs_area_edge_scalar_walk": counts.states,
            "pruned_core_vs_population_edge_path_recurrence": counts.states,
            "full_round_core_set_inclusions": counts.states,
            "full_round_core_species_persistence": counts.states,
        },
        "cycle_and_identity_checks": {
            "colored_cycles": census.colored_cycles,
            "max_colored_period": census.max_colored_period,
            "max_colored_transient": census.max_colored_transient,
            "independent_labeled_colored_edges": census.tagged_edges,
            "independent_labeled_edges_with_no_core_tag_movement": census.tagged_edges,
            "max_labeled_period": census.max_labeled_period,
            "max_labeled_transient": census.max_labeled_transient,
            "final_core_equals_stopped_original_labels": counts.states,
            "final_core_event_equals_gridlock_or_full_lane": counts.states,
            "colored_vs_labeled_terminal_cycle_path_means": counts.states,
            "colored_vs_labeled_terminal_cycle_fixed_root_means": counts.states,
            "fixed_origin_vs_spatial_average_population_layer_checks": 3 * (area + 1),
            "unresolved_orbits": 0,
        },
        "later_core_growth_initial_states": census.core_growth_states,
        "positive_recurrent_short_path_without_final_core_initial_states": census.recurrent_path_without_core_states,
        "positive_recurrent_short_path_nonjam_ringless_initial_states": census.recurrent_path_nonjam_ringless_states,
        "total_final_core_incidences_over_initial_states": sum(counts.final_core_by_cars),
        "path_mass_polynomials_ascending_p_coefficients": {
            time: [str(x) for x in counts.path_polynomial(time)]
            for time in ("initial", "one_round", "recurrent")},
        "exact_initial_iid_evaluations": values,
        "seconds": round(perf_counter() - started, 6),
    }
    print(f"CLASSIC path/core {width}x{height}: {counts.states:,} initial states, "
          f"{census.colored_cycles:,} colored cycles, {census.tagged_edges:,} independent labeled edges.", flush=True)
    return scope


def check_envelope():
    checks = 0
    for area in range(1, 10):
        for minimum in sorted({1, (area + 1) // 2, area}):
            for p in DENSITIES:
                spent = Fraction()
                budgets = {Fraction(0), Fraction(area + 1)}
                for n in range(minimum, area + 1):
                    cost = n * comb(area, n) * p ** n * (1 - p) ** (area - n)
                    budgets |= {spent, spent + cost / 2, spent + cost}
                    spent += cost
                for budget in sorted(budgets):
                    remaining, primal = budget, Fraction()
                    for n in range(minimum, area + 1):
                        capacity = comb(area, n) * p ** n * (1 - p) ** (area - n)
                        take = min(capacity, remaining / n)
                        primal += take
                        remaining -= n * take
                    dual = population_event_upper_bound(area, p, budget, minimum_population=minimum)
                    require(primal == dual and 0 <= dual <= 1,
                            "population-envelope cutoff minimum disagrees with independent primal filling")
                    checks += 1
    return {"areas": list(range(1, 10)), "densities": [str(p) for p in DENSITIES],
            "minimum_populations": "1, ceiling(area/2), area, with duplicates removed",
            "budgets": "all cumulative population costs, their intervening midpoints, zero, and area+1",
            "exact_primal_dual_comparisons": checks,
            "scope": "sharp population-law relaxation only; BML sharpness is not asserted"}


def check_controls():
    rows = [[NORTH, EAST, EAST], [0, 0, 0], [0, 0, 0]]
    orbit = trace_labeled(rows)
    path_counts = tuple(direct_path_count(orbit.rows(i), 2) for i in range(len(orbit.states)))
    require(orbit.cycle_start == 0 and orbit.period == 8 and path_counts == (1, 0, 1, 0) * 2
            and orbit.rows(0) == orbit.rows(4) and orbit.states[0] != orbit.states[4],
            "the recurrent short-path counterexample changed")
    require(not has_full_lane(rows) and all(orbit.cycle_moves(label) > 0 for label, _ in orbit.species)
            and all(core_count(orbit.rows(i)) == 0 for i in range(orbit.period)),
            "recurrent short paths were incorrectly identified with stopped identities")
    chain = [[EAST, EAST, 0]]
    require(direct_path_count(chain, 0) == 2 and direct_path_count(chain, 1) == 1
            and direct_path_count(chain, 2) == core_count(chain) == 0,
            "the occupied-root or population-edge boundary changed")
    for species in (EAST, NORTH):
        require(direct_path_mask([[species]], 10 ** 30) == scalar_path_mask([[species]], 10 ** 30)
                == maximal_frozen_core([[species]]) == ((True,),), "occupied singleton control failed")
    require(direct_path_count([[0]], 0) == core_count([[0]]) == 0, "empty control failed")
    delayed = []
    for side in (4, 6, 10):
        delay = (side - 2) // 2
        board = np.zeros((side, side), dtype=np.int8)
        for i in range(side):
            require(not board[i, (i - delay) % side] and not board[(i - delay) % side, (i + 1) % side],
                    "delayed staircase sources overlap")
            board[i, (i - delay) % side], board[(i - delay) % side, (i + 1) % side] = EAST, NORTH
        core_sizes, movements = [], []
        for _ in range(delay):
            core_sizes.append(core_count(board.tolist()))
            require(core_sizes[-1] == 0, "a delayed core formed too early")
            board, moved = step(board)
            movements.append(int(moved))
            require(int(moved) == 2 * side, "the delayed-core prefix was not fully moving")
        core_sizes.append(core_count(board.tolist()))
        following, moved = step(board)
        require(core_sizes[-1] == 2 * side and not moved and np.array_equal(board, following),
                "the delayed core did not produce permanent gridlock")
        delayed.append({"side": side, "formation_time": delay, "core_sizes": core_sizes,
                        "moving_prefix_totals": movements})

    rejections = []

    def reject(label, action, error_type=ValueError):
        try:
            action()
        except error_type:
            rejections.append(label)
        else:
            raise AssertionError(f"negative control accepted: {label}")

    reject("TRAIN core", lambda: maximal_frozen_core([[1]], rule=TRAIN))
    reject("floating path bound", lambda: path_mass_gridlock_upper_bound(2, 2, Fraction(1, 2), 0.1))
    reject("floating density", lambda: population_event_upper_bound(4, 0.5, 1))
    reject("negative budget", lambda: population_event_upper_bound(4, Fraction(1, 2), -1))
    reject("bool edge count", lambda: direct_path_mask([[1]], True))
    reject("unresolved recurrence", lambda: analyze_path_core(2, 2, steps=1, max_steps=1))
    original = path_core.classify_all

    def bad_edge(*args, **kwargs):
        classification = original(*args, **kwargs)
        successors = classification.f.copy()
        successors[1] = 1
        return replace(classification, f=successors)

    with patch.object(path_core, "classify_all", side_effect=bad_edge):
        reject("production falsely freezes an isolated car", lambda: analyze_path_core(2, 2, steps=1), AssertionError)
    return {
        "occupied_root_and_population_edge_boundary": {"rows": chain, "population": 2,
                                                        "root_counts_at_edges_0_1_2": [2, 1, 0]},
        "recurrent_short_path_without_fixation": {
            "rows": rows, "path_edges": 2, "colored_period": 4, "labeled_period": orbit.period,
            "path_root_counts": list(path_counts), "mean_roots_per_board": "1/2",
            "spatially_averaged_root_mass": "1/18", "stopped_original_tags": 0,
            "full_lane": False, "gridlock": False},
        "delayed_new_core_family": delayed,
        "singleton_and_empty_controls": 3,
        "rejected_controls": rejections,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    started, before = perf_counter(), hashes()
    domains = [check_shape(*domain) for domain in DOMAINS]
    envelope, controls = check_envelope(), check_controls()
    after = hashes()
    require(before == after, "sources changed during the path/core acceptance run")
    git = subprocess.run(["git", "rev-parse", "HEAD", "HEAD^{tree}"], cwd=ROOT, text=True, capture_output=True)
    revision, tree = git.stdout.splitlines() if git.returncode == 0 else (None, None)
    status = subprocess.run(["git", "status", "--porcelain"], cwd=ROOT, text=True, capture_output=True)
    states = sum(d["all_initial_states"] for d in domains)
    edges = sum(d["cycle_and_identity_checks"]["independent_labeled_colored_edges"] for d in domains)
    require(states == 19764 and edges == 162318, "the declared two-domain scope changed")
    report = {
        "schema": "bml.path-core-census.v1", "status": "passed", "rule": "classic",
        "revision": revision, "tree": tree, "worktree_clean": status.returncode == 0 and not status.stdout,
        "initial_iid_law": {"empty": "1-p", "east": "p/2", "north": "p/2"},
        "path_convention": "steps counts edges, including steps+1 occupied vertices; repeated vertices allowed",
        "path_and_core_root_normalization": "all width*height sites, including holes",
        "normalized_final_core": "E[K_infinity/N] with value zero on N=0",
        "recurrence_budget_per_labeled_orbit": 10000,
        "domains": domains, "exhaustive_initial_states": states,
        "independent_labeled_colored_edges": edges, "unresolved_orbits": 0,
        "population_envelope": envelope, "controls": controls,
        "runtime": {"python": platform.python_version(), "numpy": np.__version__},
        "source_sha256_before": before, "source_sha256_after": after,
        "seconds": round(perf_counter() - started, 6),
        "scope": (
            "Complete finite census of the two declared tori. Reverse pruning, a path-mask recurrence "
            "and independent scalar root walks agree. Full-round core inclusion and species persistence "
            "are checked on every state. Independent labeled replay checks every colored transition, "
            "no movement of core tags, and exact equality of final core labels with stopped original "
            "identities. Terminal-cycle means are computed independently on colored functional graphs "
            "and labeled recurrent orbits. Every initial state receives its own basin's cycle mean "
            "before initial iid weighting. A single root and spatial root averaging agree in every "
            "initial-population layer. Population-bound arithmetic assumes an established late-time "
            "per-site path/core bound; no finite-prefix observation certifies that assumption."
        ),
        "not_established": ["a late-time path-mass estimate as the torus grows",
                            "fixed-positive-density nonjamming", "BML sharpness of the population relaxation",
                            "an iid law for evolved cells", "TRAIN semantics"],
    }
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Path/core acceptance passed: {states:,} initial states, {edges:,} independent labeled edges, "
          f"{envelope['exact_primal_dual_comparisons']:,} exact population-envelope comparisons.")


if __name__ == "__main__":
    main()
