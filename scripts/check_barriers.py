#!/usr/bin/env python3
"""Reproduce finite CLASSIC guarded-barrier and initial-law evidence.

Every listed exterior domain is exhausted, with an independent scalar oracle
for both phases. Translation checks include every placement on those tori.
No finite prefix is classified as permanent flow or eventual nonjamming.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
from itertools import product
import json
from pathlib import Path
import platform
import subprocess
import sys
from time import perf_counter
from unittest.mock import patch

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from bml import barriers  # noqa: E402
from bml.barriers import (  # noqa: E402
    guarded_barrier_board, guarded_barrier_formation_upper_bound,
    guarded_barrier_pattern, guarded_barrier_probability, verify_guarded_barrier,
)
from bml.capture import find_blocker_cycles  # noqa: E402
from bml.exhaustive import decode  # noqa: E402
from bml.model import CLASSIC, EAST, EMPTY, NORTH, TRAIN, half_step, step  # noqa: E402
from check_freeflow import scalar_phase  # noqa: E402


EXTERIOR_DOMAINS = ((1, 1, 0, 0, 0), (2, 2, 0, 1, 1), (2, 3, 0, 1, 1),
                    (3, 3, 0, 2, 2), (2, 3, 1, 1, 1), (3, 3, 1, 2, 1),
                    (3, 4, 1, 2, 2), (4, 4, 1, 2, 2))
FRESHNESS_DOMAINS = ((2, 0), (7, 0), (9, 1), (19, 1), (16, 2), (34, 2), (48, 3))
DENSITIES = (Fraction(0), Fraction(1, 5), Fraction(1, 2), Fraction(2, 3), Fraction(6, 7), Fraction(1))
SOURCE_PATHS = (
    "bml/barriers.py", "bml/model.py", "bml/probability.py", "bml/formation.py",
    "bml/capture.py", "bml/exhaustive.py", "scripts/check_freeflow.py",
    "scripts/check_barriers.py", "tests/test_barriers.py", "requirements-dev.txt",
    "formal/lean/BML/Barrier.lean", "formal/lean/BML.lean", "formal/lean/Audit.lean",
    "docs/research/2026-11-19-guarded-barrier-formation.md",
)


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def hashes():
    return {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in SOURCE_PATHS}


def check_exteriors(w, h, t, a, b):
    pattern = guarded_barrier_pattern(w, h, t, east_length=a, north_length=b)
    fixed = {y * w + x: c for x, y, c in pattern.initial_cells}
    free = tuple(i for i in range(w * h) if i not in fixed)
    canonical = []
    for values in product(range(3), repeat=len(free)):
        cells = [0] * (w * h)
        for i, c in fixed.items():
            cells[i] = c
        for i, c in zip(free, values):
            cells[i] = c
        canonical.append(tuple(cells))
    initial = np.array(canonical, dtype=np.int8).reshape(-1, h, w)
    current = initial
    references = canonical
    for _ in range(t):
        middle, em = half_step(current, EAST)
        after, nm = half_step(middle, NORTH)
        following = []
        for i, cells in enumerate(references):
            expected_e, n_e = scalar_phase(cells, w, h, EAST)
            expected_n, n_n = scalar_phase(expected_e, w, h, NORTH)
            require(tuple(middle[i].flat) == expected_e and tuple(after[i].flat) == expected_n
                    and (int(em[i]), int(nm[i])) == (n_e, n_n), "independent phase replay disagrees")
            following.append(expected_n)
        # Check every seam placement against the actual production phases.
        for dy in range(h):
            for dx in range(w):
                moved = np.roll(current, (dy, dx), axis=(1, 2))
                moved_e, moved_em = half_step(moved, EAST)
                moved_n, moved_nm = half_step(moved_e, NORTH)
                require(np.array_equal(moved_e, np.roll(middle, (dy, dx), axis=(1, 2)))
                        and np.array_equal(moved_n, np.roll(after, (dy, dx), axis=(1, 2)))
                        and np.array_equal(moved_em, em) and np.array_equal(moved_nm, nm),
                        "translated phase or movement totals changed")
        references, current = following, after
    for x, y, c in pattern.target_cells:
        require(bool((current[:, y, x] == c).all()), "barrier failed for an exterior completion")
    public_checks = 0
    for index in sorted({0, len(canonical) // 2, len(canonical) - 1}):
        for dy in range(h):
            for dx in range(w):
                translated = guarded_barrier_pattern(w, h, t, east_length=a, north_length=b, x0=dx, y0=dy)
                board = np.roll(initial[index], (dy, dx), axis=(0, 1))
                verification = verify_guarded_barrier(board.tolist(), translated)
                require(verification.states[-1] == tuple(np.roll(current[index], (dy, dx), axis=(0, 1)).flat),
                        "public verifier disagrees with independent exterior census")
                public_checks += 1
    return {"width": w, "height": h, "rounds": t, "east_length": a, "north_length": b,
            "prescribed_cells": len(fixed), "exterior_cells": len(free), "boards": len(canonical),
            "independent_phase_comparisons": 2 * t * len(canonical),
            "translated_placements": w * h * len(canonical),
            "translated_phase_comparisons": 2 * t * w * h * len(canonical),
            "public_verifier_calls": public_checks}


def projected_box(side, x, y, t):
    return {((x + dx) % side, (y + dy) % side)
            for dx in range(-t, t + 1) for dy in range(-t, t + 1)}


def check_freshness():
    domains = []
    for side, t in FRESHNESS_DOMAINS:
        stride, probes, history = 4 * t + 1, 0, set()
        trials = max(0, (side - 3 * t - 1) // stride)
        for j in range((trials - 1) * stride + 1):
            for x in range(j + 1):
                history |= projected_box(side, side - 1 + x, 1 + j - x, t)
            if j % stride:
                continue
            for x in range(j + 1):
                for first in (EAST, NORTH):
                    pattern = guarded_barrier_pattern(side, side, t,
                        x0=side - 1 + x + (first == EAST), y0=1 + j - x + (first == NORTH))
                    support = {(a, b) for a, b, _ in pattern.initial_cells}
                    require(len(support) == 6 * t + 1 and not support & history,
                            "a legal probe reuses or aliases an initial site")
                    probes += 1
        domains.append({"side": side, "rounds": t, "trials_per_path": trials,
                        "all_checkpoint_position_direction_probes": probes})
    bad = guarded_barrier_pattern(9, 9, 1, x0=6, y0=0)
    overlap = {(x, y) for x, y, _ in bad.initial_cells} & projected_box(9, 0, 0, 1)
    require((8, 0) in overlap, "beyond-cutoff overlap negative control disappeared")
    return {"domains": domains, "beyond_cutoff_shared_initial_site": [8, 0]}


def check_initial_law():
    census = []
    for side in (2, 3):
        counts = [0] * (side * side + 1)
        boards = decode(np.arange(3 ** (side * side)), side, side)
        for board in boards:
            if any(c.mixed for c in find_blocker_cycles(board.tolist())):
                counts[int(np.count_nonzero(board))] += 1
        evaluations = []
        for p in DENSITIES:
            actual = sum(n * (p / 2) ** k * (1 - p) ** (side * side - k) for k, n in enumerate(counts))
            bound = guarded_barrier_formation_upper_bound(side, p)
            require(actual <= bound == min(Fraction(1), Fraction(side, 2) * p ** side),
                    "zero-time initial-cycle inequality failed")
            evaluations.append({"p": str(p), "actual": str(actual), "bound": str(bound)})
        census.append({"side": side, "all_initial_states": len(boards),
                       "mixed_cycle_counts_by_population": counts, "evaluations": evaluations})
    required = tuple(c for _, _, c in guarded_barrier_pattern(9, 9, 1).initial_cells)
    accepted = sum(values == required for values in product(range(3), repeat=len(required)))
    require(accepted == 1 and Fraction(accepted, 3 ** len(required))
            == guarded_barrier_probability(1, Fraction(2, 3)), "initial support mass is wrong")
    weights = []
    for t in range(9):
        pattern = guarded_barrier_pattern(7 * t + 2, 7 * t + 2, t)
        for p in DENSITIES:
            product_weight = Fraction(1)
            for _, _, c in pattern.initial_cells:
                product_weight *= 1 - p if c == EMPTY else p / 2
            require(product_weight == guarded_barrier_probability(t, p), "initial product integration failed")
            weights.append({"rounds": t, "p": str(p), "probability": str(product_weight)})
    return {"complete_initial_domains": census, "one_round_support_assignments": 3 ** len(required),
            "accepted_one_round_support_assignments": accepted, "exact_support_weights": weights}


def check_controls():
    rejected = []
    def reject(label, action):
        try:
            action()
        except ValueError:
            rejected.append(label)
        else:
            raise AssertionError(f"negative control accepted: {label}")
    pattern = guarded_barrier_pattern(3, 4, 1)
    rows = guarded_barrier_board(pattern)
    reject("TRAIN probability", lambda: guarded_barrier_formation_upper_bound(9, Fraction(1, 2), 1, rule=TRAIN))
    reject("floating density", lambda: guarded_barrier_probability(1, 0.5))
    reject("overlapping initial footprint", lambda: guarded_barrier_pattern(3, 3, 1))
    reject("missing initial pattern", lambda: verify_guarded_barrier(np.zeros((4, 3)).tolist(), pattern))
    real = barriers.half_step
    def bad_count(board, species, rule=CLASSIC):
        after, moves = real(board, species, rule)
        return after, moves + 1
    with patch.object(barriers, "half_step", bad_count):
        reject("wrong production movement count", lambda: verify_guarded_barrier(rows, pattern))
    with patch.object(barriers, "half_step", lambda board, species, rule=CLASSIC:
                      real(board, NORTH if species == EAST else EAST, rule)):
        reject("wrong production phase", lambda: verify_guarded_barrier(rows, pattern))
    two = guarded_barrier_pattern(5, 7, 2)
    board = np.array(guarded_barrier_board(two, exterior=np.full((7, 5), EAST).tolist()))
    x, y = two.corner
    for offset in (1, 2):
        board[y + offset, x - 1] = EMPTY
    reject("empty guards", lambda: verify_guarded_barrier(board.tolist(), two))
    after, _ = step(board)
    after, _ = step(after)
    require(after[y, x] != EMPTY, "empty-guard counterexample no longer fails dynamically")
    # Multiple rounds and arbitrary exterior samples are finite stress checks.
    rng = np.random.default_rng(714003)
    stress = 0
    for t in (2, 3, 5, 8):
        w, h = 2 * t + 3, 3 * t + 2
        for x0, y0 in ((0, 0), (w - 1, h - 1), (-w - 1, -h - 2)):
            probe = guarded_barrier_pattern(w, h, t, x0=x0, y0=y0)
            for index in range(15):
                exterior = (np.full((h, w), index) if index < 3
                            else rng.integers(0, 3, size=(h, w)))
                verify_guarded_barrier(guarded_barrier_board(probe, exterior=exterior.tolist()), probe)
                stress += 1
    delayed = []
    for side in range(4, 13):
        t = (side - 2) // 2
        board = np.zeros((side, side), dtype=np.int8)
        for i in range(side):
            require(not board[i, (i - t) % side] and not board[(i - t) % side, (i + 1) % side],
                    "delayed staircase initial sources overlap")
            board[i, (i - t) % side], board[(i - t) % side, (i + 1) % side] = EAST, NORTH
        movements = []
        for _ in range(t):
            require(not any(c.mixed for c in find_blocker_cycles(board.tolist())), "cycle formed before declared time")
            board, moved = step(board)
            require(int(moved) == 2 * side, "delayed staircase stopped in its moving prefix")
            movements.append(int(moved))
        require(any(c.mixed for c in find_blocker_cycles(board.tolist())), "delayed staircase did not form")
        after, moved = step(board)
        require(not moved and np.array_equal(board, after), "formed staircase is not a jam")
        delayed.append({"side": side, "first_mixed_cycle_time": t, "moving_prefix_totals": movements})
    return {"rejected_controls": rejected, "longer_time_exterior_replays": stress,
            "delayed_all_moving_to_jam_family": delayed}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    started, before = perf_counter(), hashes()
    domains = [check_exteriors(*domain) for domain in EXTERIOR_DOMAINS]
    freshness, initial_law, controls = check_freshness(), check_initial_law(), check_controls()
    after = hashes()
    require(before == after, "sources changed during the acceptance run")
    git = subprocess.run(["git", "rev-parse", "HEAD", "HEAD^{tree}"], cwd=ROOT, text=True, capture_output=True)
    revision, tree = git.stdout.splitlines() if git.returncode == 0 else (None, None)
    status = subprocess.run(["git", "status", "--porcelain"], cwd=ROOT, text=True, capture_output=True)
    report = {"schema": "bml.guarded-barrier-replay.v1", "status": "passed",
              "scope": "declared finite exterior domains, initial-law integration, and freshness geometry",
              "revision": revision, "tree": tree, "worktree_clean": status.returncode == 0 and not status.stdout,
              "exterior_domains": domains,
              "total_exterior_boards": sum(d["boards"] for d in domains),
              "total_translated_placements": sum(d["translated_placements"] for d in domains),
              "total_independent_phase_comparisons": sum(d["independent_phase_comparisons"] for d in domains),
              "total_translated_phase_comparisons": sum(d["translated_phase_comparisons"] for d in domains),
              "public_verifier_calls": sum(d["public_verifier_calls"] for d in domains)
                                       + controls["longer_time_exterior_replays"],
              "freshness": freshness, "initial_law": initial_law, "controls": controls,
              "runtime": {"python": platform.python_version(), "numpy": np.__version__},
              "source_sha256_before": before, "source_sha256_after": after,
              "seconds": round(perf_counter() - started, 6),
              "not_established": ["late mixed-cycle formation probability", "positive-density nonjamming",
                                  "a sharp critical density", "an iid law for evolved cells"]}
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Guarded barriers passed: {report['total_exterior_boards']:,} exterior boards; "
          f"{report['total_translated_placements']:,} translated placements; "
          f"{report['total_independent_phase_comparisons']:,} independent phase comparisons.")


if __name__ == "__main__":
    main()
