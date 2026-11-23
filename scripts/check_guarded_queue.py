#!/usr/bin/env python3
"""Reproduce guarded-queue delay and initial-iid avoidance evidence.

The exterior census uses its own scalar tagged transition, compares both
canonical production half-steps, and checks every translated placement.
Public-verifier checks are counted separately. Complete initial-state laws
then check exact cyclic avoidance and actual gridlock at the bounded time.
No cutoff is treated as a terminal outcome, and no evolved iid law is used.
"""
from __future__ import annotations

import argparse
from dataclasses import replace
from fractions import Fraction
import hashlib
from itertools import product
import json
from pathlib import Path
import platform
import sys
from time import perf_counter
from unittest.mock import patch

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from bml import guarded_queue  # noqa: E402
from bml.certificates import trace_labeled  # noqa: E402
from bml.exhaustive import decode  # noqa: E402
from bml.guarded_queue import (  # noqa: E402
    GuardedQueueCertificate, construct_guarded_queue, guarded_queue_bounds, verify_guarded_queue,
)
from bml.model import EAST, NORTH, TRAIN, half_step, is_fixed, step  # noqa: E402


DOMAINS = tuple((width, height) for width in range(2, 7) for height in range(2, 7)
                if width * height <= 12)
DENSITIES = (Fraction(0), Fraction(1, 10), Fraction(1, 2), Fraction(4, 5), Fraction(1))
SOURCE_PATHS = (
    "bml/guarded_queue.py", "bml/probability.py", "bml/capture.py", "bml/certificates.py",
    "bml/exhaustive.py", "bml/model.py", "tests/test_guarded_queue.py",
    "scripts/check_guarded_queue.py", "requirements-dev.txt",
)


def scalar_phase(labels, species, width, height, active):
    moves = []
    for source, label in enumerate(labels):
        if label < 0 or species[label] != active:
            continue
        y, x = divmod(source, width)
        target = y * width + (x + 1) % width if active == EAST else ((y + 1) % height) * width + x
        if labels[target] < 0:
            moves.append((source, target, label))
    following = list(labels)
    for source, target, label in moves:
        following[source], following[target] = -1, label
    return tuple(following), tuple(label for _, _, label in moves)


def colored(labels, species, height, width):
    return np.array([0 if label < 0 else species[label] for label in labels],
                    dtype=np.int8).reshape(height, width)


def exterior_boards(width, height, delay):
    fixed = {i: EAST for i in range(delay + 1)}
    fixed[delay + 1] = 0
    fixed.update({(height - 1) * width + i: EAST for i in range(1, delay + 1)})
    free = tuple(cell for cell in range(width * height) if cell not in fixed)
    for values in product(range(3), repeat=len(free)):
        board = [0] * (width * height)
        for cell, species in fixed.items():
            board[cell] = species
        for cell, species in zip(free, values):
            board[cell] = species
        yield tuple(board)


def check_exteriors(width, height, delay):
    started = perf_counter()
    canonical = list(exterior_boards(width, height, delay))
    production = np.array(canonical, dtype=np.int8).reshape(-1, height, width)
    species = [{cell: color for cell, color in enumerate(board) if color} for board in canonical]
    references = [tuple(cell if color else -1 for cell, color in enumerate(board)) for board in canonical]
    for t in range(delay + 1):
        after_e, me = half_step(production, EAST)
        after_n, mn = half_step(after_e, NORTH)
        for i, state in enumerate(references):
            tagged_e, e_moves = scalar_phase(state, species[i], width, height, EAST)
            tagged_n, n_moves = scalar_phase(tagged_e, species[i], width, height, NORTH)
            if (0 in e_moves) != (t == delay) or not e_moves:
                raise AssertionError("the rear tag failed its exact first-move round")
            if (not np.array_equal(colored(tagged_e, species[i], height, width), after_e[i])
                    or not np.array_equal(colored(tagged_n, species[i], height, width), after_n[i])
                    or (len(e_moves), len(n_moves)) != (int(me[i]), int(mn[i]))):
                raise AssertionError("independent tagged and production half-steps disagree")
            guard_source = tagged_e[(height - 1) * width + delay - t]
            if t < delay and guard_source >= 0 and species[i][guard_source] == NORTH:
                raise AssertionError("a north car reached the protected refill source")
            references[i] = tagged_n
        production = after_n

    translations = public_checks = 0
    for index, board in enumerate(canonical):
        for y0 in range(height):
            for x0 in range(width):
                shifted = [0] * (width * height)
                for cell, color in enumerate(board):
                    y, x = divmod(cell, width)
                    shifted[((y + y0) % height) * width + (x + x0) % width] = color
                colors = {cell: color for cell, color in enumerate(shifted) if color}
                tags = tuple(cell if color else -1 for cell, color in enumerate(shifted))
                rear = y0 * width + x0
                for t in range(delay + 1):
                    tags, e_moves = scalar_phase(tags, colors, width, height, EAST)
                    if (rear in e_moves) != (t == delay):
                        raise AssertionError("a translated rear tag missed its first-move round")
                    tags, _ = scalar_phase(tags, colors, width, height, NORTH)
                translations += 1
                # The exhaustive scalar census is not counted as calls to the
                # public verifier. Two exterior representatives are checked
                # through that full API at every origin instead.
                if index in (0, len(canonical) - 1):
                    rows = [shifted[y * width:(y + 1) * width] for y in range(height)]
                    checked = verify_guarded_queue(rows, GuardedQueueCertificate(width, height, x0, y0, delay))
                    if checked.first_rear_move != delay or checked.states[-1] != tags:
                        raise AssertionError("public verification disagrees with the independent census")
                    public_checks += 1
    result = {
        "width": width, "height": height, "delay": delay,
        "canonical_exterior_boards": len(canonical), "translated_tagged_cases": translations,
        "canonical_production_compared_rounds": len(canonical) * (delay + 1),
        "public_verifier_checks": public_checks, "seconds": round(perf_counter() - started, 6),
    }
    print(f"Guarded queue {width}x{height}, T={delay}: {len(canonical)} exteriors; "
          f"{translations} translated tagged cases", flush=True)
    return result


def pattern_union(states, delay, *, all_rows=False):
    _, height, width = states.shape
    hit = np.zeros(len(states), dtype=bool)
    for row in (range(height) if all_rows else range(1, height, 2)):
        for start in range(width):
            good = states[:, row, (start + delay + 1) % width] == 0
            for offset in range(delay + 1):
                good &= states[:, row, (start + offset) % width] == EAST
            for offset in range(1, delay + 1):
                good &= states[:, (row - 1) % height, (start + offset) % width] == EAST
            hit |= good
    return hit


def integrate(counts, p, cells):
    return sum((int(count) * (p / 2) ** n * (1 - p) ** (cells - n)
                for n, count in enumerate(counts)), Fraction())


def check_initial_law(width, height):
    cells = width * height
    states = decode(np.arange(3 ** cells), height, width)
    cars = (states != 0).sum(axis=(1, 2))
    current = states.copy()
    delays = []
    for delay in range(width - 1):
        following, moves = step(current)
        jammed = (cars > 0) & (moves == 0)
        hit = pattern_union(states, delay)
        if np.any(jammed & hit):
            raise AssertionError("a guarded initial queue reached gridlock by its certified delay")
        avoid_counts = np.bincount(cars[~hit], minlength=cells + 1)
        jam_counts = np.bincount(cars[jammed], minlength=cells + 1)
        checks = []
        for p in DENSITIES:
            bounds = guarded_queue_bounds(width, height, delay, p)
            actual = integrate(avoid_counts, p, cells)
            early_jam = integrate(jam_counts, p, cells)
            if actual != bounds.early_gridlock_upper_bound or not early_jam <= actual <= bounds.simple_upper_bound:
                raise AssertionError("exact initial-law avoidance or finite-time jam bound failed")
            checks.append({
                "p": str(p), "pattern_mass": str(bounds.pattern_probability),
                "literal_gridlock_by_delay": str(early_jam),
                "literal_selected_pattern_avoidance": str(actual),
                "cyclic_avoidance_bound": str(bounds.early_gridlock_upper_bound),
                "simple_bound": str(bounds.simple_upper_bound),
            })
        delays.append({"delay": delay, "gridlocked_initial_states": int(jammed.sum()),
                       "avoiding_initial_states": int((~hit).sum()), "checks": checks})
        current = following
    print(f"Initial iid {width}x{height}: {len(states)} states; {len(delays) * len(DENSITIES)} exact checks", flush=True)
    return {"width": width, "height": height, "states": len(states),
            "finite_time_predicate_checks": len(states) * (width - 1),
            "exact_iid_comparisons": len(delays) * len(DENSITIES), "delays": delays}


def reject(operation, label):
    try:
        operation()
    except ValueError:
        return "rejected"
    raise AssertionError(f"invalid control accepted: {label}")


def controls():
    rows = [[1, 1, 0], [0, 1, 2], [0, 2, 2]]
    after, moves = step(np.array(rows))
    orbit = trace_labeled(rows)
    if (int(moves) != 2 or not is_fixed(after) or orbit.cycle_start != 1
            or orbit.period != 1 or orbit.cycle_moves(0) != 0):
        raise AssertionError("guard omission no longer gives the pinned early jam")
    cert = GuardedQueueCertificate(3, 3, 0, 0, 1)
    negatives = {"omitted_guard_early_jam": reject(lambda: verify_guarded_queue(rows, cert), "guard")}
    empty_guard = [[1, 1, 1, 0], [0, 2, 0, 0], [0, 0, 1, 0]]
    empty_orbit = trace_labeled(empty_guard)
    if any(0 in moved for moved in empty_orbit.moved[:3]):
        raise AssertionError("the initially empty missing guard stopped being a counterexample")
    negatives["initially_empty_guard"] = reject(
        lambda: verify_guarded_queue(empty_guard, GuardedQueueCertificate(4, 3, 0, 0, 2)), "empty guard")
    valid = construct_guarded_queue(3, 3, 1)
    negatives["bad_dimension"] = reject(lambda: verify_guarded_queue(valid, replace(cert, height=2)), "dimension")
    negatives["boolean_delay"] = reject(lambda: verify_guarded_queue(valid, replace(cert, delay=True)), "bool")
    negatives["float_density"] = reject(lambda: guarded_queue_bounds(3, 3, 1, 0.5), "density")
    negatives["TRAIN_rule"] = reject(lambda: guarded_queue_bounds(3, 3, 1, Fraction(1, 2), rule=TRAIN), "TRAIN")

    swap_rows = construct_guarded_queue(4, 3, 1, exterior=[[1] * 4 for _ in range(3)])
    original = guarded_queue._tagged_half_step

    def swapped(*args):
        state, moved = original(*args)
        if args[-1] == EAST:
            state = list(state)
            state[4], state[5] = state[5], state[4]
            state = tuple(state)
        return state, moved

    with patch.object(guarded_queue, "_tagged_half_step", swapped):
        negatives["same_species_tag_swap"] = reject(
            lambda: verify_guarded_queue(swap_rows, GuardedQueueCertificate(4, 3, 0, 0, 1)), "identity swap")

    def wrong_count(state, active, **kwargs):
        out, count = half_step(state, active, **kwargs)
        return out, int(count) + 1

    with patch.object(guarded_queue, "half_step", wrong_count):
        negatives["corrupt_production_movement"] = reject(lambda: verify_guarded_queue(valid, cert), "movement")

    states = decode(np.arange(3 ** 9), 3, 3)
    cars = (states != 0).sum(axis=(1, 2))
    all_avoid = integrate(np.bincount(cars[~pattern_union(states, 1, all_rows=True)], minlength=10), Fraction(1, 2), 9)
    false_bound = Fraction(127, 128) ** 9
    if all_avoid != Fraction(15301, 16384) or not all_avoid > false_bound:
        raise AssertionError("the vertical false-independence control stopped refuting the naive bound")
    evolved, _ = step(states)
    evolved_hit = ((evolved[:, 0, 0] == EAST) & (evolved[:, 0, 1] == EAST)
                   & (evolved[:, 0, 2] == 0) & (evolved[:, 2, 1] == EAST))
    evolved_mass = integrate(np.bincount(cars[evolved_hit], minlength=10), Fraction(1, 2), 9)
    if evolved_mass != Fraction(7, 1024) or evolved_mass == Fraction(1, 128):
        raise AssertionError("the evolved-law control stopped refuting reset iid weights")
    return {
        "rejections": negatives,
        "unguarded_early_jam": {"initial": rows, "time_one": after.tolist(), "first_gridlock_time": 1},
        "initially_empty_guard": {"initial": empty_guard, "rear_does_not_move_through_round": 2},
        "vertical_overlap": {"side": 3, "delay": 1, "p": "1/2", "actual_avoidance": str(all_avoid),
                             "false_independent_bound": str(false_bound), "refuted": True},
        "evolved_iid_mutant": {"side": 3, "delay": 1, "p": "1/2", "initial_pattern_mass": "1/128",
                               "actual_time_one_pattern_mass": str(evolved_mass), "refuted": True},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    started = perf_counter()
    before = {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in SOURCE_PATHS}
    exterior = [check_exteriors(width, height, delay) for width, height in DOMAINS for delay in range(width - 1)]
    initial_law = [check_initial_law(width, height) for width, height in DOMAINS]
    report = {
        "schema": "bml.guarded-queue-replay.v1", "status": "passed", "rule": "classic",
        "runtime": {"python": platform.python_version(), "numpy": np.__version__},
        "source_sha256_before": before,
        "exterior_domains": exterior, "initial_law_domains": initial_law,
        "canonical_exterior_boards": sum(row["canonical_exterior_boards"] for row in exterior),
        "translated_tagged_cases": sum(row["translated_tagged_cases"] for row in exterior),
        "canonical_production_compared_rounds": sum(row["canonical_production_compared_rounds"] for row in exterior),
        "public_verifier_checks": sum(row["public_verifier_checks"] for row in exterior),
        "complete_initial_states": sum(row["states"] for row in initial_law),
        "finite_time_predicate_checks": sum(row["finite_time_predicate_checks"] for row in initial_law),
        "exact_iid_comparisons": sum(row["exact_iid_comparisons"] for row in initial_law),
        "controls": controls(),
        "scope": (
            "Every exterior and translated guarded pattern on the twelve listed tori, through "
            "the explicitly bounded round T. The independent scalar tagged census is distinct "
            "from representative public-verifier calls. Complete initial iid weights check "
            "cyclic avoidance and actual nonempty gridlock at time T; no evolved iid law, "
            "terminal classification from a timeout, or asymptotic critical-density proof is claimed."
        ),
    }
    after = {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in SOURCE_PATHS}
    if before != after:
        raise AssertionError("source files changed during guarded-queue validation")
    report["source_sha256_after"] = after
    report["seconds"] = round(perf_counter() - started, 6)
    print(json.dumps({key: report[key] for key in (
        "schema", "status", "canonical_exterior_boards", "translated_tagged_cases",
        "canonical_production_compared_rounds", "public_verifier_checks", "complete_initial_states",
        "finite_time_predicate_checks", "exact_iid_comparisons", "seconds",
    )}, sort_keys=True))
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
