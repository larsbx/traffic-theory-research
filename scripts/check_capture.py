#!/usr/bin/env python3
"""Reproduce the finite CLASSIC blocking/capture certificate census.

Every mixed-core witness is replayed with independent car identities, checked
against production dynamics, and checked for the exact obstacle-rank decrease.
Counts for all final phases come from the existing functional-graph classifier;
they are reported separately from the capture witnesses checked independently.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import platform
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from bml.capture import find_blocker_cycles, trace_capture, verify_capture, verify_cycle  # noqa: E402
from bml.certificates import has_blocker_cycle  # noqa: E402
from bml.exhaustive import FREE, JAM, MIXED, classify_all, decode  # noqa: E402


# Ordered (width, height) pairs; these are the entire advertised domain.
DOMAINS = ((2, 2), (3, 2), (2, 3), (4, 2), (2, 4), (3, 3))


def check_shape(width: int, height: int) -> dict:
    size = 3 ** (width * height)
    states = decode(np.arange(size, dtype=np.int64), height, width)
    classification = classify_all(height, width)
    core_count = mixed_count = identity_edges = 0
    max_rounds = max_moves = 0
    for code, state in enumerate(states):
        rows = state.tolist()
        cycles = find_blocker_cycles(rows)
        if bool(cycles) != has_blocker_cycle(rows):
            raise AssertionError(f"{width}x{height} state {code}: blocker detection disagrees")
        core_count += bool(cycles)
        for cycle in cycles:
            verify_cycle(rows, cycle)
        mixed = next((cycle for cycle in cycles if cycle.mixed), None)
        if mixed is None:
            continue
        mixed_count += 1
        result = verify_capture(rows, mixed)
        if classification.cls[code] != JAM:
            raise AssertionError(f"{width}x{height} state {code}: capture/classifier disagreement")
        identity_edges += result.rounds_to_gridlock + 1  # Includes the frozen self-edge.
        max_rounds = max(max_rounds, result.rounds_to_gridlock)
        max_moves = max(max_moves, result.total_moves)
    outcomes = {
        name: int(np.count_nonzero(classification.cls == kind))
        for name, kind in (("gridlock", JAM), ("free", FREE), ("intermediate", MIXED))
    }
    scope = {
        "width": width, "height": height, "states": size,
        "initial_core_states": int(core_count), "mixed_core_states": mixed_count,
        "independently_verified_gridlocks": mixed_count,
        "independently_replayed_edges": identity_edges,
        "max_rounds_after_mixed_core": max_rounds,
        "max_moves_after_mixed_core": max_moves,
        "functional_graph_outcomes": outcomes,
    }
    print(f"CLASSIC capture {width}x{height}: {size} states; {mixed_count} mixed-core "
          f"captures; {identity_edges} independently replayed edges", flush=True)
    return scope


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    scopes = [check_shape(width, height) for width, height in DOMAINS]
    controls = {
        "later_loop": trace_capture([[2, 2, 1], [1, 1, 0]]),
        "later_loop_cutoff": trace_capture([[2, 2, 1], [1, 1, 0]], max_steps=3),
        "balanced_partial_capture": trace_capture(
            [[1, 1, 1], [1, 0, 0], [2, 0, 0], [2, 2, 2]]
        ),
        "original_gridlocks": trace_capture([[0, 2, 2, 1], [2, 0, 2, 1]]),
        "addition_keeps_motion": trace_capture([[2, 2, 2, 1], [2, 0, 2, 1]]),
    }
    expected = {
        "later_loop": "gridlock", "later_loop_cutoff": "unresolved",
        "balanced_partial_capture": "intermediate", "original_gridlocks": "gridlock",
        "addition_keeps_motion": "intermediate",
    }
    if any(trace.outcome != expected[name] for name, trace in controls.items()):
        raise AssertionError("a pinned formation/capture control changed outcome")
    source_paths = [
        "bml/capture.py", "bml/certificates.py", "bml/exhaustive.py", "bml/model.py",
        "scripts/check_capture.py", "tests/test_capture.py", "requirements-dev.txt",
    ]
    report = {
        "schema": "bml.capture-replay.v1", "status": "passed", "rule": "classic",
        "runtime": {"python": platform.python_version(), "numpy": np.__version__},
        "source_sha256": {
            path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
            for path in source_paths
        },
        "rectangles": scopes,
        "exhaustive_states": sum(scope["states"] for scope in scopes),
        "mixed_core_states": sum(scope["mixed_core_states"] for scope in scopes),
        "independently_replayed_edges": sum(scope["independently_replayed_edges"] for scope in scopes),
        "controls": {name: asdict(trace) for name, trace in controls.items()},
        "scope": (
            "Static certificates on every state of the six listed tori; independent labeled "
            "capture replay for states containing a mixed cycle. Final-phase census uses the "
            "production functional-graph classifier. Finite evidence, not a universal source "
            "refinement, probabilistic transition result, or TRAIN-rule claim."
        ),
    }
    print(json.dumps({key: report[key] for key in (
        "schema", "status", "exhaustive_states", "mixed_core_states", "independently_replayed_edges"
    )}, sort_keys=True))
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
