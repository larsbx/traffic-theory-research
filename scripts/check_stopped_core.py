#!/usr/bin/env python3
"""Compare finite stopped-tag/core counts with the CLASSIC Lean exporter.

The independent labeled replayer supplies complete recurrence. Initial and
recurrent-entry snapshots are compared with Lean; no finite observation is
silently promoted to an eventual count. All weights remain on initial boards.
The older check_path_core.py supplies the broader path-mass census.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
from math import factorial
from pathlib import Path
import subprocess
import sys
from time import perf_counter

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from bml.certificates import LabeledOrbit, trace_labeled  # noqa: E402
from bml.path_core import direct_path_count, scalar_path_mask  # noqa: E402
from bml.probability import has_full_lane  # noqa: E402

DOMAINS = ((1, 1), (1, 2), (2, 1), (2, 2), (3, 3))
DENSITIES = (Fraction(0), Fraction(1, 5), Fraction(1, 2), Fraction(2, 3), Fraction(1))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def decode_rows(width: int, height: int, code: int) -> list[list[int]]:
    if any(type(value) is not int for value in (width, height, code)):
        raise ValueError("dimensions and code must be integers")
    if width < 1 or height < 1 or not 0 <= code < 3 ** (width * height):
        raise ValueError("expected positive dimensions and a complete ternary code")
    flat = []
    for _ in range(width * height):
        code, cell = divmod(code, 3)
        flat.append(cell)
    return [flat[i:i + width] for i in range(0, len(flat), width)]


def encode_rows(rows: list[list[int]]) -> int:
    return sum(cell * 3 ** i for i, cell in enumerate(cell for row in rows for cell in row))


def state_index(orbit: LabeledOrbit, time: int) -> int:
    if type(time) is not int or time < 0:
        raise ValueError("snapshot time must be a natural number")
    if time < len(orbit.states):
        return time
    return orbit.cycle_start + (time - orbit.cycle_start) % orbit.period


def core_labels(orbit: LabeledOrbit, time: int) -> tuple[int, ...]:
    index = state_index(orbit, time)
    rows = orbit.rows(index)
    # Walk N edges (N+1 occupied vertices), independently of reverse pruning.
    mask = scalar_path_mask(rows, len(orbit.species))
    return tuple(sorted(label for label, keep in zip(orbit.states[index],
                        (value for row in mask for value in row)) if keep))


@dataclass(frozen=True)
class Case:
    width: int
    height: int
    code: int
    orbit: LabeledOrbit
    stopped_labels: tuple[int, ...]
    full_lane: bool
    gridlock: bool
    initial_core: int
    colored_transient: int
    colored_period: int

    @property
    def population(self) -> int:
        return len(self.orbit.species)

    @property
    def stopped(self) -> int:
        return len(self.stopped_labels)

    def snapshot(self, time: int) -> tuple[int, ...]:
        index = state_index(self.orbit, time)
        rows = self.orbit.rows(index)
        mask = scalar_path_mask(rows, self.population)
        sites = tuple(i for i, keep in enumerate(value for row in mask for value in row) if keep)
        # Read original identities separately from the current occupied-site count.
        tags = tuple(label for label, _ in self.orbit.species
                     if self.orbit.states[index].index(label) in sites)
        require(len(tags) == len(sites), "current core and transported original-tag counts differ")
        jam = self.population > 0 and not self.orbit.moved[index]
        return (self.width, self.height, self.code, time, encode_rows(rows), self.population,
                len(sites), len(tags), int(jam), int(self.full_lane))


def analyze_case(width: int, height: int, code: int, *, max_steps: int = 10000) -> Case:
    rows = decode_rows(width, height, code)
    orbit = trace_labeled(rows, max_steps=max_steps)
    recurrent_states = orbit.states[orbit.cycle_start:]
    recurrent_moves = orbit.moved[orbit.cycle_start:]
    stopped = tuple(label for label, _ in orbit.species
                    if all(label not in edge for edge in recurrent_moves))
    by_positions = tuple(label for label, _ in orbit.species
                         if all(state.index(label) == recurrent_states[0].index(label)
                                for state in recurrent_states))
    require(stopped == by_positions, "zero cycle moves disagree with constant original-tag positions")
    final_core_labels = core_labels(orbit, orbit.cycle_start)
    require(stopped == final_core_labels, "eventual core does not contain exactly the stopped original tags")
    population = len(orbit.species)
    # Derive J from a genuine zero-movement round of a nonempty orbit, not from Z.
    gridlock = population > 0 and any(not moved for moved in orbit.moved)
    full_lane = has_full_lane(rows)
    z = len(stopped)
    require(0 <= z <= population, "stopped count lies outside the conserved population")
    require(population * int(gridlock) <= z <= population * int(gridlock) + population * int(full_lane),
            "the pointwise stopped-count sandwich fails")
    require(population > 0 or (z == 0 and not gridlock), "the empty state was treated as a nonempty jam")
    colored_seen = {}
    colored_transient = colored_period = None
    for time in range(len(orbit.states) + 1):
        colored = encode_rows(orbit.rows(state_index(orbit, time)))
        if colored in colored_seen:
            colored_transient = colored_seen[colored]
            colored_period = time - colored_transient
            break
        colored_seen[colored] = time
    require(colored_period is not None, "a complete labeled recurrence must close its colored orbit")
    return Case(width, height, code, orbit, stopped, full_lane, gridlock,
                len(core_labels(orbit, 0)), colored_transient, colored_period)


def scaled_initial_law(cases: list[Case], weights: list[int], *, denominator: int | None = None) -> dict:
    """Exact mass sandwich for arbitrary finite Nat weights, repeats permitted.

D is a positive common multiple of all possible nonzero populations. Dividing
by D times total weight yields probabilities only when the total is positive.
The empty-board score is explicitly zero.
"""
    if not cases or len(cases) != len(weights):
        raise ValueError("expected a nonempty support list with one weight per occurrence")
    if any(type(weight) is not int or weight < 0 for weight in weights):
        raise ValueError("initial weights must be natural numbers")
    width, height = cases[0].width, cases[0].height
    if any((case.width, case.height) != (width, height) for case in cases):
        raise ValueError("a finite law uses one torus")
    area = width * height
    D = factorial(area) if denominator is None else denominator
    if type(D) is not int or D <= 0 or any(D % n for n in range(1, area + 1)):
        raise ValueError("population denominator must be positive and divisible by 1,...,area")
    score = sum(weight * ((D // case.population) * case.stopped if case.population else 0)
                for case, weight in zip(cases, weights))
    direct = sum((weight * Fraction(case.stopped, case.population) if case.population else Fraction())
                 for case, weight in zip(cases, weights))
    jam_mass = sum(weight * int(case.gridlock) for case, weight in zip(cases, weights))
    lane_mass = sum(weight * int(case.full_lane) for case, weight in zip(cases, weights))
    total = sum(weights)
    require(Fraction(score, D) == direct, "integer population cancellation changed the normalized score")
    require(D * jam_mass <= score <= D * jam_mass + D * lane_mass,
            "the finite initial-weight stopped/core sandwich fails")
    g = Fraction(score, D * total) if total else None
    q = Fraction(jam_mass, total) if total else None
    r = Fraction(lane_mass, total) if total else None
    if total:
        require(0 <= g - q <= r, "the normalized finite-law comparison fails")
    return {"support_occurrences": len(cases), "distinct_support_codes": len({case.code for case in cases}),
            "total_weight": total, "population_denominator": D,
            "scaled_stopped_mass": score, "jam_weight": jam_mass, "full_lane_weight": lane_mass,
            "normalized_stopped_fraction": str(g) if g is not None else None,
            "gridlock_probability": str(q) if q is not None else None,
            "full_lane_probability": str(r) if r is not None else None,
            "gap": str(g - q) if g is not None else None,
            "probability_law_defined": total > 0}


def iid_initial_law(cases: list[Case], p: Fraction | int) -> dict:
    if isinstance(p, bool) or not isinstance(p, (Fraction, int)) or not 0 <= p <= 1:
        raise ValueError("density must be an exact rational in [0,1]")
    p = Fraction(p)
    area = cases[0].width * cases[0].height
    if len(cases) != 3 ** area or {case.code for case in cases} != set(range(3 ** area)):
        raise ValueError("IID evaluation requires every initial board exactly once")
    a, b = p.numerator, p.denominator
    weights = [a ** case.population * (2 * (b - a)) ** (area - case.population) for case in cases]
    result = scaled_initial_law(cases, weights)
    require(result["total_weight"] == (2 * b) ** area, "initial IID weights fail to normalize")
    if p in (0, 1):
        require(result["normalized_stopped_fraction"] == result["gridlock_probability"] == str(p),
                "empty/full density endpoint changed")
    return {"p": str(p), "initial_weight_formula": "a^N * (2*(b-a))^(area-N), p=a/b", **result}


def verify_export_rows(expected: list[tuple[int, ...]], output: str) -> None:
    lines = output.splitlines()
    require(len(lines) == len(expected), "Lean exporter returned missing or extra snapshot rows")
    for index, (row, line) in enumerate(zip(expected, lines)):
        require(line == ",".join(map(str, row)),
                f"Lean stopped/core snapshot mismatch at row {index}, request {row[:4]}: {line!r}")


def delayed_case(side: int) -> Case:
    delay = (side - 2) // 2
    rows = [[0] * side for _ in range(side)]
    for i in range(side):
        require(rows[i][(i - delay) % side] == rows[(i - delay) % side][(i + 1) % side] == 0,
                "delayed staircase sources overlap")
        rows[i][(i - delay) % side] = 1
        rows[(i - delay) % side][(i + 1) % side] = 2
    return analyze_case(side, side, encode_rows(rows))


def check_controls() -> tuple[list[tuple[Case, list[int]]], dict]:
    swapped = analyze_case(3, 3, 14)
    require(swapped.colored_period == 4 and swapped.orbit.period == 8
            and swapped.orbit.states[0] != swapped.orbit.states[4]
            and swapped.orbit.rows(0) == swapped.orbit.rows(4), "code 14 lost the identity/colored period discrepancy")
    require(swapped.stopped == 0 and not swapped.gridlock and not swapped.full_lane,
            "code 14 was misclassified as fixation")
    require(direct_path_count(swapped.orbit.rows(0), 2) == 1 and swapped.initial_core == 0,
            "code 14 no longer distinguishes short paths from the maximal core")
    targets = [(swapped, [0, 4, 8])]
    delayed = []
    for side in (4, 6):
        case = delayed_case(side)
        delay = (side - 2) // 2
        counts = [case.snapshot(t)[6] for t in range(delay + 2)]
        require(counts == [0] * delay + [2 * side] * 2
                and case.stopped == 2 * side and case.gridlock,
                "initial empty core was mistaken for the eventual core")
        targets.append((case, list(range(delay + 2))))
        delayed.append({"side": side, "code": case.code, "snapshot_core_counts": counts,
                        "stopped_original_tags": case.stopped, "formation_time": delay})
    empty, partial, jam, moving = [analyze_case(2, 2, code) for code in (0, 13, 4, 1)]
    equal_weights = scaled_initial_law([partial, jam], [1, 1])
    wrong_ratio = Fraction(partial.stopped + jam.stopped, partial.population + jam.population)
    require(equal_weights["normalized_stopped_fraction"] == "5/6" and wrong_ratio == Fraction(4, 5),
            "per-board normalization was replaced by a ratio of expected counts")
    positive_empty = scaled_initial_law([empty, partial, jam], [1, 1, 1])
    require(positive_empty["normalized_stopped_fraction"] == "5/9"
            and positive_empty["gridlock_probability"] == "1/3",
            "positive empty-board weight was discarded from normalization")
    repeated = scaled_initial_law([empty, partial, partial, jam, moving], [5, 3, 2, 7, 0])
    merged = scaled_initial_law([empty, partial, jam], [5, 5, 7])
    require(repeated["normalized_stopped_fraction"] == merged["normalized_stopped_fraction"] == "31/51"
            and repeated["gridlock_probability"] == "7/17", "repeated support or zero weights changed the finite law")
    zero_mass = scaled_initial_law([empty, partial], [0, 0])
    require(zero_mass["scaled_stopped_mass"] == 0 and not zero_mass["probability_law_defined"],
            "zero total weight was claimed as a probability law")
    return targets, {"colored_vs_labeled_recurrence": {"shape": [3, 3], "code": 14,
                     "colored_period": 4, "labeled_period": 8, "stopped_original_tags": 0,
                     "short_path_roots_at_time_zero": 1, "initial_core": 0},
                     "snapshot_core_growth": delayed,
                     "unequal_population_equal_weights": {
                         "codes": [partial.code, jam.code], "populations": [3, 2], "stopped_counts": [2, 2],
                         "weights": [1, 1], "correct_normalized_stopped_fraction": "5/6",
                         "incorrect_ratio_of_expected_counts": str(wrong_ratio), **equal_weights},
                     "positive_weight_empty_board": {"codes": [empty.code, partial.code, jam.code],
                         "populations": [0, 3, 2], "stopped_counts": [0, 2, 2], "weights": [1, 1, 1],
                         **positive_empty},
                     "nonjam_partial_full_lane": {"shape": [2, 2], "code": partial.code,
                         "population": partial.population, "stopped_count": partial.stopped,
                         "gridlock": partial.gridlock, "full_lane": partial.full_lane},
                     "repeated_support_and_zero_weights": repeated, "zero_total_weight_mass_only": zero_mass}


def source_hashes() -> dict[str, str]:
    names = {"scripts/check_stopped_core.py", "tests/test_stopped_core_acceptance.py",
             "bml/certificates.py", "bml/path_core.py", "bml/probability.py",
             "bml/fixation.py", "bml/capture.py", "bml/exhaustive.py", "bml/model.py",
             "formal/lean/lakefile.toml", "formal/lean/lean-toolchain",
             ".github/workflows/finite-bml.yml", "requirements-dev.txt"}
    # Include the complete local Lean source set: the count/mass theorems,
    # actual movement kernel, exporter refinement, aggregate import and audits.
    names.update(str(path.relative_to(ROOT)) for path in (ROOT / "formal/lean").rglob("*.lean")
                 if ".lake" not in path.relative_to(ROOT).parts)
    return {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in sorted(names)}


def git_snapshot() -> dict:
    refs = subprocess.run(["git", "rev-parse", "HEAD", "HEAD^{tree}"], cwd=ROOT,
                          check=True, text=True, capture_output=True).stdout.splitlines()
    status = subprocess.run(["git", "status", "--porcelain"], cwd=ROOT,
                            check=True, text=True, capture_output=True).stdout
    return {"head": refs[0], "tree": refs[1], "worktree_clean": not status, "status_porcelain": status}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=ROOT / "formal/lean/.lake/build/bin/stopped_core_export")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    binary = args.binary.resolve(strict=True)
    started, before, git_before = perf_counter(), source_hashes(), git_snapshot()
    binary_hash = hashlib.sha256(binary.read_bytes()).hexdigest()
    cases_by_shape = {shape: [analyze_case(*shape, code) for code in range(3 ** (shape[0] * shape[1]))]
                      for shape in DOMAINS}
    targets, controls = check_controls()
    requests = {shape: {(case.code, time): case.snapshot(time)
                       for case in cases for time in {0, case.orbit.cycle_start}}
                for shape, cases in cases_by_shape.items()}
    for case, times in targets:
        bucket = requests.setdefault((case.width, case.height), {})
        for time in times:
            bucket[case.code, time] = case.snapshot(time)
    lean_output = hashlib.sha256()
    rows_compared = 0
    for (width, height), request_map in requests.items():
        expected = [row for _, row in sorted(request_map.items())]
        arguments = [str(binary), str(width), str(height)] + [f"{row[2]}:{row[3]}" for row in expected]
        result = subprocess.run(arguments, check=True, text=True, capture_output=True, timeout=180)
        verify_export_rows(expected, result.stdout)
        lean_output.update(result.stdout.encode())
        rows_compared += len(expected)
    domains = []
    for (width, height), cases in cases_by_shape.items():
        laws = [iid_initial_law(cases, p) for p in DENSITIES]
        if (width, height) == (3, 3):
            half = next(law for law in laws if law["p"] == "1/2")
            require(half["normalized_stopped_fraction"] == "476101/3670016"
                    and half["gridlock_probability"] == "12613/131072"
                    and half["gap"] == "122937/3670016", "existing exact normalized-core fixture changed")
            require(sum(case.stopped for case in cases) == 52002, "existing final-core incidence count changed")
        domains.append({"width": width, "height": height, "all_initial_boards": len(cases),
                        "independent_labeled_edges": sum(len(case.orbit.moved) for case in cases),
                        "stopped_original_tag_incidences": sum(case.stopped for case in cases),
                        "later_core_growth_boards": sum(case.initial_core < case.stopped for case in cases),
                        "pointwise_count_sandwich_checks": len(cases),
                        "core_equals_stopped_label_set_checks": len(cases),
                        "initial_iid_laws": laws})
    print(f"Numerical comparisons passed: {sum(len(c) for c in cases_by_shape.values()):,} boards, "
          f"{rows_compared:,} Lean snapshot rows, {len(DOMAINS) * len(DENSITIES)} exact initial IID laws.", flush=True)
    after, git_after = source_hashes(), git_snapshot()
    require(before == after and git_before == git_after, "sources changed during stopped/core acceptance")
    require(binary_hash == hashlib.sha256(binary.read_bytes()).hexdigest(), "Lean exporter changed during acceptance")
    report = {"schema": "bml.stopped-core-replay.v1", "status": "passed", "rule": "CLASSIC",
              "git_before": git_before, "git_after": git_after, "source_unchanged": True,
              "source_sha256_before": before, "source_sha256_after": after,
              "lean_binary_sha256": binary_hash, "lean_rows_sha256": lean_output.hexdigest(),
              "lean_snapshot_rows": rows_compared, "exhaustive_initial_boards": sum(len(c) for c in cases_by_shape.values()),
              "complete_labeled_recurrences": sum(len(c) for c in cases_by_shape.values()),
              "unresolved_orbits": 0, "domains": domains, "controls": controls,
              "population_denominator": "area!; zero-population score is zero",
              "weight_scope": "finite initial Nat weights; repeated supports and zero weights allowed",
              "normalization": "divide scaled stopped mass by area! times total weight only when total weight is positive",
              "seconds": round(perf_counter() - started, 6),
              "not_established": ["fixed-positive-density nonjamming as the torus grows",
                                  "an asymptotic core-growth estimate", "a uniform recurrence-time bound",
                                  "unrestricted source refinement between Python and Lean"]}
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Stopped/core acceptance passed: {report['exhaustive_initial_boards']:,} initial boards, "
          f"{rows_compared:,} Lean snapshot rows, {len(DOMAINS) * len(DENSITIES)} exact initial IID laws.")


if __name__ == "__main__":
    main()
