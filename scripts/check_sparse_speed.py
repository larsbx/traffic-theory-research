#!/usr/bin/env python3
"""Replay inclusive CLASSIC B7, missed movements, and permanent-flow deadlines.

Automatic sparse cases run through exact first recurrence. Only those complete
traces certify the permanent-flow entry time; targeted finite prefixes do not.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
from itertools import combinations, product
import json
from math import gcd, lcm
from pathlib import Path
import subprocess

from check_freeflow import (
    ROOT, decode_scalar, encode_scalar, require, scalar_phase, scalar_round, static_rules,
)

import numpy as np

from bml.model import EAST, NORTH, TRAIN, step

SHAPES = (
    (1, 1), (1, 5), (5, 1), (2, 2), (2, 4), (4, 2), (3, 3), (3, 6), (6, 3),
    (4, 4), (4, 8), (8, 4), (5, 5), (5, 10), (10, 5), (6, 6),
)


def sparse_codes(w: int, h: int):
    powers = [3**i for i in range(w*h)]
    for m in range(gcd(w, h)//2 + 1):
        for slots in combinations(powers, m):
            for species in product((EAST, NORTH), repeat=m):
                yield sum(slot * sp for slot, sp in zip(slots, species))


@dataclass
class Trace:
    width: int
    height: int
    code: int
    population: int
    sparse: bool
    rounds: list[tuple[int, ...]]
    recurrence: int | None
    saturation_states: int

    def request(self) -> str:
        return f"{self.width} {self.height} {self.code} {len(self.rounds)}"

    def row(self) -> str:
        header = self.request().split() + [str(self.population), str(int(self.sparse)),
                                           str(self.deadline) if self.sparse else "-"]
        return "\t".join(header + [",".join(map(str, row)) for row in self.rounds])

    @property
    def blocked_rounds(self) -> int:
        return sum(1 - row[2] for row in self.rounds)

    @property
    def missed_moves(self) -> int:
        return sum(self.population - row[3] for row in self.rounds)

    @property
    def deadline(self) -> int | None:
        if not self.sparse:
            return None
        return lcm(self.width, self.height) * self.population * max(gcd(self.width, self.height)-2, 0)

    @property
    def permanent_flow_entry(self) -> int | None:
        if self.recurrence is None:
            return None
        return max((t + 1 for t, row in enumerate(self.rounds) if not row[2]), default=0)


def target(p: int, sp: int, w: int, h: int) -> int:
    y, x = divmod(p, w)
    return y*w + (x+1) % w if sp == EAST else ((y+1) % h)*w + x


def empty_pairs(classes: list[int], g: int) -> set[int]:
    occupied = set(classes)
    return {i for i in range(g) if i not in occupied and (i+1) % g not in occupied}


def trace_case(w: int, h: int, code: int, horizon: int | None = None) -> Trace:
    initial = decode_scalar(code, w*h)
    sites = [i for i, cell in enumerate(initial) if cell]
    species = [initial[p] for p in sites]
    g, population = gcd(w, h), len(sites)
    sparse = 2 * population <= g
    per_car_budget = max(g-2, 0)
    round_budget = population * per_car_budget
    case = f"{w}x{h} board {code}"
    if horizon is None:
        require(sparse, "density", f"{case}: automatic recurrence search requires 2m <= g")
    limit = horizon if horizon is not None else (round_budget + 1) * lcm(w, h)
    rows = []
    blocks = [0] * population
    classes = [(p % w + p // w) % g for p in sites]
    saturation_states = int(sparse and not empty_pairs(classes, g))
    require(not saturation_states or all(static_rules(initial, w, h)),
            "saturation", f"{case}: no adjacent empty pair but initial state is not static-free")
    seen = {initial: 0}
    board = initial
    recurrence = None
    for t in range(limit):
        east, after, em, nm = scalar_round(board, w, h)
        all_move = int(em + nm == population)
        static_after = int(all(static_rules(after, w, h)))
        fields = [encode_scalar(east), encode_scalar(after), all_move, em + nm, static_after]
        after_classes = []
        tagged_moves = 0
        for i, (p, sp) in enumerate(zip(sites, species)):
            q = target(p, sp, w, h)
            snapshot = board if sp == EAST else east
            moved = int(snapshot[q] == 0)
            sites[i] = q if moved else p
            y = (sites[i] % w + sites[i] // w - t - 1) % g
            require(after[sites[i]] == sp and y == (classes[i] + moved - 1) % g,
                    "tag-dynamics", f"{case} round {t}: tag {i} lost or incorrect Y-value")
            blocks[i] += 1 - moved
            tagged_moves += moved
            after_classes.append(y)
            fields.extend((sites[i], moved, y))
        require(len(set(sites)) == population and sum(bool(cell) for cell in after) == population,
                "tag-coverage", f"{case} round {t}: tag trace does not cover all cars")
        require(empty_pairs(after_classes, g) <= empty_pairs(classes, g),
                "empty-pair", f"{case} round {t}: a new corrected vacancy pair appeared")
        no_pair = not empty_pairs(after_classes, g)
        require(not sparse or not no_pair or static_after,
                "saturation", f"{case} round {t}: no empty pair without permanent free flow")
        saturation_states += int(sparse and no_pair)
        require(tagged_moves == em + nm and population - tagged_moves >= 0,
                "movement-count", f"{case} round {t}: tagged and Eulerian movement disagree")
        classes = after_classes
        rows.append(tuple(fields))
        if horizon is None and after in seen:
            recurrence = seen[after]
            break
        seen[after] = t + 1
        board = after

    trace = Trace(w, h, code, population, sparse, rows, recurrence, saturation_states)
    if horizon is None:
        require(recurrence is not None and all(row[2] for row in rows[recurrence:]),
                "eventual-movement", f"{case}: no all-moving terminal cycle found")
    if sparse:
        require(max(blocks, default=0) <= per_car_budget
                and trace.blocked_rounds <= trace.missed_moves <= round_budget,
                "block-bound", f"{case}: sparse prefix exceeds the B7 blockage budget")
        require(all(t < trace.deadline or row[2] for t, row in enumerate(rows)),
                "stabilization-deadline", f"{case}: a round at or after the deadline blocks")
        if recurrence is not None:
            require(trace.permanent_flow_entry <= trace.deadline,
                    "stabilization-deadline", f"{case}: permanent movement starts after the deadline")
    require(trace.missed_moves == sum(blocks),
            "movement-count", f"{case}: cumulative tag misses disagree with the Eulerian deficit")
    return trace


def check_controls() -> tuple[list[Trace], dict]:
    # Complement empty and one-car exhaustive cases with larger genuine sparse queues.
    three = trace_case(7, 14, 3**6 + 1 + 3)
    four = trace_case(9, 9, 2*(1 + 3**9 + 3**18 + 3**27))
    equality = trace_case(4, 4, 1 + 2*3**2)
    jam = trace_case(3, 3, 1 + 3 + 3**2, 5)
    equality_classes = [p % 4 + p // 4 for p, c in enumerate(decode_scalar(equality.code, 16)) if c]
    require(equality.sparse and 2*equality.population == 4
            and not empty_pairs(equality_classes, 4) and equality.permanent_flow_entry == 0,
            "density", "equality without an adjacent empty pair must be permanently free")
    jam_budget = jam.population * (gcd(jam.width, jam.height) - 2)
    require(not jam.sparse and jam.blocked_rounds > jam_budget
            and all(row[1] == jam.code for row in jam.rounds),
            "density", "the dense frozen row must violate the finite bound")

    # A wrap-around east queue moves together under TRAIN. CLASSIC blocks its rear.
    queue = trace_case(5, 5, 1 + 3**4, 1)
    board = np.array(decode_scalar(queue.code, 25), dtype=np.int8).reshape(5, 5)
    train_board, train_moves = step(board, TRAIN)
    require(queue.rounds[0][2] == 0 and int(train_moves) == 2
            and encode_scalar(tuple(map(int, train_board.flat))) != queue.rounds[0][1],
            "movement-rule", "TRAIN queue mutation did not differ from CLASSIC")

    # At (0,1), the east phase vacates the north car's target; at (1,1), it fills it.
    vacated = trace_case(5, 5, 2 + 3**5, 1)
    filled = trace_case(5, 5, 2*3 + 3**5, 1)
    for trace, expected in ((vacated, 1), (filled, 0)):
        pre_round = decode_scalar(trace.code, 25)
        wrong = scalar_phase(pre_round, 5, 5, NORTH)[1]
        require(trace.rounds[0][6] == expected and wrong == 1 - expected,
                "phase-order", "north must read the board produced by the east phase")
    zero = trace_case(1, 1, 0, 0)

    # Nine fully moving rounds can precede a block. The last block is later
    # than the B7 bad-round budget, while the lcm-scaled deadline remains valid.
    late = trace_case(5, 10, 1 + 2*3**5)
    late_budget = late.population * (gcd(late.width, late.height) - 2)
    require(late.blocked_rounds == 1 and late.rounds[9][2] == 0
            and all(row[2] for row in late.rounds[:9])
            and late.permanent_flow_entry == 10 > late_budget == 6
            and late.deadline == 60,
            "elapsed-time", "bad-round count or an initially moving prefix was used as permanent flow")
    boundary_one = trace_case(2, 4, 2)
    require(boundary_one.deadline == boundary_one.permanent_flow_entry == 0
            and equality.deadline == 16 and jam.deadline is None and zero.deadline == 0,
            "deadline-domain", "inclusive deadline mishandled equality, the empty board, or dense gridlock")
    require(queue.permanent_flow_entry is None and vacated.permanent_flow_entry is None,
            "deadline-domain", "a targeted prefix was misrepresented as a complete orbit")
    simultaneous = trace_case(6, 6, 13)
    require(simultaneous.blocked_rounds == 2 and simultaneous.missed_moves == 3
            and [simultaneous.population-row[3] for row in simultaneous.rounds[:2]] == [2, 1],
            "movement-count", "blocked rounds were confused with missed car movements")
    above = trace_case(4, 4, 13, 8)
    require(not above.sparse and above.deadline is None
            and above.rounds[3][1] == above.rounds[7][1] == above.code
            and all(not row[2] for row in above.rounds) and above.missed_moves == 16,
            "density", "above-boundary recurrent slowdown was admitted as inclusive sparse flow")
    return [three, four, equality, jam, queue, vacated, filled, zero, late,
            boundary_one, simultaneous, above], {
        "larger_sparse_queues": [three.population, four.population],
        "equality_no_empty_pair_is_static_free": True,
        "gcd_two_boundary_deadline_zero": True,
        "dense_fixed_row_blocked_rounds": jam.blocked_rounds,
        "train_queue_differs": True,
        "north_target_vacated_and_filled": True,
        "zero_horizon": True,
        "elapsed_time_exceeds_block_budget": {
            "shape": [5, 10], "code": late.code, "block_budget": late_budget,
            "blocked_rounds": late.blocked_rounds, "permanent_flow_entry": late.permanent_flow_entry,
            "deadline": late.deadline,
        },
        "deadline_excludes_nonsparse_boards": True,
        "finite_prefix_not_claimed_permanent": True,
        "simultaneous_blockages": {"blocked_rounds": simultaneous.blocked_rounds,
                                    "missed_moves": simultaneous.missed_moves},
        "above_boundary_recurrent_slowdown": {"shape": [4, 4], "code": above.code,
                                               "period": 4, "misses_per_period": 8},
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=ROOT / "formal/lean/.lake/build/bin/sparse_speed_export")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    binary = args.binary.resolve(strict=True)
    traces = [trace_case(w, h, code) for w, h in SHAPES for code in sparse_codes(w, h)]
    controls, control_results = check_controls()
    combined = traces + controls
    result = subprocess.run([binary], input="\n".join(t.request() for t in combined) + "\n",
                            check=True, capture_output=True, text=True, timeout=180)
    actual = result.stdout.splitlines()
    require(len(actual) == len(combined), "coverage", "missing or extra Lean trace rows")
    for line, expected in zip(actual, combined):
        require(line == expected.row(), "lean-trace", f"CLASSIC Lean/independent mismatch for {expected.request()}")

    git = subprocess.run(["git", "rev-parse", "HEAD", "HEAD^{tree}"], cwd=ROOT,
                         text=True, capture_output=True)
    revision, tree = git.stdout.splitlines() if git.returncode == 0 else (None, None)
    status = subprocess.run(["git", "status", "--porcelain"], cwd=ROOT,
                            text=True, capture_output=True)
    report = {
        "schema": "bml.sparse-speed-replay.v3",
        "worktree_clean": status.returncode == 0 and not status.stdout,
        "lean_binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
        "status": "passed", "revision": revision, "tree": tree,
        "ordered_shapes": SHAPES, "exhaustive_sparse_boards": len(traces),
        "rounds_through_first_recurrence": sum(len(t.rounds) for t in traces),
        "sparse_boards_with_blockage": sum(t.blocked_rounds > 0 for t in traces),
        "equality_boards": sum(2*t.population == gcd(t.width, t.height) for t in traces),
        "saturation_state_observations": sum(t.saturation_states for t in traces),
        "missed_move_checks": {
            "tag_and_eulerian_rounds": sum(len(t.rounds) for t in combined),
            "orbits_with_more_misses_than_blocked_rounds": sum(t.missed_moves > t.blocked_rounds for t in traces),
        },
        "deadline_checks": {
            "complete_exhaustive_orbits": len(traces),
            "max_permanent_flow_entry": max(t.permanent_flow_entry for t in traces),
            "max_deadline": max(t.deadline for t in traces),
            "zero_deadline_orbits": sum(t.deadline == 0 for t in traces),
        },
        "targeted_cases": len(controls), "controls": control_results,
        "lean_trace_sha256": hashlib.sha256(result.stdout.encode()).hexdigest(),
    }
    print(json.dumps(report, indent=2))
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
