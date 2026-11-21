#!/usr/bin/env python3
"""Replay CLASSIC B7 blockage counts and permanent-flow deadlines.

Automatic sparse cases run through exact first recurrence. Only those complete
traces certify the permanent-flow entry time; targeted finite prefixes do not.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
from itertools import combinations, product
import json
from math import comb, gcd, lcm
from pathlib import Path
import subprocess

from check_freeflow import (
    ROOT, decode_scalar, encode_scalar, require, scalar_phase, scalar_round,
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
    alternating_checks: int

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
    seen = {initial: 0}
    board = initial
    recurrence = None
    alternating_checks = 0
    for t in range(limit):
        east, after, em, nm = scalar_round(board, w, h)
        all_move = int(em + nm == population)
        fields = [encode_scalar(east), encode_scalar(after), all_move]
        after_classes = []
        for i, (p, sp) in enumerate(zip(sites, species)):
            q = target(p, sp, w, h)
            snapshot = board if sp == EAST else east
            moved = int(snapshot[q] == 0)
            sites[i] = q if moved else p
            y = (sites[i] % w + sites[i] // w - t - 1) % g
            require(after[sites[i]] == sp and y == (classes[i] + moved - 1) % g,
                    "tag-dynamics", f"{case} round {t}: tag {i} lost or incorrect Y-value")
            blocks[i] += 1 - moved
            after_classes.append(y)
            fields.extend((sites[i], moved, y))
        require(len(set(sites)) == population and sum(bool(cell) for cell in after) == population,
                "tag-coverage", f"{case} round {t}: tag trace does not cover all cars")
        require(empty_pairs(after_classes, g) <= empty_pairs(classes, g),
                "empty-pair", f"{case} round {t}: a new corrected vacancy pair appeared")
        if sparse and not empty_pairs(classes, g):
            alternating_checks += 1
            # Equality is the only sparse case without an empty pair. Covering
            # all classes forces alternating singleton classes, and every tag
            # keeps its corrected class because it moves in this round.
            require(2 * population == g and len(set(classes)) == population
                    and all((i + 1) % g not in classes for i in classes),
                    "alternating", f"{case} round {t}: no empty pair without alternating singletons")
            require(all_move == 1 and after_classes == classes,
                    "alternating-invariant", f"{case} round {t}: alternating tags did not all move")
        if 2 * population < g:
            require(bool(empty_pairs(after_classes, g)),
                    "empty-pair", f"{case} round {t}: strict sparse board has no empty pair")
        classes = after_classes
        rows.append(tuple(fields))
        if horizon is None and after in seen:
            recurrence = seen[after]
            break
        seen[after] = t + 1
        board = after

    trace = Trace(w, h, code, population, sparse, rows, recurrence, alternating_checks)
    if horizon is None:
        require(recurrence is not None and all(row[2] for row in rows[recurrence:]),
                "eventual-movement", f"{case}: no all-moving terminal cycle found")
    if sparse:
        require(max(blocks, default=0) <= per_car_budget and trace.blocked_rounds <= round_budget,
                "block-bound", f"{case}: sparse prefix exceeds the B7 blockage budget")
        require(all(t < trace.deadline or row[2] for t, row in enumerate(rows)),
                "stabilization-deadline", f"{case}: a round at or after the deadline blocks")
        if recurrence is not None:
            require(trace.permanent_flow_entry <= trace.deadline,
                    "stabilization-deadline", f"{case}: permanent movement starts after the deadline")
    return trace


def check_controls() -> tuple[list[Trace], dict]:
    # Complement empty and one-car exhaustive cases with larger genuine sparse queues.
    three = trace_case(7, 14, 3**6 + 1 + 3)
    four = trace_case(9, 9, 2*(1 + 3**9 + 3**18 + 3**27))
    equality = trace_case(4, 4, 1 + 2*3**2)
    equality_queue = trace_case(4, 4, 1 + 3)
    equality_rectangles = [
        trace_case(6, 12, 1 + 3 + 3**2),
        trace_case(12, 6, 2*(1 + 3**12 + 3**24)),
    ]
    just_above = [
        trace_case(2, 2, 1 + 3, 2),
        trace_case(3, 3, 1 + 3, 4),
        trace_case(4, 4, 1 + 3 + 3**2, 8),
    ]
    jam = trace_case(3, 3, 1 + 3 + 3**2, 5)
    equality_classes = [p % 4 + p // 4 for p, c in enumerate(decode_scalar(equality.code, 16)) if c]
    require(equality.sparse and 2*equality.population == 4 and not empty_pairs(equality_classes, 4)
            and equality.blocked_rounds == 0 and equality.permanent_flow_entry == 0,
            "density", "alternating equality must have no empty pair and move forever")
    queue_classes = [p % 4 + p // 4 for p, c in enumerate(decode_scalar(equality_queue.code, 16)) if c]
    require(bool(empty_pairs(queue_classes, 4)) and equality_queue.blocked_rounds == 1
            and equality_queue.permanent_flow_entry == 1,
            "equality-transient", "equality queue must block before entering alternating flow")
    for trace in equality_rectangles:
        require(trace.sparse and 2*trace.population == gcd(trace.width, trace.height)
                and trace.blocked_rounds > 0 and trace.recurrence is not None,
                "equality-rectangle", "rectangular equality queue did not complete its transient")
    for trace in just_above:
        g = gcd(trace.width, trace.height)
        require(trace.population == g//2 + 1 and not trace.sparse and trace.deadline is None
                and trace.blocked_rounds > trace.population * max(g-2, 0),
                "density", "just-above-boundary persistent blockage must not receive a deadline")
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
        require(trace.rounds[0][4] == expected and wrong == 1 - expected,
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
    require(equality.deadline == 16 and equality_queue.deadline == 16
            and jam.deadline is None and zero.deadline == 0,
            "deadline-domain", "deadline guarantee escaped inclusive sparsity or excluded equality/empty boards")
    require(queue.permanent_flow_entry is None and vacated.permanent_flow_entry is None,
            "deadline-domain", "a targeted prefix was misrepresented as a complete orbit")
    return [three, four, equality, equality_queue, *equality_rectangles, *just_above,
            jam, queue, vacated, filled, zero, late], {
        "larger_sparse_queues": [three.population, four.population],
        "alternating_equality_included": {
            "shape": [4, 4], "code": equality.code, "permanent_flow_entry": 0,
            "deadline": equality.deadline,
        },
        "equality_transient": {
            "shape": [4, 4], "code": equality_queue.code, "blocked_rounds": 1,
            "permanent_flow_entry": 1, "deadline": equality_queue.deadline,
        },
        "rectangular_equality_queues": [
            {"shape": [t.width, t.height], "code": t.code,
             "blocked_rounds": t.blocked_rounds, "permanent_flow_entry": t.permanent_flow_entry,
             "deadline": t.deadline} for t in equality_rectangles
        ],
        "just_above_boundary_excluded": [
            {"shape": [t.width, t.height], "code": t.code, "population": t.population,
             "blocked_rounds": t.blocked_rounds, "deadline": t.deadline} for t in just_above
        ],
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
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=ROOT / "formal/lean/.lake/build/bin/sparse_speed_export")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    binary = args.binary.resolve(strict=True)
    traces = [trace_case(w, h, code) for w, h in SHAPES for code in sparse_codes(w, h)]
    expected_boards = sum(sum(comb(w*h, m) * 2**m for m in range(gcd(w, h)//2 + 1))
                          for w, h in SHAPES)
    require(len(traces) == expected_boards, "coverage", "inclusive exhaustive enumeration is incomplete")
    controls, control_results = check_controls()
    combined = traces + controls
    result = subprocess.run([binary], input="\n".join(t.request() for t in combined) + "\n",
                            check=True, capture_output=True, text=True, timeout=600)
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
        "sparse_condition": "2m <= gcd(width,height)",
        "ordered_shapes": SHAPES, "exhaustive_sparse_boards": len(traces),
        "exhaustive_equality_boards": sum(2*t.population == gcd(t.width, t.height) for t in traces),
        "equality_boards_with_blockage": sum(
            2*t.population == gcd(t.width, t.height) and t.blocked_rounds > 0 for t in traces),
        "alternating_invariant_checks": sum(t.alternating_checks for t in traces),
        "per_shape_coverage": [
            {"shape": [w, h], "maximum_population": gcd(w, h)//2,
             "boards": sum(comb(w*h, m) * 2**m for m in range(gcd(w, h)//2 + 1)),
             "equality_boards": (comb(w*h, gcd(w, h)//2) * 2**(gcd(w, h)//2)
                                 if gcd(w, h) % 2 == 0 else 0)} for w, h in SHAPES
        ],
        "rounds_through_first_recurrence": sum(len(t.rounds) for t in traces),
        "sparse_boards_with_blockage": sum(t.blocked_rounds > 0 for t in traces),
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
