"""Does the cut-rank argument of `BML.Train.Diagonals.half_eventual_stable` apply to the
finite Kuramoto phase model of larsbx/finite-swarm-dynamics?

The blue-unit headings over F_p form a cyclic group of order n. Index them by k in Z_n. With
identity natural rotors the corrected class of an oscillator is its index. The abstract theorem
needs, in one of the two orientations of Z_n,
  step:    every index stays or moves one class back;
  release: an occupied class whose successor class is empty stays occupied.
Its conclusion is that every index is eventually constant.

This script enumerates every state of m all-to-all oscillators and counts where the hypotheses
and the conclusion hold. It imports the swarm repository's exact Python reference, so it needs
a checkout: `python scripts/swarm_cut_rank.py --swarm PATH [--write]`.
"""
from __future__ import annotations

import argparse
import itertools
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "docs/research/data/2026-11-27-swarm-cut-rank.json"
CASES = [(7, 2), (7, 3), (11, 2), (11, 3), (13, 2), (13, 3)]


def unit_group(g, f, p):
    units = [g.v(a, b) for a in range(p) for b in range(p) if (a * a + b * b) % p == 1]
    from reference.finite_phase_models import rotor_multiply
    one = g.v(1, 0)
    for gen in units:
        powers, u = [one], gen
        while u != one:
            powers.append(u)
            u = rotor_multiply(g, gen, u)
        if len(powers) == len(units):
            return powers
    raise ValueError("unit group is not cyclic")


def analyse(p: int, m: int) -> dict:
    from reference.extension_chromogeometry import ChromaticPlane, FiniteField
    from reference.finite_phase_models import PhaseState, finite_kuramoto_step
    f = FiniteField(p)
    g = ChromaticPlane(f)
    powers = unit_group(g, f, p)
    n = len(powers)
    index = {u: k for k, u in enumerate(powers)}
    weights = tuple(tuple(f.one if i != j else f.zero for j in range(m)) for i in range(m))
    rotors = (powers[0],) * m
    rows = []
    for kappa in range(1, p):
        coupling = sum((f.one for _ in range(kappa)), f.zero)

        def step(state):
            nxt = finite_kuramoto_step(g, PhaseState(tuple(powers[k] for k in state)),
                                       weights=weights, coupling=coupling, natural_rotors=rotors)
            return tuple(index[u] for u in nxt.headings)

        states = list(itertools.product(range(n), repeat=m))
        nxt = {s: step(s) for s in states}

        def hypotheses(s, sign):
            t = nxt[s]
            stays = all((b - a) % n in (0, (-sign) % n) for a, b in zip(s, t))
            release = all(b in t for b in set(s) if (b + sign) % n not in s)
            return stays, release

        def locks(s):
            seen = set()
            while s not in seen:
                seen.add(s)
                s = nxt[s]
            return nxt[s] == s

        sparse = [s for s in states if 2 * len(s) <= n]
        both = {sign: sum(all(hypotheses(s, sign)) for s in states) for sign in (1, -1)}
        rows.append({
            "kappa": kappa,
            "states": len(states),
            "step_holds": {str(sign): sum(hypotheses(s, sign)[0] for s in states) for sign in (1, -1)},
            "step_and_release_hold": {str(sign): both[sign] for sign in (1, -1)},
            "moving_states": sum(nxt[s] != s for s in states),
            "moving_states_with_step": {
                str(sign): sum(nxt[s] != s and hypotheses(s, sign)[0] for s in states)
                for sign in (1, -1)},
            "sparse_states": len(sparse),
            "sparse_states_locking": sum(locks(s) for s in sparse),
            "states_locking": sum(locks(s) for s in states),
        })
    return {"p": p, "oscillators": m, "unit_group_order": n, "by_coupling": rows}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--swarm", type=Path, required=True)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    sys.path.insert(0, str(args.swarm.resolve()))
    commit = subprocess.check_output(["git", "-C", str(args.swarm), "rev-parse", "HEAD"], text=True).strip()
    report = {
        "schema": "swarm.cut-rank.v1",
        "swarm_repository": "larsbx/finite-swarm-dynamics",
        "swarm_commit": commit,
        "model": "finite_kuramoto_step, all-to-all unit weights, identity natural rotors, no lag",
        "cases": [analyse(p, m) for p, m in CASES],
    }
    text = json.dumps(report, indent=1) + "\n"
    if args.write:
        OUT.write_text(text)
    for case in report["cases"]:
        rows = case["by_coupling"]
        print(f"F_{case['p']}, m={case['oscillators']}, n={case['unit_group_order']}: "
              f"moving states obeying step, best over kappa and orientation = "
              f"{max(max(r['moving_states_with_step'].values()) for r in rows)} of "
              f"{min(r['moving_states'] for r in rows)}..{max(r['moving_states'] for r in rows)}; "
              f"sparse locking {min(r['sparse_states_locking'] for r in rows)}.."
              f"{max(r['sparse_states_locking'] for r in rows)} of {rows[0]['sparse_states']}")


if __name__ == "__main__":
    main()
