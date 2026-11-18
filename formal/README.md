# Formal coverage and validation

The `BML` suite implements the same positive W×H torus and synchronous **east
then north** updates as `bml/model.py`. Move eligibility is read from the complete
pre-half-step state. Width or height one is allowed. A jam must be nonempty;
the empty fixed state is classified as free flow.

The formal kernel, finite correspondence checks, and prose mathematics have
different scopes. This register records those distinctions explicitly.

## Two complementary proof suites

| Suite | Proved constructions and checks | Detailed entry point |
| --- | --- | --- |
| `BML` / `BML.qnt` | Finite-torus update semantics, species transport bijections, nonempty-jam boundaries, G1/F arithmetic components, and a strong identity-aware non-monotonicity witness. Separate finite replays compare Lean and Quint with NumPy. | The register and commands below; [Lean package](lean/README.md). |
| `Traffic` / `traffic.qnt` | General-grid freezing, exact 21-Wang-tile recoding, a constructed infinite staircase for any supplied direction word, finite Fibonacci count and algebraic-length identities, and winding conditional on modular closure. Six finite grids are compared directly between Lean and Quint. | [Traffic coverage and acceptance](traffic-layer.md); [Traffic inventory](coverage.json). |

Both suites use old-state simultaneous eligibility and east-then-north full
steps. Their types, predicates, and executable comparison contracts are
separate. No general `BML`–`Traffic` equivalence or unbounded cross-language
refinement theorem is asserted. Their finite replay counts must not be added
and described as a single common domain or theorem.

The shared dependency-free Lean package pins Lean 4.34.1. `lake build` builds
`BML`, `bml_replay`, `Traffic`, and `traffic_export`. `Audit.lean` remains the BML
audit; `TrafficAudit.lean` checks the Traffic declarations and exporter.
`formal/coverage.json` is the Traffic suite's inventory, not a replacement for
the BML audit's required theorem list.

The rest of this page retains the **BML finite-torus coverage register**.
Run `python3 scripts/check_formal.py` for the separate Traffic acceptance gate,
after installing the same locked Quint dependency; its instructions and full
scope are in [traffic-layer.md](traffic-layer.md).

## BML finite-torus coverage register

| Claim | Current evidence | Remaining obligation |
|---|---|---|
| Half-step semantics, no collisions or created cars | Universal Lean proofs of source/destination behavior and an explicit bijection on each species' cars; the other species stays in place. | Relate the executable numerical `speciesCount` sum to this bijection in a separate general theorem. |
| G0 local equivalence | Lean proves full-step fixed ⇔ local blockage ⇔ no movers in either phase, on the actual finite-torus kernel. Frozen states persist through every iterate. | General eventual periodicity and correctness of the orbit classifier are still separate obligations; the cycle-average formulation is explained in prose. |
| Full occupancy and the empty boundary | Lean proves full occupancy freezes; the empty state is fixed but is not a jam. Nonemptiness is invariant under evolution. | No missing local boundary lemma is claimed. |
| G1 minimum gridlock | Prose blocker-cycle proof; executable constructions; Lean winding arithmetic: a nonzero closed nonnegative winding costs at least min(W,H). | Extract a simple blocker cycle in Lean, connect its displacements and distinct-car count, and prove the all-count constructions. |
| G2 sub-full non-gridlock construction | Prose proof, tested single-species constructions, and bounded classifier evidence. | Prove the all-count construction and its perpetual movement in Lean. |
| R, free-flow rigidity and phase classes | Prose proof; static/dynamic equivalence tested on every state of every ordered rectangle with WH≤9 and random larger examples. | Prove ⟨(1,−1)⟩ = ker(x+y mod gcd(W,H)), and connect both directions of rigidity to the kernel. |
| F, maximal free flow | Prose packing proof and constructions; Lean proves V(g)=⌊2g/3⌋ and 3V(g)=2g iff 3 divides g. | Formalize class packing, the upper bound, and the maximizing constructions. The g=1 branch remains separate. |
| Strong non-monotonicity | Lean proves code 3858 reaches a jam, while adding a stationary N yields the perpetual two-cycle 3860↔4340. An explicitly tracked original car moves every step. Independent labeled Python replay also checks the identities. | No minimality or novelty claim. |
| No initial simple loop, followed by gridlock | Reproducible identity-aware Python certificate on 3×2, compared against NumPy. | This witness is not currently a Lean theorem. |
| Python/Lean/Quint correspondence | Actual implementations are evaluated and compared on the finite domains below, including both half-steps and separate move counts. | A finite replay is not unrestricted source refinement or proof of the classifier algorithm. |
| Critical density and probabilistic switch | Published background and empirical context only. | No critical-density value, positive-density low-density phase, or dynamical loop-formation bound is proved. |

## Reproduce the BML suite

For the BML suite, use Python 3.12, Node.js 22, and the Lean toolchain pinned in
[`lean/lean-toolchain`](lean/lean-toolchain). From the repository root:

```sh
python -m pip install -r requirements-dev.txt
python -m pytest -q
npm ci --ignore-scripts --prefix formal/quint
cd formal/lean
lake build
lake env lean Audit.lean
cd ../..
python scripts/check_lean_replay.py --max-cells 9 --report .artifacts/lean-replay.json
python formal/quint/check.py --max-cells 6 --report .artifacts/quint-replay.json
```

The Lean package has no external library dependencies. Its transitive axiom
audit checks all `BML` declarations and required theorem names. The only allowed
axioms are Lean's standard `propext`, `Quot.sound`, and `Classical.choice`;
incomplete proofs, `native_decide` result axioms, and new axioms are rejected.
Concrete finite equalities use kernel-reduced `decide`; indefinite persistence
and the tracked car's perpetual movement are proved by induction.

Quint is pinned to version 0.33.1 by a package lock. The adapter invokes the
actual TypeScript evaluator; it contains no replacement traffic dynamics.
Quint parse, typecheck, and seven deterministic tests are required before the
cross-language replay. This is not an Apalache result or sampled model checking.

## Finite evidence scopes

| Check | Exhaustive scope |
|---|---|
| Lean vs NumPy, intermediate/final state and E/N move counts | 93,387 states across all 23 ordered positive rectangles with WH≤9. |
| Quint vs NumPy, same four outputs plus actual Quint internal invariants | 3,720 states across all 14 ordered positive rectangles with WH≤6, plus three 4×2 witness rows. |
| Naive orbit oracle vs pointer-doubling classifier | All 23 ordered positive rectangles with WH≤9. |
| Lemma R's static predicate vs direct free-motion simulation | All states on those same 23 rectangles; additional randomized dimensions 2…8. |
| Historical table reproduction | All 23 stored records with WH≤9, regenerated and compared in full. |
| G1 and F constructions | Every positive W,H≤12; these tests do not make the all-size claims Lean theorems. |

Quint mutation controls execute actual altered specifications and require
rejection for reversed phase order, asynchronous scanning, and invalid cell
digits that preserve the encoded successor and move counts. The last control
ensures that agreement of numeric codes cannot conceal illegal intermediate
states. An independent labeled-certificate control rejects a same-color
identity swap that preserves every occupancy snapshot.

The committed `data/exhaustive.json` contains 50 records through WH≤16, covering
298,822,278 configurations in total. It predates this formal layer. The present
acceptance reruns the WH≤9 portion and checks the larger records against the
extremal formulas; it **does not claim to have rerun** the entire 16-cell
enumeration. The 32×32 Monte Carlo output also remains inherited empirical
context, not a new critical-density experiment.

## BML hosted acceptance

[`finite-bml.yml`](../.github/workflows/finite-bml.yml) runs three jobs:
Python/orbit certificates, Lean build/audit/replay, and Quint tests/replay/mutation
controls. Each job checks out the PR's exact head and uploads its revision and
logs. Replay reports include source hashes and the explicit enumerated domain.
The existence of the workflow is not itself evidence of a successful run;
consult the run attached to the revision being reviewed.

See [the Lean package](lean/README.md), [the Quint package](quint/README.md), and
[the corrected theorem document](../docs/theorems.md) for implementation and
mathematical details.

The separate [Traffic workflow](../.github/workflows/formal.yml) runs
`scripts/check_formal.py` and uploads its own source-bound evidence. Each suite's
run must be inspected at the revision under review; a successful run of one is
not a receipt for the other's checks.
