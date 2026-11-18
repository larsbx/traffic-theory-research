# Formal coverage and validation

The `BML` suite implements the same positive W×H torus and synchronous **east
then north** updates as the `bml.model.CLASSIC` rule. Move eligibility is read from the complete
pre-half-step state. Width or height one is allowed. A jam must be nonempty;
the empty fixed state is classified as free flow.

The formal kernel, finite correspondence checks, and prose mathematics have
different scopes. This register records those distinctions explicitly.

## Update-rule boundary

The `BML` and `Traffic` suites, in Lean and Quint, implement **CLASSIC**: a destination
must be vacant in the state read at the start of that species' half-step.
The separate `BML.Train` Lean namespace and `Train.qnt` model implement
**TRAIN**, matching Python's queue propagation and full single-species ring
rotation. Its complete rectangular jam threshold, movement/count invariants,
and finite replay domains are recorded in [TRAIN.md](TRAIN.md).
A rotating full ring has unchanged occupancy with moving cars, so the CLASSIC
equivalence between a fixed point and no movement (G0) is not valid for TRAIN.
The TRAIN library proves this distinction and states its threshold using
actual zero movement.

## Separately scoped proof suites

| Suite | Proved constructions and checks | Detailed entry point |
| --- | --- | --- |
| `BML` / `BML.qnt` | Finite-torus update semantics, numerical species conservation, nonempty-jam boundaries, full G1 including every admissible exact population, persistent cores and route-cover capture, F arithmetic components, and a strong identity-aware non-monotonicity witness. The general theorems are in Lean; separate finite replays compare Lean and Quint with NumPy. | The register and commands below; [Lean package](lean/README.md). |
| `Traffic` / `traffic.qnt` | General-grid freezing, exact 21-Wang-tile recoding, a constructed infinite staircase for any supplied direction word, finite Fibonacci count and algebraic-length identities, and winding conditional on modular closure. Six finite grids are compared directly between Lean and Quint. | [Traffic coverage and acceptance](traffic-layer.md); [Traffic inventory](coverage.json). |
| `BML.Train` / `Train.qnt` | Queue and ring movement, transport bijections and numeric conservation, actual zero-movement characterization, and the full theorem that an n-car jam exists iff W+H≤n≤WH on every positive rectangle. | [TRAIN coverage and acceptance](TRAIN.md); [TRAIN inventory](train-coverage.json). |

All suites use simultaneous half-steps and east-then-north full steps. The
CLASSIC and TRAIN eligibility rules differ. Their types, predicates, and executable comparison contracts are
separate. No general `BML`–`Traffic` equivalence or unbounded cross-language
refinement theorem is asserted. Their finite replay counts must not be added
and described as a single common domain or theorem.

The shared dependency-free Lean package pins Lean 4.34.1. It contains the
`BML`, `Traffic`, and `Train` libraries, with their `bml_replay`, `g1_export`,
`traffic_export`, and `train_replay` executable targets. `Audit.lean` remains
the CLASSIC BML audit; `TrafficAudit.lean` checks the Traffic declarations and
exporter, and `TrainAudit.lean` checks the TRAIN layer.
`formal/coverage.json` is the Traffic suite's inventory, not a replacement for
the BML audit's required theorem list.

The rest of this page retains the **BML finite-torus coverage register**.
Run `python3 scripts/check_formal.py` for the separate Traffic acceptance gate,
after installing the same locked Quint dependency; its instructions and full
scope are in [traffic-layer.md](traffic-layer.md). Run
`python3 scripts/check_train.py` for the separate TRAIN gate described in
[TRAIN.md](TRAIN.md). A successful receipt from one suite does not certify the
other suites.

## BML finite-torus coverage register

| Claim | Current evidence | Remaining obligation |
|---|---|---|
| Half-step semantics, no collisions or created cars | Universal Lean proofs of source/destination behavior and an explicit bijection on each species' cars. The occupied-position list has no duplicates; its length equals the executable east-plus-north `speciesCount` sum. Both numerical species counts, and hence total car count, are conserved under every half-step and full-step iterate. | No unrestricted cross-language refinement follows from these Lean counting theorems. |
| G0 local equivalence | Lean proves full-step fixed ⇔ local blockage ⇔ no movers in either phase, on the actual finite-torus kernel. Frozen states persist through every iterate. | General eventual periodicity and correctness of the orbit classifier are still separate obligations; the cycle-average formulation is explained in prose. |
| Full occupancy and the empty boundary | Lean proves full occupancy freezes; the empty state is fixed but is not a jam. Nonemptiness is invariant under evolution. | No missing local boundary lemma is claimed. |
| Persistent occupied cores | `BlockingCore.persists` proves preservation under the actual two-phase kernel; `BlockerCycle.persists` derives a core from a supplied occupied closed walk. | The Capture closed walk may revisit sites. G1 separately extracts a simple occupied blocker cycle; the two certificate interfaces have not been identified by a general theorem. |
| Capture from a core meeting every row and column | `RouteCover.jammed_by_movementBudget` proves a nonempty jam by `M = n_E*(W-1) + n_N*(H-1)` full rounds from explicit core obstacles on every row/column. `total_moves_le` bounds every finite prefix of actual tagged moves; rank decrease is derived from kernel transport. | Construct the row/column witnesses from mixed winding in Lean. Tagged movement has a proved car bijection but no separate equality with the Eulerian `moveCount` sum. No probability of forming a core is proved. |
| Mixed-cycle capture certificates | Python validates distinct vertices, directions, edges, winding, and row/column coverage, then independently replays identities against the production kernel. The census checks 34,344 states on six tori, including all 831 mixed-core cases. Quint supplies three additional bounded persistence/capture/monochromatic controls. | These finite checks are not an unrestricted Python/Lean/Quint certificate refinement. A monochromatic core alone need not capture all cars. |
| G1 exact gridlock populations | Lean proves `(∃ s, Jam s ∧ carCount s = n) ↔ min(W,H) ≤ n ∧ n ≤ WH`. Necessity uses a simple occupied blocker cycle and its actual winding; sufficiency uses executable row/column prefix constructions with proved exact counts. Conservation proves the same existence interval for orbits reaching a jam, and excludes every future jam below the minimum. | G1 is complete for CLASSIC. Eventual positive velocity, classifier correctness, and unrestricted refinement of the distinct Python constructor remain separate. |
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
python scripts/check_capture.py --report .artifacts/capture-replay.json
npm ci --ignore-scripts --prefix formal/quint
cd formal/lean
lake build
lake env lean Audit.lean
cd ../..
python scripts/check_lean_replay.py --max-cells 9 --report .artifacts/lean-replay.json
python scripts/check_g1_constructions.py --max-side 12 --report .artifacts/g1-constructions.json
python formal/quint/check.py --max-cells 6 --report .artifacts/quint-replay.json
```

The Lean package has no external library dependencies. Its transitive axiom
audit checks the imported `BML` declarations, the G1 exporter and its global
entry point, and the required theorem names. The only allowed
axioms are Lean's standard `propext`, `Quot.sound`, and `Classical.choice`;
incomplete proofs, `native_decide` result axioms, and new axioms are rejected.
Concrete finite equalities use kernel-reduced `decide`; indefinite persistence
and the tracked car's perpetual movement are proved by induction.

Quint is pinned to version 0.33.1 by a package lock. The adapter invokes the
actual TypeScript evaluator; it contains no replacement traffic dynamics.
Quint parse, typecheck, and ten deterministic tests are required before the
cross-language replay. This is not an Apalache result or sampled model checking.

## Finite evidence scopes

All Lean/Quint replay rows in this table use CLASSIC. The separate TRAIN
domains and receipts are in [TRAIN.md](TRAIN.md#finite-executable-evidence).

| Check | Exhaustive scope |
|---|---|
| Lean vs NumPy, intermediate/final state and E/N move counts | 93,387 states across all 23 ordered positive rectangles with WH≤9. |
| Quint vs NumPy, same four outputs plus actual Quint internal invariants | 3,720 states across all 14 ordered positive rectangles with WH≤6, plus three 4×2 witness rows. |
| Naive orbit oracle vs pointer-doubling classifier | All 23 ordered positive rectangles with WH≤9. |
| Python blocker-cycle extraction and independent certificate checks | All 93,387 states on those 23 rectangles are examined; all 22,235 nonempty CLASSIC frozen states yield valid simple occupied cycles with the required winding and count bounds. This is a finite extractor regression, not refinement of Lean's existence proof. |
| Lemma R's static predicate vs direct free-motion simulation | All states on those same 23 rectangles; additional randomized dimensions 2…8. |
| Historical table reproduction | All 23 stored records with WH≤9, regenerated and compared in full. |
| Actual Lean G1 constructor vs Python CLASSIC dynamics | All 5,578 admissible exact counts on all 144 positive rectangles with W,H≤12. Exported digits and numerical counts are checked independently, followed by both actual Python half-steps and the full step. This is bounded implementation evidence alongside the universal Lean G1 theorem. |
| Python G1 and F constructions | Every positive W,H≤12. The Python constructor uses a different anchor/fill order from Lean's G1 constructor; no equality between their output arrays is asserted. F remains a prose theorem with these bounded checks. |
| Static cores and independent capture replay | All 34,344 states on 2×2, 3×2, 2×3, 4×2, 2×4, and 3×3 tori. All 831 states with a mixed core have independent tagged capture replay (964 edges, including frozen self-edges). These are separate from the kernel correspondence domains above. |

`scripts/check_capture.py` writes source-bound capture counts and separately
identified production-classifier phase totals. `trace_capture` records the first
observed direct core, mixed core, and global jam. It certifies an occupancy cycle
only after exact recurrence; an exhausted observation budget remains
`unresolved`. Neither a moving jam front nor a temporary zero in one half-step
is treated as a permanent core or complete gridlock.

See [the freezing/gridlock note](../docs/research/2026-11-18-freezing-gridlock-nucleation.md)
for the direct mixed-winding argument, AHM prior art, and the remaining formation
probability problem.

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
controls. The Lean job also runs the G1 construction exporter and rejection
controls for missing/duplicate rows, malformed digits, wrong counts, and moving
boards. Each job checks out the PR's exact head and uploads its revision and
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
