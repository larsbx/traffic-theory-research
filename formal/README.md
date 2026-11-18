# Formal coverage and validation

The `BML` suite implements the same positive W×H torus and synchronous **east
then north** updates as the `bml.model.CLASSIC` rule. Move eligibility is read from the complete
pre-half-step state. Width or height one is allowed. A jam must be nonempty;
the empty fixed state is classified as free flow.

The formal kernel, finite correspondence checks, and prose mathematics have
different scopes. This register records those distinctions explicitly.

The dated [open questions and proof roadmap](../docs/research/2026-11-18-open-questions-and-proof-roadmap.md)
records the post-TRAIN review, proposed extensions, probability and spatial-order
questions, and proof work awaiting integration from open PRs. The register below
describes the checked-out revision; the dated roadmap retains its historical
snapshot of merged and open-PR work.

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

The sparse-square TRAIN speed-one theorem is also proved in full, including
its actual-kernel bridge and numerical movement conclusion. Every N×N state
with `2 * population < N` eventually has all cars moving in every full cycle,
including the empty state.
The CLASSIC rectangular counterpart under `2 * carCount < gcd(W,H)` has a
prose proof and finite checks in [blueprint B7](blueprint.md#b7-classic-low-density-speed-one);
it is not yet formalized in Lean. Rectangular generalizations of the TRAIN
speed-one theorem remain separate obligations.

## Separately scoped proof suites

| Suite | Proved constructions and checks | Detailed entry point |
| --- | --- | --- |
| `BML` / `BML.qnt` | Finite-torus update semantics, species transport bijections, numerical species/lane invariants, full-lane reflection and north-free-strip invariance, nonempty-jam boundaries, full G1/G2, the feasible-population forced-gridlock boundary, the geometric coset identity B2, and Lemma R for the actual phases with a finite moving-window criterion and lcm return. Also persistent cores, route-cover capture, the tagged-fixation/jam/full-lane identity, F arithmetic components, and a strong identity-aware non-monotonicity witness. General theorems are in Lean; separate finite replays compare actual implementations. | The register and commands below; [Lean package](lean/README.md). |
| `Traffic` / `traffic.qnt` | General-grid freezing, exact 21-Wang-tile recoding, a constructed infinite staircase for any supplied direction word, finite Fibonacci count and algebraic-length identities, and winding conditional on modular closure. Six finite grids are compared directly between Lean and Quint. | [Traffic coverage and acceptance](traffic-layer.md); [Traffic inventory](coverage.json). |
| `BML.Train` / `Train.qnt` | Queue and ring movement, transport and trace coverage, numeric conservation, the full rectangular jam-population theorem, and eventual full speed on every N×N square with fewer than N/2 cars. Quint and cross-language checks retain finite domains. | [TRAIN coverage and acceptance](TRAIN.md); [TRAIN inventory](train-coverage.json). |

All suites use simultaneous half-steps and east-then-north full steps. The
CLASSIC and TRAIN eligibility rules differ. Their types, predicates, and executable comparison contracts are
separate. No general `BML`–`Traffic` equivalence or unbounded cross-language
refinement theorem is asserted. Their finite replay counts must not be added
and described as a single common domain or theorem.

The shared dependency-free Lean package pins Lean 4.34.1. It contains the
`BML`, `Traffic`, and `Train` libraries, with their `bml_replay`, `g1_export`, `g2_export`, `coset_export`,
`freeflow_export`, `traffic_export`, and `train_replay` executable targets. `Audit.lean` remains
the CLASSIC BML audit; `G2Audit.lean` separately checks the G2 exporter and its
entry point; `CosetAudit.lean` separately checks the coordinate exporter.
`FreeFlowAudit.lean` checks the free-flow exporter and its entry point.
`TrafficAudit.lean` checks the Traffic declarations and
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
| CLASSIC conserved lanes and strips | `BML/Lanes.lean` derives east-row and north-column numerical count conservation from actual kernel transport. Full E-rows, full N-columns, and specified north-free columns or cyclic strips are present at an iterate iff present initially; full monochromatic lanes have no hidden movement. | Mixed-cycle exclusion and the strip-crossing obstruction are proved in prose, not derived as Lean probability theorems. |
| G0 local equivalence | Lean proves full-step fixed ⇔ local blockage ⇔ no movers in either phase, on the actual finite-torus kernel. Frozen states persist through every iterate. | General eventual periodicity and correctness of the orbit classifier are still separate obligations; the cycle-average formulation is explained in prose. |
| Full occupancy and the empty boundary | Lean proves full occupancy freezes; the empty state is fixed but is not a jam. Nonemptiness is invariant under evolution. | No missing local boundary lemma is claimed. |
| Persistent occupied cores | `BlockingCore.persists` proves preservation under the actual two-phase kernel; `BlockerCycle.persists` derives a core from a supplied occupied closed walk. | The Capture closed walk may revisit sites. G1 separately extracts a simple occupied blocker cycle; the two certificate interfaces have not been identified by a general theorem. |
| One-round staircase formation | `BML/Formation.lean` proves the exact local initial-site predicate for adjacent E/N targets, simultaneous formation from a supplied geometry, and construction of the resulting successor-closed core. The [formation note](../docs/research/2026-11-18-fixed-density-formation.md) integrates the independent initial cells into an exact transfer trace. | Probability integration, torus winding/cover instantiation, early-formation bounds, and large-size limits remain prose proofs. This is not a positive critical-density theorem. |
| Capture from a core meeting every row and column | `RouteCover.jammed_by_movementBudget` proves a nonempty jam by `M = n_E*(W-1) + n_N*(H-1)` full rounds from explicit core obstacles on every row/column. `total_moves_le` bounds every finite prefix of actual tagged moves; rank decrease is derived from kernel transport. | Construct the row/column witnesses from mixed winding in Lean. Tagged movement has a proved car bijection but no separate equality with the Eulerian `moveCount` sum. No probability of forming a core is proved. |
| Tagged fixation and global gridlock | `BML/Fixation.lean` proves `hasEventuallyStoppedCar_iff_jam_or_full_lane` for every positive rectangle, using actual original-car traces. A permanently stopped car produces a future nonempty `BlockingCore`; a core without full lanes supplies `RouteCover` directly, without cycle extraction. Outside eventual jam and initial full lanes, every tag moves and every site is empty arbitrarily late. | The Palm probability identities, covariance bound, and limiting comparison in the [fixation note](../docs/research/2026-11-18-tagged-fixation-and-gridlock.md) have prose proofs. No fixed-density transition or infinite-volume limit interchange is proved. No new Quint fixation theorem is asserted. |
| Mixed-cycle capture certificates | Python validates distinct vertices, directions, edges, winding, and row/column coverage, then independently replays identities against the production kernel. The census checks 34,344 states on six tori, including all 831 mixed-core cases. Quint supplies three additional bounded persistence/capture/monochromatic controls. | These finite checks are not an unrestricted Python/Lean/Quint certificate refinement. A monochromatic core alone need not capture all cars. |
| G1 exact gridlock populations | Lean proves `(∃ s, Jam s ∧ carCount s = n) ↔ min(W,H) ≤ n ∧ n ≤ WH`. Necessity uses a simple occupied blocker cycle and its actual winding; sufficiency uses executable row/column prefix constructions with proved exact counts. Conservation proves the same existence interval for orbits reaching a jam, and excludes every future jam below the minimum. | G1 is complete for CLASSIC. Eventual positive velocity, classifier correctness, and unrestricted refinement of the distinct Python constructor remain separate. |
| G2 sub-full non-gridlock construction | Lean proves that executable `nonGridlockWith W H n` has exactly n cars and never reaches a jam for every positive W,H and n<WH. A single-species mixed lane is preserved by the actual synchronous kernel and has a mover at every iterate; zero cars use the empty-state boundary. | G2 is complete for CLASSIC. Never reaching total gridlock does not assert eventual free flow or movement of every car. |
| Forced gridlock at a fixed population | Lean proves, under feasibility n≤WH, that every n-car configuration eventually jams iff n=WH. Exact full count is equivalent to full occupancy; any sub-full count has the G2 counterexample. | The feasibility assumption avoids a vacuous universal claim above WH. This is a deterministic extremal theorem, not a probabilistic threshold. |
| B2, diagonal coset identity | Lean proves the signed action generated by the actual cyclic successor/predecessor has precisely the fibers of `phaseClass=(x+y) mod gcd(W,H)` as its orbits. It proves the origin kernel identity, the east-translated class-one criterion, and witnesses in both 0≤t<lcm(W,H) and 1≤t≤lcm(W,H). | B2 is complete for positive dimensions, including singleton axes. This is coordinate geometry; `diagonalStep` is not the traffic update. |
| R, free-flow rigidity | Lean proves `StaticFree s ↔ ∀ t, AllMove (f^t s)` for the actual east-then-north kernel on every positive rectangle. The first `lcm(W,H)` rounds suffice; both strict and inclusive time-window formulations are proved. Static-free states return after the lcm and remain periodic. Failure of a static condition forces a blocked round before the lcm. | R is complete, including empty boards and singleton axes. Perpetual free flow starts at time zero; eventual free flow is equivalent to eventual entry into `StaticFree`, with no claim that such entry always occurs or has a uniform time bound. The lcm need not be the least configuration period. |
| CLASSIC low-density eventual free flow (B7) | [Blueprint B7](blueprint.md#b7-classic-low-density-speed-one) gives a prose proof for every positive W,H under `2m < g`, where m is the car count and g=gcd(W,H). It bounds the number of rounds containing a blocked car by m(g−2) in every finite prefix. Release/survival and per-car bounds have finite computational checks. | Formalize the CLASSIC release, corrected-class, and block-count arguments. The proposed Lean signatures are specifications. The block-event bound is not an elapsed stabilization-time bound. |
| F, maximal free flow | Prose packing proof and constructions; Lean proves V(g)=⌊2g/3⌋ and 3V(g)=2g iff 3 divides g. Lemma-level proof in [blueprint B4](blueprint.md); an independent max-plus DP (`bml.freeflow_dp`) confirms the formula on 3×3, 4×4, 3×6, 5×5, 6×6 and 8×4, i.e. up to g = 6. | Formalize class packing, the upper bound, and the maximizing constructions. The g=1 branch remains separate. |
| Strong non-monotonicity | Lean proves code 3858 reaches a jam, while adding a stationary N yields the perpetual two-cycle 3860↔4340. An explicitly tracked original car moves every step. Independent labeled Python replay also checks the identities. | No minimality or novelty claim. |
| No initial simple loop, followed by gridlock | Reproducible identity-aware Python certificate on 3×2, compared against NumPy. | This witness is not currently a Lean theorem. |
| Python/Lean/Quint correspondence | Actual implementations are evaluated and compared on the finite domains below, including both half-steps and separate move counts. | A finite replay is not unrestricted source refinement or proof of the classifier algorithm. |
| Probability reductions and sparse no-gridlock window | The [probability note](../docs/research/2026-11-18-probabilistic-gridlock-bounds.md) gives prose proofs of `M = J intersect R-complement`, a uniform exponentially small ring exception, and no eventual gridlock with high probability when `p_L*L <= (2-epsilon)*log(log(L))`. Python checks finite iid probabilities and strip certificates. | The probability laws, analytic limits, mixed-cycle reduction, and strip-crossing argument are not an end-to-end Lean theorem. No fixed-positive-density nonjamming interval, sharp transition, or critical-density value is proved. |

## Reproduce the BML suite

For the BML suite, use Python 3.12, Node.js 22, and the Lean toolchain pinned in
[`lean/lean-toolchain`](lean/lean-toolchain). From the repository root:

```sh
python -m pip install -r requirements-dev.txt
python -m pytest -q
python scripts/check_capture.py --report .artifacts/capture-replay.json
python scripts/check_probability.py --report .artifacts/probability-replay.json
python scripts/check_formation.py --report .artifacts/formation-replay.json
python scripts/check_fixation.py --report .artifacts/fixation-replay.json
npm ci --ignore-scripts --prefix formal/quint
cd formal/lean
lake build
lake env lean Audit.lean
lake env lean G2Audit.lean
lake env lean CosetAudit.lean
lake env lean FreeFlowAudit.lean
cd ../..
python scripts/check_lean_replay.py --max-cells 9 --report .artifacts/lean-replay.json
python scripts/check_g1_constructions.py --max-side 12 --report .artifacts/g1-constructions.json
python scripts/check_g2_constructions.py --max-side 12 --report .artifacts/g2-constructions.json
python scripts/check_cosets.py --max-side 12 --report .artifacts/cosets.json
python scripts/check_freeflow.py --max-cells 9 --report .artifacts/freeflow.json --rows .artifacts/freeflow.tsv
python formal/quint/check.py --max-cells 6 --report .artifacts/quint-replay.json
```

The Lean package has no external library dependencies. Its transitive axiom
audits check the imported `BML` declarations, the G1, G2, coset, and free-flow exporters with their
separate global entry points, and the required theorem names. The only allowed
axioms are Lean's standard `propext`, `Quot.sound`, and `Classical.choice`;
incomplete proofs, `native_decide` result axioms, and new axioms are rejected.
Concrete finite equalities use kernel-reduced `decide`; indefinite persistence
and the tracked car's perpetual movement are proved by induction.

Quint is pinned to version 0.33.1 by a package lock. The adapter invokes the
actual TypeScript evaluator; it contains no replacement traffic dynamics.
Quint parse, typecheck, and ten deterministic tests are required before the
cross-language replay. This is not an Apalache result or sampled model checking.

## Finite evidence scopes

Traffic-state replays in this table use CLASSIC. The coset rows compare
coordinate geometry and do not apply a traffic update. The separate TRAIN
domains and receipts are in [TRAIN.md](TRAIN.md#finite-executable-evidence).
These are declared acceptance domains; source-bound receipts establish which
checks passed at a given revision.

| Check | Exhaustive scope |
|---|---|
| Lean vs NumPy, intermediate/final state and E/N move counts | 93,387 states across all 23 ordered positive rectangles with WH≤9. |
| Quint vs NumPy, same four outputs plus actual Quint internal invariants | 3,720 states across all 14 ordered positive rectangles with WH≤6, plus three 4×2 witness rows. |
| Naive orbit oracle vs pointer-doubling classifier | All 23 ordered positive rectangles with WH≤9. |
| Python blocker-cycle extraction and independent certificate checks | All 93,387 states on those 23 rectangles are examined; all 22,235 nonempty CLASSIC frozen states yield valid simple occupied cycles with the required winding and count bounds. This is a finite extractor regression, not refinement of Lean's existence proof. |
| Python Lemma R static predicate vs direct free-motion simulation | All states on those same 23 rectangles; additional randomized dimensions 2…8. |
| Actual Lean `StaticFree`/`AllMove` decisions and full phase traces vs independent dynamics | All 93,387 initial states on the 23 ordered positive rectangles with WH≤9, with 622,362 full transitions over the first lcm(W,H) rounds. The gate checks both phase states and move counts against NumPy, and perpetual movement from time zero against independent scalar orbit following. It also checks rigid moving prefixes, lcm closure of static-free states, complete coverage, and corrupted-output rejection controls. |
| Historical table reproduction | All 23 stored records with WH≤9, regenerated and compared in full. |
| Actual Lean G1 constructor vs Python CLASSIC dynamics | All 5,578 admissible exact counts on all 144 positive rectangles with W,H≤12. Exported digits and numerical counts are checked independently, followed by both actual Python half-steps and the full step. This is bounded implementation evidence alongside the universal Lean G1 theorem. |
| Actual Lean G2 constructor and traces vs Python CLASSIC dynamics | All sub-full counts 0≤n<WH on all 144 positive rectangles with W,H≤12, at times 0…2 max(W,H). Both actual Lean phases, numerical counts, trace continuity, the mixed-lane invariant, and the empty/nonempty jam boundary are checked independently. This finite trace domain supplements the universal Lean proof for all times. |
| Actual Lean diagonal geometry vs an independent modular-coordinate oracle | All 6,084 positions on 144 ordered rectangles with W,H≤12. Complete cycles reconstructed from each starting point give 283,526 orbit visits. Both the same-class and east-translated class-one relations are checked on 422,500 ordered pairs each; 12 corrupted-output controls must be rejected. These coordinate observations are separate from the traffic-configuration gate for R. |
| Python G1 and F constructions | Every positive W,H≤12. The Python constructor uses a different anchor/fill order from Lean's G1 constructor; no equality between their output arrays is asserted. F remains a prose theorem with these bounded checks. |
| Static cores and independent capture replay | All 34,344 states on 2×2, 3×2, 2×3, 4×2, 2×4, and 3×3 tori. All 831 states with a mixed core have independent tagged capture replay (964 edges, including frozen self-edges). These are separate from the kernel correspondence domains above. |
| Eventual mixed-cycle formation, ring exceptions, and strip obstructions | All 565,785 states on those six tori plus 4×3. Eventual mixed-cycle occurrence is propagated from separately detected cycles through the successor graph and compared with the jam classifier. Every allowed strip width is checked. The 4×4 non-monotonicity example is a trajectory control, not an exhaustive 4×4 census. |
| Specified winding staircase after one round | All 43,046,721 initial states on 4×4: the local preimage predicate is compared pointwise with the full-round kernel, and car-count coefficients are integrated under exact initial iid weights. This is a one-step event census, not an eventual-basin census on 4×4. |

`scripts/check_freeflow.py` checks the actual Lean proposition decisions and
complete phase traces, rather than relying only on a separately implemented
static predicate. Its scalar orbit oracle rejects any blocked round starting
at time zero, so a transient that later becomes free cannot pass as perpetual
free flow. The receipt records the declared domain, source hashes, and
rejection-control outcomes; the universal result comes from the Lean proof.

`scripts/check_capture.py` writes source-bound capture counts and separately
identified production-classifier phase totals. `trace_capture` records the first
observed direct core, mixed core, and global jam. It certifies an occupancy cycle
only after exact recurrence; an exhausted observation budget remains
`unresolved`. Neither a moving jam front nor a temporary zero in one half-step
is treated as a permanent core or complete gridlock.

See [the freezing/gridlock note](../docs/research/2026-11-18-freezing-gridlock-nucleation.md)
for the direct mixed-winding argument, AHM prior art, and the remaining formation
probability problem.

`scripts/check_probability.py` evaluates finite iid probabilities with exact
rational arithmetic and records the enumeration domain, runtime versions, and
source hashes. Its evidence supports the finite calculations; the separate
prose proofs in the [probability note](../docs/research/2026-11-18-probabilistic-gridlock-bounds.md)
justify the asymptotic statements. Configurations conditioned on exact car
counts and iid initial states have separate probability weights. None of the
probability statements applies to TRAIN by default.

`scripts/check_fixation.py` separately enumerates the seven probability domains
using recurrent **labeled** orbits. It derives each stopped-tag set from both
identity positions and recorded movements, compares the resulting jam event
with the production classifier, and checks `S = J union R` pointwise. Exact
initial-iid weights then verify the Palm score identity and covariance bound.
Its report records source hashes, domain sizes, and corrupted-witness controls.
These finite calculations support the probability code; the universal
deterministic identity is proved separately in `BML/Fixation.lean`.

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
controls. The Lean job also runs the G1 and G2 construction exporters, the
coset coordinate exporter, and the free-flow predicate/trace exporter, their
audits, and rejection controls. G1 checks frozen boards at every admissible
count; G2 replays both phases from every sub-full construction and checks the
persistent mixed lane. The coset gate reconstructs complete coordinate cycles
and checks both phase-class relations against an independent modular oracle.
The free-flow gate compares both actual traffic phases and formal predicate
decisions with NumPy and independent scalar orbit following through its
declared finite domain.
Each job checks out the PR's exact head and uploads its revision and
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
