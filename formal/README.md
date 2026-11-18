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
describes the merged layer; open-branch claims retain their separate status.

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
The CLASSIC transfer and rectangular generalizations are separate obligations.

## Separately scoped proof suites

| Suite | Proved constructions and checks | Detailed entry point |
| --- | --- | --- |
| `BML` / `BML.qnt` | Finite-torus update semantics, species transport bijections, numerical species/lane invariants, full-lane reflection, north-free-strip invariance, nonempty-jam boundaries, persistent cores, route-cover capture, the tagged-fixation/jam/full-lane identity, G1/F arithmetic components, and a strong identity-aware non-monotonicity witness. Separate finite replays compare Lean and Quint with NumPy. | The register and commands below; [Lean package](lean/README.md). |
| `Traffic` / `traffic.qnt` | General-grid freezing, exact 21-Wang-tile recoding, a constructed infinite staircase for any supplied direction word, finite Fibonacci count and algebraic-length identities, and winding conditional on modular closure. Six finite grids are compared directly between Lean and Quint. | [Traffic coverage and acceptance](traffic-layer.md); [Traffic inventory](coverage.json). |
| `BML.Train` / `Train.qnt` | Queue and ring movement, transport and trace coverage, numeric conservation, the full rectangular jam-population theorem, and eventual full speed on every N×N square with fewer than N/2 cars. Quint and cross-language checks retain finite domains. | [TRAIN coverage and acceptance](TRAIN.md); [TRAIN inventory](train-coverage.json). |

All suites use simultaneous half-steps and east-then-north full steps. The
CLASSIC and TRAIN eligibility rules differ. Their types, predicates, and executable comparison contracts are
separate. No general `BML`–`Traffic` equivalence or unbounded cross-language
refinement theorem is asserted. Their finite replay counts must not be added
and described as a single common domain or theorem.

The shared dependency-free Lean package pins Lean 4.34.1. It contains the
`BML`, `Traffic`, and `Train` libraries, with their `bml_replay`,
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
| Half-step semantics, no collisions or created cars | Universal Lean proofs of source/destination behavior and an explicit bijection on each species' cars; the other species stays in place. `BML/Lanes.lean` connects the bijection to numerical `speciesCount` conservation through both phases and every iterate. | Unrestricted correspondence with the Python source remains separate. |
| CLASSIC conserved lanes and strips | `BML/Lanes.lean` derives east-row and north-column numerical count conservation from actual kernel transport. Full E-rows, full N-columns, and specified north-free columns or cyclic strips are present at an iterate iff present initially; full monochromatic lanes have no hidden movement. | Mixed-cycle exclusion and the strip-crossing obstruction are proved in prose, not derived as Lean probability theorems. |
| Jammed representatives of positive lane profiles | `BML/Profiles.lean` constructs a ringless actual-kernel jam with exact E-row and N-column counts whenever every count is positive and the two profile maxima sum to at most the square side. It also proves that every profile predicate soundly excluding jams rejects those profiles. | The [profile note](../docs/research/2026-11-18-lane-profile-obstruction.md) derives exact iid bounds and exponentially vanishing acceptance of such certificates at every fixed `0<p<1`. Those probability statements are prose proofs and do not measure basin probabilities. |
| Disjoint-strip capacity | The [capacity note](../docs/research/2026-11-18-disjoint-strip-capacity.md) proves that `B` disjoint north-empty strips of width `k` exclude mixed cycles when `B > sum_y floor(r_y/k)`. Python validates supplied certificates and exact iid marginal laws. | The crossing and probability arguments remain prose mathematics. No Lean capacity theorem or fixed-positive-density bound is claimed. |
| G0 local equivalence | Lean proves full-step fixed ⇔ local blockage ⇔ no movers in either phase, on the actual finite-torus kernel. Frozen states persist through every iterate. | General eventual periodicity and correctness of the orbit classifier are still separate obligations; the cycle-average formulation is explained in prose. |
| Certified eventual-gridlock intervals | `BML/Absorption.lean` proves actual-kernel hit/safe soundness at every cutoff, all-time avoidance from nonjam recurrence, finite Nat-weight lower/upper bounds, nested intervals, and exactness at zero unresolved mass. Its data-valued board evaluator is proved equivalent to the original update. Actual Quint and Python counterparts are evaluated on explicit finite domains. | Initial iid normalization and analytic limits retain the scope in the [certificate note](../docs/research/2026-11-18-certified-absorption-bounds.md). No size-uniform unresolved-mass estimate, unrestricted source refinement or pointer-doubling correctness theorem is claimed. |
| Relaxation obstructions | `BML/Delay.lean` proves an initial run of T+2 east cars blocks its original rear car through round T, regardless of exterior traffic. It also proves a specific winding vacant cut disappears into a nonempty jam after one round. | The [logarithmic iid consequence and late-defect criterion](../docs/research/2026-11-18-relaxation-obstructions.md) have prose proofs. HBK defect coercivity, probability integration and late expected-defect decay are not Lean theorems. |
| Protected queues and early gridlock | `BML/GuardedQueue.lean` proves that a run of T+1 east cars followed by a hole, with T east guards in the row below, makes the original rear tag first move in round T. Its shrinking-queue induction uses the actual two-phase kernel and permits arbitrary exterior traffic. Any nonempty jam occurs strictly after T. | The [exact cyclic avoidance polynomial and logarithmic gridlock-time bound](../docs/research/2026-11-18-protected-queue-gridlock-delay.md) have prose proofs and exact finite Python checks. The companion bounded-local jam-completion construction is a prose theorem. These are not Lean probability theorems or bounds on the eventual jam probability. |
| Full occupancy and the empty boundary | Lean proves full occupancy freezes; the empty state is fixed but is not a jam. Nonemptiness is invariant under evolution. | No missing local boundary lemma is claimed. |
| Persistent occupied cores | `BlockingCore.persists` proves preservation under the actual two-phase kernel; `BlockerCycle.persists` derives a core from a supplied occupied closed walk. | The Lean closed walk may revisit sites. Extraction of a simple cycle from an arbitrary frozen state remains separate. |
| One-round staircase formation | `BML/Formation.lean` proves the exact local initial-site predicate for adjacent E/N targets, simultaneous formation from a supplied geometry, and construction of the resulting successor-closed core. The [formation note](../docs/research/2026-11-18-fixed-density-formation.md) integrates the independent initial cells into an exact transfer trace. | Probability integration, torus winding/cover instantiation, early-formation bounds, and large-size limits remain prose proofs. This is not a positive critical-density theorem. |
| Capture from a core meeting every row and column | `RouteCover.jammed_by_movementBudget` proves a nonempty jam by `M = n_E*(W-1) + n_N*(H-1)` full rounds from explicit core obstacles on every row/column. `total_moves_le` bounds every finite prefix of actual tagged moves; rank decrease is derived from kernel transport. | Construct the row/column witnesses from mixed winding in Lean. Tagged movement has a proved car bijection but no separate equality with the Eulerian `moveCount` sum. No probability of forming a core is proved. |
| Tagged fixation and global gridlock | `BML/Fixation.lean` proves `hasEventuallyStoppedCar_iff_jam_or_full_lane` for every positive rectangle, using actual original-car traces. A permanently stopped car produces a future nonempty `BlockingCore`; a core without full lanes supplies `RouteCover` directly, without cycle extraction. Outside eventual jam and initial full lanes, every tag moves and every site is empty arbitrarily late. | The Palm probability identities, covariance bound, and limiting comparison in the [fixation note](../docs/research/2026-11-18-tagged-fixation-and-gridlock.md) have prose proofs. No fixed-density transition or infinite-volume limit interchange is proved. No new Quint fixation theorem is asserted. |
| Mixed-cycle capture certificates | Python validates distinct vertices, directions, edges, winding, and row/column coverage, then independently replays identities against the production kernel. The census checks 34,344 states on six tori, including all 831 mixed-core cases. Quint supplies three additional bounded persistence/capture/monochromatic controls. | These finite checks are not an unrestricted Python/Lean/Quint certificate refinement. A monochromatic core alone need not capture all cars. |
| G1 minimum gridlock | Prose blocker-cycle proof; executable constructions; Lean winding arithmetic: a nonzero closed nonnegative winding costs at least min(W,H). | Extract a simple blocker cycle in Lean, connect its displacements and distinct-car count, and prove the all-count constructions. |
| G2 sub-full non-gridlock construction | Prose proof, tested single-species constructions, and bounded classifier evidence. | Prove the all-count construction and its perpetual movement in Lean. |
| R, free-flow rigidity and phase classes | Prose proof; static/dynamic equivalence tested on every state of every ordered rectangle with WH≤9 and random larger examples. | Prove ⟨(1,−1)⟩ = ker(x+y mod gcd(W,H)), and connect both directions of rigidity to the kernel. |
| F, maximal free flow | Prose packing proof and constructions; Lean proves V(g)=⌊2g/3⌋ and 3V(g)=2g iff 3 divides g. Lemma-level proof in [blueprint B4](blueprint.md); an independent max-plus DP (`bml.freeflow_dp`) confirms the formula on 3×3, 4×4, 3×6, 5×5, 6×6 and 8×4, i.e. up to g = 6. | Formalize class packing, the upper bound, and the maximizing constructions. The g=1 branch remains separate. |
| Strong non-monotonicity | Lean proves code 3858 reaches a jam, while adding a stationary N yields the perpetual two-cycle 3860↔4340. An explicitly tracked original car moves every step. Independent labeled Python replay also checks the identities. | No minimality or novelty claim. |
| No initial simple loop, followed by gridlock | Reproducible identity-aware Python certificate on 3×2, compared against NumPy. | This witness is not currently a Lean theorem. |
| Python/Lean/Quint correspondence | Actual implementations are evaluated and compared on the finite domains below, including both half-steps and separate move counts. | A finite replay is not unrestricted source refinement or proof of the classifier algorithm. |
| Probability reductions and sparse no-gridlock window | The [probability note](../docs/research/2026-11-18-probabilistic-gridlock-bounds.md) gives prose proofs of `M = J intersect R-complement`, a uniform exponentially small ring exception, and no eventual gridlock with high probability when `p_L*L <= 2*log(log(L))-4*log(log(log(L)))-2` eventually. Python checks finite iid probabilities and strip certificates. | The probability laws, analytic limits, cycle extraction, and strip-crossing argument are not an end-to-end Lean theorem. No fixed-positive-density nonjamming interval, sharp transition, or critical-density value is proved. |

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
python scripts/check_profiles.py --report .artifacts/profiles-replay.json
python scripts/check_capacity.py --report .artifacts/capacity-replay.json
python scripts/check_guarded_queue.py --report .artifacts/guarded-queue-replay.json
npm ci --ignore-scripts --prefix formal/quint
cd formal/lean
lake build
lake env lean Audit.lean
cd ../..
python scripts/check_lean_replay.py --max-cells 9 --report .artifacts/lean-replay.json
python formal/quint/check.py --max-cells 6 --report .artifacts/quint-replay.json
python scripts/check_absorption.py --report .artifacts/absorption-acceptance.json
```

The Lean package has no external library dependencies. Its transitive axiom
audit checks all `BML` declarations and required theorem names. The only allowed
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
| Lemma R's static predicate vs direct free-motion simulation | All states on those same 23 rectangles; additional randomized dimensions 2…8. |
| Historical table reproduction | All 23 stored records with WH≤9, regenerated and compared in full. |
| G1 and F constructions | Every positive W,H≤12; these tests do not make the all-size claims Lean theorems. |
| Static cores and independent capture replay | All 34,344 states on 2×2, 3×2, 2×3, 4×2, 2×4, and 3×3 tori. All 831 states with a mixed core have independent tagged capture replay (964 edges, including frozen self-edges). These are separate from the kernel correspondence domains above. |
| Eventual mixed-cycle formation, ring exceptions, and strip obstructions | All 565,785 states on those six tori plus 4×3. Eventual mixed-cycle occurrence is propagated from separately detected cycles through the successor graph and compared with the jam classifier. Every allowed strip width is checked. The 4×4 non-monotonicity example is a trajectory control, not an exhaustive 4×4 census. |
| Specified winding staircase after one round | All 43,046,721 initial states on 4×4: the local preimage predicate is compared pointwise with the full-round kernel, and car-count coefficients are integrated under exact initial iid weights. This is a one-step event census, not an eventual-basin census on 4×4. |
| Disjoint-strip capacity and exact marginal laws | All 565,785 states on the seven probability domains above; 8,821,224 predicates cover every strip width and cyclic partition offset. All 525 marginal evaluations match direct initial-state weights. The certificate union adds 696 states beyond all cyclic north-empty single-strip certificates in the same orientation. Separate 8×8 controls check both orientations; those controls and optimized 8×8/12×12 bounds are not basin censuses on the larger squares. |
| Prescribed lane-profile jam witnesses | Every admissible ordered positive profile pair on square sides 2–5: 16,492 pairs, each checked for exact counts, actual zero movement, and an independent labeled fixed point. Nine larger profiles are targeted controls. The separate initial-law census contains every state on sides 1–3 (19,767 states), with 15 exact density evaluations and 75 shared-cell probability-mass checks. |
| Protected queues with arbitrary exteriors | Every W,H≥2 with WH≤12, every 0≤T≤W−2, every exterior and every torus translation: 275,526 canonical boards, 3,263,850 translated tagged cases and 299,673 canonical tagged rounds compared with both production half-steps. The public verifier is separately called on 508 representatives. Initial-law checks cover all 2,278,206 states on those 12 tori, 6,208,974 finite-time predicates and 130 exact rational comparisons. These finite checks support the independent universal Lean theorem and prose probability derivation. |

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

`scripts/check_profiles.py` separately checks the prescribed-profile constructor
against exact lane counts and both production half-steps, and verifies finite
initial-law certificate bounds. Its probability output concerns acceptance of
sound profile-only certificates, not the actual eventual-gridlock event.
`scripts/check_capacity.py` checks the stronger conserved obstruction against
the complete finite basin classifier and integrates each marginal law directly.
`scripts/check_guarded_queue.py` independently replays every small guarded
pattern with every exterior and translation, checks both actual half-steps,
and integrates selected-pattern avoidance and early gridlock under exact
initial weights. It separately rejects guard omission, identity swaps and
incorrect movement counts, and refutes multiplying vertically overlapping
patterns or resetting the evolved law to iid. Its receipt binds source hashes
before and after execution; it does not infer an eventual basin from a cutoff.
The corresponding notes keep these finite checks separate from universal
Lean construction theorems and prose probability arguments.

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
