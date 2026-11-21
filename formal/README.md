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
The separate CLASSIC theorem gives eventual full movement on positive
rectangles under `2 * carCount < gcd(W,H)`, with at most `m(g−2)` blocked
rounds and permanent full movement from round `lcm(W,H) * m(g−2)` onward,
where `m = carCount` and `g = gcd(W,H)`. Rectangular TRAIN speed one remains
open in this library. See
[blueprint B7](blueprint.md#b7-classic-low-density-speed-one).

## Separately scoped proof suites

| Suite | Proved constructions and checks | Detailed entry point |
| --- | --- | --- |
| `BML` / `BML.qnt` | Finite-torus update semantics, species transport bijections, numerical species/lane invariants, full-lane reflection and north-free-strip invariance, nonempty-jam boundaries, full G1/G2, the feasible-population forced-gridlock boundary, the geometric coset identity B2, and Lemma R for the actual phases with a finite moving-window criterion and lcm return. Also the complete F free-flow capacity and exact-count constructions, persistent cores, route-cover capture, the tagged-fixation/jam/full-lane identity, and a strong identity-aware non-monotonicity witness. General theorems are in Lean; separate finite replays compare actual implementations. | The register and commands below; [Lean package](lean/README.md). |
| `Traffic` / `traffic.qnt` | General-grid freezing, exact 21-Wang-tile recoding, a constructed infinite staircase for any supplied direction word, finite Fibonacci count and algebraic-length identities, and winding conditional on modular closure. Six finite grids are compared directly between Lean and Quint. | [Traffic coverage and acceptance](traffic-layer.md); [Traffic inventory](coverage.json). |
| `BML.Train` / `Train.qnt` | Queue and ring movement, transport and trace coverage, numeric conservation, the full rectangular jam-population theorem, and eventual full speed on every N×N square with fewer than N/2 cars. Quint and cross-language checks retain finite domains. | [TRAIN coverage and acceptance](TRAIN.md); [TRAIN inventory](train-coverage.json). |

All suites use simultaneous half-steps and east-then-north full steps. The
CLASSIC and TRAIN eligibility rules differ. Their types, predicates, and executable comparison contracts are
separate. No general `BML`–`Traffic` equivalence or unbounded cross-language
refinement theorem is asserted. Their finite replay counts must not be added
and described as a single common domain or theorem.

The shared dependency-free Lean package pins Lean 4.34.1. It contains the
`BML`, `Traffic`, and `Train` libraries, with their `bml_replay`, `g1_export`, `g2_export`, `coset_export`,
`freeflow_export`, `free_max_export`, `sparse_speed_export`, `absorption_export`, `gated_export`, `traffic_export`, and `train_replay` executable targets. `Audit.lean` remains
the CLASSIC BML audit; `G2Audit.lean` separately checks the G2 exporter and its
entry point; `CosetAudit.lean` separately checks the coordinate exporter.
`FreeFlowAudit.lean` checks the free-flow predicate exporter and its entry point;
`FreeMaxAudit.lean` checks the exact-count free-flow constructor exporter.
`SparseSpeedAudit.lean` checks the CLASSIC sparse-speed replay and finite counting controls.
`AbsorptionAudit.lean` checks the certified cutoff exporter.
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
| Jammed representatives of positive lane profiles | `BML/Profiles.lean` constructs a ringless actual-kernel jam with exact E-row and N-column counts whenever every count is positive and the two profile maxima sum to at most the square side. It also proves that every profile predicate soundly excluding jams rejects those profiles. | The [profile note](../docs/research/2026-11-18-lane-profile-obstruction.md) derives exact iid bounds and exponentially vanishing acceptance of such certificates at every fixed `0<p<1`. Those probability statements are prose proofs and do not measure basin probabilities. |
| Disjoint-strip capacity | The [capacity note](../docs/research/2026-11-18-disjoint-strip-capacity.md) proves that `B` disjoint north-empty strips of width `k` exclude mixed cycles when `B > sum_y floor(r_y/k)`. Python validates supplied certificates and exact iid marginal laws. | The crossing and probability arguments remain prose mathematics. No Lean capacity theorem or fixed-positive-density bound is claimed. |
| G0 local equivalence | Lean proves full-step fixed ⇔ local blockage ⇔ no movers in either phase, on the actual finite-torus kernel. Frozen states persist through every iterate. | General eventual periodicity and correctness of the orbit classifier are still separate obligations; the cycle-average formulation is explained in prose. |
| Certified eventual-gridlock intervals | `BML/Absorption.lean` proves actual-kernel hit/safe soundness at every cutoff, all-time avoidance from nonjam recurrence, finite Nat-weight lower/upper bounds, nested intervals, and exactness at zero unresolved mass. Its data-valued board evaluator is proved equivalent to the original update. Actual Quint and Python counterparts are evaluated on explicit finite domains. | Initial iid normalization and analytic limits retain the scope in the [certificate note](../docs/research/2026-11-18-certified-absorption-bounds.md). No size-uniform unresolved-mass estimate, unrestricted source refinement or pointer-doubling correctness theorem is claimed. |
| Relaxation obstructions | `BML/Delay.lean` proves an initial run of T+2 east cars blocks its original rear car through round T, regardless of exterior traffic. It also proves a specific winding vacant cut disappears into a nonempty jam after one round. | The [logarithmic iid consequence and late-defect criterion](../docs/research/2026-11-18-relaxation-obstructions.md) have prose proofs. HBK defect coercivity, probability integration and late expected-defect decay are not Lean theorems. |
| Protected queues and early gridlock | `BML/GuardedQueue.lean` proves that a run of T+1 east cars followed by a hole, with T east guards in the row below, makes the original rear tag first move in round T. Its shrinking-queue induction uses the actual two-phase kernel and permits arbitrary exterior traffic. Any nonempty jam occurs strictly after T. | The [exact cyclic avoidance polynomial and logarithmic gridlock-time bound](../docs/research/2026-11-18-protected-queue-gridlock-delay.md) have prose proofs and exact finite Python checks. The companion bounded-local jam-completion construction is a prose theorem. These are not Lean probability theorems or bounds on the eventual jam probability. |
| Full occupancy and the empty boundary | Lean proves full occupancy freezes; the empty state is fixed but is not a jam. Nonemptiness is invariant under evolution. | No missing local boundary lemma is claimed. |
| Persistent occupied cores | `BlockingCore.persists` proves preservation under the actual two-phase kernel; `BlockerCycle.persists` derives a core from a supplied occupied closed walk. | The Capture closed walk may revisit sites. G1 separately extracts a simple occupied blocker cycle; the two certificate interfaces have not been identified by a general theorem. |
| One-round staircase formation | `BML/Formation.lean` proves the exact local initial-site predicate for adjacent E/N targets, simultaneous formation from a supplied geometry, and construction of the resulting successor-closed core. The [formation note](../docs/research/2026-11-18-fixed-density-formation.md) integrates the independent initial cells into an exact transfer trace. | Probability integration, torus winding/cover instantiation, early-formation bounds, and large-size limits remain prose proofs. This is not a positive critical-density theorem. |
| Diagonal cuts and mixed cycles | `BML/Locality.lean` proves torus box dependence, separation of distinct lifted height layers within one period, and vacancy from excluded initial origins. The [diagonal-cuts note](../docs/research/2026-11-18-diagonal-cuts.md) proves a mixed-cycle probability bound through order `sqrt(log L)` rounds at fixed density. | The adaptive product-law calculation and asymptotic limit have prose proofs. The eventual probability depends on the remaining late formation term. |
| Guarded barriers and first formation | `BML/Barrier.lean` proves a descending guarded north hole, preservation of an east wall, and an L-shaped snapshot barrier with arbitrary exterior under the actual rectangular CLASSIC kernel. The [barrier note](../docs/research/2026-11-19-guarded-barrier-formation.md) proves logarithmic first-mixed-cycle delay at every fixed `0<p<1`, and a uniform `log L/log log L` horizon for `0<=p<=p0<1`. | Spatial path trapping, initial-law conditional probabilities, and limits are prose proofs supported by independent finite replay. Formation after the cutoff remains unbounded; no fixed-positive-density nonjamming interval is proved. |
| Finite tagged waits and lap tests | `BML/Waiting.lean` gives a permanent blocker core within any `2^M`-snapshot wait by an original tag, where `M` is the conserved car count, and proves that the tag never moves again. Outside initial full lanes, this supplies a route cover. `BML/Locality.lean` proves short-rectangle projection injectivity for the smaller guarded probe. | The [tagged-wait note](../docs/research/2026-11-20-late-tagged-waits.md) proves improved finite-time probability bounds and a conditional lap formula in prose. Small-torus replay checks those reductions. The all-time conditional probability at fixed positive density remains open. |
| Capture from a core meeting every row and column | `RouteCover.jammed_by_movementBudget` proves a nonempty jam by `M = n_E*(W-1) + n_N*(H-1)` full rounds from explicit core obstacles on every row/column. `total_moves_le` bounds every finite prefix of actual tagged moves; rank decrease is derived from kernel transport. | Construct the row/column witnesses from mixed winding in Lean. Tagged movement has a proved car bijection but no separate equality with the Eulerian `moveCount` sum. No probability of forming a core is proved. |
| Tagged fixation and global gridlock | `BML/Fixation.lean` proves `hasEventuallyStoppedCar_iff_jam_or_full_lane` for every positive rectangle, using actual original-car traces. A permanently stopped car produces a future nonempty `BlockingCore`; a core without full lanes supplies `RouteCover` directly, without cycle extraction. Outside eventual jam and initial full lanes, every tag moves and every site is empty arbitrarily late. | The Palm probability identities, covariance bound, and limiting comparison in the [fixation note](../docs/research/2026-11-18-tagged-fixation-and-gridlock.md) have prose proofs. No fixed-density transition or infinite-volume limit interchange is proved. No new Quint fixation theorem is asserted. |
| Maximal core and late path mass | `BML/PathCore.lean` proves maximality, species persistence, monotone spatial membership, the exact `carCount`-edge occupied-path test, eventual equality with all permanent sites, and the original-tag/core-entry equivalence. | The count bridge, normalized probability comparison, weaker late-time `o(1)` criterion, and sharp population-only envelope in the [path-mass note](../docs/research/2026-11-19-maximal-core-and-path-mass.md) have prose proofs. No vanishing late-time mass estimate or fixed-positive-density nonjamming interval is proved. |
| Mixed-cycle capture certificates | Python validates distinct vertices, directions, edges, winding, and row/column coverage, then independently replays identities against the production kernel. The census checks 34,344 states on six tori, including all 831 mixed-core cases. Quint supplies three additional bounded persistence/capture/monochromatic controls. | These finite checks are not an unrestricted Python/Lean/Quint certificate refinement. A monochromatic core alone need not capture all cars. |
| G1 exact gridlock populations | Lean proves `(∃ s, Jam s ∧ carCount s = n) ↔ min(W,H) ≤ n ∧ n ≤ WH`. Necessity uses a simple occupied blocker cycle and its actual winding; sufficiency uses executable row/column prefix constructions with proved exact counts. Conservation proves the same existence interval for orbits reaching a jam, and excludes every future jam below the minimum. | G1 is complete for CLASSIC. Eventual positive velocity, classifier correctness, and unrestricted refinement of the distinct Python constructor remain separate. |
| G2 sub-full non-gridlock construction | Lean proves that executable `nonGridlockWith W H n` has exactly n cars and never reaches a jam for every positive W,H and n<WH. A single-species mixed lane is preserved by the actual synchronous kernel and has a mover at every iterate; zero cars use the empty-state boundary. | G2 is complete for CLASSIC. Never reaching total gridlock does not assert eventual free flow or movement of every car. |
| Forced gridlock at a fixed population | Lean proves, under feasibility n≤WH, that every n-car configuration eventually jams iff n=WH. Exact full count is equivalent to full occupancy; any sub-full count has the G2 counterexample. | The feasibility assumption avoids a vacuous universal claim above WH. This is a deterministic extremal theorem, not a probabilistic threshold. |
| B2, diagonal coset identity | Lean proves the signed action generated by the actual cyclic successor/predecessor has precisely the fibers of `phaseClass=(x+y) mod gcd(W,H)` as its orbits. It proves the origin kernel identity, the east-translated class-one criterion, and witnesses in both 0≤t<lcm(W,H) and 1≤t≤lcm(W,H). | B2 is complete for positive dimensions, including singleton axes. This is coordinate geometry; `diagonalStep` is not the traffic update. |
| R, free-flow rigidity | Lean proves `StaticFree s ↔ ∀ t, AllMove (f^t s)` for the actual east-then-north kernel on every positive rectangle. The first `lcm(W,H)` rounds suffice; both strict and inclusive time-window formulations are proved. Static-free states return after the lcm and remain periodic. Failure of a static condition forces a blocked round before the lcm. | R is complete, including empty boards and singleton axes. Perpetual free flow starts at time zero; eventual free flow is equivalent to eventual entry into `StaticFree`, with no claim that such entry always occurs or has a uniform time bound. The lcm need not be the least configuration period. |
| CLASSIC low-density eventual free flow (B7) | Lean proves every board with `2m < g` has full movement in every round at or after `lcm(W,H) * m(g−2)` on positive W×H tori, where g=gcd(W,H). The state is `StaticFree` at that deadline. Every finite prefix contains at most g−2 blocks per car and m(g−2) blocked rounds. See [blueprint B7](blueprint.md#b7-classic-low-density-speed-one). | The elapsed-time bound combines the blockage budget with B3's finite free window; it does not assert sharpness. The equality case and fixed-positive-density probabilistic criticality remain open. |
| F, maximal free flow | Lean proves the exact capacity on every positive W×H torus: max(H⌊W/2⌋,W⌊H/2⌋) when g=gcd(W,H)=1, and (WH/g)⌊2g/3⌋ otherwise. Actual phase-fiber counts feed a cyclic weighted packing bound; executable patterns attain the bound, and species-preserving deletion attains every smaller count. Static, perpetual, and eventual existence spectra are all proved. The square formula and exact two-thirds criterion 3∣L are corollaries. | F is complete for CLASSIC, including singleton axes and the empty board. This is an existential capacity theorem; it does not assert that every board below the capacity reaches free flow. Finite construction replays and independent max-plus DP checks remain separate implementation evidence. |
| Genuine un-jamming (Theorem U) | Lean proves genuine un-jamming exists exactly when both sides are at least 2 and one is at least 4. The singleton proof uses a permanent obstacle. The four small tori use kernel-checked finite certificates with the added car tracked through recurrence. | The classification is complete for CLASSIC. See [B8](blueprint.md#b8-theorem-u-genuine-un-jamming-classification). |
| No initial simple loop, followed by gridlock | Reproducible identity-aware Python certificate on 3×2, compared against NumPy. | This witness is not currently a Lean theorem. |
| Python/Lean/Quint correspondence | Actual implementations are evaluated and compared on the finite domains below, including both half-steps and separate move counts. | A finite replay is not unrestricted source refinement or proof of the classifier algorithm. |
| Probability reductions and sparse no-gridlock window | The [probability note](../docs/research/2026-11-18-probabilistic-gridlock-bounds.md) gives prose proofs of `M = J intersect R-complement`, a uniform exponentially small ring exception, and no eventual gridlock with high probability when `p_L*L <= 2*log(log(L))-4*log(log(log(L)))-2` eventually. Python checks finite iid probabilities and strip certificates. | The probability laws, analytic limits, mixed-cycle reduction, and strip-crossing argument are not an end-to-end Lean theorem. No fixed-positive-density nonjamming interval, sharp transition, or critical-density value is proved. |

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
python scripts/check_barriers.py --report .artifacts/barriers-replay.json
python scripts/check_path_core.py --report .artifacts/path-core-replay.json
npm ci --ignore-scripts --prefix formal/quint
cd formal/lean
lake build
lake env lean Audit.lean
lake env lean G2Audit.lean
lake env lean CosetAudit.lean
lake env lean FreeFlowAudit.lean
lake env lean FreeMaxAudit.lean
lake env lean SparseSpeedAudit.lean
cd ../..
python scripts/check_lean_replay.py --max-cells 9 --report .artifacts/lean-replay.json
python scripts/check_g1_constructions.py --max-side 12 --report .artifacts/g1-constructions.json
python scripts/check_g2_constructions.py --max-side 12 --report .artifacts/g2-constructions.json
python scripts/check_cosets.py --max-side 12 --report .artifacts/cosets.json
python scripts/check_freeflow.py --max-cells 9 --report .artifacts/freeflow.json --rows .artifacts/freeflow.tsv
python scripts/check_free_max.py --max-side 12 --report .artifacts/free-max.json --rows .artifacts/free-max.tsv
python scripts/check_sparse_speed.py --report .artifacts/sparse-speed.json
python scripts/check_gated.py --report .artifacts/gated-replay.json
python formal/quint/check.py --max-cells 6 --report .artifacts/quint-replay.json
python scripts/check_absorption.py --report .artifacts/absorption-acceptance.json
```

The Lean package has no external library dependencies. Its transitive axiom
audits check the imported `BML` declarations, the G1, G2, coset, free-flow predicate,
free-flow construction, and absorption exporters with their
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
| Actual Lean F constructions and both phase traces | Every exact population 0≤n≤freeMax on all 144 ordered rectangles with 1≤W,H≤12: 3,334 configurations and 146,348 full transitions through their complete lcm windows. The independent checker validates the formula, static constraints, digit boards, counts, both phase states and movements, closure, full domain coverage, and corrupted-output rejection. |
| Historical table reproduction | All 23 stored records with WH≤9, regenerated and compared in full. |
| Compiled exhaustive tables (`bml/native/classify.c`) | Every ordered shape with 17≤WH≤22 (`data/exhaustive-17-22.json`), plus all 24-cell shapes and 5×5 (`data/exhaustive-24-25.json`). The classifier uses a translation quotient, bitmask CLASSIC rounds and Floyd cycle detection; it reproduces all 50 records of `data/exhaustive.json` and the 2×9 table. These tables check the G1 minimum and the F capacity numerically on these shapes. They are finite evidence, not part of the Lean proofs. |
| Actual Lean G1 constructor vs Python CLASSIC dynamics | All 5,578 admissible exact counts on all 144 positive rectangles with W,H≤12. Exported digits and numerical counts are checked independently, followed by both actual Python half-steps and the full step. This is bounded implementation evidence alongside the universal Lean G1 theorem. |
| Actual Lean G2 constructor and traces vs Python CLASSIC dynamics | All sub-full counts 0≤n<WH on all 144 positive rectangles with W,H≤12, at times 0…2 max(W,H). Both actual Lean phases, numerical counts, trace continuity, the mixed-lane invariant, and the empty/nonempty jam boundary are checked independently. This finite trace domain supplements the universal Lean proof for all times. |
| Actual Lean diagonal geometry vs an independent modular-coordinate oracle | All 6,084 positions on 144 ordered rectangles with W,H≤12. Complete cycles reconstructed from each starting point give 283,526 orbit visits. Both the same-class and east-translated class-one relations are checked on 422,500 ordered pairs each; 12 corrupted-output controls must be rejected. These coordinate observations are separate from the traffic-configuration gate for R. |
| Python G1 and F constructions | Every positive W,H≤12. The Python constructor uses a different anchor/fill order from Lean's G1 constructor; no equality between their output arrays is asserted. The complete universal F theorem is proved separately in Lean; these checks evaluate Python constructions. |
| CLASSIC B7 sparse-speed replay | 13,978 sparse boards on 14 ordered shapes, with 121,457 rounds through first board recurrence. Compares both CLASSIC phases, original-car destinations and movement, corrected classes, and the executable deadline. Complete recurrence traces certify permanent-flow entry by that deadline; targeted finite prefixes do not claim permanence. Nine targeted cases include larger sparse queues, strict density equality, dense gridlock, TRAIN queue movement, north-phase timing, the empty prefix, and a sparse orbit whose last blockage occurs after its bad-round budget. |
| Static cores and independent capture replay | All 34,344 states on 2×2, 3×2, 2×3, 4×2, 2×4, and 3×3 tori. All 831 states with a mixed core have independent tagged capture replay (964 edges, including frozen self-edges). These are separate from the kernel correspondence domains above. |
| Maximal frozen cores and recurrent path mass | All 19,764 initial states on 2×2 and 3×3, with 162,318 independent labeled edges. Pruning is checked against scalar path walks and both the population and area cutoffs. Terminal core tags match independently stopped identities. Exact initial-law integration checks normalized core/event comparisons and population envelopes. On 3×3, 5,121 initial states acquire additional core sites and 9,387 ringless nonjam initial states have positive recurrent three-vertex path mass. These are finite states, not an all-size decay estimate. |
| Eventual mixed-cycle formation, ring exceptions, and strip obstructions | All 565,785 states on those six tori plus 4×3. Eventual mixed-cycle occurrence is propagated from separately detected cycles through the successor graph and compared with the jam classifier. Every allowed strip width is checked. The 4×4 non-monotonicity example is a trajectory control, not an exhaustive 4×4 census. |
| Specified winding staircase after one round | All 43,046,721 initial states on 4×4: the local preimage predicate is compared pointwise with the full-round kernel, and car-count coefficients are integrated under exact initial iid weights. This is a one-step event census, not an eventual-basin census on 4×4. |
| Disjoint-strip capacity and exact marginal laws | All 565,785 states on the seven probability domains above; 8,821,224 predicates cover every strip width and cyclic partition offset. All 525 marginal evaluations match direct initial-state weights. The certificate union adds 696 states beyond all cyclic north-empty single-strip certificates in the same orientation. Separate 8×8 controls check both orientations; those controls and optimized 8×8/12×12 bounds are not basin censuses on the larger squares. |
| Prescribed lane-profile jam witnesses | Every admissible ordered positive profile pair on square sides 2–5: 16,492 pairs, each checked for exact counts, actual zero movement, and an independent labeled fixed point. Nine larger profiles are targeted controls. The separate initial-law census contains every state on sides 1–3 (19,767 states), with 15 exact density evaluations and 75 shared-cell probability-mass checks. |
| Protected queues with arbitrary exteriors | Every W,H≥2 with WH≤12, every 0≤T≤W−2, every exterior and every torus translation: 275,526 canonical boards, 3,263,850 translated tagged cases and 299,673 canonical tagged rounds compared with both production half-steps. The public verifier is separately called on 508 representatives. Initial-law checks cover all 2,278,206 states on those 12 tori, 6,208,974 finite-time predicates and 130 exact rational comparisons. These finite checks support the independent universal Lean theorem and prose probability derivation. |

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

`scripts/check_path_core.py` compares each maximal core with independent
static path walks, checks its monotone spatial membership and fixed species,
and follows every initial state in its declared domain to exact labeled
recurrence. It compares the terminal core with the original stopped-tag set
and integrates terminal-cycle path averages with initial board weights.
An independent population-allocation oracle checks the exact envelope.
The source-bound receipt separates these finite checks from the universal
deterministic API and the remaining asymptotic mass estimate.

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
controls. The Lean job also runs the G1 and G2 construction exporters, the
coset coordinate exporter, the free-flow predicate/trace exporter, and the
F exact-count constructor exporter, with their audits and rejection controls. G1 checks frozen boards at every admissible
count; G2 replays both phases from every sub-full construction and checks the
persistent mixed lane. The coset gate reconstructs complete coordinate cycles
and checks both phase-class relations against an independent modular oracle.
The free-flow gate compares both actual traffic phases and formal predicate
decisions with NumPy and independent scalar orbit following through its
declared finite domain. The F gate checks every attainable population through
side length 12 against independent scalar phase updates and the exact formula.
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
