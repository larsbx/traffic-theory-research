# Lean proof suites

This dependency-free package pins **Lean 4.34.1**. The `BML` and `Traffic`
libraries implement **CLASSIC** updates, with vacant destinations required in
the pre-half-step state. The `Train` library, in namespace `BML.Train`, implements
**TRAIN** queue movement and full-ring rotation. All use simultaneous east then
north full steps. Both torus dimensions must be positive; singleton dimensions
are included.

This page retains the detailed **CLASSIC BML finite-torus register**. See the
[Traffic register](../traffic-layer.md) for its tiling/staircase layer and the
[TRAIN register](../TRAIN.md) for the complete zero-movement existence theorem,
numeric conservation, and bounded implementation comparisons. The CLASSIC
fixed-point equivalence below does not hold for TRAIN occupancy: a rotating
ring may keep the same colors in the same cells while cars move.

## Run

```sh
cd formal/lean
lake build
lake env lean Audit.lean
lake env lean AbsorptionAudit.lean
.lake/build/bin/bml_replay 3 3
```

`bml_replay WIDTH HEIGHT` enumerates all `3^(WIDTH*HEIGHT)` states. Its headerless
CSV columns are:

```text
index,east_state,next_state,east_moves,north_moves
```

State codes use `0 = empty`, `1 = east`, `2 = north`, with digit position
`x + WIDTH*y`, exactly as in `bml.exhaustive`. The executable calls the same
`halfStep`, finite-torus directions, and movement predicate used in the proofs.
It does not embed Python-produced expected transitions.

## Kernel-checked coverage

| Module | Results |
|---|---|
| `BML/Kernel.lean` | Moving sources empty and destinations fill; other species remain in place; a half-step is fixed iff its cars are blocked; a full east-then-north step is fixed iff both local blocking conditions hold; equivalence with no movement in either phase; frozen-state persistence, including after a transient; full occupancy freezes; the empty state is fixed but is not a jam. |
| `BML/Transport.lean` | Explicit bijection between each species' cars before and after its phase: survival, injectivity, and surjectivity. Nonemptiness is preserved by a full step and every iterate. `BML/Lanes.lean` now connects the transport bijection to numerical CLASSIC count conservation; the TRAIN library retains its own separate conservation proofs. |
| `BML/Lanes.lean` | Actual CLASSIC numerical species-count, east-row-count, and north-column-count conservation through half-steps, full steps, and iterates. Full E-rows and full N-columns persist and reflect backward, cannot coexist, and have no hidden movement. Specified north-free columns, cyclic strips, and row-count bounds are invariant through every iterate. |
| `BML/Profiles.lean` | An explicit square-torus configuration realizes arbitrary positive E-row and N-column count vectors whenever every row-count/column-count sum is at most the side length. Exact executable lane counts follow from an involutive cyclic-coordinate bijection. The configuration is a nonempty CLASSIC jam, has no movement or full monochromatic lane, and is fixed by the actual kernel. Same-profile existence and rejection by universally sound profile-only jam-exclusion predicates are proved. |
| `BML/Capture.lean` | Successor-closed occupied cores persist. A supplied occupied closed walk yields a core (distinct sites are not required by this Lean declaration). Full-round tagged transport is bijective. Explicit core obstacles on every row and column give a kernel-derived cyclic-distance rank, a bound `M = n_E*(W-1) + n_N*(H-1)` on every finite prefix of tagged moves, and a nonempty jam by full round M. |
| `BML/Formation.lean` | Exact local initial predicate for an E site and adjacent N site after one round, conditional on the next N target being E after the east phase; simultaneous formation from initial predicates and a supplied successor geometry; construction of the formed occupied core. All are deterministic actual-kernel results. The transfer probability and torus winding/cover instantiation remain separate prose arguments. |
| `BML/Absorption.lean` | All-time soundness of hit/safe/unresolved cutoff certificates for an absorbing target; finite natural-weight bounds, nested intervals, and exactness at zero unresolved weight. Instantiated with actual CLASSIC nonempty `Jam`, with a proved data-valued board refinement for executable probes. |
| `BML/Delay.lean` | An initial eastbound run of length `T+2` blocks its original rear car at round `T`, regardless of the exterior. A permanent full-movement starting time must exceed `T`. Kernel-checked `4x4` vacant east/south cycle that disappears into a nonempty jam after one round. |
| `BML/Fixation.lean` | Eventual constancy of an original `carTrace` is equivalent to finitely many actual moves. An eventually permanent car has an eventually permanent successor, with the north proof using the post-east checkpoint. All permanent sites form a nonempty core at a common future time. A core that misses a row forces a full E-row; a missed column forces a full N-column. Consequently, some original car fixes iff eventual nonempty jam or an initial full monochromatic lane occurs. All cars fix iff the state is empty or eventually jams. Outside both exceptional events, every original car moves and every site becomes empty arbitrarily late. |
| `BML/Torus.lean` | Positive finite cyclic coordinates with proved inverse shifts; the general kernel is instantiated on `Fin WIDTH × Fin HEIGHT`; executable base-three encoding, decoding, and counts. |
| `BML/Arithmetic.lean` | Divisibility of positive winding lengths implies the `min(WIDTH, HEIGHT)` lower bound. The proposed class packing expression simplifies to `floor(2*g/3)` and attains exact `2/3` iff `3` divides `g`. These are arithmetic components of G1 and F. |
| `BML/Witnesses.lean` | A stronger nonmonotonicity example on width 4, height 2. State `3858` reaches jam `2048` after three steps. Adding one north car at `(0,0)` yields `3860 ↔ 4340`, which never jams. The added car remains blocked forever. An explicitly tracked original north car moves at every step. |

The full-step fixed-point converse does not assume that two consecutive updates
cannot cancel. It proves that a moved east car leaves its source empty, and the
north phase cannot restore an east car there. The east phase must therefore
already be fixed; the north condition follows.

`Jam` explicitly requires a nonempty state. In particular, the empty state is not
a counterexample to the classification convention that assigns it free flow.

The strong witness's `originalTrace` is an identity-following recurrence using
`transport`, rather than a statement that some unlabeled car moves. The tracked
car occupies column 1 in both cycle states and was present before the added car.

For capture, `RouteCover` supplies an already occupied successor-closed core
and a specified core obstacle on every row and every column. The public theorem
`RouteCover.jammed_by_movementBudget` derives strict decrease from actual
`CanMove` events and tagged transport; it does not assume rank decrease as an
unproved premise. `RouteCover.total_moves_le` counts moves through original car
tags and the proved `carTrace_bijection`. A separate equality with the existing
Eulerian `moveCount` function is not claimed.

`Fixation.lean` now also constructs `RouteCover` from any nonempty closed core
when there is no full E-row or full N-column. Its proof minimizes cyclic distance
to a hypothetically missed lane, then propagates along a finite cyclic lane.
It does not assume a supplied winding cycle or use the unmerged general cycle
extraction proof. Direct construction from a mixed occupied blocker cycle,
without the no-full-lane hypothesis, remains a prose argument with Python
certificate checks. The capture mechanism is already used in
Angel–Holroyd–Martin's torus proof; no novelty claim is made.

The new event identity is
`hasEventuallyStoppedCar_iff_jam_or_full_lane`. `HasEventuallyStoppedCar`
quantifies over a species and an initially present car, and requires its actual
`carTrace` to become constant after some round. The theorem
`tagEventuallyStopped_iff_finitely_many_moves` connects this definition to the
actual `RoundCanMove` events, including singleton dimensions. `EventuallyJammed`
requires the existing nonempty `Jam`; `HasFullMonochromaticLane` refers to the
initial state. Thus the identity has no empty-configuration exception hidden
in its definitions. The separate theorem
`allCarsEventuallyStopped_iff_empty_or_jam` explicitly includes the empty state,
where universal fixation is vacuous. `eventuallyJammed_every_tag_stops` follows
every initially present tag and supplies the deterministic implication needed
for stopped-car counts.

The successor proof distinguishes full-round and post-east checkpoints. At
full-round checkpoints continued occupancy permits at most an E-to-N species
change; after the east phase it permits at most an N-to-E change. A finite
common stabilization time yields the future core. The existing movement budget
applies from that core's appearance; this argument provides no effective bound
on its formation time. `every_tag_moves_arbitrarily_late` proves infinitely many
actual moves outside eventual jam and the initial full-lane event. It does not
assert eventual speed one. `every_site_empty_arbitrarily_late` proves the
corresponding repeated vacancy statement.

`Lanes.lean` uses the finite-list cardinality helpers in `Train/Counting.lean`.
Those helpers import only `BML.Torus` and assume no TRAIN movement semantics;
the conservation proofs use CLASSIC `transport` and `halfStep`.
`Fixation.lean` also imports finite cyclic predicate propagation from
`Train/Finite.lean`, which likewise imports only `BML.Torus`; no TRAIN kernel or
transition result is used. The
probability laws and limiting arguments in the
[probability note](../../docs/research/2026-11-18-probabilistic-gridlock-bounds.md)
remain prose mathematics. Numerical conservation does not establish those
asymptotics or a probabilistic critical density.

The public invariant results include `speciesCount_iterate`,
`eastRowCount_iterate`, `northColumnCount_iterate`,
`fullEastRow_iterate_iff`, `fullNorthColumn_iterate_iff`,
`hasFullMonochromaticLane_iterate_iff`, `northFreeStrip_iterate_iff`, and
`eastRowsBelow_iterate_iff`. `NorthFreeStrip` permits arbitrary lengths for its
deterministic invariant; any use of distinct columns in a probability argument
must separately require that the length not exceed the width.

### Jammed representatives of prescribed lane profiles

`Profiles.lean` treats a square of positive side length `L` and arbitrary vectors
`r c : Fin L → Nat`. Its main hypotheses are `1 ≤ r y`, `1 ≤ c x`, and
`r y + c x ≤ L` for every row and column. Equivalently, the sum of the two
profile maxima is at most `L`. The caps interface
`exists_jam_with_lane_profile_of_caps` accepts any proved upper bounds `R,C`
with `R+C ≤ L`. Positivity makes `L=1` inadmissible and keeps every individual
lane count strictly below `L`.

The executable `laneProfileJam` puts E at `(x,y)` when the forward cyclic
distance from `x` to `y` is below `r y`, and N when the distance from `y` to `x`
is in `[1,c x]`. These are the modular placements `E(y-j,y)` for `0≤j<r y`
and `N(x,x-i)` for `1≤i≤c x`. Disjointness and exact numerical counts are
proved rather than assumed. `laneProfileJam_jam`, `laneProfileJam_no_moves`,
`laneProfileJam_fixed`, and `laneProfileJam_no_full_lane` cover the actual
CLASSIC dynamics and exclude a full-lane explanation of the constructed jam.

`exists_jam_with_same_lane_profile` says that any configuration satisfying
these profile bounds shares its exact conserved count vectors with an already
jammed configuration. It does not assert that the original configuration
evolves into that representative. The theorem
`admissible_profile_cannot_certify_no_jam` explicitly assumes a predicate of
only the two vectors is sound for excluding already jammed states, and proves
that the predicate rejects every admissible profile. This applies in particular
to universally sound certificates of eventual nonjamming. Probability estimates
for typical iid profiles and their consequence for the acceptance probability
of such certificates remain prose results in the
[lane-profile note](../../docs/research/2026-11-18-lane-profile-obstruction.md).
No bound on a jammed basin's conditional probability, and no fixed-density
transition theorem, follows from representative existence alone.

## Audit and trust boundary

`Audit.lean` traverses every imported CLASSIC `BML` declaration and its transitive axiom
dependencies. It checks that the required theorem names are present and rejects
any axiom outside Lean's usual `propext`, `Quot.sound`, and `Classical.choice`.
Thus incomplete proofs and native decision-result axioms fail the audit.
Concrete witness proofs use kernel-reduced `decide`, and the infinite-time
claims use induction.

The CLASSIC replay executable provides finite comparison evidence against the Python
and Quint implementations. Such comparisons are not an all-size source
refinement proof. General correctness of the encoding/counting routines is not
claimed merely because they compile.

## Certified eventual-gridlock bounds

`BML/AbsorptionExport.lean` exports the verified cutoff probe:

```sh
.lake/build/bin/absorption_export 2 2 0,1,2,4,8,16
.lake/build/bin/absorption_export 4 4 0,1,2 18626220
```

Rows are `initial_code,cutoff,terminal_code,verdict,population`, in cutoff-major
order. Verdicts are `0 = hit`, `1 = safe`, and `2 = unresolved`. A nonempty
terminal jam certifies a hit; exact recurrence of a non-target terminal state
certifies all-time avoidance. An unresolved orbit retains its entire initial
weight in the upper bound. A safe orbit need not reach full speed.

The executable stores each board as data, and `boardConfig_iterate` proves
that its updates agree with the original function-valued CLASSIC kernel.
`AbsorptionAudit.lean` separately checks the exporter and its transitive
axiom dependencies. The finite three-language gate is
`python scripts/check_absorption.py` from the repository root; it checks
22,320 exhaustive cutoff rows and larger targeted cases. See the
[certificate note](../../docs/research/2026-11-18-certified-absorption-bounds.md)
for exact probability accounting and the separate remaining asymptotic target.
The queue-based probability and logarithmic-time arguments are prose results
in the [relaxation note](../../docs/research/2026-11-18-relaxation-obstructions.md),
not Lean probability theorems.

## TRAIN library and executable

`Train/Threshold.lean` proves, for every positive W,H, that a nonempty
zero-movement n-car TRAIN state exists iff W+H≤n≤WH. Its explicit all-count
constructor is connected to the executable kernel, and the singleton interval
is empty. `Train/Conservation.lean` proves numeric species/population
conservation and separates actual movement from occupancy equality.

The complete speed-one layer uses `Train/Diagonals.lean` for eventual stability
of sparse corrected cyclic traces, and `Train/DiagonalDynamics.lean` for actual
identity transport, trace coverage, and release before an empty diagonal.
`Train/FreeFlow.lean` proves that maximum actual move count means every car
moves in its own phase. The final theorem in `Train/SpeedOne.lean` has
hypothesis `2 * population s < N` on N×N and
conclusion that, from some time onward, every full-cycle move count equals the
initial population. Both `sparse_square_eventually_fullSpeed` and
`sparse_square_moves_equal_population` are kernel-checked for the actual TRAIN
step. See [the detailed proof and scope](../TRAIN.md#sparse-squares-eventual-speed-one).
The empty state is included; there is no effective time bound or CLASSIC
transfer in this statement.

```sh
cd formal/lean
lake build Train train_replay
lake env lean TrainAudit.lean
.lake/build/bin/train_replay --max-cells 6
.lake/build/bin/train_replay --construct 8
```

The standard replay is headerless TSV with ten fields:

```text
width,height,input,east,north,full,eastMoves,northMoves,cycleNorthMoves,stuck
```

`north` and `northMoves` refer to a north half-step on the original board;
`full` and `cycleNorthMoves` use the state after the east half-step. These
movement counts include homogeneous-ring rotation. The constructor mode emits
the requested and actual populations before the standard row's eight fields
after width and height. The Boolean `stuckCheck` is proved equivalent to the
semantic `Stuck` predicate. `TrainAudit.lean` audits this layer separately;
[`scripts/check_train.py`](../../scripts/check_train.py) compares its outputs
with the actual Quint interpreter and Python TRAIN implementation.

## Remaining obligations

This package does **not** prove the full list G0–F. The missing general
mathematics remains:

- Extract a simple blocker cycle from every nonempty frozen finite state, then
  connect its torus winding and distinct-car count to G1; formalize all G1
  constructions.
- Formalize the G2 non-gridlocking configurations for every sub-full car count.
- Prove the subgroup/coset assertion and both directions of rigidity Lemma R.
- Connect Lemma R to the cyclic class packing upper bound and all densest
  constructions in F.
- Formalize eventual periodicity/classifier correctness and unrestricted
  Python-to-Lean source correspondence.
- Construct `RouteCover` witnesses directly from a mixed occupied blocker cycle
  without a separate no-full-lane hypothesis, and connect the Python certificate
  verifier to those Lean witnesses. The new closed-core theorem already covers
  every nonempty core in the absence of full monochromatic lanes.

No probabilistic critical density, asymptotic typical-case theorem, or
quasicrystal spectral statement is asserted by this layer.
