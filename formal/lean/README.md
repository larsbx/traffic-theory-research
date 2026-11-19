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
the sparse-square eventual-speed-one theorem, numeric conservation, and bounded
implementation comparisons. The CLASSIC
fixed-point equivalence below does not hold for TRAIN occupancy: a rotating
ring may keep the same colors in the same cells while cars move.

## Run

```sh
cd formal/lean
lake build
lake env lean Audit.lean
lake env lean G2Audit.lean
lake env lean CosetAudit.lean
lake env lean FreeFlowAudit.lean
lake env lean FreeMaxAudit.lean
lake env lean SparseSpeedAudit.lean
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
| `BML/Transport.lean` | Explicit bijection between each species' cars before and after its phase: survival, injectivity, and surjectivity. Nonemptiness is preserved by a full step and every iterate. Numerical CLASSIC conservation is derived in `BML/Counting.lean` and `BML/Lanes.lean`; the TRAIN library retains its own separate conservation proofs. |
| `BML/Profiles.lean` | An explicit square-torus configuration realizes arbitrary positive E-row and N-column count vectors whenever every row-count/column-count sum is at most the side length. Exact executable lane counts follow from an involutive cyclic-coordinate bijection. The configuration is a nonempty CLASSIC jam, has no movement or full monochromatic lane, and is fixed by the actual kernel. Same-profile existence and rejection by universally sound profile-only jam-exclusion predicates are proved. |
| `BML/Capture.lean` | Successor-closed occupied cores persist. A supplied occupied closed walk yields a core (distinct sites are not required by this Lean declaration). Full-round tagged transport is bijective. Explicit core obstacles on every row and column give a kernel-derived cyclic-distance rank, a bound `M = n_E*(W-1) + n_N*(H-1)` on every finite prefix of tagged moves, and a nonempty jam by full round M. |
| `BML/Formation.lean` | Exact local initial predicate for an E site and adjacent N site after one round, conditional on the next N target being E after the east phase; simultaneous formation from initial predicates and a supplied successor geometry; construction of the formed occupied core. All are deterministic actual-kernel results. The transfer probability and torus winding/cover instantiation remain separate prose arguments. |
| `BML/Absorption.lean` | All-time soundness of hit/safe/unresolved cutoff certificates for an absorbing target; finite natural-weight bounds, nested intervals, and exactness at zero unresolved weight. Instantiated with actual CLASSIC nonempty `Jam`, with a proved data-valued board refinement for executable probes. |
| `BML/Delay.lean` | An initial eastbound run of length `T+2` blocks its original rear car at round `T`, regardless of the exterior. A permanent full-movement starting time must exceed `T`. Kernel-checked `4x4` vacant east/south cycle that disappears into a nonempty jam after one round. |
| `BML/GuardedQueue.lean` | A main E run at offsets `0..T`, a hole at `T+1`, and a lower E guard at offsets `1..T` force the original rear tag's first move to occur in round `T`, regardless of the exterior. One-round and iterated shrinking follow from the actual two-phase kernel. Any nonempty jam time is strictly greater than `T`. Generic results assume east-next commutes with north-previous; torus specializations discharge this premise. |
| `BML/Fixation.lean` | Eventual constancy of an original `carTrace` is equivalent to finitely many actual moves. An eventually permanent car has an eventually permanent successor, with the north proof using the post-east checkpoint. All permanent sites form a nonempty core at a common future time. A core that misses a row forces a full E-row; a missed column forces a full N-column. Consequently, some original car fixes iff eventual nonempty jam or an initial full monochromatic lane occurs. All cars fix iff the state is empty or eventually jams. Outside both exceptional events, every original car moves and every site becomes empty arbitrarily late. |
| `BML/Locality.lean` | A radius-`T` lifted box determines the time-`T` torus color. Lifted points at height gaps in `(0,L)` have distinct projections on the square torus. Excluding compatible initial origins of both species forces time-`T` vacancy. |
| `BML/Torus.lean` | Positive finite cyclic coordinates with proved inverse shifts; the general kernel is instantiated on `Fin WIDTH × Fin HEIGHT`; executable base-three encoding, decoding, and counts. |
| `BML/Counting.lean` | The position enumeration is complete and has no duplicates. Filtered species lists agree with the executable `speciesCount` sums; the occupied-list length is their sum. Transport induces a list permutation, proving numerical species conservation under every half-step, and total-count conservation under every full-step iterate. |
| `BML/Enumeration.lean` | Explicit row-major and reverse row/column bijections, with quotient/remainder inverses. A configuration occupying exactly a prefix of n ranks has actual car count n. |
| `BML/AllCounts.lean` | Total executable `gridlockWith` constructs a CLASSIC jam at every exact population `min(WIDTH, HEIGHT) ≤ n ≤ WIDTH*HEIGHT`. Frozen-state and exact-count proofs cover both orientations, partial final lines, and singleton dimensions. |
| `BML/FiniteCycle.lean` | Every endofunction on a nonempty finite closed carrier has a positive simple cycle bounded by the carrier's length. The proof uses pigeonhole reasoning and a minimal positive return time. |
| `BML/Blocking.lean` | A frozen state's blocker map preserves occupancy. An actual blocker walk lifts to nonnegative east/north displacements and seam-crossing counts. Closure implies divisibility by the torus side lengths, hence the shorter-side lower bound. |
| `BML/Extremal.lean` | Full east rows and full north columns are nonempty frozen states with exactly WIDTH and HEIGHT cars. Choosing the shorter line attains `min(WIDTH, HEIGHT)`. |
| `BML/Gridlock.lean` | Every jam has a simple occupied blocker cycle of length between `min(WIDTH, HEIGHT)` and its actual car count. Combining this with the all-count constructor proves the full G1 iff, both for already-jammed states and the existence of orbits reaching a jam. Fewer cars never reach a jam at any iterate. |
| `BML/Ring.lean` | Iterating a positive cyclic coordinate has the expected modular value and period; every site is reachable from every other site in fewer than the lane length many shifts. |
| `BML/Congruence.lean` | Bézout coefficients derived from gcd induction; the compatible signed congruence criterion; the representative-pair `coset_iff` statement with its necessary coordinate bound. |
| `BML/Cosets.lean` | Signed translations form an action on actual finite cyclic coordinates. Natural-time iteration agrees with `diagonalStep=(cyclicNext,cyclicPrev)`. Arbitrary-point reachability is exactly equality of `phaseClass`; the origin orbit is its zero class, and an east translation selects the next class. |
| `BML/CosetTimes.lean` | Signed times reduce modulo lcm(WIDTH,HEIGHT); the actual diagonal step returns exactly at multiples of that lcm. Both ordinary and east-translated coset relations have witnesses below lcm and positive witnesses at most lcm. |
| `BML/Rigid.lean` | `AllMove` evaluates north movement after the east phase. A fully moving half-step and full round translate the active species exactly; any moving prefix gives both inverse-coordinate and forward-coordinate occupancy equivalences. These statements hold for arbitrary invertible directions. |
| `BML/Encounters.lean` | Connects B2's diagonal orbits to east/north forward encounters. Equal phase classes meet at a positive time at most the lcm; the next phase class supplies an east-target/north-position encounter before the lcm. Also phase-class shift identities and lcm returns for each direction. |
| `BML/FreeFlowConditions.lean` | Defines `StaticFree` by the two same-species adjacency exclusions and the forbidden equal/next phase classes for each east/north pair. |
| `BML/FreeFlowNecessity.lean` | Full movement in the first lcm rounds implies every static condition, using rigid prefixes and bounded encounter witnesses. |
| `BML/FreeFlow.lean` | Static conditions imply actual full movement and are invariant under the traffic step. Lemma R gives the static/perpetual equivalence, strict and inclusive finite-window criteria, and a blocked-round witness when a condition fails. Static-free configurations return after the lcm; eventual full movement is equivalent to eventual entry into the static-free set. |
| `BML/FiniteSums.lean` | Duplicate-free finite sums, cyclic reindexing, rotation, interchange of coordinate sums, and adjacent-pair double counting. |
| `BML/PhaseCounts.lean` | Each actual phase fiber has WH/g sites. Exact species/count partitions, adjacent-species class capacities, and cross-species exclusions connect StaticFree to weighted packing. Saturating a phase pattern multiplies its occupied-class count by WH/g. |
| `BML/FreePacking.lean` | Universal weighted cyclic packing bound M⌊2g/3⌋ for g≥2. Three consecutive classes carry at most 2M; an empty class allows exact remainder rounding, and no empty class forces one species. |
| `BML/FreePureBound.lean` | Same-species lane counts are bounded by half the lane length. On a coprime torus StaticFree forces one species, giving the sharp maximum of the two directional capacities. |
| `BML/FreePattern.lean`, `BML/FreeConstruction.lean` | Explicit cyclic NE· and E· blocks attain ⌊2g/3⌋ occupied classes, with proved wraparound rules and exact counts. Phase-saturated and alternating pure-species boards give an executable maximizing configuration on every positive rectangle. |
| `BML/FreeDeletion.lean` | Arbitrary species-preserving deletion preserves StaticFree. Executable row-major prefix deletion retains exactly min(n, original count) cars. |
| `BML/FreeMaximum.lean` | Complete Theorem F: actual free-flow count is at most freeMax; freeWith attains every count through that maximum. Static, perpetual and eventual free-flow existence have the same exact population interval. Above capacity no orbit can enter StaticFree. On squares capacity is L⌊2L/3⌋, attaining density two thirds iff 3∣L. |
| `BML/Lanes.lean` | An east-only mixed row or north-only mixed column preserves a car and a hole under each actual full step; cyclic reachability supplies a mover at every iterate, supporting G2. The absent species phase is the identity. Numerical species, east-row, and north-column counts are conserved through both phases and iterates. Full E-rows and full N-columns persist and reflect backward, cannot coexist, and have no hidden movement. Specified north-free columns, cyclic strips, and row-count bounds are invariant through every iterate. |
| `BML/NonGridlock.lean` | Total executable `nonGridlockWith` has exactly n cars and never jams for every n<WIDTH*HEIGHT. Its column-major east prefix has a mixed first or last row when WIDTH≥2; width-one boards use a north prefix. The zero population remains empty and is not Jam. This completes G2. |
| `BML/GridlockThresholds.lean` | Actual car count equals area iff every cell is occupied. On every positive torus and for every feasible n≤WIDTH*HEIGHT, every n-car configuration eventually jams iff n=WIDTH*HEIGHT. |
| `BML/Arithmetic.lean` | Divisibility of positive winding lengths implies the `min(WIDTH, HEIGHT)` lower bound. The class packing expression simplifies to `floor(2*g/3)` and attains exact `2/3` iff `3` divides `g`. These are arithmetic components of G1 and F. |
| `BML/Witnesses.lean` | A stronger nonmonotonicity example on width 4, height 2. State `3858` reaches jam `2048` after three steps. Adding one north car at `(0,0)` yields `3860 ↔ 4340`, which never jams. The added car remains blocked forever. An explicitly tracked original north car moves at every step. |

The full-step fixed-point converse does not assume that two consecutive updates
cannot cancel. It proves that a moved east car leaves its source empty, and the
north phase cannot restore an east car there. The east phase must therefore
already be fixed; the north condition follows.

`Jam` explicitly requires a nonempty state. In particular, the empty state is not
a counterexample to the classification convention that assigns it free flow.

The minimum-gridlock proof connects three independently checked statements:
the occupied-position list is closed under the blocker map; finite cycle
extraction supplies distinct occupied vertices; and the actual east/north walk
closes only after a positive winding of at least the shorter side. Thus

```text
min(WIDTH, HEIGHT) ≤ cycle length ≤ carCount
carCount = speciesCount east + speciesCount north
```

`few_cars_never_jam` uses numerical conservation to apply this bound at every
future time. It does not assert eventual speed one or formalize the
positive-asymptotic-velocity consequence. `jam_carCount_iff` combines the lower
bound with the executable all-count construction to prove
`(∃ s, Jam s ∧ carCount s = n) ↔ min(WIDTH, HEIGHT) ≤ n ∧ n ≤ WIDTH*HEIGHT`.
`exists_eventual_jam_with_count_iff` proves the same interval for initial
populations admitting an orbit that reaches a jam.

`exists_never_jam_with_count` completes G2 with an exact population and a
conclusion quantified over every natural time. For positive populations below
area, the constructor uses a board of one species containing a mixed cyclic
lane. Its car and hole persist under the actual synchronous phase, and cyclic
reachability finds a car directly before a hole. This supplies a mover at each
iterate. Other lanes can remain blocked, so this is an avoidance-of-total-jam
theorem, not an assertion that every car eventually moves freely.

`forced_eventual_jam_iff` combines G2 with full occupancy. Its premise
`n ≤ WIDTH*HEIGHT` is necessary: above the area there are no n-car boards and
the universal quantifier would be true vacuously. Empty boards are fixed but
not jammed; on 1×1 the only sub-full population is zero. Single rows and columns
are covered without an extra lower bound on the other dimension.

`g1_export --max-side 12` evaluates the actual Lean constructor at all 5,578
admissible counts on the 144 positive rectangles within those side bounds.
Its TSV columns are width, height, requested count, actual count, east count,
north count, and row-major cell digits. `scripts/check_g1_constructions.py`
checks complete coverage, valid digits, all counts, and zero movement under
both actual Python CLASSIC phases. It does not compare this constructor's
array with the differently ordered Python `gridlock_with` construction.

`g2_export --max-side 12` evaluates the actual Lean G2 constructor at every
sub-full population on those 144 rectangles, then emits the actual intermediate
and final configurations through times `0…2 max(WIDTH, HEIGHT)`. Its TSV columns
are width, height, population, time, actual count, east count, north count, east
moves, north moves, jam flag, and row-major digits before the east phase, after
the east phase, and after the north phase. `scripts/check_g2_constructions.py`
checks exact coverage, both Python CLASSIC phases and movement counts, trace
continuity, species and population preservation, the persistent mixed lane, and
the special empty-state convention. These are finite implementation checks;
the unbounded-time conclusion comes from the Lean theorem.

### B2: coset geometry on actual cyclic coordinates

`phaseClass w h p = (p.x+p.y) % gcd(w,h)` identifies each signed
`diagonalShift` orbit with one phase-class fiber. `diagonalShift_exists_iff`
proves this for arbitrary points; `diagonal_kernel_iff` gives the zero-class
statement at the origin. `iterate_diagonalStep` connects the arithmetic action
to the actual cyclic successor/predecessor functions. The signed witness can
be chosen as a natural time in `[0,lcm)` or `[1,lcm]`, and starting at the actual
east neighbor gives the next class modulo the gcd. All statements cover
positive dimensions, including singleton axes and gcd one. `phaseClass_surjective`
realizes every residue, and coprime sides give one diagonal orbit.
`iterate_diagonalStep_eq_self_iff` identifies return times as precisely the
multiples of the lcm, hence fixes the least positive period.

This completes blueprint B2, with the witness windows used by B3. The
auxiliary `diagonalStep` acts on positions; it is not `torusStep` acting on
configurations. No free-motion hypothesis is assumed in B2, and its conclusion
alone does not characterize a traffic orbit as free. B3 supplies the rigid-motion
bridge and both implications of R below. The packing and constructions in F
remain open formal obligations.

`coset_export --max-side 12` emits width, height, gcd, lcm, source x/y,
diagonal-successor x/y, source class, east-translated x/y, and translated class.
`scripts/check_cosets.py` checks all 6,084 exported positions on 144 rectangles,
reconstructs a full cycle from every source (283,526 orbit visits), and compares
the sequence with independent modular-coordinate arithmetic. Each of the
same-class and east-translated reachability relations is checked on 422,500
ordered pairs. Twelve rejection controls cover incomplete/duplicate data,
malformed rows, coordinate range, step signs, modulus, period, phase class,
east translation, and its class. This finite gate supplements the universal
proof; a source-bound receipt records whether a run passed.

### B3: the actual free-flow characterization

For `E = eastDirection w h hw`, `N = northDirection w h hh`, and
`f = torusStep w h hw hh`, `AllMove E N s` requires every east car to move
in s and every north car to move in `halfStep E .east s`. The north condition
therefore reads the actual intermediate state. `StaticFree w h hw hh s`
forbids adjacent east cars along an east edge, adjacent north cars along a
north edge, and an east/north pair whose phase classes are equal or differ by
one in the east-to-north order.

`lemmaR` proves

```text
StaticFree s ↔ ∀ t, AllMove E N (f^t s).
```

`staticFree_allMove` proves eligibility in both actual phases, and
`staticFree_step` preserves the static conditions. Induction then gives
`staticFree_iterate` and perpetual movement. Conversely,
`staticFree_of_allMove_before_lcm` combines the rigid-prefix occupancy
equivalences with B2's encounters: a forbidden next-class pair blocks an east
target at some t<lcm, while an equal-class pair would put both species in one
cell at a positive time at most lcm. Thus the first lcm fully moving rounds
already force the static conditions.

`lemmaR_finite_lt` states that perpetual movement is equivalent to full
movement for every `0 ≤ t < lcm(w,h)`; `lemmaR_finite` gives the inclusive
`t ≤ lcm(w,h)` version. `lemmaR_window` relates the strict window directly to
`StaticFree`, and `not_staticFree_iff_blocked_before_lcm` gives a finite
witness of failure. `freeFlow_returns_lcm` and `freeFlow_periodic` prove
return after the lcm and repetition with that period at every later time.
Unlike the diagonal position action's exact period in B2, a configuration
may have a smaller least period; the empty state is one example.

These theorems cover every positive rectangle, including singleton axes and
the empty board. They characterize movement from time zero.
`eventually_allMove_iff_reaches_staticFree` separately identifies eventual
permanent full movement with eventual entry into the static-free set. B7 gives
a sufficient population condition and an explicit deadline for such entry.

`freeflow_export --max-cells 9` enumerates every initial configuration on
every ordered positive rectangle with WH≤9. Each row contains actual Lean
decisions of `StaticFree` and `AllMove`, plus both phase traces over
L=lcm(W,H) rounds. Its headerless TSV fields are:

```text
width,height,input_code,lcm,static_free,all_move_window,first_blocked,state_codes,east_codes,east_moves,north_moves,all_move_flags
```

The five final fields are comma-separated natural-number lists.
`state_codes` contains L+1 full states from t=0 through t=L. The remaining
four contain L entries for the intermediate east-phase states, each phase's
move counts, and full-round `AllMove` flags. `first_blocked` is the earliest
blocked round, or the sentinel L if all t<L rounds move fully. State codes
use the same row-major base-three encoding as `bml_replay`.

`scripts/check_freeflow.py --max-cells 9 --report .artifacts/freeflow.json
--rows .artifacts/freeflow.tsv` checks all 93,387 initial states on 23
rectangles and 622,362 full transitions. It compares actual intermediate
and final states and movement counts with NumPy, and compares perpetual
movement with a separate scalar orbit-following oracle. That oracle observes
blockage from time zero, including before any eventually free cycle. The
checker also verifies rigid moving prefixes, lcm closure for static-free
states, exact coverage, and corrupted-output rejection controls. These are declared finite
acceptance checks; a source-bound receipt records successful runs.

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
It does not assume a supplied winding cycle or use the independently compiled
G1 theorem `jam_has_simple_blocker_cycle` in `Gridlock.lean`. The G1 simple-cycle
certificate and Capture's closed-walk/core interfaces remain separate; no
general identification of those certificates is claimed. Direct construction
from a mixed occupied blocker cycle without the no-full-lane hypothesis
remains a prose argument with Python certificate checks. The capture mechanism is already used in
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

### B4: exact free-flow capacity

`BML/FreeMaximum.lean` proves Theorem F on every positive rectangle. With
`g=gcd(WIDTH,HEIGHT)`, `freeMax` is the maximum of the two pure-direction
half-lane capacities when g=1, and `(WIDTH*HEIGHT/g)*floor(2*g/3)` otherwise.
The phase-count bridge proves each fiber has `WIDTH*HEIGHT/g` cells and turns
actual static-free configurations into the five weighted packing constraints.
The cyclic packing theorem uses a triple cap and exact remainder rounding;
its no-empty-class case forces one species and double-counts adjacent pairs.

`maxFreeConfig` is an executable maximizing board. The phase pattern consists
of `N E empty` and `E empty` blocks; the coprime branch selects a larger
alternating pure-species board. `thinConfig` deletes a row-major occupied
suffix, so `freeWith WIDTH HEIGHT hw n` has exactly n cars whenever
`n≤freeMax`. Every component has an independent exact-count and StaticFree
proof. No upper-bound theorem is used to justify the constructor's count.

`exists_staticFree_with_count_iff`, `exists_perpetual_allMove_with_count_iff`,
and `exists_eventual_allMove_with_count_iff` give the same interval of
attainable populations. The eventual statement uses car-count conservation;
it does not establish convergence for arbitrary boards below capacity.
Singleton axes and the empty 1×1 maximum are included. The square corollaries
prove capacity `L*floor(2*L/3)` and exact two-thirds density iff `3∣L`.

`free_max_export --max-side 12` exports all 3,334 exact-count constructions
on 144 rectangles, with 146,348 transitions through their full lcm windows.
`scripts/check_free_max.py` checks the actual Lean formula, board and species
counts, static decision, both phase snapshots and movement counts, closure,
and complete coverage against independent scalar updates. Twenty-two
rejection controls exercise corrupted output. `FreeMaxAudit.lean` audits the
exporter separately from the universal theorems required by `Audit.lean`.
These are finite implementation checks; all-size optimality comes from Lean.

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

`Audit.lean` traverses the imported CLASSIC `BML` declarations, the G1 exporter,
and its global entry point, checking their transitive axiom dependencies.
`G2Audit.lean`, `CosetAudit.lean`, and `FreeFlowAudit.lean` separately check
their exporters and global entry points; the G2, B2, and B3 mathematical
theorems are required by the main BML audit. Each audit requires the named
mathematical results to be theorem declarations and rejects
any axiom outside Lean's usual `propext`, `Quot.sound`, and `Classical.choice`.
Thus incomplete proofs and native decision-result axioms fail the audit.
Concrete witness proofs use kernel-reduced `decide`, and the infinite-time
claims use induction.

The CLASSIC replay executable provides finite comparison evidence against the Python
and Quint implementations. Such comparisons are not an all-size source
refinement proof. The numerical counting identities and conservation have
general Lean proofs; unrestricted encoding correctness and cross-language
source correspondence remain separate obligations.

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
The unguarded queue's probability and logarithmic lower bound on permanent
full-movement settling are prose results
in the [relaxation note](../../docs/research/2026-11-18-relaxation-obstructions.md),
not Lean probability theorems.

`BML/GuardedQueue.lean` separately provides a local obstruction to early
gridlock. Its `GuardedEastQueue` predicate specifies `T+1` east cars in the
main row, an empty site immediately ahead, and `T` east cars in the preceding
north row at offsets `1,...,T`. The guard is empty when `T=0`.
`GuardedEastQueue.step` proves that a full CLASSIC round shortens both runs
and advances the hole one site toward the rear. A guard car may itself move
east: the proof needs only that the east phase cannot turn it into a north
car, so it cannot fill the newly vacated main site in the following phase.

`GuardedEastQueue.rear_first_move` states that the original tag's `carTrace`
equals its initial coordinate at every time `t <= T`, equals its east
successor at time `T+1`, and that this successor is a different coordinate.
`GuardedEastQueue.jam_after` proves `T < U` whenever a nonempty jam occurs at
time `U`. The public torus declarations
`torus_guardedEastQueue_first_move`, `torus_guardedEastQueue_jam_after`, and
`torus_guardedEastQueue_no_jam_through` use only positive dimensions and the
supplied pattern; they impose no condition on the exterior. For the iid
application, `H >= 2` and `T+2 <= W` ensure that the prescribed sites are
distinct. The pattern probability, cyclic-window avoidance bound, and
logarithmic lower bound on gridlock time are separate prose results.

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

## B7. CLASSIC sparse speed one

`BML/SparseDynamics.lean` proves the corrected diagonal dynamics using
`phaseIndex_east`, `phaseIndex_north`, and the CLASSIC `roundTransport`.
Release is checked with north eligibility on the east intermediate. A pair
of corrected vacancies at the end of a finite prefix persists backwards
through that prefix. Conservation and `2 * carCount < gcd(w,h)` supply a
pair at the end of every prefix.

`BML/SparseSpeed.lean` proves `low_density_tag_block_bound`,
`low_density_block_bound`, and `low_density_speed_one`. These bound each
original tag's block count by `g−2`, the number of blocked rounds by
`carCount * (g−2)`, and give eventual `AllMove` for the actual torus orbit.

`low_density_speed_one_deadline` strengthens the time conclusion: under
the same strict hypothesis, every round at or after
`sparseSpeedDeadline w h s = lcm(w,h) * carCount * (g−2)` has `AllMove`.
`low_density_staticFree_deadline` proves entry into `StaticFree` by that
deadline. The reusable `staticFree_of_blockedRoundCount_bound` accepts any
uniform finite-prefix blockage budget, without a sparsity hypothesis.
This combines the finite blockage budget with
`lemmaR_finite_lt`: `K+1` disjoint windows of length `lcm(w,h)` cannot
all contain a blockage when every prefix has at most `K` blocked rounds.
The empty board has deadline zero; a nonempty sparse board has `g ≥ 3`.
The deadline is a sufficient upper bound, with no sharpness claim.
`low_density_square_speed_one_deadline` specializes it to `n * m * (n−2)`
on an `n×n` square with `2m < n`.

The BML audit checks these public theorem declarations. The separate replay
compares both CLASSIC phases and original-tag traces with an independent
scalar implementation. Its header exports the proved deadline formula for
sparse boards and `-` outside the strict hypothesis. Complete recurrent
traces check permanent-flow entry by the deadline. A targeted `5×10`
two-car orbit first becomes permanently free at round 10 despite having
bad-round budget 6, distinguishing the two quantities.
Run `python scripts/check_sparse_speed.py` from the
repository root after `lake build`.

## Remaining obligations

The deterministic G0, G1, G2, B7, Lemma R, and Theorem F statements now have
kernel-checked proofs, with their nonempty/empty conventions and exact
population scopes recorded above. Further obligations include:

- Formalize eventual periodicity/classifier correctness and unrestricted
  Python-to-Lean source correspondence.
- Construct `RouteCover` witnesses directly from a mixed occupied blocker cycle
  without a separate no-full-lane hypothesis, and connect the Python certificate
  verifier to those Lean witnesses. The new closed-core theorem already covers
  every nonempty core in the absence of full monochromatic lanes.

No probabilistic critical density, asymptotic typical-case theorem, or
quasicrystal spectral statement is asserted by this layer.
