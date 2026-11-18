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
| `BML/Capture.lean` | Successor-closed occupied cores persist. A supplied occupied closed walk yields a core (distinct sites are not required by this Lean declaration). Full-round tagged transport is bijective. Explicit core obstacles on every row and column give a kernel-derived cyclic-distance rank, a bound `M = n_E*(W-1) + n_N*(H-1)` on every finite prefix of tagged moves, and a nonempty jam by full round M. |
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
| `BML/Lanes.lean` | An east-only mixed row or north-only mixed column preserves a car and a hole under each actual full step; cyclic reachability supplies a mover at every iterate, supporting G2. The absent species phase is the identity. Numerical species, east-row, and north-column counts are conserved through both phases and iterates. Full E-rows and full N-columns persist and reflect backward, cannot coexist, and have no hidden movement. Specified north-free columns, cyclic strips, and row-count bounds are invariant through every iterate. |
| `BML/NonGridlock.lean` | Total executable `nonGridlockWith` has exactly n cars and never jams for every n<WIDTH*HEIGHT. Its column-major east prefix has a mixed first or last row when WIDTH≥2; width-one boards use a north prefix. The zero population remains empty and is not Jam. This completes G2. |
| `BML/GridlockThresholds.lean` | Actual car count equals area iff every cell is occupied. On every positive torus and for every feasible n≤WIDTH*HEIGHT, every n-car configuration eventually jams iff n=WIDTH*HEIGHT. |
| `BML/Arithmetic.lean` | Divisibility of positive winding lengths implies the `min(WIDTH, HEIGHT)` lower bound. The proposed class packing expression simplifies to `floor(2*g/3)` and attains exact `2/3` iff `3` divides `g`. These are arithmetic components of G1 and F. |
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
alone does not characterize a traffic orbit as free. The rigid-motion bridge,
the two implications of R, and the packing/constructions in F remain open.

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

The mixed-winding argument that constructs these row/column witnesses remains
a prose proof with Python certificate checks. The universal Lean capture result
begins at the explicit `RouteCover` witnesses. This is a formalization of the
blocking/capture mechanism already used in Angel–Holroyd–Martin's torus proof,
with an explicit integer movement bound, not a novelty claim.

`Lanes.lean` uses the finite-list cardinality helpers in `Train/Counting.lean`.
Those helpers import only `BML.Torus` and assume no TRAIN movement semantics;
the new conservation proofs use CLASSIC `transport` and `halfStep`. The
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

## Audit and trust boundary

`Audit.lean` traverses the imported CLASSIC `BML` declarations, the G1 exporter,
and its global entry point, checking their transitive axiom dependencies.
`G2Audit.lean` and `CosetAudit.lean` separately check their exporters and global
entry points; the G2 and B2 mathematical theorems are required by the main BML
audit. Each audit
requires the named mathematical results to be theorem declarations and rejects
any axiom outside Lean's usual `propext`, `Quot.sound`, and `Classical.choice`.
Thus incomplete proofs and native decision-result axioms fail the audit.
Concrete witness proofs use kernel-reduced `decide`, and the infinite-time
claims use induction.

The CLASSIC replay executable provides finite comparison evidence against the Python
and Quint implementations. Such comparisons are not an all-size source
refinement proof. The numerical counting identities and conservation have
general Lean proofs; unrestricted encoding correctness and cross-language
source correspondence remain separate obligations.

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

- Use the proved coset identity and bounded witness times to establish rigid
  traffic evolution and both directions of Lemma R.
- Connect Lemma R to the cyclic class packing upper bound and all densest
  constructions in F.
- Formalize eventual periodicity/classifier correctness and unrestricted
  Python-to-Lean source correspondence.
- Construct `RouteCover` witnesses from a mixed occupied blocker cycle's winding,
  and connect the Python certificate verifier to those Lean witnesses.

No probabilistic critical density, asymptotic typical-case theorem, or
quasicrystal spectral statement is asserted by this layer.
