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
| `BML/Transport.lean` | Explicit bijection between each species' cars before and after its phase: survival, injectivity, and surjectivity. Nonemptiness is preserved by a full step and every iterate. |
| `BML/Capture.lean` | Successor-closed occupied cores persist. A supplied occupied closed walk yields a core (distinct sites are not required by this Lean declaration). Full-round tagged transport is bijective. Explicit core obstacles on every row and column give a kernel-derived cyclic-distance rank, a bound `M = n_E*(W-1) + n_N*(H-1)` on every finite prefix of tagged moves, and a nonempty jam by full round M. |
| `BML/Torus.lean` | Positive finite cyclic coordinates with proved inverse shifts; the general kernel is instantiated on `Fin WIDTH × Fin HEIGHT`; executable base-three encoding, decoding, and counts. |
| `BML/Counting.lean` | The position enumeration is complete and has no duplicates. Filtered species lists agree with the executable `speciesCount` sums; the occupied-list length is their sum. Transport induces a list permutation, proving numerical species conservation under every half-step, and total-count conservation under every full-step iterate. |
| `BML/Enumeration.lean` | Explicit row-major and reverse row/column bijections, with quotient/remainder inverses. A configuration occupying exactly a prefix of n ranks has actual car count n. |
| `BML/AllCounts.lean` | Total executable `gridlockWith` constructs a CLASSIC jam at every exact population `min(WIDTH, HEIGHT) ≤ n ≤ WIDTH*HEIGHT`. Frozen-state and exact-count proofs cover both orientations, partial final lines, and singleton dimensions. |
| `BML/FiniteCycle.lean` | Every endofunction on a nonempty finite closed carrier has a positive simple cycle bounded by the carrier's length. The proof uses pigeonhole reasoning and a minimal positive return time. |
| `BML/Blocking.lean` | A frozen state's blocker map preserves occupancy. An actual blocker walk lifts to nonnegative east/north displacements and seam-crossing counts. Closure implies divisibility by the torus side lengths, hence the shorter-side lower bound. |
| `BML/Extremal.lean` | Full east rows and full north columns are nonempty frozen states with exactly WIDTH and HEIGHT cars. Choosing the shorter line attains `min(WIDTH, HEIGHT)`. |
| `BML/Gridlock.lean` | Every jam has a simple occupied blocker cycle of length between `min(WIDTH, HEIGHT)` and its actual car count. Combining this with the all-count constructor proves the full G1 iff, both for already-jammed states and the existence of orbits reaching a jam. Fewer cars never reach a jam at any iterate. |
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

`g1_export --max-side 12` evaluates the actual Lean constructor at all 5,578
admissible counts on the 144 positive rectangles within those side bounds.
Its TSV columns are width, height, requested count, actual count, east count,
north count, and row-major cell digits. `scripts/check_g1_constructions.py`
checks complete coverage, valid digits, all counts, and zero movement under
both actual Python CLASSIC phases. It does not compare this constructor's
array with the differently ordered Python `gridlock_with` construction.

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

## Audit and trust boundary

`Audit.lean` traverses the imported CLASSIC `BML` declarations, the G1 exporter,
and its global entry point, checking their transitive axiom dependencies. It
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

- Formalize the G2 non-gridlocking configurations for every sub-full car count.
- Prove the subgroup/coset assertion and both directions of rigidity Lemma R.
- Connect Lemma R to the cyclic class packing upper bound and all densest
  constructions in F.
- Formalize eventual periodicity/classifier correctness and unrestricted
  Python-to-Lean source correspondence.
- Construct `RouteCover` witnesses from a mixed occupied blocker cycle's winding,
  and connect the Python certificate verifier to those Lean witnesses.

No probabilistic critical density, asymptotic typical-case theorem, or
quasicrystal spectral statement is asserted by this layer.
