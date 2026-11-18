# TRAIN: jam thresholds and eventual speed one

The `BML.Train` Lean namespace and `Train.qnt` Quint model implement the
repository's **TRAIN** rule: during a species' half-step, a queue moves into a
hole together, and a full ring of that species rotates. Both phases read their
complete input state; an east half-step is followed by a north half-step.
This is a separate update rule from the **CLASSIC** `BML` and `Traffic` suites.

The full rectangular jam-existence theorem and sparse-square eventual-speed-one
theorem are kernel-checked in Lean. The
cross-language checks below validate actual implementations on finite domains;
they do not establish unrestricted source refinement or a global Quint proof.

## Theorem T: every possible jam population

For every positive width W, height H, and natural number n,

\[
\bigl(\exists s:\; s\text{ is nonempty},\;
 \text{both successive TRAIN half-steps have zero movers},\;
 |s|=n\bigr)
\quad\Longleftrightarrow\quad
W+H\le n\le WH.
\]

The theorem is
[`BML.Train.noMoves_population_iff`](lean/Train/Threshold.lean).
`jam_population_iff` states the result for W,H at least two using `Jam`;
`jam_population_iff_positive` covers all positive dimensions. `Jam` means
nonempty and `Stuck`, where neither species can move in the original state.
`noMoves_iff_stuck` proves that this equals zero movement in the two successive
half-steps. `population` counts occupied coordinates and is proved equal to
the sum of the executable east and north species counts.

If either dimension is one, the numerical interval is empty and
`no_jam_singleton` proves that no nonempty jam exists. The empty board has no
movers but is excluded from `Jam`. Every TRAIN jam persists under every finite
iterate of the actual step function.

This is an **existence** threshold for zero-movement states. It does not say
that every state above the threshold eventually jams, or that every state
below it eventually reaches speed one. No critical-density or random-initial-
condition probability claim follows from this theorem.

### Lower bound

A stopped north car must encounter an east car in its column: a queue ending
at a hole moves, and a full north ring also moves. The corresponding statement
holds for an east car and a north blocker in its row. Hence every occupied
column contains an east car. An east car's occupied target forces the next
column to be occupied, so finite cyclic propagation gives an east car in every
column. The symmetric argument gives a north car in every row.

Choosing one east car from each column and one north car from each row gives
W+H distinct cars. The Lean proof makes those choices into disjoint, duplicate-
free lists and bounds their combined length by the occupied-coordinate count.
The upper bound n≤WH follows from filtering the complete coordinate list.
These arguments cover singleton dimensions as well as larger rectangles.

### Explicit construction for every population in the interval

For W,H≥2, put k=n−(W+H), with

\[
0\le k < (W-1)(H-1).
\]

Coordinates increase east and north and are reduced modulo W and H. The
executable function `stuckConfig W H k` assigns cells as follows:

| Coordinates | Cell |
| --- | --- |
| y=0 and x<W−1 | E |
| (x,y)=(W−1,H−1) | E |
| x=W−1 and y<H−1 | N |
| x<W−1 and 1≤y≤H−1, with j=x(H−1)+(H−1−y)≤k | N |
| All other coordinates | Empty |

At k=0 the occupied successor path has direction word

\[
E^{W-1}N^{H-1}EN,
\]

starting at (0,0), and winds once around each torus direction. Its final north
car is the interior position j=0. Increasing k adds the next interior north
cars in increasing j order. Each added car points to a previously occupied
cell, with top-row cars pointing around the wrap to an east car on the bottom
row.

The constructor has W east cars, H−1 north cars on the right column, and k+1
interior north cars: its population is W+H+k=n. Lean proves this using an
explicit duplicate-free enumeration, including an inverse between interior
indices and coordinates. Every directed target is occupied. Every row also
contains a north car and every column an east car, excluding homogeneous
rotating rings. `stuckConfig_jam` connects those facts to the actual TRAIN
movement predicate; `stuckConfig_population` proves the exact count. The
Python `bml.extremal.train_stuck_with` uses this same coordinate formula.

## Sparse squares: eventual speed one

**Formal status:** the complete theorem is kernel-checked in
[`Train/SpeedOne.lean`](lean/Train/SpeedOne.lean). It connects the cyclic
argument, actual TRAIN identity transport and release, and numeric full-speed
characterization. No diagonal-motion or release hypothesis remains assumed
in its public statement.

The theorem is Austin–Benjamini Proposition 1 for the repository's
TRAIN dynamics. On a positive N×N square, for every starting configuration s,

\[
2|s|<N
\quad\Longrightarrow\quad
\exists T\;\forall t\ge T:\quad
\operatorname{totalMoveCount}(\operatorname{torusStep}^{t}(s))=|s|.
\]

The public entry points are `BML.Train.sparse_square_eventually_fullSpeed`
and the explicit numerical statement
`BML.Train.sparse_square_moves_equal_population`. The strict hypothesis is
`2 * population s < N`, with no species-balance assumption. Time counts full
east-then-north cycles. `FullSpeed` means that the actual total number of
moves during one such cycle equals its population. The proved
`fullSpeed_iff_all_phases_move` identifies this numerical condition with every
east car moving in its phase and every north car moving in the following phase.
Population conservation makes the right-hand side the initial population.
The empty configuration is included and has zero moves out of zero cars.

This is eventual **full movement**, stronger than the absence of a jam. It
does not supply an effective upper bound on T, a positive random-density
transition, or a statement for every rectangular torus. The actual-kernel
bridge is specific to TRAIN; the proposed CLASSIC transfer remains unproved.

### Adjacent empty pairs and a permanent cut

The proof follows the corrected-diagonal idea of
[Austin–Benjamini, Proposition 1, pp. 2–3](https://arxiv.org/pdf/math/0607759v3),
with adjacent empty pairs replacing maximal empty arcs. Label the initial
cars and follow them through the proved transport maps. For car i define

\[
Y_t^i=x_t^i+y_t^i-t\pmod N.
\]

Every car moves at most once per full cycle. If it moves, its corrected class
stays fixed; otherwise the class decreases by one. A nonempty physical
diagonal followed by an empty diagonal releases at least one car: an east car
has a vacant target if any east car is present; otherwise the diagonal's north
cars have vacant targets that the east phase cannot fill.

At every time, fewer than N/2 labeled cars leave two adjacent corrected
classes empty. Indeed, if every class or its successor were occupied, the
occupied tags together with their predecessors would cover N classes using
at most twice the number of cars. Repeated tags only make that cover smaller.

An adjacent empty pair at time t+1 was already empty at t. A car in its old
second class would have to stay there or move into the first class, both
impossible. If the old first class were occupied, the now-known empty second
class would trigger release and keep the first class occupied at t+1, also
impossible. Thus the finite sets of empty pairs decrease with time. Since
none is empty, a finite-list argument supplies a pair present at every time.
Individual pairs may disappear; the proof does not assume every initial pair
persists.

Cut the cyclic order at one permanently empty class. Each car then has a
natural-number rank that stays unchanged when it moves physically and drops
by one when it is blocked. A decreasing sequence of natural numbers attains
its minimum, so each corrected trace eventually stays fixed. Taking a common
time for the finite list of cars and using the movement equivalence yields
full speed. No eventual-periodicity assumption or bounded simulation is used
in this proof.

The square hypothesis cannot simply be replaced by `2m < min(W,H)`. On a 5×7
torus, one east and one north car satisfy that inequality but cannot both
move forever without interference: under hypothetical rigid motion, the
Chinese remainder theorem forces an east-target/north-position collision.
The formal theorem here makes no rectangular speed-one claim.

## Movement, occupancy, and invariants

A TRAIN move is counted even when another same-species car fills its source
during the same half-step. In particular, a full east ring rotates and its
unlabeled occupancy can remain unchanged. The Lean layer proves an explicit
fixed-occupancy state with moving cars. It therefore never uses occupancy
equality as a substitute for zero movement.

The kernel proves source/destination behavior, preservation of the other
species, and a bijection transporting the active species' cars through a
half-step. Numeric conservation then proves that the executable species counts
and occupied population remain unchanged through half-steps and all full-step
iterates. The movement counter counts `CanMove` at every coordinate, including
full-ring movers; zero total move count is equivalent to `Stuck`.

On a positive finite torus, Lean proves the exact characterization

\[
\text{TRAIN Stuck}
\quad\Longleftrightarrow\quad
\text{CLASSIC directed targets are occupied}
\;\land\;\text{no full E row}
\;\land\;\text{no full N column}.
\]

The `Traffic` suite's 21 Wang tile types encode the directed-target condition.
That condition alone is insufficient for a TRAIN jam, since it permits
homogeneous moving rings. There is no claimed TRAIN Wang encoding, or an
unbounded identification between the separate `Traffic` and `BML.Train`
libraries.

## Lean coverage

| Module | Kernel-checked scope |
| --- | --- |
| [Train/Kernel.lean](lean/Train/Kernel.lean) | Executable queue propagation and full-ring movement on cyclic directions; equivalence of the bounded queue scan and literal backward-propagated movement mask plus ring movement; local movement recurrence; car transport bijections; opposite blockers for stopped cars; `NoMoves`/`Stuck` equivalence and jam persistence. |
| [Train/Torus.lean](lean/Train/Torus.lean) | Positive finite cyclic coordinates, cyclic iteration formulas and period closure, row/column ring characterizations, and TRAIN stuck iff CLASSIC blocking plus absence of homogeneous rings. |
| [Train/Counting.lean](lean/Train/Counting.lean) and [Train/Finite.lean](lean/Train/Finite.lean) | Complete duplicate-free finite enumeration, filtered counts, bijective counting, population bounds, and finite cyclic propagation. |
| [Train/Conservation.lean](lean/Train/Conservation.lean) | Executable numeric species/population conservation, movement-count characterization, and fixed occupancy with positive movement. |
| [Train/Threshold.lean](lean/Train/Threshold.lean) | The W+H lower bound, explicit all-count construction, full Theorem T, and singleton impossibility, all linked to actual TRAIN semantics. |
| [Train/FreeFlow.lean](lean/Train/FreeFlow.lean) | Move-count bounds; maximal numerical movement iff every active car moves in both successive phases; eventual full speed iff eventual move counts equal the initial population. |
| [Train/Diagonals.lean](lean/Train/Diagonals.lean) | Sparse cyclic label lists have adjacent empty pairs; backward heredity gives a permanent pair; cut ranks give eventual stability and a common time for all labels. This abstract theorem is compiled. |
| [Train/DiagonalDynamics.lean](lean/Train/DiagonalDynamics.lean) | Identity transport through full cycles; injective traces covering every current car; corrected diagonal changes exactly according to actual movement; release of a car before an empty diagonal, including the north phase after east movement. |
| [Train/SpeedOne.lean](lean/Train/SpeedOne.lean) | Full movement iff every occupied car moves; the complete square theorem `2 * population s < N` implies eventual full speed, including empty states; eventual actual move counts equal the initial population. |
| [Train/Export.lean](lean/Train/Export.lean) | Executable `stuckCheck` iff semantic `Stuck`; the replay and constructor exporters call the proved kernel and its movement counters directly. The cross-language agreement is checked separately on the finite domains below. |

The shared package pins Lean 4.34.1 and uses its standard library without
Mathlib. `TrainAudit.lean` checks the compiled TRAIN declarations and required
public theorem inventory. The permitted axioms are the standard `propext`,
`Quot.sound`, and `Classical.choice`; admitted proofs, new axioms, and
`native_decide` certificates are not permitted. Declaration totals include
generated helpers and are not counts of independent mathematical results.

## Finite executable evidence

The TRAIN Quint suite has 19 pure tests and five stateful tests. The stateful
model starts from an arbitrary 3×2 board and either half-step phase. The
standalone checker evaluates the actual Quint TypeScript interpreter and
compares its outputs with Python's TRAIN implementation.

| Check | Explicit finite domain |
| --- | --- |
| Three-way complete small-board TRAIN replay | Lean, Quint, and Python: 3,720 boards over all 14 ordered positive rectangles with WH≤6. |
| Three-way larger movement controls | Lean, Quint, and Python: 74 targeted boards on 7×1, 1×7, 8×2, 2×8, 3×3, 4×3, 3×4, and 4×4. |
| Three-way constructor comparison | Lean, Quint, and Python: all 96 admissible all-count constructors with 2≤W,H≤8 and WH≤16. |
| Lean/Python all-count constructor comparison | 784 constructors: every n in W+H…WH for every 2≤W,H≤8. The 96-board Quint domain is a subset. |

Every standard replay row has ten fields: width, height, input code,
independent east and north half-step codes, east-then-north full-step code,
independent east and north move counts, north move count after the east phase,
and the stuck flag. The gate compares every field, checks enumeration order
and completeness, and separately checks species counts and actual zero
movement. Constructor rows also carry requested and actual populations. The
784-board Lean/Python constructor comparison has been executed successfully;
the complete source-bound gate records all domains together for each revision.

Internal checks inspect legal intermediate boards, species and vacancy counts,
mover sources and targets, count bounds, zero-movement/blocker equivalence,
stuck persistence, the W+H lower bound, and singleton exclusion on the
evaluated inputs. Five actual mutated specifications must be rejected:
CLASSIC movement, missing full-ring movement, truncated queue propagation,
reversed phase order, and illegal cell digits. The last control preserves the
serialized observables and is rejected by the internal state invariant.

These are finite tests and comparisons. No Apalache verification or unrestricted
Lean–Quint/Python refinement is claimed. The finite TRAIN replay compares
unlabeled boards and counts; the Lean transport and trace theorems establish
identity coverage separately. The CLASSIC suites retain their own evidence
domains. A configured acceptance domain describes what a run must check;
the source-bound receipt for the revision under review records whether that
run actually passed.

### Eventual-speed-one acceptance

[`train_flow_check.py`](quint/train_flow_check.py) evaluates **all 1,305** states
with `2 * population < N` on squares N=1,…,5. It generates these sparse boards
directly and verifies that their actual TRAIN successors stay in the enumerated
domain. Its closed functional graphs come from actual Quint output, checked
against Python. Every terminal-cycle edge must move all cars; merely ruling
out zero-movement jams is insufficient. The shared `scripts/check_train.py`
gate also requires Lean agreement on every exported field and every targeted
orbit edge.

| N | Enumerated sparse states | Terminal cycles | Largest transient before a cycle |
| --- | ---: | ---: | ---: |
| 1 | 1 | 1 | 0 |
| 2 | 1 | 1 | 0 |
| 3 | 19 | 7 | 0 |
| 4 | 33 | 9 | 0 |
| 5 | 1,251 | 206 | 5 |
| **Total states** | **1,305** | | |

Every terminal cycle in these square domains has full actual movement. These
finite transient values are observations on the stated graphs, not a general
stabilization-time bound.

Eight explicit orbit certificates add 53 checked transition rows. The first
three extend the positive sparse-square examples beyond N=5; the others test
phase order, the strict population boundary, rectangular scope, and the
difference between fixed occupancy and movement. Some rows overlap the
exhaustive domains; 53 is a certificate-row count, not a count of additional
distinct states.

| Case | W×H | Initial code | Transient | Period | Rows | Eventually full movement |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| Delayed pair | 6×6 | 7 | 1 | 6 | 7 | Yes |
| Blocked train | 7×7 | 22 | 1 | 7 | 8 | Yes |
| Wrapped train | 8×8 | 2,194 | 1 | 8 | 9 | Yes |
| North reads the east result | 5×5 | 20,920,706,407 | 1 | 5 | 6 | Yes |
| Equality-boundary empty pair | 4×4 | 3,720,087 | 1 | 4 | 5 | Yes |
| Rectangular counterexample | 5×7 | 7 | 1 | 15 | 16 | No |
| Fixed-occupancy jam | 2×2 | 52 | 0 | 1 | 1 | No |
| Rotating singleton ring | 1×1 | 1 | 0 | 1 | 1 | Yes |

The 5×7 counterexample has two cars and satisfies `2m < min(W,H)`, but its
terminal cycle has 29 moves in 30 car-step opportunities, giving velocity
29/30. The orbit certificate checks the return to code 1,459 after 15 steps;
it does not infer recurrence from a simulation cutoff.

The flow layer adds ten named Quint tests and six adversarial controls to the
existing TRAIN acceptance. The controls reject a half-step diagonal clock,
using the independent north count for a complete cycle, treating fixed
occupancy as full movement, extending the square claim to the 5×7 example,
truncated orbit closure, and incomplete enumeration. The clock control runs
an altered Quint specification; the others exercise the certificate and
comparison checks. These are bounded tests, distinct from the all-N Lean
theorem. Source-bound receipts record the exact commands and results for the
revision being reviewed.

## Reproduce and review

From the repository root, install the pinned dependencies, then run the TRAIN
acceptance gate:

```sh
python -m pip install -r requirements-dev.txt
npm ci --ignore-scripts --prefix formal/quint
python3 scripts/check_train.py --report .artifacts/train-acceptance.json
```

The component commands are:

```sh
cd formal/lean
lake build Train train_replay
lake env lean TrainAudit.lean
cd ../..
npm --prefix formal/quint run typecheck:train
npm --prefix formal/quint run test:train
python3 formal/quint/train_check.py --max-cells 6 --rows .artifacts/train-quint.tsv --report .artifacts/train-quint-replay.json
python3 formal/quint/train_flow_check.py --rows .artifacts/train-flow-quint.tsv --report .artifacts/train-flow-quint.json
```

Put the pinned Lake executable on `PATH`, or set `TRAIN_LAKE` to that executable.
The gate verifies Lean and Quint versions and rejects a source change during
the run.

See [train-coverage.json](train-coverage.json) for the required inventory and
the [TRAIN workflow](../.github/workflows/train.yml) for hosted acceptance.
Reports record tool versions, source hashes, enumerated domains, and run
results. Workflow presence is not evidence that a particular revision passed.
The CLASSIC `Audit.lean` and `TrafficAudit.lean` remain independent audits.

## Sources and remaining boundaries

Austin and Benjamini's written movement rule and Proposition 6 give the square
threshold 2N. The W+H statement here extends their lower-bound argument to
rectangles and supplies a fully checked construction at every allowed count.
This repository does not claim novelty for that extension. See
[Austin–Benjamini, arXiv:math/0607759v3](https://arxiv.org/pdf/math/0607759v3)
and the [rule comparison and proof](../docs/theorems.md#5b-the-train-rule-austinbenjamini-prop-6-on-rectangles).
The separate CLASSIC rule is Model I of
[Biham–Middleton–Levine (1992)](https://arxiv.org/pdf/cond-mat/9206001).

Austin–Benjamini's Proposition 1 is the source of the square speed-one theorem
above; the adjacent-empty-pair proof is a formalization of its corrected-diagonal
argument, with no novelty claim. The proposed transfer to CLASSIC, effective
stabilization-time bounds, sharp random-density thresholds, and loop-formation
probability bounds remain outside this formalization. The separate CLASSIC library proves
complete G1/G2 and the forced-gridlock boundary among feasible populations:
every n-car configuration eventually jams exactly when n=WH, assuming n≤WH.
That forced boundary does not transfer to TRAIN: a fully east-filled TRAIN
board has rotating rings. CLASSIC G2 establishes never reaching a nonempty
jam for its sub-full constructions, without asserting eventual speed one.
The remaining CLASSIC R/F obligations are listed in
[the shared register](README.md). The CLASSIC B2 coset identity is proved for
the auxiliary `(1,-1)` action on actual cyclic coordinates, including signed
and bounded forward witnesses. It does not by itself prove the CLASSIC
rigid-orbit/free-flow characterization or transfer the TRAIN speed-one theorem.
Real projection,
Fibonacci frequency limits, and diffraction likewise remain outside the
TRAIN proof layer.
