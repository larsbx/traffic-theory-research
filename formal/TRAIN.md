# TRAIN: movement semantics and the complete rectangular jam threshold

The `BML.Train` Lean namespace and `Train.qnt` Quint model implement the
repository's **TRAIN** rule: during a species' half-step, a queue moves into a
hole together, and a full ring of that species rotates. Both phases read their
complete input state; an east half-step is followed by a north half-step.
This is a separate update rule from the **CLASSIC** `BML` and `Traffic` suites.

The full rectangular existence theorem is kernel-checked in Lean. The
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

These are finite tests and comparisons. No Apalache verification, unrestricted
Lean–Quint/Python refinement, or individual-car identity replay is claimed for
this TRAIN suite. The CLASSIC suites retain their own separate evidence
domains. A configured acceptance domain describes what a run must check;
the source-bound receipt for the revision under review records whether that
run actually passed.

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

Austin–Benjamini's eventual-speed-one result below N/2, its proposed transfer
to CLASSIC, sharp random-density thresholds, and loop-formation probability
bounds remain outside this formalization. The CLASSIC G1/G2/R/F obligations
listed in [the shared register](README.md) are unchanged. Real projection,
Fibonacci frequency limits, and diffraction likewise remain outside the
TRAIN proof layer.
