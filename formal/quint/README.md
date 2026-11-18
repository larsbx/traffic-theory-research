# Executable Quint BML models

This directory contains three separately scoped suites using the same pinned
Quint 0.33.1 interpreter and simultaneous finite-torus half-steps.
`BML.qnt` provides the CLASSIC east-then-north replay against the NumPy kernel.
`traffic.qnt` provides explicit half-step phases and the 21-tile Wang encoding,
with a separate CLASSIC replay against Lean. `Train.qnt` implements TRAIN
queue movement and full-ring rotation. The distinct filenames also work on
filesystems that do not distinguish upper and lower case.

| Suite | Entry points | Deterministic coverage |
|---|---|---|
| Finite BML replay | `BML.qnt`, `check.py`, `evaluate.py` | Ten Quint tests; every state of all 14 ordered positive rectangles with at most six cells, plus three `4x2` witness rows; three executed mutation controls. |
| Phase and Wang layer | `traffic.qnt`, `bml_tests.qnt`, `bml_model.qnt`, `bml_export.qnt`, `export.cjs` | 25 pure tests and four state-transition tests; 1,560 boards on six tori, with both phases for 3,120 half-step cases. |
| TRAIN movement | `Train.qnt`, `train_tests.qnt`, `train_model.qnt`, `train_check.py`, `train_evaluate.py` | 19 pure tests and five stateful tests; 3,720 boards on 14 rectangles, 74 larger targeted boards, 96 constructor boards, and five executed mutation controls. |

All acceptance commands use Quint's TypeScript backend. No Rust backend
download or Apalache installation is needed.

## Reproduce

From the repository root, with Node.js, Python, and the repository's Python
dependencies installed:

```sh
npm ci --ignore-scripts --prefix formal/quint
npm run typecheck --prefix formal/quint
npm test --prefix formal/quint
python formal/quint/check.py --max-cells 6
```

The `typecheck` command checks the two CLASSIC suites. `npm test` runs the 25 pure and four
state-transition tests for the phase and Wang layer. `check.py` parses and
typechecks `BML.qnt`, runs its ten deterministic tests, and then performs the
NumPy replay and mutation controls. To run only those ten tests:

```sh
npm run test:replay-model --prefix formal/quint
```

The optional commands below extend the replay bound or run seeded simulation:

```sh
python formal/quint/check.py --max-cells 9
npm run simulate --prefix formal/quint
```

The package and lockfile pin `@informalsystems/quint` to `0.33.1`.
TRAIN has separate `typecheck:train` and `test:train` commands, documented
below. See [the formal register](../README.md) for the separate acceptance gates.

## Shared conventions

- A board is a list of cell codes: 0 vacant, 1 eastbound, 2 northbound.
- Cell `(x,y)` has index `x + width*y`; y increases northward.
- The cell at index i contributes `cell * 3^i` to the board's ternary code.
- East and north each move synchronously. Every eligibility decision reads the
  input board of that half-step. CLASSIC requires an initially vacant target;
  TRAIN also moves queues together and rotates homogeneous rings.
- Dimensions are positive. In the CLASSIC suites a car whose target is its own
  cell is blocked. TRAIN counts that car as moving around its singleton ring.
- `BML.qnt` and `Train.qnt` apply east first, then north. `traffic.qnt` accepts
  phase 1 for east or phase 2 for north and can start in either phase.
- The stateful `bml_model.qnt` toggles phase after every half-step, including an
  unchanged board. Its 3x2 initialization nondeterministically chooses any of
  the 729 boards and either initial phase; subsequent steps are deterministic.
- The pure functions require legal cell codes and correctly sized boards;
  the phase layer also requires phase 1 or 2. The stateful model validates
  those conditions at initialization.

## Finite BML replay against NumPy

`check.py --max-cells 6` compares the actual Quint model with the NumPy kernel
for **every state of every ordered positive rectangle** within the declared
area bound: 3,720 states across 14 rectangles. It checks the east intermediate
state, final state, and each phase's move count. It also checks species
conservation and the equivalence of a fixed point, local blocking, and zero
moves on those states.

For **every** replayed state the Quint interpreter itself evaluates `invariant`,
including alphabet/length validity of the actual intermediate and final lists,
species conservation, movement bounds, fixed-point/blocking/zero-move
equivalence, and full-occupancy blocking. An extra flag is validated by the
adapter and then removed from its public CSV output. This matters because
base-three encoding is not injective on lists with invalid digits.

Three extra rows cover a `4x2` nonmonotonicity witness (`3858`, `3860`, `4340`).
Quint checks the occupancy orbit; individual-car identity claims are established
separately by the Lean transport proof and independent labeled Python checker.
Actual modified Quint models with reversed phases and with an asynchronous
phase must be rejected by the same correspondence comparator. These mutation
controls demonstrate that phase-order and simultaneous-update defects are
observable by the gate.

A third modified Quint model preserves the five encoded result fields while
introducing illegal digits (`[1,1]`, `[4,0]`, and `[7,-1]` all encode as `4`).
The invariant flag must reject this model before its output is accepted.

### Blocking-core capture controls

The three added deterministic controls check a successor-closed occupied core,
its preservation through both phases, and capture by the explicit movement
budget. On the 3×3 witness `5738`, the six-site core winds in both directions;
two further car moves lead to a jam after two full rounds (the general budget
is 16). A full east row with a circulating car on another row is a negative
control for treating every permanent core as a global capture certificate.
Invalid core indices, an empty core, and a broken successor chain are rejected.

`captureCheck` executes the actual `transition` for at most the stated budget;
these are bounded controls. The universal theorem from explicit core obstacles
on all rows and columns is proved separately in `BML/Capture.lean`.

### Replay interface

```sh
python formal/quint/evaluate.py 2 3
python formal/quint/evaluate.py 4 2 --indices 3858 3860 4340
```

Each output line is CSV without a header:

```text
index,east_state,next_state,east_moves,north_moves
```

The Python adapter contains no traffic dynamics. It sends expressions to the
actual Quint interpreter and validates every returned row. Full enumeration
through the CLI is capped at nine cells; explicit state indices can use tori
up to sixteen cells. `evaluate_rows` provides the same protocol as an importable
Python function.

## Phase and Wang layer

The deterministic suite contains 25 pure tests and four state-transition tests.
The repository acceptance gate checks the actual passed-test names in Quint's
JSON output against `formal/coverage.json`, and rejects failed or ignored tests.
Six tests enumerate every board on the 1x1, 1x2, 2x1, 2x2, 3x2, and 2x3 tori:
1,560 boards and both phases, or 3,120 half-step cases.

For each enumerated board the suite checks validity, ternary-code round trip,
tile decoding, frozen/valid-matching equivalence, absence of eligible moves in
both phases, species counts, half-step fixed points, frozen permanence, and
full-cycle fixed points. These are exhaustive checks over the stated finite
domains, executed as universal predicates by Quint.

Named controls cover wraparound in both directions, inactive species, a blocked
queue whose front car moves, rejection of sequential cascade behavior, occupied
destinations, truncated blocking paths, a quiet half-step that is not gridlock,
phase order, the 21 allowed Wang types, forbidden tiles, and mismatched edges.
Stateful tests check both phases and phase toggles even for empty or fully
occupied boards.

The `simulate` command is an additional seeded check of 100 nondeterministic
initializations for at most 20 half-steps. It is not exhaustive.

### Half-step export against Lean

From the repository root:

```sh
mkdir -p .artifacts
node formal/quint/export.cjs > .artifacts/quint.tsv
```

The exporter runs Quint itself, then converts the resulting ITF integer rows to
TSV. It contains no independent implementation of BML transitions.
The table has no header. Each tab-separated row contains:

1. width
2. height
3. input board code
4. phase (1 or 2)
5. output board code after one half-step
6. next phase
7. frozen input flag (0 or 1)
8. valid matching flag for the encoded input tiles (0 or 1)
9. board code after tile encoding and decoding
10. number of allowed local Wang tile types (21)

Dimensions appear in the order listed above, then input code increases from
zero, with phase 1 before phase 2. The output has exactly 3,120 rows. This
ten-column TSV is distinct from the five-column full-cycle CSV replay protocol.

## TRAIN queue and ring movement

`Train.qnt` implements the queue propagation and full-ring rotation rule
separately from the two CLASSIC models. The named tests include moving queues,
opposite-species blockers, wraparound, full rings and singleton rings, long
propagation, independent movement counts, phase order, and occupancy fixed
points with positive movement. `train_model.qnt` initializes an arbitrary 3×2
board and either phase, then tests conservation and phase alternation through
both quiet and moving steps.

```sh
npm --prefix formal/quint run typecheck:train
npm --prefix formal/quint run test:train
python3 formal/quint/train_check.py --max-cells 6 --rows .artifacts/train-quint.tsv --report .artifacts/train-quint-replay.json
python3 scripts/check_train.py --report .artifacts/train-acceptance.json
```

The standalone checker compares Quint with Python TRAIN on all 3,720 boards
with WH≤6, 74 larger targeted boards, and 96 constructor boards with
2≤W,H≤8 and WH≤16. It requires all 24 named tests and rejects five actual
mutants: CLASSIC substitution, omitted ring movement, truncated queue
propagation, reversed phases, and illegal cell digits hidden by equal encoded
outputs. Its internal invariant inspects the actual lists before serialization.

The shared TRAIN gate adds Lean and checks all ten exported fields across the
three implementations on those domains. It also compares Lean and Python
constructors at every admissible count for all 2≤W,H≤8, a total of 784 boards.
The 96-board Quint constructor domain is a subset of that 784-board domain.
These scopes and source-bound receipts are separate from the universal Lean
threshold proof described in [TRAIN.md](../TRAIN.md).

### TRAIN replay protocol

```sh
python3 formal/quint/train_evaluate.py 2 3
```

The output is headerless ten-column TSV:

```text
width,height,input,east,north,full,eastMoves,northMoves,cycleNorthMoves,stuck
```

The north half-step and `northMoves` use the original board. The full step and
`cycleNorthMoves` use the east result. The stuck flag is one exactly when both
species have zero movers; it does not require a nonempty board. This protocol
differs from the phase/Wang TSV despite having the same number of fields.

No TRAIN Wang encoding, individual-car identity replay, unrestricted
cross-language refinement, or Apalache verification is claimed.

### Sparse-square eventual-speed acceptance

`train_flow_check.py` checks all 1,305 configurations with
`2 * population < N` on N×N squares, N=1,…,5. The state counts are 1, 1, 19,
33, and 1,251. Population conservation makes each finite domain closed under
TRAIN transitions. The checker analyzes every terminal cycle and requires
`eastMoves + cycleNorthMoves` to equal the population on every cycle edge.
Checking only that a terminal cycle is not a jam would not establish speed one.

```sh
python3 formal/quint/train_flow_check.py --rows .artifacts/train-flow-quint.tsv --report .artifacts/train-flow-quint.json
```

The standalone checker compares actual Quint transitions with Python and
requires ten additional tests from `train_flow_tests.qnt`, with none ignored.
The shared TRAIN gate also compares the Lean output. All terminal cycles in
the five square domains have full movement; their cycle counts are 1, 1, 7,
9, and 206, and their maximum transients are 0, 0, 0, 0, and 5.

Eight explicit orbit certificates contribute 53 transition rows: positive
sparse examples on 6×6, 7×7, and 8×8, and five boundary/phase controls. The 5×7
two-car counterexample has a 15-step terminal cycle with 29 moves in 30
car-step opportunities, so its mean velocity is 29/30 and it does not attain
speed one. The 4×4 equality-boundary example shows that an individual empty
pair can disappear, although empty pairs are backward hereditary. A 2×2 jam
and rotating 1×1 ring distinguish occupancy equality from actual movement.
The exact initial codes, cycle lengths, and overlaps are recorded in
[TRAIN.md](../TRAIN.md#eventual-speed-one-acceptance).

Six adversarial controls reject a half-step clock, the independent north
count used as a cycle count, fixed occupancy misclassified as full movement,
rectangular overreach, a truncated recurrence certificate, and incomplete
domain enumeration. The clock control evaluates an altered Quint file; the
remaining controls test certificate/comparison rejection. This is bounded
functional-graph evidence, separate from the complete all-size Lean theorem.

## Proof boundary

The pure definitions describe arbitrary positive dimensions, but the commands
above establish only finite executable checks in their stated scopes. The
deterministic tests use explicit finite quantification and fixed witnesses;
`--max-samples=1` does not make those tests a random search. No Apalache
verification or unbounded source-refinement theorem is claimed.

These Quint suites do not prove eventual classification for all configurations,
G1/G2/Theorem F, a critical density, high-density random gridlock, infinite
Fibonacci frequencies, trigonometric identities, or diffraction theorems.
The separate Lean libraries prove complete CLASSIC G1/G2, the forced-gridlock
boundary among feasible CLASSIC populations n≤WH, the B2 coordinate coset
identity, the actual-phase CLASSIC free-flow characterization R, and the rectangular TRAIN
zero-movement existence threshold and sparse-square speed-one theorem; the
Quint runs remain bounded evidence.
CLASSIC G2 constructs a board of each sub-full count that never reaches a
nonempty jam, without claiming eventual free flow. Full CLASSIC occupancy
forces a jam at time zero. The empty fixed state has no movers but is not a
nonempty jam, including on the 1×1 torus. In TRAIN, fixed occupancy can coexist
with moving cars, and the model's stuck predicate uses mover counts; the
CLASSIC forced-gridlock boundary does not transfer to that rule.

The separate `coset_export`/`scripts/check_cosets.py` gate compares Lean's
actual cyclic-coordinate action and phase classes with independent Python
modular arithmetic. It reconstructs coordinate cycles and checks same-class
and east-translated reachability on a finite domain; it does not invoke Quint
or evaluate traffic configurations. The universal B2 proof supplies signed
and bounded forward witnesses. The separate Lean proof of R connects these
to actual traffic orbits: static conditions are equivalent to full movement
from time zero, and checking the first lcm(W,H) rounds suffices. Such
configurations return after the lcm, possibly with a smaller least period.
Eventual entry into this static-free set is a separate question; no general
convergence statement is implied. The packing and maximizing constructions
of F remain unformalized.

The separate `freeflow_export`/`scripts/check_freeflow.py` gate evaluates
the actual Lean static and movement predicates and full traffic phase traces.
Its default domain is all 93,387 initial states on the 23 ordered positive
rectangles with WH≤9, covering 622,362 full transitions. NumPy and an
independent scalar orbit oracle check the phases and movement from time zero;
source-bound receipts record successful runs and rejection controls. This
gate does not invoke Quint or extend the Quint replay domain above.
