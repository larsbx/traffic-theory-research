# Executable Quint BML models

This directory preserves two complementary suites, using the same pinned
Quint 0.33.1 interpreter and the same simultaneous finite-torus dynamics.
`BML.qnt` provides the east-then-north replay against the NumPy kernel.
`traffic.qnt` provides explicit half-step phases and the 21-tile Wang encoding,
with a separate replay against Lean. The distinct filenames also work on
filesystems that do not distinguish upper and lower case.

| Suite | Entry points | Deterministic coverage |
|---|---|---|
| Finite BML replay | `BML.qnt`, `check.py`, `evaluate.py` | Ten Quint tests; every state of all 14 ordered positive rectangles with at most six cells, plus three `4x2` witness rows; three executed mutation controls. |
| Phase and Wang layer | `traffic.qnt`, `bml_tests.qnt`, `bml_model.qnt`, `bml_export.qnt`, `export.cjs` | 25 pure tests and four state-transition tests; 1,560 boards on six tori, with both phases for 3,120 half-step cases. |

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

The `typecheck` command checks both suites. `npm test` runs the 25 pure and four
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
See [the formal-layer README](../README.md) for the combined acceptance gate.

## Shared conventions

- A board is a list of cell codes: 0 vacant, 1 eastbound, 2 northbound.
- Cell `(x,y)` has index `x + width*y`; y increases northward.
- The cell at index i contributes `cell * 3^i` to the board's ternary code.
- East and north each move synchronously. Every eligibility decision reads the
  input board of that half-step, including destinations vacated by other cars.
- Dimensions are positive. On one-cell-wide or one-cell-high tori, a car whose
  destination is its own cell is blocked.
- `BML.qnt` applies east first, then north. `traffic.qnt` accepts phase 1 for
  east or phase 2 for north and can start in either phase.
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

## Proof boundary

The pure definitions describe arbitrary positive dimensions, but the commands
above establish only finite executable checks in their stated scopes. The
deterministic tests use explicit finite quantification and fixed witnesses;
`--max-samples=1` does not make those tests a random search. No Apalache
verification or unbounded source-refinement theorem is claimed.

These suites do not prove eventual classification for all configurations,
G1/G2/Theorem F, a critical density, high-density random gridlock, infinite
Fibonacci frequencies, trigonometric identities, or diffraction theorems.
The empty state is fixed and vacuously free; neither module confuses its
fixed-point property with the nonempty gridlock classification.
