# Quint finite BML model

`BML.qnt` gives an executable specification of the torus dynamics. A state is
a list of `0` (empty), `1` (east), or `2` (north). Cell `(x,y)` has index
`y * width + x`; its base-three digit contributes `cell * 3^index` to the state
identifier. East cars move first, synchronously; north cars then move
synchronously in the resulting state. Positive dimensions include one-cell-wide
and one-cell-high tori: a car whose target is its own cell is blocked.

## Reproduce

From the repository root, with Node.js, Python, and the repository's Python
dependencies installed:

```sh
npm ci --ignore-scripts --prefix formal/quint
python formal/quint/check.py --max-cells 6
# Larger finite replay, optional:
python formal/quint/check.py --max-cells 9
```

The package and lockfile pin `@informalsystems/quint` to `0.33.1`. Evaluation
explicitly uses its TypeScript backend, so no Rust backend download or Apalache
installation is needed. The acceptance command parses and typechecks the model,
runs seven deterministic Quint tests, and compares its results with the NumPy
kernel for **every state of every ordered positive rectangle** within the
declared area bound. It checks the east intermediate state, final state, and
each phase's move count. It also checks species conservation and the equivalence
of a fixed point, local blocking, and zero moves on those states.
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

## Replay interface

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

## Proof boundary

The pure definitions describe arbitrary positive dimensions, but the commands
above establish only finite executable checks in their stated scopes. They do
not prove a refinement theorem for arbitrary tori, eventual classification for
all configurations, G1/G2/Theorem F, or a critical density. The seven Quint tests
use explicit finite quantification and fixed witnesses; `--max-samples=1` does
not make those tests a random search. No Apalache verification is claimed.
The empty state is fixed and vacuously free; this module does not confuse its
fixed-point property with the nonempty gridlock classification.
