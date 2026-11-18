# Executable Quint traffic model

The package lock pins Quint 0.33.1. All acceptance commands use its TypeScript
backend, avoiding an implicit download of a native simulation backend.

## Run

From this directory:

    npm ci --ignore-scripts
    npm run typecheck
    npm test
    npm run simulate

The deterministic cross-language table can be emitted from the repository root:

    node formal/quint/export.cjs > .artifacts/quint.tsv

Create the output directory before redirecting. The exporter runs Quint itself,
then converts the resulting ITF integer rows to TSV. It contains no independent
implementation of BML transitions.

## Conventions

- A board is a list of cell codes: 0 vacant, 1 eastbound, 2 northbound.
- The index is x + width*y; y increases northward.
- Phase 1 updates eastbound cars; phase 2 updates northbound cars.
- Each half-step reads the old board for every eligibility decision.
- The phase toggles after every half-step, including an unchanged board.
- Functions in bml.qnt require positive dimensions, a correctly sized board,
  legal cell codes, and phase 1 or 2. The concrete model checks these conditions
  at initialization.
- The stateful bml_model.qnt uses a 3x2 torus. Initialization nondeterministically
  chooses any of its 729 boards and either initial phase. Subsequent steps are
  deterministic.

## Acceptance boundary

The deterministic suite contains 25 pure tests and four state-transition tests.
The repository acceptance gate checks the actual passed-test names in Quint's
JSON output against formal/coverage.json, and rejects failed or ignored tests.
Six tests enumerate every board on the 1x1, 1x2, 2x1, 2x2, 3x2, and 2x3 tori:
1,560 boards and both phases, or 3,120 half-step cases.

For each enumerated board the suite checks validity, ternary-code round trip,
tile decoding, frozen/valid-matching equivalence, absence of eligible moves in
both phases, species counts, half-step fixed points, frozen permanence, and
full-cycle fixed points. These are exhaustive checks over the stated finite
domains, executed as universal predicates by Quint. They are not an unbounded
theorem or an Apalache model-checking result.

Named controls cover wraparound in both directions, inactive species, a blocked
queue whose front car moves, rejection of sequential cascade behavior, occupied
destinations, truncated blocking paths, a quiet half-step that is not gridlock,
phase order, the 21 allowed Wang types, forbidden tiles, and mismatched edges.
Stateful tests check both phases and phase toggles even for empty or fully
occupied boards.

The simulate command is an additional seeded check of 100 nondeterministic
initializations for at most 20 half-steps. It must not be described as exhaustive.
No high-density random-gridlock, infinite Fibonacci frequency, trigonometric,
or diffraction theorem is established by this bounded model.

## Export format

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

Board codes are little-endian ternary: the cell at index i contributes cell*3^i.
Dimensions appear in the order listed above, then input code increases from zero,
with phase 1 before phase 2. The output has exactly 3,120 rows.
