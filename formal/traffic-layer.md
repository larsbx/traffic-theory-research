# Traffic: tilings, staircases, and bounded correspondence

The `Traffic` Lean library and `traffic.qnt` Quint model implement deterministic
BML traffic semantics and selected exact constructions from the [research note](../docs/research/2026-11-18-bml-tilings-quasicrystals-trigonometry.md).
Lean proofs apply to the domains in their theorem statements. Quint checks and
the executable correspondence table apply to explicitly bounded finite grids.

This is the detailed register for the **Traffic suite**. Start at the
[shared formal coverage register](README.md) for both suites. The separate
`BML` library preserves the finite-torus transport and strong non-monotonicity
proofs, arithmetic components of G1/F, and its Python/Quint replay evidence.
No general theorem identifying the `BML` and `Traffic` definitions is claimed.

Both formal suites use **CLASSIC** old-state-vacancy movement. The Python
**TRAIN** rule is separate and has no Lean/Quint coverage here. Under TRAIN,
full single-species rings rotate without changing occupancy; consequently the
CLASSIC fixed-point/blocking equivalence and its Wang interpretation do not
transfer to TRAIN. All finite comparisons, frozen-state tests, and staircase
results on this page are scoped to CLASSIC.

## Reproduce the acceptance gate

Requirements: Lean 4.34.1 (including Lake), Node.js compatible with Quint 0.33.1,
npm, and Python 3. CI pins Node 24.22.3 and verifies the Lean release archive's
SHA-256 before installation. Lean uses only its bundled standard library.

From the repository root:

    cd formal/quint
    npm ci --ignore-scripts
    cd ../..
    python3 scripts/check_formal.py

The repository's lean-toolchain file pins the Lean release. Put that release's
Lake on PATH, or set TRAFFIC_LAKE to its executable. The gate rejects mismatched
Lean or Quint versions.

The gate builds the Traffic library and exporter within the shared Lean package, runs
`TrafficAudit.lean` over imported Traffic declarations, checks this suite's
required theorem inventory, typechecks and tests Quint,
runs a separately labeled seeded simulation, and compares both implementations
on every specified board and phase. Failures return a nonzero exit code.
The gate checks Quint's structured test results against the named inventory in
coverage.json, requiring all 25 pure and four action tests with none ignored.

Logs, both transition tables, and a machine-readable acceptance.json are written
under formal/artifacts/ (ignored by Git). The report records tool versions,
commands, source-file hashes, and the exact Git revision when run in a checkout.
It also rejects source changes during the run. The GitHub workflow checks out
the PR head explicitly and uploads the evidence as an artifact.

## Lean coverage

| Module | Kernel-checked result | Boundary |
| --- | --- | --- |
| Traffic/Core.lean | Eligible cars leave/arrive; a half-step fixes a board iff no move is eligible; freezing iff both directed target conditions; a full-cycle fixed point iff frozen; frozen configurations remain fixed; full occupancy freezes. | Arbitrary grid with inverse predecessor/successor maps. No probability or population-count theorem. |
| Traffic/Wang.lean | All 27 triples are enumerated; exactly 21 distinct types are allowed; valid tilings correspond uniquely to frozen configurations; both encoding inverses and translation-compatible pullbacks. | Fixed tile orientation and the given grid adjacency. |
| Traffic/Torus.lean | Explicit nonempty cyclic coordinates and proofs that predecessor/successor are inverse, including singleton axes. | Width and height are successor naturals. |
| Traffic/Geometry.lean | An actual bi-infinite staircase for any supplied direction word, exact support and injectivity, semantic freezing and persistence. | Does not construct a bi-infinite Fibonacci hull word or prove its density/frequency limits. |
| Traffic/Geometry.lean | Finite Fibonacci substitution counts, Fibonacci word lengths, exact integer-pair arithmetic representing a + b*phi, and substitution scaling of formal projected displacement. | Algebraic identities, without a real embedding, orthogonal projection, or trigonometric analysis. |
| Traffic/Geometry.lean | A finite lifted walk closed modulo the side lengths has east/north counts that are integer winding multiples; a nonempty walk has a positive winding count. | Modular closure is an explicit hypothesis. A finite dependency-cycle existence theorem and its bridge to this predicate are still open. |
| Traffic/Export.lean | Executable finite frozen/Wang checks are equivalent to the semantic Lean predicates; enumeration covers every coordinate. | Exported transitions use Core.halfStep directly. Finite Lean–Quint agreement is checked separately. |

The Traffic suite's required public theorem names are listed in
[coverage.json](coverage.json).
The inventory is checked against the compiled environment rather than inferred
from theorem-name text in source files.

### Axiom audit

`TrafficAudit.lean` examines every declaration originating in Traffic and its submodules,
including generated/private declarations and the exporter's global entry point.
It also includes declarations carrying the project namespace. Any dependency
outside the standard allowlist is an error:

- propext
- Quot.sound
- Classical.choice

The full inventory includes compiler-generated theorem declarations, so its
total must not be described as a count of independent mathematical results.
No added mathematical axioms, admitted proofs, or native_decide certificates
are used. Kernel proofs and compiled executable output are different evidence:
the latter is checked by the bounded cross-language comparison.

## Quint and executable correspondence

Quint 0.33.1 is locked in package.json and package-lock.json. This suite uses
`traffic.qnt`, with `bml_tests.qnt`, `bml_model.qnt`, and `bml_export.qnt` as its
test, stateful, and export modules. The model uses
the TypeScript interpreter, with no implicit native-backend download.
The upstream `BML.qnt` suite remains separate. See
[quint/README.md](quint/README.md) for both suites' commands and conventions.

The deterministic suites contain 25 pure tests and four action tests. Six
universal checks enumerate the complete board domains:

| Grid | Boards | Half-step cases, both phases |
| --- | ---: | ---: |
| 1 x 1 | 3 | 6 |
| 1 x 2 | 9 | 18 |
| 2 x 1 | 9 | 18 |
| 2 x 2 | 81 | 162 |
| 3 x 2 | 729 | 1,458 |
| 2 x 3 | 729 | 1,458 |
| **Total** | **1,560** | **3,120** |

These checks cover species conservation, validity, old-state simultaneous moves,
half-step and full-cycle fixed points, frozen permanence, and Wang recoding.
Controls distinguish blocked queues from sequential cascades, quiet half-steps
from complete freezing, genuine wraparound from row-boundary mistakes, and a
truncated path from an infinite blocked staircase.

The stateful model additionally chooses a 3 x 2 initial board and initial phase
nondeterministically. Phase alternation, conservation, frozen absorption, and
Wang equivalence are safety predicates. The seeded run checks 100 initializations
for at most 20 half-steps with seed 20261118. That run is simulation evidence.
The finite universal tests are exhaustive over their stated domains; no
Apalache or unbounded temporal verification is claimed.

### Shared observable contract

Cells use 0 = empty, 1 = east, 2 = north. Phases use 1 = east and 2 = north.
The site index is x + width*y, with north increasing y. Board codes are
little-endian ternary. Each half-step reads the old configuration for all
movement decisions, and the phase toggles even when the board does not change.

The Lean executable and Quint interpreter independently emit the same ten
columns, recorded in coverage.json. The JavaScript Quint adapter only serializes
the interpreter's ITF result; it does not reimplement traffic transitions.
The gate rejects missing, duplicate, reordered, or disagreeing rows and checks
additional concrete movement controls and species counts.

This is exhaustive agreement on six finite grids, not a proved unbounded
refinement between Lean and Quint.

## Remaining research obligations

The formalized staircase theorem accepts any bi-infinite direction word.
Connecting it specifically to an infinite Fibonacci tiling still requires
constructing the relevant hull element and proving the real geometric and
asymptotic claims. Finite Fibonacci count identities do not replace that work.

The following remain outside this layer:

- The probabilistic high-density gridlock theorem and its percolation proof.
- Real frequency limits, zero areal density limits, orthogonal projection,
  trigonometric identities, and diffraction or spatial spectral theorems.
- A species-conservation theorem in the `Traffic` library and an unbounded
  Lean–Quint refinement. The separate `BML` library already proves species
  transport bijections and nonemptiness preservation; relating its executable
  `speciesCount` sum to those bijections remains a separate obligation.
- A formal finite-graph cycle existence proof and its bridge to modular closure.
- Complete Lean proofs of G1, G2, Lemma R, and Theorem F in
  [the extremal research note](../docs/theorems.md). `Traffic` supplies G0 and
  winding under modular closure; `BML` also supplies G1/F arithmetic components
  and the proved strong non-monotonicity witness. Neither suite completes the
  general extremal arguments.
- Reproduction of the published large-grid intermediate-state experiments.

Published claims in the research note retain their literature attribution.
The deterministic kernel and bounded checks do not promote them to newly
formalized results.
