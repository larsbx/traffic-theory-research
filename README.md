# traffic-theory-research

Research notes on traffic cellular automata, blocking, spatial order, and their
connections to tiling and dynamical-systems theory.

## Research notes

- [Open questions and proof roadmap](docs/research/2026-11-18-open-questions-and-proof-roadmap.md)
  (2026-11-18): the post-TRAIN review, including an explicit periodic N-car
  family, the equality/gcd/time-bound extensions, CLASSIC rigidity and packing,
  probability and Fibonacci/spectral gaps, and current merged versus open-PR
  proof status. Prose arguments and finite checks are labeled separately from Lean.
- [BML gridlock, tilings, quasicrystals, and trigonometry](docs/research/2026-11-18-bml-tilings-quasicrystals-trigonometry.md)
  (2026-11-18): the rigorous high-density theorem, an exact encoding of frozen
  configurations by 21 Wang tiles, a Fibonacci blocking staircase and its
  projection, torus winding, published geometric traffic analysis, and diffraction.
- [When does BML gridlock switch?](docs/theorems.md) (2026-11-18): an open
  probabilistic threshold question, plus extremal existence results on finite tori:
  - gridlock exists ⟺ min(W,H) ≤ n ≤ WH;
  - gridlock is never forced below full density;
  - for g = gcd(W,H) ≥ 2, maximal free-flow count is (WH/g)·⌊2g/3⌋;
    for g = 1, it is max(H⌊W/2⌋, W⌊H/2⌋);
  - adding a stationary car can make an original car move forever: a proved
    4×2 non-monotonicity witness; a Python identity replay on 3×4 shows one
    added car reviving all seven original cars;
  - under Austin–Benjamini's train rule, the least stuck configuration has W+H
    cars when W,H≥2; singleton dimensions admit no nonempty jam;
  - a separate TRAIN square-lattice result gives eventual speed one when
    `2 * population < N`, with a complete Lean proof for the actual movement rule;
  - the square-density 2/3 observation is already in the 1992 literature, and
    a time-zero blocking-loop bound does not control eventual jamming.
- [Freezing, nucleation, and BML gridlock](docs/research/2026-11-18-freezing-gridlock-nucleation.md)
  (2026-11-18): separates formation of a persistent blocking core from capture
  of the surrounding traffic. Lean proves capture from explicit core obstacles
  on every row and column within `n_E*(W-1) + n_N*(H-1)` full rounds; Python
  verifies mixed-cycle geometry and independently replays tagged cars. The
  results do not determine a probabilistic jamming threshold.
- [Probabilistic gridlock bounds](docs/research/2026-11-18-probabilistic-gridlock-bounds.md)
  (2026-11-18): proves in prose that mixed-cycle formation agrees with eventual
  gridlock outside an exponentially rare initial full-lane event, and that
  `p_L*L <= (2-epsilon)*log(log(L))` implies vanishing gridlock probability.
  It also proves limits of conserved-lane and fixed-time arguments. Lean checks
  the underlying CLASSIC count invariants; exact finite Python probabilities
  and obstruction checks remain distinct from these asymptotic proofs. A
  fixed positive critical density is still unproved.
- [Fixed-density mixed-cycle formation](docs/research/2026-11-18-fixed-density-formation.md)
  (2026-11-18): initial-law exponential bounds on early capture formation and
  an exact one-round winding-cycle probability. A transfer calculation and a
  complete 4x4 one-step census quantify the failure of evolved independence.
  Lean checks the deterministic preimage and formed core; positivity of a
  critical density remains open.
- [Tagged fixation and global gridlock](docs/research/2026-11-18-tagged-fixation-and-gridlock.md)
  (2026-11-18): proves that some car eventually stops exactly when the system
  eventually jams or initially contains a full monochromatic lane. It connects
  global jam probability to the fixation probability of the car initially at a
  specified occupied site, with an explicit error tending to zero at every
  fixed positive density. The deterministic theorem, exact finite labeled
  evidence, and prose probability argument have separately recorded scopes.
- [Formal coverage and validation](formal/README.md): the CLASSIC finite-torus
  `BML` proofs, identity-preserving transport and non-monotonicity witness, together
  with the complementary `Traffic` tiling/staircase proofs, the complete
  [TRAIN rectangular jam theorem](formal/TRAIN.md), actual Quint evaluation,
  bounded correspondence, and the remaining proof obligations.

## Code

- `bml/model.py` — pure, vectorised dynamics (classical and Austin–Benjamini train rule).
- `bml/exhaustive.py` — exact classification of every state (pointer doubling on the step map).
- `bml/extremal.py` — constructions and characterisations.
- `bml/certificates.py` — independent labeled orbits and blocker-cycle certificates.
- `bml/capture.py` — checked blocker cycles, identity-aware capture certificates,
  and separate formation/capture observations with explicit unresolved cutoffs.
- `bml/probability.py` — exact finite iid basin probabilities, initial full-lane
  probabilities, and checked conserved-strip obstructions and probability bounds.
- `bml/fixation.py` — independent labeled fixation counts and exact initial-iid
  Palm probabilities, including the car-weighted jam probability and ring error.
- `bml/analysis.py` — tables for all tori with WH ≤ 16, written to `data/exhaustive.json` (~6 min).
- `bml/nonmonotone.py` — un-jamming pairs with car identities tracked.
- `bml/montecarlo.py` — empirical jam curves (not a proof).

```sh
python -m pip install -r requirements-dev.txt
python -m pytest -q
python scripts/check_capture.py --report .artifacts/capture-replay.json
python scripts/check_probability.py --report .artifacts/probability-replay.json
python scripts/check_fixation.py --report .artifacts/fixation-replay.json
python -m bml.analysis 16    # regenerate data/exhaustive.json
```

For the pinned Lean and Quint toolchains, run the commands in the
[formal coverage register](formal/README.md). Hosted acceptance checks out the
PR's exact head and publishes separate Python, Lean, and Quint receipts.

## Formalization suites

The `BML` and `Traffic` suites formalize the **CLASSIC** rule: movement requires
a vacant destination in the pre-half-step state. The separate `BML.Train` Lean
namespace and `Train.qnt` Quint model implement **TRAIN**, where queues can move
together and full rings rotate. An unchanged occupancy pattern can hide TRAIN
movement, so its jam predicate uses actual zero movement. The CLASSIC G0
fixed-point result does not transfer.

- **BML:** the finite-torus kernel, species transport bijections, numerical
  species and lane-count conservation, full-lane reflection, and conserved
  north-free strips. It proves local G0 equivalences and the complete G1 theorem:
  an n-car jam exists exactly when `min(W,H) ≤ n ≤ W*H`. Lean extracts a simple
  occupied blocker cycle, proves its winding and car-count bounds, and constructs
  a jam at every admissible exact count. Conservation also proves that fewer
  cars can never evolve into a jam. The complete G2 construction realizes every
  `0 ≤ n < W*H` with a state that never jams: zero cars use the empty state, while
  a positive population has a single-species mixed lane retaining both a car
  and a hole at every iterate. Among feasible populations, all configurations
  eventually jam iff `n = W*H`. The coset theorem identifies the actual cyclic
  `(1,-1)` coordinate orbits with `x+y mod gcd(W,H)`, including signed and bounded
  forward witnesses. Lemma R connects this geometry to the actual traffic
  phases: the static adjacency and phase-class conditions hold exactly when
  every car moves in every round starting at time zero. Checking the first
  `lcm(W,H)` rounds suffices, and each such configuration returns after that
  many rounds, possibly with a smaller least period. The suite also proves
  permanent cores and route-cover capture bounds. Some original car eventually
  stops exactly when the state eventually jams or initially has a full E-row
  or N-column. Arithmetic components of F and the strong 4×2 non-monotonicity
  witness are also proved. Finite replays compare Lean with NumPy on 93,387
  states and Quint with NumPy on 3,720 states plus three witness rows; see the
  [BML evidence register](formal/README.md#finite-evidence-scopes).
- **Traffic:** the exact 21-Wang-tile correspondence, an infinite blocked
  staircase for any supplied bi-infinite direction word, finite Fibonacci
  counts and formal algebraic scaling, and winding under explicit modulo
  closure. Its acceptance gate compares 3,120 board/phase cases between Lean
  and Quint across six small grids; see the
  [Traffic evidence register](formal/traffic-layer.md).
- **TRAIN:** executable queue and ring semantics, car transport and numeric
  species/population conservation, and the complete theorem that a nonempty
  zero-movement n-car state exists exactly when W+H≤n≤WH, for every positive
  rectangle. The interval is empty for singleton dimensions. The proof includes
  a construction for every allowed count. Lean and Quint replay evidence is
  recorded separately from this universal Lean theorem; see the
  [TRAIN evidence register](formal/TRAIN.md).
  It also proves that every N×N state with `2 * population < N` eventually
  reaches full speed: all cars move in every later full cycle. The empty state
  is included. This square theorem supplies no effective stabilization-time
  bound. The CLASSIC counterpart has a separate prose proof in
  [blueprint B7](formal/blueprint.md#b7-classic-low-density-speed-one),
  with its Lean formalization still open.

These are separately scoped proof and validation suites in one pinned Lean
package. The replay domains are finite executable checks, and no general
cross-language or cross-library refinement is claimed. The infinite staircase
proof does not supply an infinite Fibonacci hull, real projection, or a spatial
spectral theorem.


## Evidence and scope

The notes distinguish published theorems, published numerical or geometric
analysis, direct mathematical derivations, and proposed research obligations.
Direct derivations carry no claim of novelty.

The repository contains executable CLASSIC and TRAIN models, historical exhaustive tables
(`data/exhaustive.json`), machine-checked kernel and exact gridlock-population
theorems, and an automated test suite. The complete CLASSIC G1, G2, and TRAIN T
existence thresholds are proved in Lean for every positive rectangle, including
their constructions at every admissible exact count. CLASSIC G2 establishes
perpetual avoidance of total gridlock, which does not require eventual free
flow. The TRAIN square speed-one result below N/2 cars also has a complete
Lean proof. The coset identity B2 is formalized on the actual torus coordinates;
the general free-flow equivalence R is proved for the actual CLASSIC kernel,
including a finite moving-window criterion and return after `lcm(W,H)` rounds.
It characterizes perpetual free flow from the current state; it does not assert
that every state eventually reaches free flow. The packing and maximizing
constructions in F remain prose proofs with bounded computational support,
including the independent max-plus DP checks.
The formal register states the exact
replay domains and distinguishes regenerated data from inherited tables.

The initial research boundary is explicit: permanent blocking is a property of
traffic time evolution; quasiperiodicity and pure point spatial spectrum concern
spatial order. Establishing one does not by itself establish the others.
