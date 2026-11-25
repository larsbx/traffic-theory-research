# traffic-theory-research

Research notes on traffic cellular automata, blocking, spatial order, and their
connections to tiling and dynamical-systems theory.

## Research notes

- [Protected queues delay global gridlock](docs/research/2026-11-18-protected-queue-gridlock-delay.md)
  (2026-11-18): a universal Lean proof shows that a short guarded east queue
  forces its original rear car to make its first move at a prescribed round,
  regardless of the exterior. Exact cyclic-pattern probabilities give a
  logarithmic lower bound on gridlock time with high probability at every
  fixed `0<p<1`. A separate prose construction shows that every bounded local
  pattern has an eventually jammed completion on sufficiently large squares.
  Neither statement establishes a positive critical density.
- [Certified bounds for eventual gridlock](docs/research/2026-11-18-certified-absorption-bounds.md)
  (2026-11-18): universal Lean soundness for hit/safe/unresolved cutoff
  certificates, exact initial-weight probability intervals, and actual
  Lean/Quint/Python replay. The complementary
  [relaxation obstructions](docs/research/2026-11-18-relaxation-obstructions.md)
  prove a queue-delay mechanism, a logarithmic settling-time obstruction,
  failed vacancy/defect shortcuts, and a conditional late-defect criterion.
  The fixed-positive-density transition remains open.
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
  `p_L*L <= 2*log(log(L))-4*log(log(log(L)))-2` eventually implies vanishing
  gridlock probability; the earlier leading-order window follows as a corollary.
  It also proves limits of conserved-lane and fixed-time arguments. Lean checks
  the underlying CLASSIC count invariants; exact finite Python probabilities
  and obstruction checks remain distinct from these asymptotic proofs. A
  fixed positive critical density is still unproved.
- [Limits of deterministic lane-profile certificates](docs/research/2026-11-18-lane-profile-obstruction.md)
  (2026-11-18): Lean constructs a ringless jam with any positive E-row and
  N-column profiles whose two maxima sum to at most the side length. Exact
  initial-law bounds show that such profiles occur with high probability at
  every fixed `0<p<1`. Consequently every sound nonjamming certificate based
  only on lane counts has vanishing acceptance probability. This does not
  estimate the jam basin within a profile class.
- [Disjoint-strip capacity bounds](docs/research/2026-11-18-disjoint-strip-capacity.md)
  (2026-11-18): several disjoint north-empty strips can exceed the conserved
  east-row capacity even when every single-strip test fails. An exact
  convolution gives stronger finite iid gridlock bounds, with complete small
  torus checks. The geometric and probability arguments have prose proofs.
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
- [Diagonal cuts and the first mixed cycle](docs/research/2026-11-18-diagonal-cuts.md)
  (2026-11-18). This bounds mixed-cycle formation through order `sqrt(log L)`
  rounds at every fixed density below one. The proof explores a blocker path
  using only initial cells and identifies the late formation term still to control.
- [Guarded barriers and logarithmic mixed-cycle delay](docs/research/2026-11-19-guarded-barrier-formation.md)
  (2026-11-19). A Lean-proved queue produces an L-shaped path barrier from
  `6T` prescribed cars and one hole. Its initial-law probability improves
  first mixed-cycle exclusion to order `log L` at each fixed `0<p<1`.
  Combining it with empty-origin cuts gives a uniform `log L/log log L`
  horizon for `0<=p<=p0<1`. Late formation and a positive nonjamming interval
  remain open; probability integration and limits have prose proofs.
- [Maximal frozen cores and the path-mass estimate](docs/research/2026-11-19-maximal-core-and-path-mass.md)
  (2026-11-19). Lean identifies the maximal occupied closed core by a finite
  path test and proves that it increases to exactly the eventual permanent
  sites. A population-weighted argument weakens the sufficient fixed-density
  path estimate from uniform `o(1/L)` to late-time or averaged `o(1)`.
  The normalized limiting core fraction equals gridlock probability up to
  the exponentially small full-lane exception. An exact population envelope
  converts a supplied mass estimate into a finite bound; proving the needed
  decay under the evolved law remains open.
- [Stopped original cars and exact finite core mass](docs/research/2026-11-21-stopped-core-counts.md)
  (2026-11-21). Lean now proves the eventual core/stopped-tag cardinality
  identification and finite initial-weight jam/full-lane comparison with
  exact population normalization. The actual exporter is proved to refine
  the CLASSIC board and tagged traces; independent finite recurrence checks
  cover empty boards, partial fixation, and unequal-population mixtures.
- [Theorems for real traffic flow](docs/research/2026-11-24-real-traffic-theorems.md) (2026-11-24):
  five results under physical, measurable assumptions (jam spacing, saturation flow, signal green
  fractions, a speed limit). They cover a jam-density bound on gridlock size, permanent gridlock
  under re-routing ([R2 traps and safe-cell certificates](formal/lean/README.md#lane-graph-traps-and-safe-cells-r2)),
  a closure-time bound, a signal-plan cut bound on throughput, and a Little's-law
  envelope for the macroscopic fundamental diagram. Each comes with proofs, simulator checks and
  the real data that would test it.
- [Gridlock on Real Street Networks](docs/paper/paper.pdf) (paper, 2026-11-23): the results below
  in academic form. It separates BML itself (L0), the lane-graph extension (L1) and the bridge to
  real traffic (L2), with a claim register, proofs, the Lean status of the certificate, and 600 seeded
  experiments on six city centres ([source and data](docs/paper/README.md)).
- [Dynamics-free mathematics on real street maps](docs/research/2026-11-23-dynamics-free-map-mathematics.md)
  (2026-11-23): G0/G1 restated for lane graphs under exclusion + commitment alone (jam cores
  live on the *jam graph* and need ≥ girth cars). It also adds a per-cell throughput lemma with
  a max-flow bound, Sturmian free speeds of straight streets (1 + min(|tan θ|, |cot θ|)), and a
  graph-zeta risk index, all computed from OpenStreetMap by `GET /api/analyze`.
- [Formal coverage and validation](formal/README.md): the CLASSIC finite-torus
  `BML` proofs, identity-preserving transport and non-monotonicity witness, together
  with the complementary `Traffic` tiling/staircase proofs, the complete
  [TRAIN rectangular jam theorem](formal/TRAIN.md), actual Quint evaluation,
  bounded correspondence, and the remaining proof obligations.

## Simulator

- [Gridlock City](app/README.md): a retro pixel-art traffic simulator on real OpenStreetMap streets,
  driven by the BML rule generalised to lane graphs. It reduces exactly to `bml.model.step`
  on the torus, which is tested against 80 Python orbits. Frozen "ghost" cars are β-cycle
  certificates, the map form of Lemma G0, and jam cores need at least girth-many cars, as in
  G1. It includes a BML lab with live theorem readouts.

## Code

- `bml/model.py` — pure, vectorised dynamics (classical and Austin–Benjamini train rule).
- `bml/exhaustive.py` — exact classification of every state (pointer doubling on the step map).
- `bml/extremal.py` — constructions and characterisations.
- `bml/certificates.py` — independent labeled orbits and blocker-cycle certificates.
- `bml/capture.py` — checked blocker cycles, identity-aware capture certificates,
  and separate formation/capture observations with explicit unresolved cutoffs.
- `bml/probability.py` — exact finite iid basin probabilities, initial full-lane
  probabilities, and checked conserved-strip obstructions and probability bounds.
- `bml/absorption.py` — verified finite traces and exact eventual-gridlock
  intervals, with omitted initial probability retained as unresolved.
- `bml/obstructions.py` — raw phase-aware defects and queue-delay bounds,
  with actual-kernel controls for proposed fixed-density proof routes.
- `bml/guarded_queue.py` — exterior-independent delayed movement certificates
  and exact cyclic-pattern upper bounds on early global gridlock.
- `bml/barriers.py` — arbitrary-exterior snapshot barriers, exact initial-law
  weights, and a logarithmic first-mixed-cycle bound.
- `bml/path_core.py` — finite direct paths, maximal frozen-core pruning, and
  exact population-law conversion of a supplied late-time mass bound.
- `bml/fixation.py` — independent labeled fixation counts and exact initial-iid
  Palm probabilities, including the car-weighted jam probability and ring error.
- `bml/profiles.py` — explicit jams with prescribed lane counts and exact upper
  bounds on acceptance of sound nonjamming certificates that use only those counts.
- `bml/capacity.py` — checked disjoint-strip capacity obstructions and exact
  marginal-law bounds on eventual gridlock.
- `bml/analysis.py` — tables for all tori with WH ≤ 16, written to `data/exhaustive.json` (~6 min).
- `bml/nonmonotone.py` — un-jamming pairs with car identities tracked.
- `bml/thin.py` — thin-torus (2×W) jam structure and exact bounds on q; certificates that q is
  not monotone for every W ≥ 24 (`scripts/thin_certificates.py`, `data/thin-nonmonotone.json`).
- `bml/montecarlo.py` — empirical jam curves (not a proof).

```sh
python -m pip install -r requirements-dev.txt
python -m pytest -q
python scripts/check_capture.py --report .artifacts/capture-replay.json
python scripts/check_probability.py --report .artifacts/probability-replay.json
python scripts/check_fixation.py --report .artifacts/fixation-replay.json
python scripts/check_profiles.py --report .artifacts/profiles-replay.json
python scripts/check_capacity.py --report .artifacts/capacity-replay.json
python scripts/check_guarded_queue.py --report .artifacts/guarded-queue-replay.json
python scripts/check_barriers.py --report .artifacts/barriers-replay.json
python scripts/check_path_core.py --report .artifacts/path-core-replay.json
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
  many rounds, possibly with a smaller least period. B7 proves permanent full
  movement from round `lcm(W,H) * m * (gcd(W,H) - 2)` onward for every board
  with `2m ≤ gcd(W,H)`, including the alternating singleton-class equality
  regime formalized in B7.6. Its separate blockage bound is at most
  `m * (gcd(W,H) - 2)` blocked rounds in any finite prefix. The suite also
  proves permanent cores and route-cover capture bounds. Some original car eventually
  stops exactly when the state eventually jams or initially has a full E-row
  or N-column. Arithmetic components of F and the strong 4×2 non-monotonicity
  witness are also proved. Exact jammed representatives of bounded positive
  lane profiles and guarded-queue first-movement bounds are proved for the
  actual kernel as well. Finite replays compare Lean with NumPy on 93,387
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
  bound. The rectangular CLASSIC proof uses the CLASSIC transport kernel.
  See [blueprint B7](formal/blueprint.md#b7-classic-low-density-speed-one).

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
that every state eventually reaches free flow. Theorem F is also proved in
Lean: the exact free-flow capacity, executable maximizing constructions,
and constructions at every smaller population hold on every positive rectangle.
The same capacity bounds eventual free flow by car-count conservation. Independent
max-plus DP checks and actual Lean construction replays give finite implementation
evidence alongside the universal proofs.
The formal register states the exact
replay domains and distinguishes regenerated data from inherited tables.

The initial research boundary is explicit: permanent blocking is a property of
traffic time evolution; quasiperiodicity and pure point spatial spectrum concern
spatial order. Establishing one does not by itself establish the others.
