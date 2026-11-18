# traffic-theory-research

Research notes on traffic cellular automata, blocking, spatial order, and their
connections to tiling and dynamical-systems theory.

## Research notes

- [BML gridlock, tilings, quasicrystals, and trigonometry](docs/research/2026-11-18-bml-tilings-quasicrystals-trigonometry.md)
  (2026-11-18): the rigorous high-density theorem, an exact encoding of frozen
  configurations by 21 Wang tiles, a Fibonacci blocking staircase and its
  projection, torus winding, published geometric traffic analysis, and diffraction.
- [When does BML gridlock switch?](docs/theorems.md) (2026-11-18): an open
  probabilistic threshold question, plus extremal existence results on finite tori:
  - gridlock exists ⟺ n ≥ min(W,H);
  - gridlock is never forced below full density;
  - for g = gcd(W,H) ≥ 2, maximal free-flow count is (WH/g)·⌊2g/3⌋;
    for g = 1, it is max(H⌊W/2⌋, W⌊H/2⌋);
  - adding a stationary car can make an original car move forever: a proved
    4×2 non-monotonicity witness; a Python identity replay on 3×4 shows one
    added car reviving all seven original cars;
  - under Austin–Benjamini's train rule, the least stuck configuration has W+H cars;
  - the square-density 2/3 observation is already in the 1992 literature, and
    a time-zero blocking-loop bound does not control eventual jamming.
- [Formal coverage and validation](formal/README.md): the CLASSIC finite-torus
  `BML` proofs, identity-preserving transport and non-monotonicity witness, together
  with the complementary `Traffic` tiling/staircase proofs, actual Quint
  evaluation, bounded correspondence, and the remaining proof obligations.

## Code

- `bml/model.py` — pure, vectorised dynamics (classical and Austin–Benjamini train rule).
- `bml/exhaustive.py` — exact classification of every state (pointer doubling on the step map).
- `bml/extremal.py` — constructions and characterisations.
- `bml/certificates.py` — independent labeled orbits and blocker-cycle certificates.
- `bml/analysis.py` — tables for all tori with WH ≤ 16, written to `data/exhaustive.json` (~6 min).
- `bml/nonmonotone.py` — un-jamming pairs with car identities tracked.
- `bml/montecarlo.py` — empirical jam curves (not a proof).

```sh
python -m pip install -r requirements-dev.txt
python -m pytest -q
python -m bml.analysis 16    # regenerate data/exhaustive.json
```

For the pinned Lean and Quint toolchains, run the commands in the
[formal coverage register](formal/README.md). Hosted acceptance checks out the
PR's exact head and publishes separate Python, Lean, and Quint receipts.

## Formalization suites

Both Lean libraries and both Quint suites formalize the **CLASSIC** rule:
movement requires a vacant destination in the pre-half-step state. Python also
implements **TRAIN**, where queues can move together and full rings rotate.
The formal results and replays below do not cover TRAIN; an unchanged occupancy
pattern can hide movement under that rule, so the CLASSIC G0 fixed-point result
does not transfer.

- **BML:** the finite-torus kernel, numerical species-count conservation, local
  G0 equivalences, and the exact minimum jam size `min(W,H)`. Lean extracts a
  simple occupied blocker cycle, proves its winding and car-count bounds, and
  constructs a jam attaining the minimum. Conservation also proves that fewer
  cars can never evolve into a jam. The suite includes arithmetic components
  of F and the strong 4×2 non-monotonicity witness. Finite replays compare Lean with NumPy on 93,387
  states and Quint with NumPy on 3,720 states plus three witness rows; see the
  [BML evidence register](formal/README.md#finite-evidence-scopes).
- **Traffic:** the exact 21-Wang-tile correspondence, an infinite blocked
  staircase for any supplied bi-infinite direction word, finite Fibonacci
  counts and formal algebraic scaling, and winding under explicit modulo
  closure. Its acceptance gate compares 3,120 board/phase cases between Lean
  and Quint across six small grids; see the
  [Traffic evidence register](formal/traffic-layer.md).

These are separately scoped proof and validation suites in one pinned Lean
package. The replay domains are finite executable checks, and no general
cross-language or cross-library refinement is claimed. The infinite staircase
proof does not supply an infinite Fibonacci hull, real projection, or a spatial
spectral theorem.


## Evidence and scope

The notes distinguish published theorems, published numerical or geometric
analysis, direct mathematical derivations, and proposed research obligations.
Direct derivations carry no claim of novelty.

The repository contains an executable BML model, historical exhaustive tables
(`data/exhaustive.json`), machine-checked kernel and minimum-gridlock theorems,
and an automated test suite. G1's lower bound and attainment at its minimum are
proved in Lean for every positive rectangle. Its construction at every larger
admissible car count, and the general G2/R/F arguments, remain prose proofs with
bounded computational support. The formal register states the exact
replay domains and distinguishes regenerated data from inherited tables.

The initial research boundary is explicit: permanent blocking is a property of
traffic time evolution; quasiperiodicity and pure point spatial spectrum concern
spatial order. Establishing one does not by itself establish the others.
