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
    4×2 non-monotonicity witness; on 3×4 one added car revives all seven
    original cars;
  - under Austin–Benjamini's train rule, the least stuck configuration has W+H cars;
  - the square-density 2/3 observation is already in the 1992 literature, and
    a time-zero blocking-loop bound does not control eventual jamming.
- [Finite BML formal coverage](formal/README.md): Lean kernel proofs and
  identity-preserving transport, actual Quint evaluation, bounded correspondence,
  axiom audit, reproducible witnesses, and the remaining general proof obligations.

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

## Evidence and scope

The notes distinguish published theorems, published numerical or geometric
analysis, direct mathematical derivations, and proposed research obligations.
Direct derivations carry no claim of novelty.

The repository contains an executable BML model, historical exhaustive tables
(`data/exhaustive.json`), machine-checked local kernel theorems, and an automated
test suite. The full G1/G2/R/F extremal arguments are still prose proofs with
bounded computational support; the Lean arithmetic components are not presented
as formal proofs of those full results. The formal register states the exact
replay domains and distinguishes regenerated data from inherited tables.

The initial research boundary is explicit: permanent blocking is a property of
traffic time evolution; quasiperiodicity and pure point spatial spectrum concern
spatial order. Establishing one does not by itself establish the others.
