# traffic-theory-research

Research notes on traffic cellular automata, blocking, spatial order, and their
connections to tiling and dynamical-systems theory.

## Research notes

- [BML gridlock, tilings, quasicrystals, and trigonometry](docs/research/2026-11-18-bml-tilings-quasicrystals-trigonometry.md)
  (2026-11-18): the rigorous high-density theorem, an exact encoding of frozen
  configurations by 21 Wang tiles, a Fibonacci blocking staircase and its
  projection, torus winding, published geometric traffic analysis, and diffraction.
- [When does BML gridlock switch?](docs/theorems.md) (2026-11-18): the precise open
  threshold problem, plus exact worst-case thresholds on every finite torus:
  - gridlock exists ⟺ n ≥ min(W,H);
  - gridlock is never forced below full density;
  - free flow is rigid, and the densest free flow is (WH/g)·⌊(g+⌊g/3⌋)/2⌋ with
    g = gcd(W,H), density → 2/3 on L×L;
  - adding one car can un-jam a configuration, even reviving all the original cars
    (non-monotonicity);
  - under Austin–Benjamini's train rule, the least stuck configuration has W+H cars.

## Code

- `bml/model.py` — pure, vectorised dynamics (classical and Austin–Benjamini train rule).
- `bml/exhaustive.py` — exact classification of every state (pointer doubling on the step map).
- `bml/extremal.py` — constructions and characterisations.
- `bml/analysis.py` — tables for all tori with WH ≤ 16, written to `data/exhaustive.json` (~6 min).
- `bml/nonmonotone.py` — un-jamming pairs with car identities tracked.
- `bml/montecarlo.py` — empirical jam curves (not a proof).

```sh
pip install numpy pytest hypothesis
python -m pytest -q          # 479 tests
python -m bml.analysis 16    # regenerate data/exhaustive.json
```

## Evidence and scope

The notes distinguish published theorems, published numerical or geometric
analysis, direct mathematical derivations, and proposed research obligations.
Direct derivations carry no claim of novelty.

The repository contains an executable BML model, exhaustive classification
receipts (`data/exhaustive.json`) and an automated test suite. It does not yet
contain machine-checked proofs.

The initial research boundary is explicit: permanent blocking is a property of
traffic time evolution; quasiperiodicity and pure point spatial spectrum concern
spatial order. Establishing one does not by itself establish the others.
