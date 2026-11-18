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
  - free flow is rigid, with exact finite-torus capacity formulas and density
    tending to 2/3 on L×L;
  - adding one car can un-jam a configuration (non-monotonicity).

## Code

- `bml/model.py` — pure, vectorised dynamics.
- `bml/exhaustive.py` — exact classification of every state (pointer doubling on the step map).
- `bml/extremal.py` — constructions and characterisations.
- `bml/analysis.py` — tables for all tori with WH ≤ 16, written to `data/exhaustive.json` (~6 min).
- `bml/montecarlo.py` — empirical jam curves (not a proof).

```sh
pip install numpy pytest hypothesis
python -m pytest -q          # 405 tests
python -m bml.analysis 16    # regenerate data/exhaustive.json
```

## Evidence and scope

The notes distinguish published theorems, published numerical or geometric
analysis, direct mathematical derivations, and proposed research obligations.
Direct derivations carry no claim of novelty.

The repository contains a Python BML model, exhaustive classification receipts
(`data/exhaustive.json`), automated tests, and the scoped Lean and Quint layer
below. The extremal claims in `docs/theorems.md` beyond the G0 fixed-point
characterization remain outside the Lean proofs.

## Formalization

The [Lean and Quint layer](formal/README.md) supplies:

- Lean 4.34.1 proofs connecting actual simultaneous traffic updates to freezing,
  the exact 21-Wang-tile correspondence, infinite blocking staircases, finite
  Fibonacci counts and algebraic scaling, and conditional winding arithmetic.
- An executable Quint 0.33.1 torus model, 29 deterministic tests, and explicitly
  bounded exhaustive checks over six grid sizes.
- A common acceptance gate comparing every one of 3,120 finite board/phase
  cases between Lean and Quint, with a compiled theorem/axiom audit and
  source-bound CI evidence.

Run instructions, exact theorem coverage, and limits are in the formalization
README and its machine-readable coverage manifest.

The initial research boundary is explicit: permanent blocking is a property of
traffic time evolution; quasiperiodicity and pure point spatial spectrum concern
spatial order. Establishing one does not by itself establish the others.
