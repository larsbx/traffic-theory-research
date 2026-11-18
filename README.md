# traffic-theory-research

Rigorous results on the Biham–Middleton–Levine (BML) traffic model on finite tori.

- **[docs/theorems.md](docs/theorems.md)** — precise statement of the open BML threshold
  problem, plus proved worst-case thresholds:
  - gridlock exists ⟺ n ≥ min(W,H);
  - gridlock is never forced below full density;
  - free flow is rigid, and the densest free flow is (WH/g)·⌊(g+⌊g/3⌋)/2⌋ with g = gcd(W,H),
    density → 2/3 on L×L;
  - adding one car can un-jam a configuration (non-monotonicity).
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
