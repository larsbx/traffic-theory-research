"""Write test/fixtures/bml-python.json: random BML tori stepped by bml.model (CLASSIC and TRAIN).

The JS engine must reproduce these orbits exactly on the torus lane graph.
Run from the repository root: PYTHONPATH=. python app/scripts/bml_fixture.py
"""
import json
import pathlib

import numpy as np

from bml.model import CLASSIC, TRAIN, step

rng = np.random.default_rng(20261118)
cases = []
for w, h in [(1, 4), (3, 1), (2, 2), (3, 4), (5, 5), (6, 4), (7, 3), (8, 8), (9, 6), (12, 10)]:
    for p in (0.2, 0.45, 0.7, 0.9):
        for rule in (CLASSIC, TRAIN):
            s = rng.choice([0, 1, 2], size=(h, w), p=[1 - p, p / 2, p / 2]).astype(np.int8)
            orbit, moves = [s.tolist()], []
            for _ in range(12):
                s, m = step(s, rule)
                orbit.append(s.tolist())
                moves.append(int(m))
            cases.append({"W": w, "H": h, "rule": rule, "orbit": orbit, "moves": moves})

out = pathlib.Path(__file__).resolve().parents[1] / "test" / "fixtures" / "bml-python.json"
out.write_text(json.dumps({"source": "bml.model.step", "cases": cases}, separators=(",", ":")))
print(f"{len(cases)} cases → {out}")
