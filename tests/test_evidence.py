"""Reproduce the small part of the historical table, rather than trusting its formulas."""
import json
from pathlib import Path

import numpy as np

from bml.analysis import run
from bml.exhaustive import FREE, classify_all
from bml.extremal import max_free
from bml.model import EAST, NORTH, is_fixed, step


def test_historical_tables_replayed_for_every_rectangle_with_at_most_nine_cells():
    data = json.loads((Path(__file__).parents[1] / "data/exhaustive.json").read_text())
    checked = 0
    for record in data:
        if record["h"] * record["w"] <= 9:
            actual = run(record["h"], record["w"])
            # JSON normalizes integer keys in the count table to strings.
            assert json.loads(json.dumps(actual)) == record
            checked += 1
    assert checked == 23


def test_empty_fixed_state_is_free_not_gridlock():
    assert is_fixed(np.zeros((1, 1), np.int8))
    assert int(classify_all(1, 1).cls[0]) == FREE


def test_one_car_forces_free_flow_when_both_dimensions_exceed_one():
    for h, w in [(2, 2), (2, 3), (3, 2), (4, 5)]:
        for species in (EAST, NORTH):
            for y in range(h):
                for x in range(w):
                    state = np.zeros((h, w), np.int8)
                    state[y, x] = species
                    for _ in range(h * w):
                        state, moved = step(state)
                        assert moved == 1


def test_coprime_free_flow_formula_is_a_separate_branch():
    assert max_free(2, 3) == 3
    assert max_free(3, 4) == 6
    assert max_free(1, 1) == 0
