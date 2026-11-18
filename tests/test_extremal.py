"""Theorems G1, G2, F and Lemma R: constructions checked by simulation, characterisations
checked exhaustively, formulas checked against data/exhaustive.json."""
import json
from pathlib import Path

import numpy as np
import pytest
from hypothesis import given, settings, strategies as st

from bml.model import EAST, NORTH, is_fixed, counts
from bml.exhaustive import decode, classify_all, JAM
from bml.extremal import (gridlock_with, non_gridlock_with, min_gridlock, statically_free,
                          dynamically_free, max_free, max_free_config, V)

SIDES = range(1, 13)
SHAPES = [(h, w) for h in SIDES for w in SIDES]
DATA = Path(__file__).parents[1] / "data" / "exhaustive.json"


@pytest.mark.parametrize("h,w", SHAPES)
def test_gridlock_exists_for_every_n_from_min_side(h, w):
    for n in range(min_gridlock(h, w), h * w + 1):
        s = gridlock_with(h, w, n)
        assert is_fixed(s) and sum(counts(s)) == n


@pytest.mark.parametrize("h,w", [(h, w) for h, w in SHAPES if h * w <= 40])
def test_non_gridlock_exists_below_full_density(h, w):
    for n in range(h * w):
        s = non_gridlock_with(h, w, n)
        assert sum(counts(s)) == n and (n == 0 or not is_fixed(s))
        if n:  # it never reaches a fixed point: single-species lines with a car and a hole
            assert any(0 < (row != 0).sum() < len(row) for row in (s if (s == NORTH).sum() == 0 else s.T))


@pytest.mark.parametrize("h,w", SHAPES)
def test_max_free_config_attains_bound(h, w):
    s = max_free_config(h, w)
    assert sum(counts(s)) == max_free(h, w)
    assert statically_free(s) and dynamically_free(s)


@pytest.mark.parametrize("h,w", [(h, w) for h in range(1, 10) for w in range(1, 10) if h * w <= 9])
def test_lemma_R_static_iff_dynamic_exhaustive(h, w):
    for s in decode(np.arange(3 ** (h * w), dtype=np.int64), h, w):
        assert statically_free(s) == dynamically_free(s)


@settings(max_examples=400, deadline=None)
@given(st.integers(2, 8), st.integers(2, 8), st.data())
def test_lemma_R_static_iff_dynamic_random(h, w, data):
    p = data.draw(st.floats(0.05, 0.7))
    rng = np.random.default_rng(data.draw(st.integers(0, 2**32 - 1)))
    u = rng.random((h, w))
    s = np.where(u < p / 2, EAST, np.where(u < p, NORTH, 0)).astype(np.int8)
    assert statically_free(s) == dynamically_free(s)


def test_V_matches_block_optimum():
    """V(g) = max over partitions of g into parts ≥ 2 of Σ ⌈ℓ/2⌉."""
    from functools import lru_cache

    @lru_cache(None)
    def best(g):
        return max([(l + 1) // 2 + best(g - l) for l in range(2, g + 1) if g - l != 1], default=0)
    assert all(V(g) == best(g) for g in range(2, 60))


@pytest.mark.skipif(not DATA.exists(), reason="run python -m bml.analysis first")
def test_formulas_match_exhaustive_data():
    for r in json.loads(DATA.read_text()):
        h, w = r["h"], r["w"]
        assert r["n_jam_min"] == min_gridlock(h, w)
        assert r["n_free_max"] == max_free(h, w)
        assert r["n_all_jam_from"] == h * w
