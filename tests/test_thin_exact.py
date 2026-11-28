"""Exact 2×W jam counts by gap decomposition, and the smallest non-monotone thin torus."""
import itertools
import os
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np
import pytest

from bml.iid import certify_positive_derivative
from bml.levels import jams
from bml.native import build
from bml.thin import column_types
from bml.thin_exact import (_noplug, gap_jam_counts, heavy_counts, jam_counts,
                            nonmonotone_certificate, plug_jam_counts, probability, sandwich)

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import thin_exact as script  # noqa: E402


def native(name, *args, env=None):
    out = subprocess.run([str(build(name)), *map(str, args)], check=True, capture_output=True,
                         text=True, env=env).stdout
    return [list(map(int, line.split())) for line in out.split("\n") if line.strip()]


@pytest.mark.parametrize("g", [1, 2, 3, 4, 5, 6])
def test_gap_enumerator_fast_path_matches_floyd_brute_force(g):
    env = dict(os.environ, GAP_JAM_CHECK="1")
    assert native("gap_jam", g) == native("gap_jam", g, env=env)


def test_gap_data_matches_fresh_enumeration():
    for g in range(9):
        assert gap_jam_counts()[g] == [__import__("math").comb(2 * g, k) + j
                                       for k, j in native("gap_jam", g)]
    assert sorted(gap_jam_counts()) == list(range(15))


@pytest.mark.parametrize("W", [2, 3, 4, 5])
def test_plug_part_against_brute_force(W):
    """Gap independence: P(plug ∧ jam) from the renewal sum equals direct enumeration."""
    states = np.array(list(itertools.product((0, 1, 2), repeat=2 * W)), np.int8).reshape(-1, 2, W)
    J = jams(states)
    plug = [0] * (2 * W + 1)
    free_heavy = [0] * (2 * W + 1)
    for s, j in zip(states, J):
        if j:
            n = int((s != 0).sum())
            if "P" in column_types(s):
                plug[n] += 1
            else:
                assert int((s == 1).sum()) >= W            # plug-free jams need W east cars
                free_heavy[n] += 1
    assert plug == plug_jam_counts(W)
    assert all(f <= h for f, h in zip(free_heavy, heavy_counts(W)))


def test_noplug_enumerator_counts_the_whole_class():
    for W in range(2, 10):
        rows = native("noplug_jam", W)
        assert [s for _, _, s in rows] == heavy_counts(W)


def test_exact_counts_reproduce_every_exhaustive_2xW_table():
    tables = script.exhaustive_2xW()
    checked = 0
    for W in sorted(_noplug()):
        if W in tables:
            counts = jam_counts(W)
            assert all(counts[n] == tables[W].get(n, 0) for n in range(2 * W + 1)), W
            checked += 1
    assert checked >= 11                                     # 2×2 … 2×12


def test_sandwich_contains_exact_values():
    for W in (8, 12, 14):
        exact = [jam_counts(W)[n] for n in range(2 * W + 1)]
        for p in (Fraction(1, 5), Fraction(1, 2), Fraction(9, 10)):
            lo, hi = sandwich(W, p)
            assert lo <= probability(exact, W, p) <= hi


def test_monotone_through_2x14():
    """q is strictly increasing on (0, 1] on 2×13 and 2×14 (2×W ≤ 12 is in the iid note)."""
    for W in (13, 14):
        assert certify_positive_derivative(jam_counts(W), 2 * W) is not None


def test_2x15_is_not_monotone():
    assert nonmonotone_certificate(**script.NONMONOTONE)["holds"]
    # negative control: the same bounds cannot separate the reversed or a flat pair
    assert not nonmonotone_certificate(15, "1/5", "1/5")["holds"]
    assert not nonmonotone_certificate(14, "1/5", "13/40")["holds"]


def test_verify_script_passes():
    assert script.verify()
