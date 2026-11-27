"""Thin tori 2×W: structure lemmas, exact bounds, and the non-monotonicity certificates."""
import itertools
import json
import subprocess
import sys
from fractions import Fraction
from math import comb
from pathlib import Path

import numpy as np
import pytest

from bml.levels import jams
from bml.model import EAST
from bml.thin import (asymptotic_certificate, canonical, certificate, decay_certificate,
                      gap_condition, gap_event, gap_ok, lower, plug_without_lone, renewal_radius,
                      upper)

ROOT = Path(__file__).resolve().parents[1]


def all_states(h, w):
    return np.array(list(itertools.product((0, 1, 2), repeat=h * w)), np.int8).reshape(-1, h, w)


def iid_weight(s, p):
    n = int((s != 0).sum())
    return (p / 2) ** n * (1 - p) ** (s.size - n)


def long_movers(s):
    return int((canonical(s) == EAST).sum())


@pytest.mark.parametrize("shape", [(2, 3), (3, 2), (2, 4), (4, 2), (2, 5), (5, 2)])
def test_structure_lemmas_exhaustive(shape):
    """Every state, every car count: jam ⇒ (≥ W long-axis movers) or gap condition;
    plug and no lone short-axis car ⇒ jam."""
    states = all_states(*shape)
    W = max(shape)
    seen_winding = False
    for s, j in zip(states, jams(states)):
        if j and not gap_condition(s):
            assert long_movers(s) >= W, s
            seen_winding = True
        if plug_without_lone(s):
            assert j, s
    assert seen_winding            # the exception is real: winding cycles and full lanes occur


@pytest.mark.parametrize("shape", [(2, 9), (9, 2), (2, 14), (14, 2)])
def test_structure_lemmas_random(shape):
    rng = np.random.default_rng(sum(shape))
    W, cells = max(shape), shape[0] * shape[1]
    batch = []
    for _ in range(3000):
        n = int(rng.integers(1, W))
        flat = np.zeros(cells, np.int8)
        flat[rng.choice(cells, n, replace=False)] = rng.integers(1, 3, n)
        batch.append(flat.reshape(shape))
    batch = np.array(batch)
    J = jams(batch)
    assert J.sum() > 20                                     # the test sees jams at all
    for s, j in zip(batch, J):
        if j:
            assert gap_condition(s)                         # n < W, so fewer than W movers
        if plug_without_lone(s):
            assert j


@pytest.mark.parametrize("W", [3, 4, 5])
def test_bound_formulas_match_brute_force(W):
    """lower = P(plug ∧ no lone), gap_event = P(gap condition), exactly, by enumeration."""
    states = all_states(2, W)
    for p in (Fraction(1, 3), Fraction(3, 5)):
        assert lower(W, p) == sum(iid_weight(s, p) for s in states if plug_without_lone(s))
        assert gap_event(W, p) == sum(iid_weight(s, p) for s in states if gap_condition(s))


def test_gap_dp_matches_brute_force():
    p = Fraction(2, 7)
    G = gap_ok(5, p)
    cell = {0: 1 - p, 1: p / 2, 2: p / 2}                     # 1 = long-axis mover, 2 = short
    for g in range(5):
        tot = Fraction(0)
        for cols in itertools.product(itertools.product((0, 1, 2), repeat=2), repeat=g):
            if any(c == (2, 2) for c in cols):
                continue                                      # a plug ends the gap
            e = sum(c.count(1) for c in cols)
            dmax = max([d + 1 for d, c in enumerate(cols) if 2 in c], default=0)
            if e >= dmax:
                tot += np.prod([cell[x] for c in cols for x in c], dtype=object) if cols else 1
        assert G[g] == tot


def test_float_and_exact_modes_agree():
    for W, p in [(12, Fraction(1, 4)), (30, Fraction(53, 200))]:
        assert abs(float(upper(W, p)) - upper(W, float(p))) < 1e-12
        assert abs(float(lower(W, p)) - lower(W, float(p))) < 1e-15


def _exact_thin_tables():
    out = []
    for name in ("exhaustive.json", "exhaustive-17-22.json", "exhaustive-24-25.json"):
        data = json.loads((ROOT / "data" / name).read_text())
        if isinstance(data, dict):
            data = [dict(h=int(k.split("x")[0]), w=int(k.split("x")[1]), table=v)
                    for k, v in data.items()]
        out += [r for r in data if 2 in (r["h"], r["w"]) and r["h"] * r["w"] >= 6]
    return out


def test_bounds_sandwich_exact_jam_probability():
    tables = _exact_thin_tables()
    assert len(tables) >= 18
    for r in tables:
        W = r["h"] * r["w"] // 2
        for p in (Fraction(k, 10) for k in range(1, 10)):
            q = sum(v["jam"] * (p / 2) ** int(n) * (1 - p) ** (2 * W - int(n))
                    for n, v in r["table"].items())
            assert lower(W, p) <= q <= upper(W, p)


def test_gap_tail_bound_dominates_gap_probability():
    """The exponential-moment bound used in renewal_radius is ≥ G(g) term by term."""
    p, theta = Fraction(7, 20), Fraction(7, 5)
    b = 1 - p + p * theta / 2
    s, wL = b * b, p * b
    r = (s + wL) / theta
    for g, G in enumerate(gap_ok(40, p)):
        assert G <= s ** g + (wL / (s + wL)) * sum(r ** d * s ** (g - d) for d in range(1, g + 1))


def test_renewal_radius_rejects_bad_parameters():
    with pytest.raises(AssertionError):
        renewal_radius(Fraction(7, 20), Fraction(7, 5), Fraction(3, 2))   # outside convergence


def test_certificates_and_data_claims():
    data = json.loads((ROOT / "data" / "thin-nonmonotone.json").read_text())
    assert (data["W_min"], data["W1"]) == (24, 80)
    assert [c["W"] for c in data["finite"]] == list(range(24, 80))
    for c in data["finite"]:
        assert certificate(c["W"], c["p1"], c["p2"])["holds"]
    a = data["asymptotic"]
    assert asymptotic_certificate(a["p2"], a["theta"], a["z"], a["W1"], a["K"])["holds"]
    assert [d["p"] for d in data["decay"]] == ["1/2", "7/10", "9/10", "19/20", "49/50"]
    for d in data["decay"]:
        assert decay_certificate(d["p"], d["theta"], d["z"], d["K"])["holds"]
        assert d["tail_base"] < 1 and d["renewal_base"] < 1


def test_decay_certificate_negative_control():
    assert not decay_certificate(Fraction(9, 10), Fraction(11, 10), Fraction(103, 100))["holds"]


def test_decay_bound_dominates_monte_carlo_and_shrinks():
    """Theorem P numerically: U_W(p) ≥ q_W(p), and U_W(p) decreases in W at p = 0.9."""
    from bml.native import thin_jam_count
    j, n = thin_jam_count(32, 0.9, 100_000, seed=11)
    assert j / n < float(upper(32, Fraction(9, 10)))
    assert upper(64, 0.9) < upper(48, 0.9) < upper(32, 0.9)


def test_bounds_do_not_separate_below_24():
    """Negative control and the stated range: the bounds alone certify nothing at W = 23."""
    assert not certificate(23, Fraction(9, 100), Fraction(1, 4))["holds"]
    from bml.thin import find_certificate
    assert not find_certificate(23, 200, 40)["holds"]


def test_asymptotic_certificate_fails_too_early():
    a = dict(p2=Fraction(7, 20), theta=Fraction(7, 5), z=Fraction(117, 100))
    assert asymptotic_certificate(**a, W1=80)["holds"]
    assert not asymptotic_certificate(**a, W1=60)["holds"]


def test_verifier_script():
    out = subprocess.run([sys.executable, str(ROOT / "scripts" / "thin_certificates.py")],
                         capture_output=True, text=True, check=True)
    assert "OK" in out.stdout


def test_native_monte_carlo_matches_exact_2x10():
    from bml.native import thin_jam_count
    table = next(r for r in _exact_thin_tables() if (r["h"], r["w"]) == (2, 10))["table"]
    for p in (0.2, 0.5):
        q = sum(v["jam"] * (p / 2) ** int(n) * (1 - p) ** (20 - int(n)) for n, v in table.items())
        j, n = thin_jam_count(10, p, 200_000, seed=7)
        assert abs(j / n - q) < 5 * (q * (1 - q) / n) ** 0.5


def test_monte_carlo_data_claims():
    """The §4 summary of the note: no grid decrease through 2×14, a ≥ 5σ one on 2×15 and beyond."""
    rows = json.loads((ROOT / "data" / "thin-monte-carlo.json").read_text())
    assert len(rows) == 12 * 23 and {r["samples"] for r in rows} == {4_000_000}

    def largest_drop(W):
        pts = sorted((r["p"], r["jams"] / r["samples"], r["samples"]) for r in rows if r["W"] == W)
        return max(((qi - qj) / ((qi * (1 - qi) + qj * (1 - qj)) / n) ** 0.5
                    for i, (_, qi, n) in enumerate(pts) for (_, qj, _) in pts[i + 1:]), default=0)

    assert all(largest_drop(W) < 3 for W in (12, 13, 14))
    assert 5 < largest_drop(15) < 7
    assert all(largest_drop(W) > 15 for W in range(16, 24))


@pytest.mark.parametrize("shape", [(2, 5), (5, 2), (3, 3), (3, 4), (4, 3)])
def test_full_lane_rigidity_any_height(shape):
    """The Lean statements of `BML/ThinRigidity.lean`, on every state of an H×W torus.

    A jam with fewer than W east cars has a full north column, and with fewer than H north
    cars a full east row. A full north column with every north car in such a column jams, and
    likewise for east rows."""
    from bml.model import NORTH
    states = all_states(*shape)
    H, W = shape
    north_col = (states == NORTH).all(axis=1)          # (state, x)
    east_row = (states == EAST).all(axis=2)            # (state, y)
    n_east = (states == EAST).sum(axis=(1, 2))
    n_north = (states == NORTH).sum(axis=(1, 2))
    north_confined = ((states != NORTH) | north_col[:, None, :]).all(axis=(1, 2))
    east_confined = ((states != EAST) | east_row[:, :, None]).all(axis=(1, 2))
    j = np.asarray(jams(states), bool)
    assert north_col.any(axis=1)[j & (n_east < W)].all()
    assert east_row.any(axis=1)[j & (n_north < H)].all()
    assert j[north_col.any(axis=1) & north_confined].all()
    assert j[east_row.any(axis=1) & east_confined].all()
    assert (j & (n_east < W)).any() and (north_col.any(axis=1) & north_confined).any()


@pytest.mark.parametrize("shape", [(2, 5), (3, 3), (3, 4), (4, 3)])
def test_gap_east_count_any_height(shape):
    """`BML.gap_east_count_lower_bound`: in a state that jams, let G be a set of columns whose
    edges are full north columns, and let c, c+1, …, c+d−1 be non-full columns of G with a
    north car in c. Then G holds at least d east cars."""
    from bml.model import NORTH
    states = all_states(*shape)
    H, W = shape
    j = np.asarray(jams(states), bool)
    checked = 0
    for s in states[j]:
        plug = (s == NORTH).all(axis=0)
        cuts = [x for x in range(W) if plug[x]]
        gaps = ([list(range(W))] if not cuts else
                [[(a + 1 + i) % W for i in range((b - a - 1) % W)]
                 for a, b in zip(cuts, cuts[1:] + cuts[:1])])
        for gap in gaps:
            east = int((s[:, gap] == EAST).sum())
            for k, c in enumerate(gap):
                if (s[:, c] == NORTH).any():
                    d = W if not cuts else len(gap) - k
                    assert d <= east, (s, gap, c)
                    checked += 1
    assert checked
