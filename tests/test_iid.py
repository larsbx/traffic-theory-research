"""Exact iid jam probabilities: Bernstein identities, and the finite monotonicity theorem."""
import json
from fractions import Fraction
from math import comb
from pathlib import Path

import pytest

from bml.iid import level_fractions, probability, derivative_bernstein, certified_nondecreasing

ROOT = Path(__file__).parents[1]
TABLES = json.loads((ROOT / "data" / "exhaustive.json").read_text())
ADDS = {(r["h"], r["w"]): r for r in json.loads((ROOT / "data" / "jam-additions.json").read_text())}


def jam_counts(r):
    return {int(n): v["jam"] for n, v in r["table"].items()}


def not_free_counts(r):
    return {int(n): v["jam"] + v["mixed"] for n, v in r["table"].items()}


@pytest.mark.parametrize("r", TABLES, ids=lambda r: f"{r['h']}x{r['w']}")
def test_bernstein_form_matches_direct_sum_and_derivative(r):
    N = r["h"] * r["w"]
    c = jam_counts(r)
    b = level_fractions(c, N)
    for p in (Fraction(1, 7), Fraction(1, 2), Fraction(5, 6)):
        bern = sum(b[n] * comb(N, n) * p ** n * (1 - p) ** (N - n) for n in range(N + 1))
        assert bern == probability(c, N, p)
    # P′ via Bernstein coefficients agrees with a symmetric difference quotient on a polynomial
    d = derivative_bernstein(c, N)
    p, eps = Fraction(1, 3), Fraction(1, 10**6)
    dq = (probability(c, N, p + eps) - probability(c, N, p - eps)) / (2 * eps)
    dp = sum(d[n] * comb(N - 1, n) * p ** n * (1 - p) ** (N - 1 - n) for n in range(N))
    assert abs(dq - dp) < Fraction(1, 10**6)
    assert probability(c, N, Fraction(1)) == 1          # full occupancy always jams


@pytest.mark.parametrize("r", TABLES, ids=lambda r: f"{r['h']}x{r['w']}")
def test_finite_iid_monotonicity_theorem(r):
    """On every torus with WH ≤ 16 the jam fraction b_n, and the fraction never reaching
    free flow, are nondecreasing in n. So both iid probabilities are nondecreasing in p."""
    N = r["h"] * r["w"]
    assert certified_nondecreasing(jam_counts(r), N)
    assert certified_nondecreasing(not_free_counts(r), N)


@pytest.mark.parametrize("r", TABLES, ids=lambda r: f"{r['h']}x{r['w']}")
def test_addition_identity(r):
    """b_{n+1} − b_n = (jam-creating − jam-destroying single-car additions at level n) / #pairs."""
    h, w = r["h"], r["w"]; N = h * w
    b = level_fractions(jam_counts(r), N)
    a = ADDS[(h, w)]
    for n in range(N):
        pairs = comb(N, n) * 2 ** n * 2 * (N - n)
        assert b[n + 1] - b[n] == Fraction(a["create"][n] - a["destroy"][n], pairs)
        assert a["create"][n] >= a["destroy"][n]
