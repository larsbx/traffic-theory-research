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


def test_monotonicity_extends_to_2x9():
    """Exact per-level counts on 2×9 (3^18 states, from bml.exhaustive.classify_all):
    both fractions remain nondecreasing at 18 cells."""
    d = json.loads((ROOT / "data" / "exhaustive-2x9.json").read_text())
    N = 18
    jam = dict(enumerate(d["jam"]))
    not_free = {n: j + m for n, (j, m) in enumerate(zip(d["jam"], d["mixed"]))}
    assert sum(comb(N, n) * 2 ** n for n in range(N + 1)) == 3 ** N
    assert jam[N] == 2 ** N and certified_nondecreasing(jam, N) and certified_nondecreasing(not_free, N)


@pytest.mark.parametrize("h,w,n", [(2, 8, 4), (2, 8, 5), (3, 4, 6), (4, 3, 7), (3, 3, 5)])
def test_rooted_level_counter_matches_exhaustive(h, w, n):
    from bml.levels import level_jam_count
    r = next(r for r in TABLES if (r["h"], r["w"]) == (h, w))
    assert level_jam_count(h, w, n) == r["table"][str(n)]["jam"]


def test_fixed_count_monotonicity_fails_on_thin_tori():
    """Exact counts from bml.levels (minutes to recompute). On 2×11, 2×12 and 2×14,
    b_7 < b_6, so jam probability is NOT monotone in the car count in general. On 2×10,
    levels 5–8 are still nondecreasing."""
    d = {(r["h"], r["w"]): r for r in json.loads((ROOT / "data" / "level-counterexample.json").read_text())}
    def b(h, w):
        N = h * w
        return {int(n): Fraction(j, comb(N, int(n)) * 2 ** int(n))
                for n, j in d[(h, w)]["jam_by_level"].items()}
    for hw in [(2, 11), (2, 12), (2, 14)]:
        assert b(*hw)[7] < b(*hw)[6]
    b10 = b(2, 10)
    assert b10[5] <= b10[6] <= b10[7] <= b10[8]


@pytest.mark.parametrize("h,w", [(2, 2), (2, 3), (3, 3)])
def test_jams_agrees_with_classifier_on_every_state(h, w):
    """bml.levels.jams vs bml.exhaustive.classify_all on whole tori, empty state included."""
    import numpy as np
    from bml.exhaustive import classify_all, decode, JAM
    from bml.levels import jams
    c = classify_all(h, w)
    states = decode(np.arange(3 ** (h * w), dtype=np.int64), h, w)
    assert (jams(states) == (c.cls == JAM)).all()


EXT = (json.loads((ROOT / "data" / "exhaustive-17-22.json").read_text())
       + json.loads((ROOT / "data" / "exhaustive-24-25.json").read_text()))


@pytest.mark.parametrize("h,w", [(2, 3), (3, 3), (2, 4), (3, 4), (4, 4), (2, 8), (1, 7)])
def test_native_classifier_matches_numpy_tables(h, w):
    """bml/native/classify.c (translation quotient, Floyd per orbit) vs bml.exhaustive tables."""
    from bml.native import classify_counts
    r = next(r for r in TABLES if (r["h"], r["w"]) == (h, w))
    assert classify_counts(h, w) == {int(n): v for n, v in r["table"].items()}


@pytest.mark.parametrize("r", EXT, ids=lambda r: f"{r['h']}x{r['w']}")
def test_extended_tables_17_to_25_cells(r):
    """Exhaustive tables for every shape with 17–22 cells and the 24/25-cell shapes (bml.native): totals, G1, F, and the
    monotonicity facts recorded in the finite iid monotonicity note."""
    from bml.extremal import max_free, min_gridlock
    from bml.iid import certify_positive_derivative
    h, w = r["h"], r["w"]; N = h * w
    t = {int(n): v for n, v in r["table"].items()}
    assert sum(sum(v.values()) for v in t.values()) == 3 ** N
    assert min(n for n in t if n > 0 and t[n]["jam"]) == min_gridlock(h, w)
    assert max(n for n in t if t[n]["free"]) == max_free(h, w)
    jam = {n: v["jam"] for n, v in t.items()}
    not_free = {n: v["jam"] + v["mixed"] for n, v in t.items()}
    assert certified_nondecreasing(not_free, N)
    if (h, w) in {(2, 11), (11, 2), (2, 12), (12, 2)}:
        b = level_fractions(jam, N)
        assert b[7] < b[6] and not certified_nondecreasing(jam, N)
        assert certify_positive_derivative(jam, N) is not None      # yet q(p) is increasing
    else:
        assert certified_nondecreasing(jam, N)


def test_positivity_certificate_rejects_a_decreasing_polynomial():
    """Negative control: the 3×3 mixed-cycle probability decreases near p = 1."""
    from bml.iid import certify_positive_derivative
    assert certify_positive_derivative({6: 384, 7: 1872, 8: 1062, 9: 174}, 9, max_elevations=300) is None


def test_positivity_certificate_edge_cases():
    """Codex review on #32: constant probabilities and a vanishing derivative at p = 1."""
    from bml.iid import certify_positive_derivative
    assert certify_positive_derivative({}, 3) is None                       # impossible event
    assert certify_positive_derivative({0: 1, 1: 4, 2: 4}, 2) is None       # certain event
    assert certify_positive_derivative({1: 2, 2: 2}, 2) is None             # P = p − p²/2, P′(1) = 0
    assert certify_positive_derivative({1: 2, 2: 4}, 2) is not None         # P = p, P′ = 1
