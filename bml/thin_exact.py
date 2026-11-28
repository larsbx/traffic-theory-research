"""Thin tori, exactly: jam counts of the 2×W torus from independent gaps.

Once a configuration has a plug, its gaps evolve independently. Plug cells never change, no car
crosses a plug column (bml.thin, Lemma 1), and a gap's dynamics reads only its own cells. So the
jamming configurations with a plug are the cyclic plug/gap compositions in which every gap jams:
a renewal sum over blocks (plug = two N cars) × (jamming gap of length l − 1). Gap jam counts by
car number come from the exact enumeration in ``bml/native/gap_jam.c``
(data/thin-gap-jams.json).

Without a plug, a jam needs a winding blocking cycle, hence at least W east cars (bml.thin,
Lemma 2). That "heavy" class is classified exactly by ``bml/native/noplug_jam.c``, one
translation class at a time (data/thin-noplug-jams.json). Where that data is missing, it is
bounded by the size of the class:

    plug_jam(W, p)  ≤  q_W(p)  ≤  plug_jam(W, p) + P(no plug ∧ #E ≥ W).

Counts are integers; probabilities are exact rationals.
"""
from __future__ import annotations

import json
from fractions import Fraction
from functools import lru_cache
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
GAPS = ROOT / "data" / "thin-gap-jams.json"            # bml/native/gap_jam.c
NOPLUG = ROOT / "data" / "thin-noplug-jams.json"       # bml/native/noplug_jam.c


def _pmul(a: list[int], b: list[int]) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def _padd(a: list[int], b: list[int]) -> list[int]:
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def probability(counts: list[int], W: int, p) -> Fraction:
    """iid probability of a set of 2×W configurations given by its counts per car number."""
    p = Fraction(p)
    return sum((c * (p / 2) ** n * (1 - p) ** (2 * W - n) for n, c in enumerate(counts)), Fraction(0))


@lru_cache(None)
def gap_jam_counts() -> dict[int, list[int]]:
    """{g: [jamming gap states with k cars, k = 0 … 2g]}. The data lists the states that contain
    a lone column; the C(2g, k) lone-free states all jam (bml.thin, Lemma 4)."""
    raw = json.loads(GAPS.read_text())["lone_jams"]
    return {int(g): [comb(2 * int(g), k) + j for k, j in enumerate(row)] for g, row in raw.items()}


def plug_jam_counts(W: int) -> list[int]:
    """Number of n-car configurations of 2×W that have a plug and jam, n = 0 … 2W."""
    J = gap_jam_counts()
    b = [[0]] + [_pmul([0, 0, 1], J[l - 1]) for l in range(1, W + 1)]   # plug = two N cars
    c = [[1]] + [[0]] * W
    for m in range(1, W + 1):
        acc = [0]
        for l in range(1, m + 1):
            acc = _padd(acc, _pmul(b[l], c[m - l]))
        c[m] = acc
    tot = [0]
    for l in range(1, W + 1):                                # the block covering column 0
        tot = _padd(tot, [l * x for x in _pmul(b[l], c[W - l])])
    return (tot + [0] * (2 * W + 1))[:2 * W + 1]


def heavy_counts(W: int) -> list[int]:
    """Number of n-car configurations of 2×W with no plug and at least W east cars."""
    types = [(0, 0, 1), (0, 1, 2), (1, 1, 2), (1, 2, 2), (2, 2, 1)]   # (E, cars, multiplicity)
    dist = {(0, 0): 1}
    for _ in range(W):
        new: dict = {}
        for (e, n), w in dist.items():
            for de, dn, m in types:
                new[(e + de, n + dn)] = new.get((e + de, n + dn), 0) + w * m
        dist = new
    out = [0] * (2 * W + 1)
    for (e, n), w in dist.items():
        if e >= W:
            out[n] += w
    return out


def sandwich(W: int, p) -> tuple[Fraction, Fraction]:
    lo = probability(plug_jam_counts(W), W, p)
    return lo, lo + probability(heavy_counts(W), W, p)


def nonmonotone_certificate(W: int, p1, p2) -> dict:
    """q(p1) ≥ plug part(p1) > plug part(p2) + heavy class(p2) ≥ q(p2), with p1 < p2."""
    p1, p2 = Fraction(p1), Fraction(p2)
    lo, hi = sandwich(W, p1)[0], sandwich(W, p2)[1]
    return dict(W=W, p1=str(p1), p2=str(p2), lower=float(lo), upper=float(hi),
                holds=bool(p1 < p2 and lo > hi))


@lru_cache(None)
def _noplug() -> dict:
    return {int(W): v for W, v in json.loads(NOPLUG.read_text())["by_width"].items()}


def jam_counts(W: int) -> dict[int, int]:
    """Exact number of jamming n-car configurations of 2×W (needs plug-free data for W)."""
    plug, free = plug_jam_counts(W), _noplug()[W]
    assert free["seen"] == heavy_counts(W)          # the enumeration covered the whole class
    return {n: plug[n] + free["jam"][n] for n in range(2 * W + 1)}
