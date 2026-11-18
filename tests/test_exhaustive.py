"""bml.exhaustive must agree with naive orbit-following on every state of small tori."""
import numpy as np
import pytest

from bml.model import step, counts
from bml.exhaustive import decode, encode, JAM, FREE, MIXED, classify_all

SHAPES = [(h, w) for h in range(1, 10) for w in range(1, 10) if h * w <= 9]


def naive_class(s):
    seen, orbit = {}, []
    while (key := s.tobytes()) not in seen:
        seen[key] = len(orbit)
        nxt, m = step(s)
        orbit.append(int(m))
        s = nxt
    cyc = orbit[seen[key]:]
    n = sum(counts(s))
    return FREE if n == 0 else JAM if max(cyc) == 0 else FREE if min(cyc) == n else MIXED


@pytest.mark.parametrize("h,w", SHAPES)
def test_encode_decode_roundtrip(h, w):
    idx = np.arange(3 ** (h * w), dtype=np.int64)
    assert (encode(decode(idx, h, w)) == idx).all()


@pytest.mark.parametrize("h,w", SHAPES)
def test_classification_matches_naive(h, w):
    res = classify_all(h, w)
    states = decode(np.arange(3 ** (h * w), dtype=np.int64), h, w)
    assert [naive_class(s) for s in states] == res.cls.tolist()
