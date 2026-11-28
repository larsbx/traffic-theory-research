"""B10.5 exact finite correspondence. Run from the repository root with pytest.
Independent word enumeration, marked-block encoding and integer DP comparisons.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import comb

import numpy as np
from bml.thin import gap_condition, gap_event, gap_ok, upper

P = (2, 2)
COLS = tuple(product(range(3), repeat=2))
NONPLUG = tuple(c for c in COLS if c != P)


def good_gap(gap):
    return (P not in gap and
            sum(c.count(1) for c in gap) >=
            max((i for i, c in enumerate(gap, 1) if 2 in c), default=0))


def direct_event(word):
    """Eastward traversal between consecutive plugs (not the block codec)."""
    w = len(word)
    plugs = [i for i, c in enumerate(word) if c == P]
    if not plugs:
        return False
    for a, b in zip(plugs, plugs[1:] + plugs[:1]):
        g = (b - a - 1) % w
        gap = tuple(word[(a + i) % w] for i in range(1, g + 1))
        if sum(c.count(1) for c in gap) < max(
                (g-i for i, c in enumerate(gap) if 2 in c), default=0):
            return False
    return True


def encode(word):
    """Unique block containing index zero; then traverse west around the ring."""
    w = len(word)
    if not w or P not in word:
        raise ValueError('nonempty ring with a plug required')
    offset = next(i for i in range(w) if word[i] == P)
    linear = tuple(word[(offset-i) % w] for i in range(w))
    starts = [i for i, c in enumerate(linear) if c == P] + [w]
    blocks = tuple(linear[a:b] for a, b in zip(starts, starts[1:]))
    if not all(good_gap(b[1:]) for b in blocks):
        raise ValueError('invalid gap')
    assert offset < len(blocks[0])
    return offset, blocks


def decode(offset, blocks):
    if not blocks or any(not b or b[0] != P or not good_gap(b[1:]) for b in blocks):
        raise ValueError('invalid blocks')
    if not 0 <= offset < len(blocks[0]):
        raise ValueError('invalid mark')
    linear = tuple(c for b in blocks for c in b)
    w = len(linear)
    word = [None] * w
    for i, c in enumerate(linear):
        word[(offset-i) % w] = c
    return tuple(word)


def sequences(n):
    if n == 0:
        yield ()
    else:
        for l in range(1, n+1):
            for gap in product(NONPLUG, repeat=l-1):
                if good_gap(gap):
                    for rest in sequences(n-l):
                        yield ((P,) + gap,) + rest


def counts(word):
    return sum(c.count(0) for c in word)


def mass(hist, w, p):
    return sum((n*(1-p)**empty*(p/2)**(2*w-empty)
                for empty, n in hist.items()), F(0))


def recurrence(w, p):
    g = gap_ok(w, p)
    b = [F(0)] + [(p/2)**2 * x for x in g]
    c = [F(1)] + [F(0)]*w
    for m in range(1, w+1):
        c[m] = sum(b[l]*c[m-l] for l in range(1,m+1))
    return [l*b[l]*c[w-l] for l in range(1,w+1)], c[w]


def test_all_labelled_rings_and_inverse():
    densities = [F(0), F(1,7), F(1,2), F(9,10), F(1)]
    for w in range(1,5):
        hist = Counter()
        by_len = [Counter() for _ in range(w)]
        seen = set()
        for word in product(COLS, repeat=w):
            direct = direct_event(word)
            board = np.array(word, dtype=np.int8).T
            assert gap_condition(board) == direct
            if w != 2:
                mirrored = np.where(board.T == 1, 2, np.where(board.T == 2, 1, 0))
                assert gap_condition(mirrored) == direct
            if not direct:
                try:
                    encode(word)
                except ValueError:
                    continue
                raise AssertionError('invalid event encoded')
            code = encode(word)
            assert decode(*code) == word and code not in seen
            seen.add(code)
            hist[counts(word)] += 1
            by_len[len(code[1][0])-1][counts(word)] += 1
        # Exhaust the other direction independently, including repeated blocks.
        generated = {(i, blocks) for blocks in sequences(w) for i in range(len(blocks[0]))}
        assert seen == generated
        for code in generated:
            assert encode(decode(*code)) == code
        for p in densities:
            terms, c = recurrence(w,p)
            assert terms == [mass(h,w,p) for h in by_len]
            assert sum(terms) == mass(hist,w,p) == gap_event(w,p)
            assert sum(terms) <= w*c
            tail = sum(F(comb(2*w,k))*(p/2)**k*(1-p/2)**(2*w-k)
                       for k in range(w,2*w+1))
            assert upper(w,p) == tail+sum(terms)


def test_raw_gap_and_negative_controls():
    for g in range(5):
        hist = Counter(counts(gap) for gap in product(NONPLUG,repeat=g) if good_gap(gap))
        for p in (F(0),F(2,7),F(1,2),F(1)):
            assert gap_ok(g+1,p)[g] == mass(hist,g,p)
            assert mass(hist,g,p) <= (1-(p/2)**2)**g
    p = F(1,2)
    a = (p/2)**2
    g1 = 1-a-p*(1-p)
    assert gap_ok(2,p)[1] == g1 == F(11,16)
    assert g1/(1-a) != g1  # conditional normalization is not allowed
    assert gap_event(2,p) == a*a+2*a*g1
    assert gap_event(2,p) != a*a+a*g1  # omitting mark factor
    assert not direct_event((P,(2,0)))  # lone+empty isolated gap
    assert direct_event((P,(2,1)))
    assert not direct_event(((1,0),(1,0)))  # no plug, even though no lone
    assert encode((P,P,P)) == (0,((P,),(P,),(P,)))
    assert encode(((0,0),(0,0),P))[0] == 2
    # Orientation-sensitive: one lone at distance 2 versus distance 1.
    assert not direct_event((P,(2,1),(0,0)))
    assert direct_event((P,(0,0),(2,1)))


def test_forbidden_triple_bound():
    for p in (F(1,10), F(1,2), F(9,10)):
        a = (p/2)**2
        delta = a*a*p*(1-p)
        assert 0 < delta < 1
        for w in (3,6,9,12,24):
            assert gap_event(w,p) <= (1-delta)**(w//3)


def classic_step(word):
    """Independent synchronous E-then-N update on ordered column pairs."""
    w = len(word)
    east = [list(c) for c in word]
    for x, col in enumerate(word):
        for y, cell in enumerate(col):
            if cell == 1 and word[(x+1)%w][y] == 0:
                east[x][y] = 0
                east[(x+1)%w][y] = 1
    north = [c[:] for c in east]
    for x, col in enumerate(east):
        for y, cell in enumerate(col):
            if cell == 2 and col[1-y] == 0:
                north[x][y] = 0
                north[x][1-y] = 2
    return tuple(map(tuple,north))


def test_independent_dynamics_and_forbidden_pattern():
    from functools import lru_cache
    @lru_cache(None)
    def jams(word):
        seen = set()
        while word not in seen:
            seen.add(word)
            nxt = classic_step(word)
            if nxt == word:
                return any(any(c) for c in word)
            word = nxt
        return False
    for w in range(1,5):
        hist = Counter()
        for word in product(COLS,repeat=w):
            j = jams(word)
            if j:
                assert sum(c.count(1) for c in word) >= w or direct_event(word)
                hist[counts(word)] += 1
            if w>=3 and any(word[x]==P and word[(x+1)%w] in ((0,2),(2,0))
                            and word[(x+2)%w]==P for x in range(w)):
                assert not j
        for p in (F(0),F(1,7),F(1,2),F(9,10),F(1)):
            q = mass(hist,w,p)
            delta = (p/2)**4*p*(1-p)
            assert q <= upper(w,p)
            assert q <= (1-delta)**(w//3)
            if p in (0,1):
                assert q == p
    # A high-east-count example: the new local obstruction is independent
    # of the global east tail (W=6, east count=6).
    high = (P,(2,0),P,(1,1),(1,1),(1,1))
    assert sum(c.count(1) for c in high) == len(high)
    assert not jams(high)
