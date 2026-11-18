"""Independent exact maximum of free-flow car counts (checks Theorem F beyond exhaustive sizes).

Uses Lemma R: free flow ⟺ C1 (no E directly west of E), C2 (no N directly south of N), and
C3 (with A, B the classes φ = x+y mod g of E and N cars: A ∩ B = ∅ and (A+1) ∩ B = ∅).
For each admissible class labelling, a max-plus transfer matrix over rows maximises the count
on the cyclic stack of rows. No step of the Theorem F packing argument is used.
"""
from __future__ import annotations

import itertools
from math import gcd

import numpy as np

NEG = -10**9


def max_free_exact(h: int, w: int) -> int:
    g = gcd(h, w)
    rows = np.array([r for r in itertools.product((0, 1, 2), repeat=w)
                     if not any(r[x] == 1 and r[(x + 1) % w] == 1 for x in range(w))])
    cnt = (rows != 0).sum(1)
    vert_ok = ~((rows[:, None, :] == 2) & (rows[None, :, :] == 2)).any(-1)
    best = 0
    for lab in itertools.product("AB.", repeat=g):
        if any(lab[c] == "A" and lab[(c + 1) % g] == "B" for c in range(g)):
            continue
        allowed = []
        for y in range(h):
            cls = np.array([lab[(x + y) % g] for x in range(w)])
            allowed.append(((rows != 1) | (cls == "A")).all(1) & ((rows != 2) | (cls == "B")).all(1))
        trans = [np.where(allowed[y][:, None] & allowed[(y + 1) % h][None, :] & vert_ok,
                          cnt[None, :], NEG) for y in range(h)]
        for s0 in np.nonzero(allowed[0])[0]:
            v = np.full(len(rows), NEG); v[s0] = cnt[s0]
            for y in range(h - 1):
                v = (v[:, None] + trans[y]).max(0)
            best = max(best, int(np.where(allowed[h - 1] & vert_ok[:, s0], v, NEG).max()))
    return best
