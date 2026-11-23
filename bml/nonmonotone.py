"""Non-monotonicity with car identities: x gridlocks, y = x + one car does not, and some
*original* car of x moves infinitely often in y (so the un-jamming is not merely the added
car circulating on its own)."""
from __future__ import annotations

import sys

import numpy as np

from bml.model import CLASSIC, EAST, NORTH, AXIS, movers_mask
from bml.exhaustive import JAM, classify_all, decode


def labelled_step(s, ids, rule=CLASSIC):
    moved = set()
    for sp in (EAST, NORTH):
        ax, mv = AXIS[sp], movers_mask(s, sp, rule)
        moved |= set(ids[mv].tolist())
        s = np.where(np.roll(mv, 1, axis=ax), sp, np.where(mv, 0, s)).astype(np.int8)
        ids = np.where(np.roll(mv, 1, axis=ax), np.roll(ids, 1, axis=ax), np.where(mv, -1, ids))
    return s, ids, moved


def recurrent_movers(s, rule=CLASSIC):
    """Ids of cars that move on the terminal cycle (car i starts at the i-th occupied cell)."""
    ids = np.full(s.shape, -1)
    ids[s != 0] = np.arange(int((s != 0).sum()))
    seen = set()
    while (k := s.tobytes()) not in seen:
        seen.add(k)
        s, ids, _ = labelled_step(s, ids, rule)
    start, moved = s.tobytes(), set()
    while True:
        s, ids, m = labelled_step(s, ids, rule)
        moved |= m
        if s.tobytes() == start:
            return moved


def witnesses(h, w, limit=None, rule=CLASSIC):
    """Yield (x, y, cell, original_movers) for non-trivial un-jamming pairs."""
    c = classify_all(h, w, rule)
    idx = np.arange(len(c.cls), dtype=np.int64)
    found = 0
    for i in range(h * w):
        for sp in (EAST, NORTH):
            x = idx[(c.cls == JAM) & (((idx // 3 ** i) % 3) == 0)]
            y = x + sp * 3 ** i
            for xi, yi in zip(x[c.cls[y] != JAM], y[c.cls[y] != JAM]):
                ys = decode(np.array([yi]), h, w)[0]
                new_id = int((ys.reshape(-1) != 0)[:i].sum())       # id of the added car
                orig = recurrent_movers(ys, rule) - {new_id}
                if orig:
                    yield decode(np.array([xi]), h, w)[0], ys, (i // w, i % w), sorted(orig)
                    found += 1
                    if limit and found >= limit:
                        return


if __name__ == "__main__":
    h, w = int(sys.argv[1]), int(sys.argv[2])
    total = trivial = 0
    best = None
    for x, y, cell, orig in witnesses(h, w):
        total += 1
        if best is None or int((x != 0).sum()) < int((best[0] != 0).sum()):
            best = (x, y, cell, orig)
    print(f"{h}x{w}: non-trivial un-jamming pairs = {total}")
    if best:
        sym = {0: ".", 1: ">", 2: "^"}
        for name, g in (("x (jams)", best[0]), ("y = x + car (flows)", best[1])):
            print(name); print("\n".join("".join(sym[v] for v in row) for row in g[::-1]))
        print("added at (y,x) =", best[2], "original cars still moving:", best[3])


def gated_witness(h: int, w: int):
    """Genuine un-jamming pair (x, y, added_cell) for min(h, w) >= 2 and max(h, w) >= 4.

    Columns family (w >= 4): column 0 is a full N ring minus (x,y) = (0,0), column 1 holds a
    single N car at row 0, column 2 is a full N ring, column w-1 is a full E column. y adds
    an N car at (0,0), which closes the gate. Rows family (h >= 4, used when w < 4): the same
    with rows for columns and species swapped. See docs/theorems.md §4 (Theorem U).
    """
    from bml.model import EAST, NORTH
    assert min(h, w) >= 2 and max(h, w) >= 4
    x = np.zeros((h, w), np.int8)
    if w >= 4:
        x[:, 0] = NORTH; x[0, 0] = 0
        x[0, 1] = NORTH
        x[:, 2] = NORTH
        x[:, w - 1] = EAST
        sp = NORTH
    else:
        x[0, :] = EAST; x[0, 0] = 0
        x[1, 0] = EAST
        x[2, :] = EAST
        x[h - 1, :] = NORTH
        sp = EAST
    y = x.copy(); y[0, 0] = sp
    return x, y, (0, 0)
