"""Exhaustive phase tables and worst-case thresholds for all tori with W·H ≤ 16."""
from __future__ import annotations

import json
import sys

import numpy as np

from bml.exhaustive import JAM, FREE, MIXED, classify_all, decode

NAMES = {JAM: "jam", FREE: "free", MIXED: "mixed"}


def phase_table(c):
    n = c.n_east.astype(int) + c.n_north
    return {int(k): {NAMES[v]: int(((n == k) & (c.cls == v)).sum()) for v in NAMES}
            for k in range(c.h * c.w + 1)}


def thresholds(table, cells):
    has = lambda k, name: table[k][name] > 0
    only_jam = lambda k: table[k]["free"] == table[k]["mixed"] == 0
    return {
        "n_jam_min": min(k for k in table if k > 0 and has(k, "jam")),
        "n_free_max": max(k for k in table if has(k, "free")),
        "n_mixed": [k for k in table if has(k, "mixed")],
        "n_all_jam_from": min(k for k in range(1, cells + 1)
                              if all(only_jam(j) for j in range(k, cells + 1))),
    }


def monotonicity(c):
    """Pairs (x, x + one car): how often does adding a car turn JAM into non-JAM?"""
    size, cells = len(c.cls), c.h * c.w
    idx = np.arange(size, dtype=np.int64)
    unjam, witness = 0, None
    for i in range(cells):
        empty = ((idx // 3 ** i) % 3) == 0
        for sp in (1, 2):
            x = idx[empty]
            y = x + sp * 3 ** i
            bad = (c.cls[x] == JAM) & (c.cls[y] != JAM)
            unjam += int(bad.sum())
            if witness is None and bad.any():
                k = int(np.argmax(bad))
                witness = [decode(np.array([x[k]]), c.h, c.w)[0].tolist(),
                           decode(np.array([y[k]]), c.h, c.w)[0].tolist(),
                           NAMES[int(c.cls[y[k]])]]
    return {"jam_to_nonjam_by_adding_one_car": unjam, "witness": witness}


def run(h, w):
    c = classify_all(h, w)
    table = phase_table(c)
    return {"h": h, "w": w, "table": table, **thresholds(table, h * w), **monotonicity(c)}


if __name__ == "__main__":
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    out = [run(h, w) for h in range(1, limit + 1) for w in range(1, limit + 1) if h * w <= limit]
    json.dump(out, open("data/exhaustive.json", "w"), indent=1)
    for r in out:
        print(f"{r['h']}x{r['w']}: jam_min={r['n_jam_min']} free_max={r['n_free_max']} "
              f"all_jam_from={r['n_all_jam_from']} mixed_n={r['n_mixed']} "
              f"unjam_by_adding={r['jam_to_nonjam_by_adding_one_car']}")
