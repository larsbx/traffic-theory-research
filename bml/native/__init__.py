"""Compiled exhaustive classifier (bml/native/classify.c), built on first use with gcc -fopenmp."""
from __future__ import annotations

import subprocess
from functools import lru_cache
from pathlib import Path

HERE = Path(__file__).parent
SRC, BIN = HERE / "classify.c", HERE / "classify"


@lru_cache(None)
def build() -> Path:
    if not BIN.exists() or BIN.stat().st_mtime < SRC.stat().st_mtime:
        subprocess.run(["gcc", "-O3", "-march=native", "-fopenmp", "-o", str(BIN), str(SRC)],
                       check=True)
    return BIN


def classify_counts(h: int, w: int) -> dict[int, dict[str, int]]:
    """Exact per-car-count counts {n: {'jam','free','mixed'}} over all 3^(wh) states."""
    out = subprocess.run([str(build()), str(w), str(h)], check=True, capture_output=True, text=True)
    table = {}
    for line in out.stdout.split("\n"):
        if line.strip():
            n, j, f, m = map(int, line.split())
            table[n] = {"jam": j, "free": f, "mixed": m}
    return table
