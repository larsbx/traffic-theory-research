"""Compiled kernels, built on first use with gcc:
classify.c (exhaustive classifier, -fopenmp) and thin_mc.c (2×W Monte Carlo)."""
from __future__ import annotations

import subprocess
from functools import lru_cache
from pathlib import Path

HERE = Path(__file__).parent


@lru_cache(None)
def build(name: str = "classify") -> Path:
    src, binary = HERE / f"{name}.c", HERE / name
    if not binary.exists() or binary.stat().st_mtime < src.stat().st_mtime:
        subprocess.run(["gcc", "-O3", "-march=native", "-fopenmp", "-o", str(binary), str(src)],
                       check=True)
    return binary


def classify_counts(h: int, w: int) -> dict[int, dict[str, int]]:
    """Exact per-car-count counts {n: {'jam','free','mixed'}} over all 3^(wh) states."""
    out = subprocess.run([str(build()), str(w), str(h)], check=True, capture_output=True, text=True)
    table = {}
    for line in out.stdout.split("\n"):
        if line.strip():
            n, j, f, m = map(int, line.split())
            table[n] = {"jam": j, "free": f, "mixed": m}
    return table


def thin_jam_count(w: int, p: float, samples: int, seed: int = 0) -> tuple[int, int]:
    """(jams, samples) for iid samples on the 2×w torus, each classified exactly."""
    out = subprocess.run([str(build("thin_mc")), str(w), repr(p), str(samples), str(seed)],
                         check=True, capture_output=True, text=True)
    j, n = map(int, out.stdout.split())
    return j, n
