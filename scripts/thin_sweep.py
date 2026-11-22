"""Monte Carlo evidence below the certified range: q on 2×W, W = 12..23 (data/thin-monte-carlo.json).

Each sample is classified exactly (Floyd cycle detection in bml/native/thin_mc.c); seeds are fixed.
Evidence only. Runtime about 10 minutes on 4 cores.
"""
import json
import sys
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from bml.native import build, thin_jam_count  # noqa: E402

PS = [round(0.025 * k, 3) for k in range(2, 25)]
SAMPLES = 4_000_000


def run(job):
    W, p = job
    j, n = thin_jam_count(W, p, SAMPLES, seed=1000 * W + int(p * 1000))
    return dict(W=W, p=p, jams=j, samples=n)


if __name__ == "__main__":
    build("thin_mc")
    with ProcessPoolExecutor(4) as ex:
        rows = list(ex.map(run, [(W, p) for W in range(12, 24) for p in PS]))
    (ROOT / "data" / "thin-monte-carlo.json").write_text(json.dumps(rows, indent=0) + "\n")
