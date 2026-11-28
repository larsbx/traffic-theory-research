"""Exact jam probability of the 2×W torus by gap decomposition (bml.thin_exact).

    python scripts/thin_exact.py                      # verify every stored claim (seconds)
    python scripts/thin_exact.py --gaps 14            # recompute data/thin-gap-jams.json, g ≤ 14
    python scripts/thin_exact.py --noplug 2 ... 14    # recompute data/thin-noplug-jams.json

Recomputation is long: gap g = 14 takes about 2 h and plug-free W = 14 about an hour on 4 cores.
Verification checks:
  1. the exact counts reproduce every exhaustive 2×W table (W ≤ 12), level by level;
  2. q is strictly increasing on (0, 1] wherever the plug-free class was classified;
  3. q is not monotone on 2×15, from the plug part alone (NONMONOTONE below).
"""
import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from bml.iid import certify_positive_derivative  # noqa: E402
from bml.native import build  # noqa: E402
from bml.thin_exact import GAPS, NOPLUG, _noplug, jam_counts, nonmonotone_certificate  # noqa: E402

NONMONOTONE = dict(W=15, p1="1/5", p2="13/40")


def run(name, *args):
    out = subprocess.run([str(build(name)), *map(str, args)], check=True, capture_output=True,
                         text=True).stdout
    return [list(map(int, line.split())) for line in out.split("\n") if line.strip()]


def exhaustive_2xW():
    out = {}
    for name in ("exhaustive.json", "exhaustive-17-22.json", "exhaustive-24-25.json"):
        for r in json.loads((ROOT / "data" / name).read_text()):
            if r["h"] == 2:
                out[r["w"]] = {int(n): v["jam"] for n, v in r["table"].items()}
    return out


def verify() -> bool:
    ok = True
    tables = exhaustive_2xW()
    widths = sorted(_noplug())
    for W in widths:
        counts = jam_counts(W)
        if W in tables:
            match = all(counts[n] == tables[W].get(n, 0) for n in range(2 * W + 1))
            print(f"2x{W}: exact counts {'match' if match else 'DIFFER FROM'} the exhaustive table")
            ok &= match
        else:
            e = certify_positive_derivative(counts, 2 * W)
            print(f"2x{W}: q strictly increasing on (0,1]: "
                  f"{'certified, ' + str(e) + ' degree raises' if e is not None else 'NOT certified'}")
            ok &= e is not None
    c = nonmonotone_certificate(**NONMONOTONE)
    print(f"2x{c['W']}: q({c['p1']}) >= {c['lower']:.6f} > {c['upper']:.6f} >= q({c['p2']}): {c['holds']}")
    return ok and c["holds"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--gaps", type=int)
    ap.add_argument("--noplug", type=int, nargs="*")
    args = ap.parse_args()
    if args.gaps is not None:
        rows = {g: [j for _, j in run("gap_jam", g)] for g in range(args.gaps + 1)}
        GAPS.write_text(json.dumps(dict(source="bml/native/gap_jam.c", lone_jams=rows)) + "\n")
    if args.noplug:
        data = {W: dict(jam=[j for _, j, _ in r], seen=[s for _, _, s in r])
                for W in args.noplug for r in [run("noplug_jam", W)]}
        NOPLUG.write_text(json.dumps(dict(source="bml/native/noplug_jam.c", by_width=data)) + "\n")
    sys.exit(0 if verify() else 1)


if __name__ == "__main__":
    main()
