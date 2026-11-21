"""Write or verify data/thin-nonmonotone.json: exact non-monotonicity certificates for q on 2×W.

    python scripts/thin_certificates.py --write    # search grids, then check exactly
    python scripts/thin_certificates.py            # recheck every stored certificate exactly
"""
import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from bml.thin import asymptotic_certificate, certificate, find_certificate  # noqa: E402

DATA = Path(__file__).resolve().parents[1] / "data" / "thin-nonmonotone.json"
W_MIN, W1 = 24, 80
ASYMPTOTIC = dict(p2=Fraction(7, 20), theta=Fraction(7, 5), z=Fraction(117, 100), W1=W1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()
    if args.write:
        certs = [find_certificate(W) for W in range(W_MIN, W1)]
        out = dict(rule="CLASSIC", shape="2xW and Wx2", W_min=W_MIN, W1=W1,
                   finite=certs, asymptotic=asymptotic_certificate(**ASYMPTOTIC))
        DATA.write_text(json.dumps(out, indent=1) + "\n")
    data = json.loads(DATA.read_text())
    ok = all(certificate(c["W"], c["p1"], c["p2"])["holds"] for c in data["finite"])
    ok &= [c["W"] for c in data["finite"]] == list(range(data["W_min"], data["W1"]))
    a = data["asymptotic"]
    ok &= asymptotic_certificate(a["p2"], a["theta"], a["z"], a["W1"], a["K"])["holds"]
    ok &= a["W1"] == data["W1"]
    print(f"thin-torus certificates W = {data['W_min']}..{data['W1'] - 1} exact, W >= {data['W1']} "
          f"asymptotic: {'OK' if ok else 'FAILED'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
