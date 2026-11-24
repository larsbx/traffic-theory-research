"""Summarise docs/research/data/2026-11-24-sumo.json against the theorems (R1, R2, R5).
    python sumo/analyze.py
"""
from __future__ import annotations

import json
import pathlib
import statistics as st
from collections import Counter, defaultdict

DATA = pathlib.Path(__file__).resolve().parent.parent / "docs" / "research" / "data" / "2026-11-24-sumo.json"


def summarise(results):
    out = {}
    # R5: lambda * meanTrip <= distRate in every run; ratio near 1 when nothing is stuck
    ratios = [(r["lambda"] * r["meanTrip"] / r["distRate"], r["stuck600"] / max(1, r["running"])) for r in results if r["distRate"] > 0]
    out["R5"] = {
        "runs": len(ratios),
        "violations": sum(q > 1 + 1e-9 for q, _ in ratios),
        "maxRatio": max(q for q, _ in ratios),
        "meanRatioNoStuck": st.mean([q for q, s in ratios if s == 0]) if any(s == 0 for _, s in ratios) else None,
        "meanRatioStuck": st.mean([q for q, s in ratios if s > 0]) if any(s > 0 for _, s in ratios) else None,
        "runsNoStuck": sum(s == 0 for _, s in ratios),
    }
    # R2: paired fixed vs rerouting
    pairs = defaultdict(dict)
    for r in results:
        pairs[(r["place"], r["period"], r["seed"])][r["reroute"]] = r
    rows = []
    for (place, period, seed), d in sorted(pairs.items()):
        if False in d and True in d:
            rows.append({"place": place, "period": period, "seed": seed,
                         "fixedStuck": d[False]["stuck600"], "rerouteStuck": d[True]["stuck600"],
                         "fixedRunning": d[False]["running"], "rerouteRunning": d[True]["running"],
                         "fixedTrips": d[False]["trips"], "rerouteTrips": d[True]["trips"]})
    reasons = {False: Counter(), True: Counter()}
    for r in results:
        reasons[r["reroute"]].update(r.get("reasons", {}))
    by = defaultdict(lambda: {"fixed": [], "reroute": [], "fixedTrips": [], "rerouteTrips": []})
    for x in rows:
        k = (x["place"], x["period"])
        by[k]["fixed"].append(x["fixedStuck"]); by[k]["reroute"].append(x["rerouteStuck"])
        by[k]["fixedTrips"].append(x["fixedTrips"]); by[k]["rerouteTrips"].append(x["rerouteTrips"])
    out["R2"] = {
        "pairs": len(rows),
        "rerouteLess": sum(x["rerouteStuck"] < x["fixedStuck"] for x in rows),
        "rerouteEqual": sum(x["rerouteStuck"] == x["fixedStuck"] for x in rows),
        "rerouteMore": sum(x["rerouteStuck"] > x["fixedStuck"] for x in rows),
        "totalStuck": {"fixed": sum(x["fixedStuck"] for x in rows), "reroute": sum(x["rerouteStuck"] for x in rows)},
        "reasons": {"fixed": dict(reasons[False]), "reroute": dict(reasons[True])},
        "byPlacePeriod": {f"{p}@{per}": {k: st.mean(v) for k, v in d.items()} for (p, per), d in sorted(by.items())},
    }
    # R1: n >= L / s_jam on gridlock cycles of leader edges (s_jam = 5 m car + 2.5 m minGap), and the
    # refinement n >= (L - B) / s_jam with B the junction boxes SUMO keeps clear on the loop
    S_JAM = 7.5
    cyc = [c for r in results for c in r["r1Cycles"]]
    out["R1"] = {
        "cycles": len(cyc),
        "n": [c["n"] for c in cyc],
        "density": [round(c["n"] / c["length"], 4) for c in cyc],
        "offBoxDensity": [round(c["n"] / (c["length"] - c["box"]), 4) for c in cyc],
        "plainBoundHolds": sum(c["n"] >= c["length"] / S_JAM - 1e-9 for c in cyc),
        "boxBoundHolds": sum(c["n"] >= (c["length"] - c["box"]) / S_JAM - 1e-9 for c in cyc),
        "boxBoundSlack": [round(c["n"] - (c["length"] - c["box"]) / S_JAM, 2) for c in cyc],
    }
    return out


if __name__ == "__main__":
    d = json.loads(DATA.read_text())
    s = summarise(d["results"])
    print(json.dumps(s, indent=1))
