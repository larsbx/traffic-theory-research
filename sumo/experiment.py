"""SUMO test of the real-traffic theorems: every preset x demand x seed, with fixed routes and with
SUMO's rerouting device. Writes docs/research/data/2026-11-24-sumo.json.
    python sumo/experiment.py            (about 30-60 min on 4 cores)
"""
from __future__ import annotations

import json
import os
from concurrent.futures import ProcessPoolExecutor

import build
import run

PERIODS = [4.0, 2.0, 1.0]   # seconds between insertions: 900, 1800, 3600 veh/h for one hour
SEEDS = [1, 2, 3]


def case(args):
    pid, period, seed, reroute = args
    place = next(p for p in build.PRESETS["places"] if p["id"] == pid)
    net = build.OUT / f"{pid}.net.xml"
    routes = build.trips(place, net, period, seed)
    res = run.run(net, routes, build.OUT / f"{pid}.p{period}.s{seed}.r{int(reroute)}", reroute, seed)
    return {"place": pid, "period": period, "seed": seed, "reroute": reroute, **res}


if __name__ == "__main__":
    build.OUT.mkdir(exist_ok=True)
    places = [p["id"] for p in build.PRESETS["places"]]
    for p in build.PRESETS["places"]:
        if not (build.OUT / f"{p['id']}.net.xml").exists():
            build.netconvert(p, build.fetch(p))
    for p in places:  # routes once per (place, period, seed), before the parallel runs
        for period in PERIODS:
            for seed in SEEDS:
                build.trips(next(x for x in build.PRESETS["places"] if x["id"] == p), build.OUT / f"{p}.net.xml", period, seed)
    jobs = [(p, period, seed, rr) for p in places for period in PERIODS for seed in SEEDS for rr in (False, True)]
    with ProcessPoolExecutor(max_workers=min(4, os.cpu_count() or 1)) as pool:
        results = []
        for r in pool.map(case, jobs):
            results.append(r)
            print(r["place"], r["period"], r["seed"], "reroute" if r["reroute"] else "fixed", "stuck", r["stuck600"], "/", r["running"], flush=True)
    out = build.HERE.parent / "docs" / "research" / "data" / "2026-11-24-sumo.json"
    import sumo as _s
    out.write_text(json.dumps({"generated": "sumo/experiment.py", "sumoHome": "eclipse-sumo (PyPI)",
                               "periods": PERIODS, "seeds": SEEDS, "end": run.END, "window": run.WINDOW,
                               "results": results}, indent=1))
    print("wrote", out)
