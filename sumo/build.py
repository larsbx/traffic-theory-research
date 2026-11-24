"""Build SUMO scenarios for the six presets: OSM extract -> netconvert network -> random trips.

Uses the same 720 x 480 m windows as app/data/presets.json. Outputs go to sumo/out/ (git-ignored).
    python sumo/build.py [--places midtown,...]
"""
from __future__ import annotations

import argparse
import json
import math
import pathlib
import subprocess
import sys
import urllib.request

import sumo

HERE = pathlib.Path(__file__).resolve().parent
OUT = HERE / "out"
PRESETS = json.loads((HERE.parent / "app" / "data" / "presets.json").read_text())
LEFT = {"bank", "shibuya"}  # left-hand traffic
W, H = 720.0, 480.0         # metres, the app's window
AGENT = "traffic-theory-research-sumo/1.0 (+https://github.com/larsbx/traffic-theory-research)"
SUMO_HOME = pathlib.Path(sumo.SUMO_HOME)


def bbox(lat: float, lon: float) -> tuple[float, float, float, float]:
    """(west, south, east, north) of the W x H metre window round (lat, lon)."""
    dlat = H / 2 / 6371008.8 * 180 / math.pi
    dlon = W / 2 / (6371008.8 * math.cos(math.radians(lat))) * 180 / math.pi
    return lon - dlon, lat - dlat, lon + dlon, lat + dlat


def fetch(place: dict) -> pathlib.Path:
    path = OUT / f"{place['id']}.osm.xml"
    if not path.exists():
        w, s, e, n = bbox(place["lat"], place["lon"])
        req = urllib.request.Request(f"https://api.openstreetmap.org/api/0.6/map?bbox={w},{s},{e},{n}", headers={"User-Agent": AGENT})
        path.write_bytes(urllib.request.urlopen(req, timeout=120).read())
    return path


def netconvert(place: dict, osm: pathlib.Path) -> pathlib.Path:
    net = OUT / f"{place['id']}.net.xml"
    args = [str(SUMO_HOME / "bin" / "netconvert"), "--osm-files", str(osm), "-o", str(net),
            "--keep-edges.by-vclass", "passenger", "--remove-edges.isolated", "--geometry.remove",
            "--roundabouts.guess", "--junctions.join", "--tls.guess-signals", "--tls.discard-simple",
            "--tls.join", "--no-warnings", "--no-turnarounds.except-deadend"]
    if place["id"] in LEFT:
        args.append("--lefthand")
    subprocess.run(args, check=True)
    return net


def trips(place: dict, net: pathlib.Path, period: float, seed: int) -> pathlib.Path:
    stem = OUT / f"{place['id']}.p{period}.s{seed}"
    routes = stem.with_suffix(".rou.xml")
    if not routes.exists():
        subprocess.run([sys.executable, str(SUMO_HOME / "tools" / "randomTrips.py"), "-n", str(net),
                        "-o", str(stem.with_suffix(".trips.xml")), "-r", str(routes), "--period", str(period),
                        "--fringe-factor", "10", "--min-distance", "200", "--validate", "--seed", str(seed),
                        "-e", "3600"], check=True, stdout=subprocess.DEVNULL)
    return routes


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--places", default=",".join(p["id"] for p in PRESETS["places"]))
    ids = ap.parse_args().places.split(",")
    OUT.mkdir(exist_ok=True)
    for place in (p for p in PRESETS["places"] if p["id"] in ids):
        net = netconvert(place, fetch(place))
        print(place["id"], net.stat().st_size // 1024, "KB")
