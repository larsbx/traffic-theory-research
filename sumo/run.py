"""Run one SUMO scenario and measure what the real-traffic theorems talk about.

At the end of the run (insertion stops at 3600 s, measurement at 4500 s, teleporting disabled so
that gridlock persists) it builds a wait-for graph from TraCI: a stopped vehicle waits on a stopped
leader within 3 m, or on a stopped junction foe it must yield to. Cycles are gridlock cores.
Summary and tripinfo outputs give the R5 (Little) quantities.
"""
from __future__ import annotations

import pathlib
import xml.etree.ElementTree as ET

import sumo
import traci

SUMO_BIN = str(pathlib.Path(sumo.SUMO_HOME) / "bin" / "sumo")
END, SAMPLE, WINDOW = 4510, 4500, (600, 3600)  # sample before the end: SUMO closes TraCI at --end


def wait_for_graph(stuck_s: float = 120.0):
    """{veh: [(blocker, kind, headway_m)]} over vehicles stopped for at least stuck_s seconds."""
    vehs = traci.vehicle.getIDList()
    stopped = {v for v in vehs if traci.vehicle.getSpeed(v) < 0.1 and traci.vehicle.getWaitingTime(v) >= stuck_s}
    g = {}
    for v in stopped:
        out = []
        lead = traci.vehicle.getLeader(v, 30.0)
        lane = traci.vehicle.getLaneID(v)
        at_stop_line = traci.lane.getLength(lane) - traci.vehicle.getLanePosition(v) < 3.0
        # held by the leader: bumper to bumper, or waiting at the stop line for room beyond the junction
        if lead and lead[0] in stopped and (lead[1] < 3.0 or (at_stop_line and lead[1] < 30.0)):
            headway = lead[1] + traci.vehicle.getMinGap(v) + traci.vehicle.getLength(lead[0])
            out.append((lead[0], "leader", headway))
        else:
            for foe in traci.vehicle.getJunctionFoes(v, 15.0):
                fid, ego_response = foe[0], foe[7]
                if fid in stopped and ego_response:
                    out.append((fid, "junction", None))
        g[v] = out
    return g


def stuck_reasons(stuck_s: float = 600.0):
    """Why each long-stopped vehicle is stopped: behind a stopped leader, at a red light, unable to
    leave its lane (no link from it to the next route edge), or other."""
    from collections import Counter
    reasons = Counter()
    for v in traci.vehicle.getIDList():
        if traci.vehicle.getSpeed(v) >= 0.1 or traci.vehicle.getWaitingTime(v) < stuck_s:
            continue
        lane, route, i = traci.vehicle.getLaneID(v), traci.vehicle.getRoute(v), traci.vehicle.getRouteIndex(v)
        nxt = route[i + 1] if 0 <= i < len(route) - 1 else None
        links = [l[0].rsplit("_", 1)[0] for l in traci.lane.getLinks(lane)]
        lead = traci.vehicle.getLeader(v, 30.0)
        tls = traci.vehicle.getNextTLS(v)
        if nxt and nxt not in links and not lane.startswith(":"):
            reasons["wrong lane (needs a lane change)"] += 1
        elif lead and lead[1] < 30.0:
            reasons["behind stopped leader"] += 1
        elif tls and tls[0][2] < 3.0 and tls[0][3] in "rRyY":
            reasons["at red light"] += 1
        else:
            reasons["other"] += 1
    return dict(reasons)


def cycles(g):
    """Simple cycles of the functional part of g (first edge per vehicle) plus all junction edges, via DFS."""
    found, color, stack = [], {}, []

    def dfs(v):
        color[v] = 1
        stack.append(v)
        for (w, kind, h) in g.get(v, []):
            if color.get(w) == 1:
                found.append(stack[stack.index(w):])
            elif w in g and color.get(w, 0) == 0:
                dfs(w)
        stack.pop()
        color[v] = 2

    for v in g:
        if color.get(v, 0) == 0:
            dfs(v)
    return found


def run(net, routes, out_stem, reroute: bool, seed: int):
    summary, tripinfo = f"{out_stem}.summary.xml", f"{out_stem}.tripinfo.xml"
    args = [SUMO_BIN, "-n", str(net), "-r", str(routes), "--end", str(END), "--time-to-teleport", "-1",
            "--seed", str(seed), "--no-step-log", "--no-warnings", "--summary-output", summary,
            "--tripinfo-output", tripinfo, "--tripinfo-output.write-unfinished"]
    if reroute:
        args += ["--device.rerouting.probability", "1", "--device.rerouting.period", "30",
                 "--device.rerouting.adaptation-interval", "10"]
    traci.start(args)
    try:
        traci.simulationStep(SAMPLE)
        g = wait_for_graph()
        stuck600 = sum(1 for v in traci.vehicle.getIDList()
                       if traci.vehicle.getSpeed(v) < 0.1 and traci.vehicle.getWaitingTime(v) >= 600)
        running = len(traci.vehicle.getIDList())
        cyc = cycles(g)
        core = {v for c in cyc for v in c}
        # R1 data: cycles made only of leader edges, with their headways
        r1 = []
        for c in cyc:
            edges = [next((e for e in g[v] if e[0] == c[(i + 1) % len(c)]), None) for i, v in enumerate(c)]
            if all(e and e[1] == "leader" for e in edges):
                r1.append({"n": len(c), "length": sum(e[2] for e in edges), "maxHeadway": max(e[2] for e in edges)})
        reasons = stuck_reasons()
    finally:
        traci.close()
    return {"stuck600": stuck600, "running": running, "cycles": len(cyc), "coreVehicles": len(core),
            "reasons": reasons, "r1Cycles": r1, **little(summary, tripinfo)}


def little(summary, tripinfo):
    """R5 on the window: completed-trip rate x mean length vs distance rate (running x mean speed)."""
    t0, t1 = WINDOW
    steps = [s for s in ET.parse(summary).getroot() if t0 <= float(s.get("time")) < t1]
    dist_rate = sum(float(s.get("running")) * max(0.0, float(s.get("meanSpeed"))) for s in steps) / len(steps)
    nbar = sum(float(s.get("running")) for s in steps) / len(steps)
    done = [t for t in ET.parse(tripinfo).getroot().iter("tripinfo")
            if float(t.get("depart")) >= t0 and 0 <= float(t.get("arrival", -1)) < t1]
    lam = len(done) / (t1 - t0)
    ell = sum(float(t.get("routeLength")) for t in done) / max(1, len(done))
    return {"trips": len(done), "lambda": lam, "meanTrip": ell, "Nbar": nbar, "distRate": dist_rate}
