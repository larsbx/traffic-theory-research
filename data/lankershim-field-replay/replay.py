#!/usr/bin/env python3
"""Extract an observed geometry-only discharge baseline, not a signal replay."""
import argparse
from collections import Counter, defaultdict
import csv
import hashlib
import json
from pathlib import Path

START, STOP = 1118936940000, 1118937600000
THRESHOLDS = (330, 340, 350)
STEP = 100
BIN = 30_000

def read(parts):
    tracks, inputs = defaultdict(dict), []
    for p in parts:
        rows = 0
        with p.open(newline="") as file:
            for row in csv.DictReader(file):
                v, t, f = map(int, (row["vehicle_id"], row["global_time"], row["frame_id"]))
                y, speed = map(float, (row["local_y"], row["v_vel"]))
                lane = int(row["lane_id"])
                if not START <= t < STOP or (t - START) % STEP or not 180 <= y <= 380 or (row["int_id"], row["section_id"]) not in {("0", "2"), ("2", "0")}:
                    raise ValueError("row outside the pinned query")
                point = f, y, speed, lane, row["section_id"]
                if t in tracks[v]:
                    raise ValueError(f"non-unique sample: {v}, {t}")
                tracks[v][t] = point
                rows += 1
        if rows == 0 or rows >= 100_000:
            raise ValueError(f"empty or possibly truncated API slice: {p}")
        inputs.append(dict(file=p.name, rows=rows, sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
    return tracks, inputs

def extract(tracks, y):
    counts = [0] * ((STOP - START) // BIN)
    lanes, gap_candidates = Counter(), 0
    for samples in tracks.values():
        prev_t, prev = None, None
        for t, p in sorted(samples.items()):
            if prev and prev[1] < y <= p[1]:
                if t - prev_t == STEP and p[0] - prev[0] == 1:
                    counts[(t - START)//BIN] += 1
                    lanes[p[3]] += 1
                    break
                gap_candidates += 1
            prev_t, prev = t, p
    return dict(total=sum(counts), bins_30s=counts, lane_counts=dict(sorted(lanes.items())),
                unaccepted_gap_transitions=gap_candidates)

def upstream_stops(tracks):
    # A kinematic proxy only: count sustained slow trajectories in the last
    # ten feet of the 100 ft band upstream of the 340 ft screenline.
    observed = 0
    for samples in tracks.values():
        run = 0
        prev_t = None
        qualifying = False
        for t, (_, y, speed, _, section) in sorted(samples.items()):
            if 240 <= y < 250 and 0 <= speed <= 3 and section == "2":
                run = run + 1 if prev_t is not None and t - prev_t == STEP else 1
                qualifying |= run >= 31
                prev_t = t
            else:
                run, prev_t = 0, None
        observed += qualifying
    return observed

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("parts", nargs=3, type=Path)
    args = parser.parse_args()
    tracks, inputs = read(args.parts)
    print(json.dumps(dict(start_ms=START, end_exclusive_ms=STOP, inputs=inputs, vehicle_ids=len(tracks),
                          screenlines={str(y): extract(tracks, y) for y in THRESHOLDS},
                          sustained_slow_90_to_100ft_upstream=upstream_stops(tracks)), indent=2))
if __name__ == "__main__":
    main()
