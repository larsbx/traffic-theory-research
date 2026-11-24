# SUMO test of the real-traffic theorems

This harness tests R1, R2 and R5 from
[`docs/research/2026-11-24-real-traffic-theorems.md`](../docs/research/2026-11-24-real-traffic-theorems.md)
in Eclipse SUMO, a microscopic simulator. SUMO uses the Krauß car-following model, real lane
geometry, keep-clear junctions and guessed signal plans. It runs on the app's six OSM preset
windows (720 × 480 m).

```sh
pip install eclipse-sumo traci sumolib   # SUMO 1.28 wheels; no system install needed
python sumo/build.py                     # OSM extract -> netconvert -> sumo/out/ (git-ignored)
python sumo/experiment.py                # 6 places x 3 demands x 3 seeds x {fixed, rerouting} = 108 runs
python sumo/analyze.py                   # summary against R1, R2, R5
```

| file | role |
|---|---|
| `build.py` | Fetches the OSM extract and runs `netconvert`, with guessed signals, joined junctions, and left-hand traffic for bank and shibuya. Generates trips with `randomTrips.py`: one hour of insertions from the fringe at 900, 1800 or 3600 veh/h. |
| `run.py` | Runs one scenario with teleporting off. At t = 4500 s it builds a TraCI wait-for graph from stopped leaders and junction foes, then finds its cycles (gridlock cores) and their junction-box lengths. It also reads the R5 quantities from the summary and tripinfo outputs over the window [600, 3600) s. |
| `experiment.py` | The full grid, on 4 processes. Writes [`docs/research/data/2026-11-24-sumo.json`](../docs/research/data/2026-11-24-sumo.json). |
| `analyze.py` | The summary reported in the note's §SUMO. |
