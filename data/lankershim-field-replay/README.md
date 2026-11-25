# Lankershim Boulevard: first field replay baseline

This packet measures vehicle crossings at a **virtual screenline**, not an independently surveyed stop line or a calibrated simulation. It makes no change to the R2 proof bank.

- Source: [U.S. DOT NGSIM trajectory archive](https://data.transportation.gov/Automobiles/Next-Generation-Simulation-NGSIM-Vehicle-Trajector/8ect-6jqj). The Lankershim metadata PDF attached there identifies northbound as direction 2, through as movement 1, and local longitudinal front-center position in feet. Its cited longitudinal accuracy is about four feet.
- Site: Lankershim Boulevard / Universal Hollywood Drive, NGSIM intersection 2, with approach records from section 2. See the [FHWA site study](https://highways.dot.gov/media/264146).
- Window: June 16, 2005, 08:49:00–09:00:00 Pacific daylight time, right endpoint excluded. The [primary replay](https://horowitz.me.berkeley.edu/Publications_files/All_papers_numbered/Su_TRB_2013_Simulation_of_Cell_Transmission_Model_Using_NGSIM_data.pdf) reported downstream spillover near intersection 1 in this window. Intersection 2 is the downstream observation site here; its discharge is not itself evidence of the extent or cause of upstream spillover.

## Reproduce

Requires curl and Python 3, with no Python dependencies. From this directory:

```sh
sh fetch.sh
python -m unittest -v
python replay.py part0.csv part1.csv part2.csv > observed.json
diff -u result.json observed.json
```

The data downloads are split into three nonoverlapping windows and pinned by SHA-256 in `result.json`. Exact CSV-byte changes should be reviewed before replacing the baseline. The packet does not include source video or raw CSV files.

## Measured result

100,667 sampled trajectory rows from 330 vehicle IDs meet the query. At the 350 ft screenline, 252 northbound through vehicles crossed in adjacent frames, in three observed lanes (75, 89 and 88 crossings at the first downstream sample). The 340 ft cut gives 254 and flags six candidate transitions across gaps; 330 ft gives 322 and includes additional lane codes. These are distinct measurement cuts, not substitute geometries. Select and freeze the physical reference from the lane map before attempting phase-level scoring. Separately nine vehicle IDs met the proxy of at most 3 ft/s for at least three seconds in the 240–250 ft band. The proxy does not establish a contiguous queue or its cause.

## Next comparison

1. Register a physical stop line and lane-to-cell mapping from the intersection geometry or video. Compare against the three cuts, and document lane changes and data gaps instead of silently counting inferred crossings.
2. Retrieve the cycle-by-cycle controller record **RSM088-061605** named in FHWA's metadata, then independently align it with video markings. The primary replay reports the intersection 2 controller clock about **28 seconds ahead** of video/trajectory time. Treat that as a candidate offset, not a verified correction. Do not infer a phase from the discharge observations used to score the model. The controller record was not present among the trajectory table's listed attachments.
3. Feed the aligned effective green to a finite phase-aware model. Compare cumulative crossings, per-cycle discharge and queue recovery on held-out cycles; sweep the allowable clock offsets. Mark out-of-view demand and downstream occupancy unknown rather than empty. Keep modeled R2 guarantees (structural traps under the stated legal-move semantics) separate from measured discharge and from throughput or permanent-gridlock claims.
