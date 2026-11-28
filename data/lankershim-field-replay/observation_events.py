#!/usr/bin/env python3
"""Exact, source-bound observation evidence; never infer traffic state from gaps.

The mathematical object here is a pair of measured front-center samples.
An accepted crossing is an adjacent-frame *measurement bracket* at a declared
virtual screenline. It is not an interpolated crossing instant, a surveyed
stop-line event, a vehicle exit, or evidence that a street cell is vacant.
"""

import argparse
from collections import Counter, defaultdict
import csv
from dataclasses import dataclass
from decimal import Decimal, InvalidOperation
from fractions import Fraction
import hashlib
import io
import json
from pathlib import Path
import re


START, STOP, STEP, BIN = 1118936940000, 1118937600000, 100, 30_000
CUTS = (Fraction(330), Fraction(340), Fraction(350))
COLUMNS = ("vehicle_id", "frame_id", "global_time", "local_y", "lane_id",
           "int_id", "section_id", "v_vel")
DATASET = "https://data.transportation.gov/resource/8ect-6jqj.csv"
SCHEMA = "gridlock-field-observation-evidence-v1"
QUERY = {
    "dataset": DATASET,
    "location": "lankershim", "direction": "2", "movement": "1",
    "start_ms": START, "end_exclusive_ms": STOP,
    "local_y_feet_inclusive": [180, 380],
    "intersection_or_section": "int_id='2' OR section_id='2'",
    "columns": list(COLUMNS), "order": ["global_time", "vehicle_id", "frame_id"],
    "partition_ms": 220_000, "limit_per_partition": 100_000,
}


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def digest(value):
    return hashlib.sha256(canonical(value).encode()).hexdigest()


def natural(text, field):
    """Integer IDs and timestamps must not pass through floating point."""
    if not isinstance(text, str) or not re.fullmatch(r"[0-9]+", text):
        raise ValueError(f"{field}: expected a nonnegative integer, got {text!r}")
    return int(text)


def exact_decimal(text, field):
    if not isinstance(text, str) or not re.fullmatch(
            r"[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?", text):
        raise ValueError(f"{field}: expected a finite decimal, got {text!r}")
    try:
        value = Decimal(text)
    except InvalidOperation as error:
        raise ValueError(f"{field}: invalid decimal {text!r}") from error
    if not value.is_finite():
        raise ValueError(f"{field}: nonfinite decimal")
    return Fraction(value)


def rational(value):
    """String numerators/denominators survive JSON clients without rounding."""
    value = Fraction(value)
    return {"num": str(value.numerator), "den": str(value.denominator)}


@dataclass(frozen=True)
class RowReference:
    part_sha256: str
    csv_row: int

    def to_json(self):
        return {"partSha256": self.part_sha256, "csvRow": self.csv_row}


@dataclass(frozen=True)
class Observation:
    source: int
    vehicle: int
    frame: int
    time_ms: int
    y: Fraction
    speed: Fraction
    lane: int
    section: int
    intersection: int
    reference: RowReference
    raw_y: str
    raw_speed: str

    @property
    def identity(self):
        return self.source, self.vehicle

    def to_json(self):
        return {
            "source": self.source, "vehicle": self.vehicle, "frame": self.frame,
            "timeMs": self.time_ms, "y": rational(self.y), "speed": rational(self.speed),
            "lane": self.lane, "section": self.section, "intersection": self.intersection,
            "provenance": self.reference.to_json(),
            "decimalLexemes": {"local_y": self.raw_y, "v_vel": self.raw_speed},
        }


@dataclass
class ObservationSet:
    samples: list
    sources: list
    inputs: list
    pinned: bool

    def tracks(self):
        tracks = defaultdict(list)
        for index, sample in enumerate(self.samples):
            tracks[sample.identity].append(index)
        for indices in tracks.values():
            indices.sort(key=lambda i: (self.samples[i].time_ms, self.samples[i].frame))
        return dict(sorted(tracks.items()))


def read_observations(parts, manifest=None):
    """Read one source capture, joining vehicles across its verified partitions.

    A source is the query and the complete input-byte commitment, not a CSV
    filename. A vehicle ID is scoped to that source, never globally unique.
    """
    parts = [Path(part) for part in parts]
    if not parts:
        raise ValueError("no observation inputs")
    expected = None
    if manifest is not None:
        if (manifest.get("start_ms"), manifest.get("end_exclusive_ms")) != (START, STOP):
            raise ValueError("manifest observation window differs from the pinned query")
        expected = {item["sha256"]: item for item in manifest["inputs"]}
        if len(expected) != len(manifest["inputs"]) or len(parts) != len(expected):
            raise ValueError("manifest/input partition inventory mismatch")

    samples, inputs, seen_rows, seen_inputs = [], [], set(), set()
    for part in parts:
        # Parse precisely the bytes whose digest is checked. Reopening the
        # pathname after hashing would permit a replacement between the two.
        raw_bytes = part.read_bytes()
        part_hash = hashlib.sha256(raw_bytes).hexdigest()
        if part_hash in seen_inputs:
            raise ValueError(f"duplicate input partition: {part}")
        seen_inputs.add(part_hash)
        if expected is not None and part_hash not in expected:
            raise ValueError(f"input SHA-256 does not match the pinned manifest: {part}")
        count = 0
        with io.StringIO(raw_bytes.decode("utf-8"), newline="") as file:
            reader = csv.DictReader(file)
            if reader.fieldnames != list(COLUMNS):
                raise ValueError(f"unexpected source columns: {part}")
            for csv_row, row in enumerate(reader, start=2):
                if None in row or any(value is None for value in row.values()):
                    raise ValueError(f"malformed CSV row: {part}:{csv_row}")
                vehicle = natural(row["vehicle_id"], "vehicle_id")
                frame = natural(row["frame_id"], "frame_id")
                time_ms = natural(row["global_time"], "global_time")
                lane = natural(row["lane_id"], "lane_id")
                section = natural(row["section_id"], "section_id")
                intersection = natural(row["int_id"], "int_id")
                y = exact_decimal(row["local_y"], "local_y")
                speed = exact_decimal(row["v_vel"], "v_vel")
                if not (START <= time_ms < STOP and (time_ms - START) % STEP == 0
                        and 180 <= y <= 380
                        and (intersection, section) in {(0, 2), (2, 0)}):
                    raise ValueError(f"row outside pinned query: {part}:{csv_row}")
                key = vehicle, time_ms
                if key in seen_rows:
                    raise ValueError(f"non-unique source/vehicle/time sample: {key}")
                seen_rows.add(key)
                samples.append(Observation(
                    0, vehicle, frame, time_ms, y, speed, lane, section, intersection,
                    RowReference(part_hash, csv_row), row["local_y"], row["v_vel"]))
                count += 1
        if count == 0 or count >= QUERY["limit_per_partition"]:
            raise ValueError(f"empty or possibly truncated source partition: {part}")
        if expected is not None and count != expected[part_hash]["rows"]:
            raise ValueError(f"row count differs from source manifest: {part}")
        inputs.append({
            "file": part.name, "rows": count, "sha256": part_hash,
            "pinnedFile": expected[part_hash]["file"] if expected is not None else None,
        })
    if expected is not None and seen_inputs != set(expected):
        raise ValueError("missing pinned source partitions")
    # Canonical content identity is invariant under input argument order and
    # local file renames; row references still identify the original bytes.
    commitment = {"query": QUERY, "parts": sorted(
        ({"sha256": item["sha256"], "rows": item["rows"]} for item in inputs),
        key=lambda item: item["sha256"])}
    source = {
        "index": 0, "kind": "recorded_trajectory_capture",
        "sourceId": "sha256:" + digest(commitment), "commitment": commitment,
        "pinnedManifestMatched": expected is not None,
        "identityScope": "vehicle_id within this exact source capture, across CSV partitions",
    }
    samples.sort(key=lambda sample: (sample.time_ms, sample.vehicle, sample.frame))
    return ObservationSet(samples, [source], inputs, expected is not None)


def slow_proxy(sample):
    return sample.section == 2 and 240 <= sample.y < 250 and 0 <= sample.speed <= 3


def classify_pair(before, after, cut):
    identity = before.identity == after.identity
    adjacent = identity and after.frame == before.frame + 1 and after.time_ms == before.time_ms + STEP
    bracket = before.y < cut <= after.y
    return {
        "identity": identity, "adjacent": adjacent, "forwardBracket": bracket,
        "crossing": adjacent and bracket,
        "changedLane": identity and before.lane != after.lane,
        "gapCandidate": identity and bracket and not adjacent,
        "slowBefore": slow_proxy(before),
    }


def indexed_pairs(observations, cuts=CUTS):
    pairs = []
    for indices in observations.tracks().values():
        for left, right in zip(indices, indices[1:]):
            before, after = observations.samples[left], observations.samples[right]
            pairs.append({"before": left, "after": right,
                          "expected": [classify_pair(before, after, cut) for cut in cuts]})
    # This establishes a reproducible observation ordering, not causal order
    # between different vehicles with identical timestamps.
    pairs.sort(key=lambda pair: (
        observations.samples[pair["after"]].time_ms,
        observations.samples[pair["before"]].time_ms,
        observations.samples[pair["before"]].source,
        observations.samples[pair["before"]].vehicle,
        observations.samples[pair["after"]].frame))
    return pairs


def first_crossing_counts(samples, pairs, number_of_cuts):
    seen, totals = set(), [0] * number_of_cuts
    for pair in pairs:
        before = samples[pair["before"]]
        for index, classification in enumerate(pair["expected"]):
            key = before.source, before.vehicle, index
            if classification["crossing"] and key not in seen:
                seen.add(key)
                totals[index] += 1
    return totals


def geometry(cuts):
    return [{
        "id": "virtual-local-y-" + str(cut) + "-ft",
        "role": "virtual_screenline", "coordinate": "local_y",
        "coordinateObject": "recorded vehicle front-center longitudinal position",
        "unit": "feet", "threshold": rational(cut),
        "physicalStopLineRegistration": None, "laneToCellMapping": None,
    } for cut in cuts]


def evidence_bundle(observations, cuts=CUTS, pairs=None):
    cuts = tuple(map(Fraction, cuts))
    pairs = indexed_pairs(observations, cuts) if pairs is None else pairs
    return {
        "schema": SCHEMA,
        "sources": observations.sources,
        "inputs": observations.inputs,
        "geometry": geometry(cuts),
        "clock": {
            "field": "global_time", "unit": "milliseconds", "nominalFramePeriodMs": STEP,
            "controllerAlignment": None, "observedSignalPhases": False,
        },
        "interpretation": {
            "crossing": "adjacent measured front-center samples bracket a virtual screenline",
            "crossingTime": "unresolved within the observation window; no interpolation",
            "gap": "unknown intervening trajectory; never physical exit or vacant cell",
            "laneChange": "different recorded lane codes; never assumed same-lane motion",
            "missingVehicle": "unknown under this filtered query; never vacant-cell evidence",
            "ordering": "end timestamp, start timestamp, source, vehicle, frame; ties serialize only",
            "physicalExitEvidence": False, "streetCellVacancyEvidence": False,
        },
        "samples": [sample.to_json() for sample in observations.samples],
        "cuts": [rational(cut) for cut in cuts], "pairs": pairs,
        "expectedFirstCrossings": first_crossing_counts(observations.samples, pairs, len(cuts)),
    }


def summarize(observations, cuts=CUTS, pairs=None):
    pairs = indexed_pairs(observations, cuts) if pairs is None else pairs
    screenlines = {}
    for index, cut in enumerate(cuts):
        seen, lanes, bins = set(), Counter(), [0] * ((STOP - START) // BIN)
        all_crossings = gap_before_first = all_gaps = lane_changed_first = 0
        for pair in pairs:
            before, after = observations.samples[pair["before"]], observations.samples[pair["after"]]
            classification = pair["expected"][index]
            all_crossings += classification["crossing"]
            all_gaps += classification["gapCandidate"]
            if before.identity in seen:
                continue
            if classification["gapCandidate"]:
                gap_before_first += 1
            if classification["crossing"]:
                seen.add(before.identity)
                lanes[after.lane] += 1
                bins[(after.time_ms - START) // BIN] += 1
                lane_changed_first += classification["changedLane"]
        screenlines[str(cut)] = {
            "total": len(seen), "bins_30s": bins,
            "lane_counts": dict(sorted(lanes.items())),
            "lane_count_convention": "recorded lane code at first downstream sample",
            "first_crossings_with_changed_lane_code": lane_changed_first,
            "same_lane_first_crossings": len(seen) - lane_changed_first,
            "all_adjacent_brackets": all_crossings,
            "unaccepted_gap_transitions": gap_before_first,
            "all_gap_candidates": all_gaps,
        }
    adjacent = sum(pair["expected"][0]["adjacent"] for pair in pairs)
    changed_lane = sum(pair["expected"][0]["changedLane"] for pair in pairs)
    slow_time_only = slow_frame_and_time = 0
    for indices in observations.tracks().values():
        time_run = frame_run = 0
        previous = None
        qualifies_time = qualifies_frame = False
        for index in indices:
            current = observations.samples[index]
            if slow_proxy(current):
                contiguous_time = previous is not None and current.time_ms == previous.time_ms + STEP
                contiguous_frame = contiguous_time and current.frame == previous.frame + 1
                time_run = time_run + 1 if contiguous_time else 1
                frame_run = frame_run + 1 if contiguous_frame else 1
                qualifies_time |= time_run >= 31
                qualifies_frame |= frame_run >= 31
                previous = current
            else:
                time_run = frame_run = 0
                previous = None
        slow_time_only += qualifies_time
        slow_frame_and_time += qualifies_frame
    examples = {}
    for name, predicate, cut_index in (
        ("adjacent_350ft_crossing", lambda pair: pair["expected"][2]["crossing"], 2),
        ("uncertain_340ft_crossing", lambda pair: pair["expected"][1]["gapCandidate"], 1),
        ("changed_lane_code", lambda pair: pair["expected"][0]["changedLane"], 0),
    ) if tuple(cuts) == CUTS else ():
        selected = next((pair for pair in pairs if predicate(pair)), None)
        if selected is not None:
            examples[name] = {
                "before": observations.samples[selected["before"]].to_json(),
                "after": observations.samples[selected["after"]].to_json(),
                "cut": rational(cuts[cut_index]), "expected": selected["expected"][cut_index],
            }
    return {
        "schema": SCHEMA, "start_ms": START, "end_exclusive_ms": STOP,
        "sources": observations.sources, "inputs": observations.inputs,
        "rows": len(observations.samples), "vehicle_ids": len(observations.tracks()),
        "pairs": len(pairs), "adjacent_frame_time_pairs": adjacent,
        "unknown_intervening_trajectory_pairs": len(pairs) - adjacent,
        "pairs_with_changed_lane_code": changed_lane,
        "screenlines": screenlines,
        "sustained_slow_90_to_100ft_upstream": slow_time_only,
        "sustained_slow_with_both_frame_and_time_adjacency": slow_frame_and_time,
        "physical_exit_events": 0, "street_cell_vacancy_events": 0,
        "physical_stopline_registered": False, "controller_clock_aligned": False,
        "evidence_examples": examples,
    }


def check_baseline(summary, baseline):
    if summary["rows"] != sum(item["rows"] for item in baseline["inputs"]):
        raise ValueError("exact observation adapter changed the pinned row total")
    if summary["vehicle_ids"] != baseline["vehicle_ids"]:
        raise ValueError("exact observation adapter changed source-scoped vehicle count")
    for cut, expected in baseline["screenlines"].items():
        observed = summary["screenlines"][cut]
        for key in ("total", "bins_30s", "unaccepted_gap_transitions"):
            if observed[key] != expected[key]:
                raise ValueError(f"exact observation adapter disagrees with baseline {cut} {key}")
        if {str(key): value for key, value in observed["lane_counts"].items()} != expected["lane_counts"]:
            raise ValueError(f"exact observation adapter disagrees with baseline {cut} lane counts")
    if summary["sustained_slow_90_to_100ft_upstream"] != baseline["sustained_slow_90_to_100ft_upstream"]:
        raise ValueError("exact observation adapter changed the baseline kinematic proxy")


def event_records(observations, cuts=CUTS, pairs=None):
    """Normalized evidence windows with row provenance, not traffic commands."""
    pairs = indexed_pairs(observations, cuts) if pairs is None else pairs
    events = []
    for identity, indices in observations.tracks().items():
        for kind, index in (("observation_start", indices[0]), ("observation_end", indices[-1])):
            sample = observations.samples[index]
            events.append({
                "kind": kind, "source": identity[0], "vehicle": identity[1],
                "startMs": sample.time_ms, "endMs": sample.time_ms,
                "sample": index, "provenance": [sample.reference.to_json()],
                "interpretation": "query/track boundary; physical entry or exit unknown",
            })
    for pair in pairs:
        before, after = observations.samples[pair["before"]], observations.samples[pair["after"]]
        classification = pair["expected"][0]
        base = {
            "source": before.source, "vehicle": before.vehicle,
            "startMs": before.time_ms, "endMs": after.time_ms,
            "before": pair["before"], "after": pair["after"],
            "provenance": [before.reference.to_json(), after.reference.to_json()],
            "deltaFrame": after.frame - before.frame, "deltaTimeMs": after.time_ms - before.time_ms,
            "fromLane": before.lane, "toLane": after.lane,
            "changedLane": classification["changedLane"],
        }
        events.append({**base,
            "kind": "adjacent_observation_pair" if classification["adjacent"] else "observation_gap",
            "measuredLongitudinalChangeFt": rational(after.y - before.y),
            "interveningTrajectory": "adjacent samples" if classification["adjacent"] else "unknown",
        })
        for cut, result in zip(cuts, pair["expected"]):
            if result["crossing"] or result["gapCandidate"]:
                events.append({**base,
                    "kind": "observed_crossing_window" if result["crossing"] else "candidate_gap_crossing",
                    "geometryId": "virtual-local-y-" + str(cut) + "-ft",
                    "thresholdFt": rational(cut), "geometryRole": "virtual_screenline",
                    "exactCrossingTimeMs": None, "physicalStopLine": False,
                })
    events.sort(key=lambda event: (event["endMs"], event["startMs"], event["source"],
                                    event["vehicle"], event["kind"], event.get("geometryId", "")))
    for event in events:
        event["eventId"] = "sha256:" + digest({
            "sourceId": observations.sources[event["source"]]["sourceId"], **event})
    return events


def fixture_bundle():
    """Deliberately constructed contract controls, explicitly not field data."""
    samples, pairs = [], []
    fixture_hash = hashlib.sha256(b"synthetic Gridlock observation correspondence controls v1").hexdigest()

    def sample(vehicle, frame, time_ms, y, speed="1", lane=2, source=0, section=2, intersection=0):
        result = Observation(source, vehicle, frame, time_ms, exact_decimal(y, "fixture y"),
            exact_decimal(speed, "fixture speed"), lane, section, intersection,
            RowReference(fixture_hash, len(samples) + 2), y, speed)
        samples.append(result)
        return len(samples) - 1

    def pair(left, right):
        pairs.append({"before": left, "after": right,
                      "expected": [classify_pair(samples[left], samples[right], cut) for cut in CUTS]})

    specs = [
        # Exact boundary, gaps in either clock, identity mismatch, lane change.
        ({"y": "349.9999999999999999999"}, {"y": "350"}),
        ({"y": "349"}, {"y": "351", "frame": 3, "time_ms": START + 200}),
        ({"y": "349"}, {"y": "351", "frame": 3}),
        ({"y": "349"}, {"y": "351", "time_ms": START + 200}),
        ({"y": "349"}, {"y": "351", "source": 1}),
        ({"y": "349"}, {"y": "351", "vehicle": 999}),
        ({"y": "351"}, {"y": "349"}),
        ({"y": "350"}, {"y": "351"}),
        ({"y": "350"}, {"y": "350"}),
        ({"y": "349", "lane": 2}, {"y": "351", "lane": 3}),
        # The kinematic proxy is exact, and does not assert a queue or phase.
        ({"y": "249.9999999999999999999", "speed": "3"}, {"y": "250"}),
        ({"y": "245", "speed": "3.0000000000000000001"}, {"y": "245"}),
        ({"y": "240", "speed": "-0.000"}, {"y": "240"}),
        ({"y": "250", "speed": "0"}, {"y": "250"}),
        ({"y": "245", "speed": "-0.01"}, {"y": "245"}),
        ({"y": "245", "speed": "0", "section": 0, "intersection": 2}, {"y": "245"}),
    ]
    for vehicle, (left, right) in enumerate(specs, start=1):
        a = sample(**{"vehicle": vehicle, "frame": 1, "time_ms": START, **left})
        b = sample(**{"vehicle": vehicle, "frame": 2, "time_ms": START + STEP, **right})
        pair(a, b)
    # Recrossings remain distinct windows but first-per-vehicle totals count once.
    recross = [sample(100, frame + 1, START + frame * STEP, y)
               for frame, y in enumerate(("329", "351", "329", "351"))]
    for a, b in zip(recross, recross[1:]):
        pair(a, b)
    # Reused vehicle IDs in a different capture are a distinct observed object.
    pair(sample(100, 1, START, "329", source=1),
         sample(100, 2, START + STEP, "351", source=1))
    sources = [{"index": index, "kind": "synthetic_control",
                "sourceId": f"synthetic:observation-controls:{index}",
                "description": "Constructed test samples, not observed traffic"} for index in range(2)]
    return evidence_bundle(ObservationSet(samples, sources, [], False), CUTS, pairs)


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as file:
        json.dump(value, file, separators=(",", ":"), ensure_ascii=True)
        file.write("\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("parts", nargs="*", type=Path)
    parser.add_argument("--manifest", type=Path, default=Path(__file__).with_name("result.json"))
    parser.add_argument("--cases", type=Path, help="shared-sample JSON for Lean correspondence")
    parser.add_argument("--events", type=Path, help="ordered evidence windows as JSON Lines")
    parser.add_argument("--report", type=Path, help="exact source and comparison summary")
    parser.add_argument("--fixture-cases", type=Path, help="write explicit synthetic controls only")
    args = parser.parse_args()
    if args.fixture_cases:
        if args.parts or args.cases or args.events or args.report:
            parser.error("synthetic controls must be generated separately from real-data outputs")
        bundle = fixture_bundle()
        write_json(args.fixture_cases, bundle)
        print(json.dumps({"kind": "synthetic_control", "samples": len(bundle["samples"]),
                          "pairs": len(bundle["pairs"]), "firstCrossings": bundle["expectedFirstCrossings"]}))
        return
    if len(args.parts) != 3:
        parser.error("supply the three pinned CSV partitions, or --fixture-cases")
    baseline = json.loads(args.manifest.read_text())
    observations = read_observations(args.parts, baseline)
    pairs = indexed_pairs(observations)
    summary = summarize(observations, pairs=pairs)
    check_baseline(summary, baseline)
    summary["pinned_baseline_matched"] = True
    if args.cases:
        write_json(args.cases, evidence_bundle(observations, pairs=pairs))
    if args.events:
        args.events.parent.mkdir(parents=True, exist_ok=True)
        records = event_records(observations, pairs=pairs)
        with args.events.open("w", encoding="utf-8") as file:
            for record in records:
                file.write(canonical(record) + "\n")
        summary["evidence_events"] = len(records)
        summary["evidence_events_sha256"] = hashlib.sha256(args.events.read_bytes()).hexdigest()
    if args.report:
        write_json(args.report, summary)
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
