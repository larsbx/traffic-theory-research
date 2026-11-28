import csv
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from observation_events import (
    COLUMNS, CUTS, START, STOP, Observation, ObservationSet, RowReference,
    classify_pair, evidence_bundle, event_records, exact_decimal, fixture_bundle,
    indexed_pairs, natural, read_observations, slow_proxy, summarize, write_json,
)


def sample(vehicle=1, frame=1, time_ms=START, y="349", speed="1", lane=2,
           source=0, section=2, intersection=0):
    return Observation(source, vehicle, frame, time_ms, exact_decimal(y, "y"),
        exact_decimal(speed, "speed"), lane, section, intersection,
        RowReference("fixture-sha256", frame + 1), y, speed)


def row(vehicle=1, frame=1, time_ms=START, y="349", speed="1", lane=2,
        section=2, intersection=0):
    return {
        "vehicle_id": str(vehicle), "frame_id": str(frame), "global_time": str(time_ms),
        "local_y": str(y), "lane_id": str(lane), "int_id": str(intersection),
        "section_id": str(section), "v_vel": str(speed),
    }


class ObservationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.directory = Path(self.temporary.name)

    def tearDown(self):
        self.temporary.cleanup()

    def write_csv(self, name, rows, columns=COLUMNS):
        path = self.directory / name
        with path.open("w", newline="", encoding="utf-8") as file:
            writer = csv.DictWriter(file, fieldnames=columns)
            writer.writeheader()
            writer.writerows(rows)
        return path

    def manifest(self, paths, counts):
        return {
            "start_ms": START, "end_exclusive_ms": STOP,
            "inputs": [{"file": path.name, "rows": count,
                        "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
                       for path, count in zip(paths, counts)],
        }

    def test_decimal_boundary_is_not_rounded_into_a_crossing(self):
        almost = exact_decimal("349.9999999999999999999", "local_y")
        self.assertEqual(float(almost), 350.0)
        self.assertLess(almost, Fraction(350))
        self.assertEqual(almost.denominator, 10 ** 19)
        self.assertEqual(exact_decimal("-0.000", "v_vel"), 0)
        self.assertEqual(exact_decimal("3.125e-2", "v_vel"), Fraction(1, 32))
        before = sample(y="349.9999999999999999999")
        after = sample(frame=2, time_ms=START + 100, y="350")
        self.assertTrue(classify_pair(before, after, Fraction(350))["crossing"])

    def test_nonfinite_values_and_float_timestamps_are_rejected(self):
        for bad in ("NaN", "Infinity", "-inf", "", " 3", "1/2", "1_000"):
            with self.subTest(decimal=bad), self.assertRaises(ValueError):
                exact_decimal(bad, "local_y")
        for bad in ("1118936940000.0", "1e12", "-1", "", "1 2"):
            with self.subTest(integer=bad), self.assertRaises(ValueError):
                natural(bad, "global_time")

    def test_vehicle_identity_is_scoped_to_the_source_capture(self):
        before = sample()
        for after in (
            sample(vehicle=2, frame=2, time_ms=START + 100, y="351"),
            sample(source=1, frame=2, time_ms=START + 100, y="351"),
        ):
            result = classify_pair(before, after, Fraction(350))
            self.assertTrue(result["forwardBracket"])
            self.assertFalse(result["identity"])
            self.assertFalse(result["adjacent"])
            self.assertFalse(result["crossing"])
            self.assertFalse(result["gapCandidate"])

    def test_both_frame_and_timestamp_adjacency_are_required(self):
        before = sample()
        for frame, time_ms in ((3, START + 100), (2, START + 200), (3, START + 200)):
            result = classify_pair(before, sample(frame=frame, time_ms=time_ms, y="351"), Fraction(350))
            self.assertFalse(result["adjacent"])
            self.assertFalse(result["crossing"])
            self.assertTrue(result["gapCandidate"])
        result = classify_pair(before, sample(frame=2, time_ms=START + 100, y="351"), Fraction(350))
        self.assertTrue(result["crossing"])
        self.assertFalse(result["gapCandidate"])

    def test_same_vehicle_can_cross_csv_partition_boundary(self):
        left = self.write_csv("left.csv", [row(frame=1, y="349")])
        right = self.write_csv("right.csv", [row(frame=2, time_ms=START + 100, y="351")])
        manifest = self.manifest([left, right], [1, 1])
        data = read_observations([left, right], manifest)
        reverse_inputs = read_observations([right, left], manifest)
        self.assertEqual(data.sources[0]["sourceId"], reverse_inputs.sources[0]["sourceId"])
        self.assertEqual(len(data.tracks()), 1)
        pairs = indexed_pairs(data)
        self.assertEqual(len(pairs), 1)
        self.assertTrue(pairs[0]["expected"][2]["crossing"])
        bundle = evidence_bundle(data, pairs=pairs)
        self.assertEqual(bundle["expectedFirstCrossings"], [0, 0, 1])
        self.assertNotEqual(bundle["samples"][0]["provenance"]["partSha256"],
                            bundle["samples"][1]["provenance"]["partSha256"])
        self.assertEqual(bundle["samples"][0]["provenance"]["csvRow"], 2)

    def test_source_commitment_survives_renaming_but_not_byte_substitution(self):
        path = self.write_csv("part.csv", [row()])
        manifest = self.manifest([path], [1])
        original = read_observations([path], manifest)
        renamed = self.directory / "renamed.csv"
        renamed.write_bytes(path.read_bytes())
        self.assertEqual(read_observations([renamed], manifest).sources[0]["sourceId"],
                         original.sources[0]["sourceId"])
        # A semantically ignored trailing blank line still changes the exact source.
        renamed.write_bytes(renamed.read_bytes() + b"\n")
        with self.assertRaisesRegex(ValueError, "SHA-256"):
            read_observations([renamed], manifest)

    def test_hashed_bytes_are_the_same_bytes_that_get_parsed(self):
        path = self.write_csv("part.csv", [row(y="349")])
        replacement = self.write_csv("replacement.csv", [row(y="351")]).read_bytes()
        manifest = self.manifest([path], [1])
        original_read = Path.read_bytes

        def replace_after_read(candidate):
            content = original_read(candidate)
            if candidate == path:
                path.write_bytes(replacement)
            return content

        with patch.object(Path, "read_bytes", replace_after_read):
            accepted = read_observations([path], manifest)
        self.assertEqual(accepted.samples[0].y, Fraction(349))
        self.assertEqual(accepted.inputs[0]["sha256"], manifest["inputs"][0]["sha256"])
        self.assertEqual(path.read_bytes(), replacement)

    def test_missing_duplicate_and_miscounted_pinned_partitions_are_rejected(self):
        left = self.write_csv("left.csv", [row(vehicle=1)])
        right = self.write_csv("right.csv", [row(vehicle=2)])
        manifest = self.manifest([left, right], [1, 1])
        with self.assertRaisesRegex(ValueError, "inventory mismatch"):
            read_observations([left], manifest)
        with self.assertRaisesRegex(ValueError, "duplicate input partition"):
            read_observations([left, left], manifest)
        manifest["inputs"][0]["rows"] = 2
        with self.assertRaisesRegex(ValueError, "row count"):
            read_observations([left, right], manifest)

    def test_overlapping_rows_are_not_silently_replaced(self):
        left = self.write_csv("left.csv", [row(y="349")])
        right = self.write_csv("right.csv", [row(y="351")])
        with self.assertRaisesRegex(ValueError, "non-unique source/vehicle/time"):
            read_observations([left, right])

    def test_scope_and_missing_fields_are_not_inferred(self):
        for i, bad in enumerate((
            row(time_ms=START - 100), row(time_ms=START + 50), row(time_ms=STOP),
            row(y="179.999"), row(y="380.001"), row(section=0, intersection=0),
            row(lane=""), row(y="NaN"), row(time_ms=str(START) + ".0"),
        )):
            with self.subTest(row=bad), self.assertRaises(ValueError):
                read_observations([self.write_csv(f"bad{i}.csv", [bad])])
        missing = self.write_csv("missing.csv", [{key: value for key, value in row().items() if key != "lane_id"}],
                                 [key for key in COLUMNS if key != "lane_id"])
        with self.assertRaisesRegex(ValueError, "source columns"):
            read_observations([missing])

    def test_gaps_and_track_disappearance_never_emit_exits_or_vacancies(self):
        path = self.write_csv("gap.csv", [row(y="349"), row(frame=3, time_ms=START + 200, y="351")])
        data = read_observations([path])
        events = event_records(data)
        kinds = [event["kind"] for event in events]
        self.assertIn("observation_gap", kinds)
        self.assertIn("candidate_gap_crossing", kinds)
        self.assertIn("observation_end", kinds)
        self.assertNotIn("observed_crossing_window", kinds)
        self.assertNotIn("exit", kinds)
        self.assertNotIn("vacancy", kinds)
        for event in events:
            self.assertTrue(event["provenance"])
            self.assertTrue(event["eventId"].startswith("sha256:"))
        summary = summarize(data)
        self.assertEqual(summary["screenlines"]["350"]["total"], 0)
        self.assertEqual(summary["screenlines"]["350"]["unaccepted_gap_transitions"], 1)
        self.assertEqual(summary["physical_exit_events"], 0)
        self.assertEqual(summary["street_cell_vacancy_events"], 0)

    def test_lane_change_is_retained_and_downstream_lane_is_only_a_reporting_convention(self):
        rows = [row(frame=i + 1, time_ms=START + i * 100, y=y, lane=lane)
                for i, (y, lane) in enumerate((("349", 2), ("351", 3), ("349", 3), ("351", 2)))]
        data = read_observations([self.write_csv("lanes.csv", rows)])
        observed = summarize(data)["screenlines"]["350"]
        self.assertEqual(observed["total"], 1)
        self.assertEqual(observed["all_adjacent_brackets"], 2)
        self.assertEqual(observed["lane_counts"], {3: 1})
        self.assertEqual(observed["first_crossings_with_changed_lane_code"], 1)
        self.assertEqual(observed["same_lane_first_crossings"], 0)
        crossings = [event for event in event_records(data) if event["kind"] == "observed_crossing_window"]
        self.assertEqual((crossings[0]["fromLane"], crossings[0]["toLane"]), (2, 3))
        self.assertIsNone(crossings[0]["exactCrossingTimeMs"])
        self.assertEqual(crossings[0]["geometryRole"], "virtual_screenline")
        self.assertFalse(crossings[0]["physicalStopLine"])

    def test_gap_candidates_after_first_crossing_do_not_change_legacy_count(self):
        rows = [row(frame=frame, time_ms=START + time, y=y)
                for frame, time, y in ((1, 0, "339"), (3, 200, "341"), (4, 300, "339"),
                                       (5, 400, "341"), (7, 600, "339"), (9, 800, "341"))]
        observed = summarize(read_observations([self.write_csv("recross.csv", rows)]))["screenlines"]["340"]
        self.assertEqual(observed["total"], 1)
        self.assertEqual(observed["unaccepted_gap_transitions"], 1)
        self.assertEqual(observed["all_gap_candidates"], 2)

    def test_slow_proxy_uses_exact_values_and_can_distinguish_the_two_clock_contracts(self):
        self.assertTrue(slow_proxy(sample(y="249.9999999999999999999", speed="3")))
        self.assertFalse(slow_proxy(sample(y="245", speed="3.0000000000000000001")))
        self.assertFalse(slow_proxy(sample(y="250", speed="0")))
        self.assertFalse(slow_proxy(sample(y="245", speed="-0.01")))
        rows = [row(frame=(999 if i == 15 else i + 1), time_ms=START + i * 100, y="245", speed="0")
                for i in range(31)]
        summary = summarize(read_observations([self.write_csv("clock-break.csv", rows)]))
        self.assertEqual(summary["sustained_slow_90_to_100ft_upstream"], 1)
        self.assertEqual(summary["sustained_slow_with_both_frame_and_time_adjacency"], 0)

    def test_event_order_and_identifiers_are_deterministic_without_claiming_causality(self):
        rows = [row(vehicle=2, frame=2, time_ms=START + 100, y="351"), row(vehicle=1, y="349"),
                row(vehicle=2, y="349"), row(vehicle=1, frame=2, time_ms=START + 100, y="351")]
        data = read_observations([self.write_csv("unordered.csv", rows)])
        first = event_records(data)
        self.assertEqual(first, event_records(data))
        self.assertEqual([event["endMs"] for event in first], sorted(event["endMs"] for event in first))
        self.assertEqual(len({event["eventId"] for event in first}), len(first))
        bundle = evidence_bundle(data)
        self.assertIn("ties serialize only", bundle["interpretation"]["ordering"])
        self.assertFalse(bundle["interpretation"]["streetCellVacancyEvidence"])
        self.assertIsNone(bundle["clock"]["controllerAlignment"])
        self.assertIsNone(bundle["geometry"][0]["physicalStopLineRegistration"])

    def test_fixture_corpus_is_explicitly_synthetic_and_shared_samples_keep_exact_rationals(self):
        bundle = fixture_bundle()
        self.assertEqual(bundle["expectedFirstCrossings"], [2, 2, 4])
        self.assertEqual(len(bundle["samples"]), 38)
        self.assertEqual(len(bundle["pairs"]), 20)
        self.assertTrue(all(source["kind"] == "synthetic_control" for source in bundle["sources"]))
        self.assertEqual(bundle["samples"][0]["y"]["den"], str(10 ** 19))
        self.assertTrue(bundle["pairs"][0]["expected"][2]["crossing"])
        self.assertFalse(bundle["pairs"][4]["expected"][2]["identity"])
        path = self.directory / "nested" / "cases.json"
        write_json(path, bundle)
        self.assertEqual(json.loads(path.read_text()), bundle)


if __name__ == "__main__":
    unittest.main()
