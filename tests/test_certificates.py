"""Identity-aware finite certificates for the two research-boundary witnesses."""
import json
from dataclasses import replace
from pathlib import Path

import numpy as np
import pytest

from bml.certificates import has_blocker_cycle, trace_labeled
from bml.exhaustive import encode
from bml.model import step


WITNESSES = json.loads((Path(__file__).parents[1] / "data/formal-witnesses.json").read_text())


def check_against_numpy(orbit):
    """Compare every certificate edge and move count with the original kernel."""
    for i, moved_labels in enumerate(orbit.moved):
        current = np.array(orbit.rows(i), dtype=np.int8)
        following = i + 1 if i + 1 < len(orbit.states) else orbit.cycle_start
        actual, moved = step(current)
        assert actual.tolist() == orbit.rows(following)
        assert int(moved) == len(moved_labels)
        assert len(moved_labels) == len(set(moved_labels))
        assert sorted(label for label in orbit.states[i] if label >= 0) == [
            label for label, _ in orbit.species
        ]
        for label, species in orbit.species:
            source = orbit.states[i].index(label)
            destination = orbit.states[following].index(label)
            if label not in moved_labels:
                assert destination == source
                continue
            y, x = divmod(source, orbit.width)
            expected = (y * orbit.width + (x + 1) % orbit.width if species == 1
                        else ((y + 1) % orbit.height) * orbit.width + x)
            assert destination == expected and destination != source


def test_added_stationary_car_changes_an_original_cars_fate():
    witness = WITNESSES["nonmonotonicity"]
    original, added = witness["original"], witness["added"]
    assert np.array(original).shape == np.array(added).shape == (witness["height"], witness["width"])
    flat_before, flat_after = np.array(original).ravel(), np.array(added).ravel()
    assert np.flatnonzero(flat_before != flat_after).tolist() == [witness["addition_cell"]]
    assert flat_before[witness["addition_cell"]] == 0
    assert flat_after[witness["addition_cell"]] == witness["addition_species"]
    assert int(encode(np.array([original]))[0]) == witness["original_code"]
    assert int(encode(np.array([added]))[0]) == witness["added_code"]

    labels = [i if sp else -1 for i, sp in enumerate(flat_before)]
    labels[witness["addition_cell"]] = witness["addition_label"]
    before = trace_labeled(original)
    after = trace_labeled(added, labels)
    check_against_numpy(before)
    check_against_numpy(after)
    assert (before.cycle_start, before.period) == (witness["original_transient"], witness["original_period"])
    assert (after.cycle_start, after.period) == (witness["added_transient"], witness["added_period"])
    assert all(before.cycle_moves(label) == 0 for label, _ in before.species)
    original_label = witness["original_car_moving_forever"]
    assert original_label in dict(before.species)
    assert after.cycle_moves(original_label) == witness["moves_per_added_cycle"] == after.period
    assert after.cycle_moves(witness["addition_label"]) == witness["added_car_moves_per_cycle"] == 0
    assert all(witness["addition_label"] not in moves for moves in after.moved)


def test_absence_of_an_initial_blocking_loop_does_not_prevent_later_gridlock():
    witness = WITNESSES["loop_formation"]
    assert np.array(witness["initial"]).shape == (witness["height"], witness["width"])
    assert int(encode(np.array([witness["initial"]]))[0]) == witness["initial_code"]
    assert has_blocker_cycle(witness["initial"]) is witness["initial_blocker_cycle"]
    orbit = trace_labeled(witness["initial"])
    check_against_numpy(orbit)
    assert (orbit.cycle_start, orbit.period) == (witness["transient"], witness["period"])
    final = orbit.rows(orbit.cycle_start)
    assert final == witness["final"]
    assert has_blocker_cycle(final) is witness["final_blocker_cycle"]
    assert not orbit.moved[orbit.cycle_start]


@pytest.mark.parametrize("rows", [[], [[]], [[0, 1], [2]], [[3]], [[1.9]], [["1"]]])
def test_certificate_rejects_invalid_grid(rows):
    with pytest.raises(ValueError):
        trace_labeled(rows)


def test_certificate_does_not_call_a_truncated_orbit_a_cycle():
    with pytest.raises(ValueError, match="step budget"):
        trace_labeled(WITNESSES["loop_formation"]["initial"], max_steps=2)


def test_certificate_rejects_duplicate_car_identity():
    with pytest.raises(ValueError, match="distinct"):
        trace_labeled([[1, 0, 2]], [0, -1, 0])


def test_comparator_rejects_same_color_identity_teleportation():
    witness = WITNESSES["nonmonotonicity"]
    after = trace_labeled(witness["added"], [8, 1, 2, 3, 4, -1, 6, 7])
    altered = tuple(2 if label == 1 else 1 if label == 2 else label for label in after.states[1])
    mutant = replace(after, states=(after.states[0], altered))
    assert mutant.rows(1) == after.rows(1)  # Occupancy alone cannot detect this mutation.
    with pytest.raises(AssertionError):
        check_against_numpy(mutant)
