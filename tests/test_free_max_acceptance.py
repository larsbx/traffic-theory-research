"""Adversarial acceptance tests independent of the Lean exporter executable."""
from dataclasses import replace

import pytest

from scripts.check_free_max import (
    FreeMaxError, capacity, check_output, expected_keys, fixture,
    negative_controls, parse_rows, validate_trace,
)


# Explicit maximizing boards for every ordered shape through side three.
# The 3x3 case contains both species and attains the density 2/3 boundary.
MAXIMIZERS = {
    (1, 1): (0,),
    (1, 2): (2, 0),
    (1, 3): (2, 0, 0),
    (2, 1): (1, 0),
    (2, 2): (1, 0, 0, 1),
    (2, 3): (1, 0, 1, 0, 1, 0),
    (3, 1): (1, 0, 0),
    (3, 2): (2, 2, 2, 0, 0, 0),
    (3, 3): (2, 1, 0, 1, 0, 2, 0, 2, 1),
}


def small_output() -> str:
    rows = []
    for w, h, n in expected_keys(3):
        maximum = MAXIMIZERS[w, h]
        occupied = [i for i, digit in enumerate(maximum) if digit]
        keep = set(occupied[:n])
        initial = tuple(digit if i in keep else 0 for i, digit in enumerate(maximum))
        rows.append(fixture(w, h, initial).tsv())
    return "\n".join(rows) + "\n"


def test_complete_small_domain_replays_both_species_and_closing_edges():
    output = small_output()
    rows, rectangles = check_output(output, 3)
    assert [row.key for row in rows] == expected_keys(3)
    assert len(rectangles) == 9
    assert rows[-1].car_count == 6 and (rows[-1].east_count, rows[-1].north_count) == (3, 3)
    assert all(row.state_digits[0] == row.state_digits[-1] for row in rows)
    assert parse_rows("\n".join(row.tsv() for row in rows)) == rows


def test_rejection_controls_fail_for_their_targeted_reasons():
    rows, _ = check_output(small_output(), 3)
    controls = negative_controls(rows, 3)
    assert len(controls) == 22
    observed = {control["name"]: control["reason"] for control in controls}
    assert observed["corrupted-closing-edge"] == "phase-mismatch"
    assert observed["missing-final-state"] == "trace-length"
    assert observed["wrong-formula"] == "formula"
    assert sum(reason == "static-blocked" for reason in observed.values()) == 4


def test_dropping_only_the_maximum_population_is_not_complete_coverage():
    rows = parse_rows(small_output())
    with pytest.raises(FreeMaxError, match="missing") as error:
        check_output("\n".join(row.tsv() for row in rows[:-1]), 3)
    assert error.value.reason == "coverage"


def test_ternary_validation_precedes_integer_normalization():
    row = fixture(3, 1, (1, 0, 0))
    for malformed in ("٠10", "-10", "310"):
        with pytest.raises(FreeMaxError) as error:
            validate_trace(replace(row, east_digits=(malformed, *row.east_digits[1:])))
        assert error.value.reason == "invalid-digits"


@pytest.mark.parametrize("width,height,expected", [
    (1, 1, 0), (1, 12, 6), (12, 1, 6), (2, 3, 3), (3, 2, 3),
    (3, 3, 6), (4, 4, 8), (5, 5, 15), (6, 6, 24), (7, 7, 28),
    (10, 12, 60), (9, 12, 72),
])
def test_capacity_branches_and_small_remainders(width, height, expected):
    assert capacity(width, height) == expected
