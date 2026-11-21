"""Independent finite controls for the CLASSIC stopped/core acceptance bridge."""
from fractions import Fraction
from math import factorial

import pytest

from scripts import check_stopped_core as acceptance


@pytest.fixture(scope="module")
def square2():
    return [acceptance.analyze_case(2, 2, code) for code in range(81)]


def test_full_small_domain_core_label_identity_and_pointwise_sandwich(square2):
    # Complete finite support: J is read from actual zero-movement rounds,
    # Z from original identities, and K from snapshot successor walks.
    assert len(square2) == 81
    assert sum(case.stopped for case in square2) == 112
    for case in square2:
        n, z = case.population, case.stopped
        assert n * case.gridlock <= z <= n * (case.gridlock + case.full_lane)
        assert acceptance.core_labels(case.orbit, case.orbit.cycle_start) == case.stopped_labels
        row = case.snapshot(case.orbit.cycle_start)
        assert row[6] == row[7] == z
        assert row[8] == int(case.gridlock)
    empty = square2[0]
    assert empty.population == empty.stopped == 0 and not empty.gridlock
    partial = square2[13]
    assert partial.population == 3 and partial.stopped == 2 and partial.full_lane and not partial.gridlock


def test_normalization_uses_per_board_population_and_preserves_empty_mass(square2):
    partial, jam, empty = square2[13], square2[4], square2[0]
    equal = acceptance.scaled_initial_law([partial, jam], [1, 1])
    assert equal["normalized_stopped_fraction"] == "5/6"
    ratio_of_expectations = Fraction(partial.stopped + jam.stopped, partial.population + jam.population)
    assert ratio_of_expectations == Fraction(4, 5) != Fraction(equal["normalized_stopped_fraction"])
    with_empty = acceptance.scaled_initial_law([empty, partial, jam], [1, 1, 1])
    assert with_empty["normalized_stopped_fraction"] == "5/9"
    assert with_empty["gridlock_probability"] == "1/3"
    assert with_empty["total_weight"] == 3  # Empty mass is retained in the law.
    assert with_empty["scaled_stopped_mass"] == 40


def test_denominator_cancellation_repeats_and_zero_weights(square2):
    support = [square2[0], square2[13], square2[13], square2[4], square2[1]]
    weights = [5, 3, 2, 7, 0]
    result = acceptance.scaled_initial_law(support, weights)
    merged = acceptance.scaled_initial_law([square2[0], square2[13], square2[4]], [5, 5, 7])
    assert result["population_denominator"] == factorial(4) == 24
    assert result["scaled_stopped_mass"] == 248
    assert result["normalized_stopped_fraction"] == merged["normalized_stopped_fraction"] == "31/51"
    assert result["gap"] == "10/51"
    doubled = acceptance.scaled_initial_law(support, weights, denominator=48)
    assert doubled["scaled_stopped_mass"] == 2 * result["scaled_stopped_mass"]
    assert doubled["normalized_stopped_fraction"] == result["normalized_stopped_fraction"]
    zero = acceptance.scaled_initial_law([square2[0], square2[13]], [0, 0])
    assert zero["scaled_stopped_mass"] == zero["total_weight"] == 0
    assert not zero["probability_law_defined"] and zero["normalized_stopped_fraction"] is None
    for denominator in (0, 1, 5, -24, True, 24.0):
        with pytest.raises(ValueError, match="population denominator"):
            acceptance.scaled_initial_law(support, weights, denominator=denominator)
    for weights in ([5, 3, 2, -1, 0], [5, 3, 2, True, 0], [5, 3, 2, 0.5, 0]):
        with pytest.raises(ValueError, match="natural"):
            acceptance.scaled_initial_law(support, weights)


def test_initial_iid_weights_and_density_endpoints(square2):
    for p in acceptance.DENSITIES:
        result = acceptance.iid_initial_law(square2, p)
        assert result["total_weight"] == (2 * p.denominator) ** 4
        assert 0 <= Fraction(result["gap"]) <= Fraction(result["full_lane_probability"])
    assert acceptance.iid_initial_law(square2, 0)["normalized_stopped_fraction"] == "0"
    assert acceptance.iid_initial_law(square2, 1)["normalized_stopped_fraction"] == "1"
    for p in (True, 0.5, -1, Fraction(3, 2)):
        with pytest.raises(ValueError, match="exact rational"):
            acceptance.iid_initial_law(square2, p)
    with pytest.raises(ValueError, match="every initial board"):
        acceptance.iid_initial_law(square2[:-1] + [square2[0]], Fraction(1, 2))


def test_colored_period_and_snapshot_core_shortcuts_are_detected():
    code14 = acceptance.analyze_case(3, 3, 14)
    assert code14.colored_period == 4 and code14.orbit.period == 8
    assert code14.orbit.rows(0) == code14.orbit.rows(4)
    assert code14.orbit.states[0] != code14.orbit.states[4]
    assert code14.stopped == 0 and not code14.full_lane and not code14.gridlock
    assert acceptance.direct_path_count(code14.orbit.rows(0), 2) == 1
    assert code14.snapshot(0)[6] == code14.snapshot(4)[6] == code14.snapshot(8)[6] == 0
    for side in (4, 6):
        delayed = acceptance.delayed_case(side)
        delay = (side - 2) // 2
        assert delayed.initial_core == 0 < delayed.stopped == 2 * side
        assert delayed.snapshot(delay - 1)[6] == 0
        assert delayed.snapshot(delay)[6] == delayed.snapshot(delay + 1)[6] == 2 * side
    with pytest.raises(ValueError, match="did not recur"):
        acceptance.analyze_case(3, 3, 14, max_steps=4)


def test_export_comparison_rejects_wrong_counts_missing_and_reordered_rows(square2):
    expected = [square2[0].snapshot(0), square2[13].snapshot(0), square2[13].snapshot(2)]
    output = "\n".join(",".join(map(str, row)) for row in expected) + "\n"
    acceptance.verify_export_rows(expected, output)
    for field in (4, 5, 6, 7, 8, 9):
        corrupted = [list(row) for row in expected]
        corrupted[1][field] += 1
        mutant = "\n".join(",".join(map(str, row)) for row in corrupted)
        with pytest.raises(AssertionError, match="mismatch"):
            acceptance.verify_export_rows(expected, mutant)
    with pytest.raises(AssertionError, match="missing or extra"):
        acceptance.verify_export_rows(expected, "\n".join(output.splitlines()[:-1]))
    with pytest.raises(AssertionError, match="mismatch"):
        acceptance.verify_export_rows(expected, "\n".join(reversed(output.splitlines())))
