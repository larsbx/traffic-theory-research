"""Exact initial-law calculations, finite basins, and lane-obstruction controls."""
from dataclasses import replace
from fractions import Fraction
from math import comb

import numpy as np
import pytest

from bml import probability
from bml.capture import find_blocker_cycles, trace_capture
from bml.certificates import trace_labeled
from bml.exhaustive import decode
from bml.model import TRAIN, step
from bml.probability import (
    EVENT_NAMES, EventCounts, FiniteCensus, analyze_torus, eventually_reaches, has_full_lane,
    make_strip_certificate, ring_probability, strip_bound_terms,
    strip_upper_bound, verify_strip_certificate,
)


@pytest.fixture(scope="module")
def square3():
    return analyze_torus(3, 3)


def test_exact_square3_bernstein_counts_and_negative_mixed_derivative(square3):
    jam = square3.event("gridlock")
    mixed = square3.event("eventual_mixed")
    assert jam.by_cars == (0, 0, 0, 6, 36, 180, 798, 2538, 1881, 512)
    assert mixed.by_cars == (0, 0, 0, 0, 0, 0, 384, 1872, 1062, 174)
    assert jam.coefficients == tuple(map(Fraction, (
        0, 0, 0, "1/112", "1/56", "5/112", "19/128", "141/256", "209/256", 1,
    )))
    assert mixed.coefficients[-4:] == tuple(map(Fraction, ("1/14", "13/32", "59/128", "87/256")))
    assert jam.coefficients_nondecreasing
    assert not mixed.coefficients_nondecreasing
    assert mixed.derivative(1) == Fraction(-279, 256)
    assert mixed.probability(Fraction(99, 100)) > mixed.probability(1)
    assert jam.probability(0) == 0 and jam.probability(1) == 1
    assert jam.derivative(1) == Fraction(423, 256)


def test_square2_exact_probability_polynomial():
    jam = analyze_torus(2, 2).event("gridlock")
    assert jam.by_cars == (0, 0, 4, 8, 16)
    assert jam.coefficients == (0, 0, Fraction(1, 6), Fraction(1, 4), 1)
    for p in (Fraction(0), Fraction(1, 7), Fraction(1, 2), Fraction(1)):
        assert jam.probability(p) == p ** 2 - p ** 3 + p ** 4
        assert jam.derivative(p) == 2 * p - 3 * p ** 2 + 4 * p ** 3


def test_initial_mixed_is_not_eventual_mixed_or_an_evolved_iid_law(square3):
    initial = square3.event("initial_mixed")
    eventual = square3.event("eventual_mixed")
    assert initial.total == 573 and eventual.total == 3492
    uniform = Fraction(2, 3)
    assert initial.probability(uniform) == Fraction(573, 19683)
    assert eventual.probability(uniform) == Fraction(3492, 19683)
    rows = [[2, 2, 1], [1, 1, 0]]
    assert not find_blocker_cycles(rows)
    assert trace_capture(rows).first_mixed_round == 4


def test_exact_ring_probability_identity_and_strip_bounds(square3):
    assert square3.event("full_lane").total == 4214
    assert square3.event("eventual_mixed").by_cars == square3.event("ringless_gridlock").by_cars
    for p in (Fraction(0), Fraction(1, 7), Fraction(1, 2), Fraction(2, 3), Fraction(1)):
        j = square3.event("gridlock").probability(p)
        m = square3.event("eventual_mixed").probability(p)
        r = ring_probability(3, 3, p)
        assert r == square3.event("full_lane").probability(p)
        assert 0 <= j - m <= r <= 6 * (p / 2) ** 3
        assert all(j <= strip_upper_bound(3, 3, p, k) for k in range(1, 4))
        for event in square3.events:
            if p == Fraction(2, 3):
                assert event.probability(p) == Fraction(event.total, square3.states)
    assert ring_probability(3, 3, 1) == Fraction(169, 256)


def test_strip_bound_exposes_union_terms_and_clamps_only_the_final_sum():
    terms = strip_bound_terms(3, 2, Fraction(1, 2), 2)
    assert terms == (Fraction(5, 16), Fraction(175, 256), Fraction(3, 16))
    assert sum(terms) == Fraction(303, 256)
    assert strip_upper_bound(3, 2, Fraction(1, 2), 2) == 1
    assert strip_upper_bound(3, 2, Fraction(1, 10), 2) == Fraction(33199, 160000)
    assert strip_upper_bound(3, 2, 0, 2) == 0


STRIP_ROWS = [[0, 0, 2, 0], [1, 0, 0, 0]]


def test_cyclic_strip_certificate_binds_conserved_lane_profiles():
    certificate = make_strip_certificate(STRIP_ROWS, start=3, k=3)
    assert certificate.east_rows == (0, 1)
    assert certificate.north_columns == (0, 0, 1, 0)
    state = np.array(STRIP_ROWS, dtype=np.int8)
    for _ in range(8):
        verify_strip_certificate(state.tolist(), certificate)
        state, _ = step(state)
    assert trace_capture(STRIP_ROWS).outcome != "gridlock"


@pytest.mark.parametrize("changes", [
    {"width": 5}, {"height": True}, {"width": 4.0},
    {"start": -1}, {"start": 4}, {"start": True},
    {"k": 0}, {"k": 5}, {"k": True}, {"k": 1.5},
    {"east_rows": None}, {"north_columns": 1}, {"east_rows": (0,)},
    {"east_rows": (0, True)}, {"north_columns": (0, 0, 0, 0)},
    {"east_rows": (0, 2)}, {"start": 1},
])
def test_forged_strip_certificates_are_rejected(changes):
    certificate = make_strip_certificate(STRIP_ROWS, start=3, k=3)
    with pytest.raises(ValueError):
        verify_strip_certificate(STRIP_ROWS, replace(certificate, **changes))


def test_no_full_north_column_condition_is_essential():
    rows = [[2, 0], [2, 0]]
    assert has_full_lane(rows) and trace_capture(rows).outcome == "gridlock"
    with pytest.raises(ValueError, match="full north"):
        make_strip_certificate(rows, start=1, k=1)
    with pytest.raises(ValueError, match="strictly less"):
        make_strip_certificate([[1, 1], [0, 0]], start=0, k=2)


def test_strip_checker_and_all_width_census_agree_on_every_2x2_input():
    census = analyze_torus(2, 2)
    counts = [0, 0]
    union = set()
    for code, state in enumerate(decode(np.arange(81), 2, 2)):
        rows = state.tolist()
        for k in (1, 2):
            certificates = []
            for start in (0, 1):
                try:
                    certificates.append(make_strip_certificate(rows, start, k))
                except ValueError:
                    pass
            if certificates:
                counts[k - 1] += 1
                union.add(code)
                assert trace_capture(rows).outcome != "gridlock"
    assert tuple(counts) == census.strip_certified_by_k == (5, 9)
    assert len(union) == census.strip_certified_union == 13


def test_graph_reachability_finds_targets_at_zero_later_and_never():
    successors = np.array([1, 2, 3, 3, 5, 4, 6])
    targets = np.array([False, False, False, True, False, False, True])
    expected = np.array([True, True, True, True, False, False, True])
    assert np.array_equal(eventually_reaches(successors, targets), expected)
    assert targets.tolist() == [False, False, False, True, False, False, True]
    assert eventually_reaches(np.array([0]), np.array([False])).tolist() == [False]


@pytest.mark.parametrize("successors,targets", [
    (np.array([], dtype=int), np.array([], dtype=bool)),
    (np.array([1]), np.array([True])),
    (np.array([-1]), np.array([True])),
    (np.array([0.0]), np.array([True])),
    (np.array([False]), np.array([True])),
    (np.array([[0]]), np.array([True])),
    (np.array([0]), np.array([1])),
    (np.array([0]), np.array([True, False])),
    ([0], np.array([True])),
])
def test_malformed_functional_graph_is_rejected(successors, targets):
    with pytest.raises(ValueError):
        eventually_reaches(successors, targets)


def test_mutant_that_uses_only_initial_mixed_cycles_is_rejected(monkeypatch):
    real = probability.eventually_reaches
    calls = 0

    def only_initial_mixed(successors, targets):
        nonlocal calls
        calls += 1
        return real(successors, targets) if calls == 1 else targets.copy()

    monkeypatch.setattr(probability, "eventually_reaches", only_initial_mixed)
    with pytest.raises(AssertionError, match="independently propagated M"):
        analyze_torus(3, 2)


def test_mutant_with_missing_direct_mixed_targets_is_rejected(monkeypatch):
    monkeypatch.setattr(probability, "find_blocker_cycles", lambda rows, **kwargs: ())
    with pytest.raises(AssertionError, match="independently propagated M"):
        analyze_torus(2, 2)


def test_adding_a_car_can_remove_eventual_mixed_capture_outside_R():
    before = [[1, 2, 2, 1], [2, 1, 1, 0], [1, 0, 2, 1], [2, 1, 1, 0]]
    after = [[1, 2, 2, 1], [2, 1, 1, 0], [1, 2, 2, 1], [2, 1, 1, 0]]
    assert not has_full_lane(before) and not has_full_lane(after)
    assert [(y, x) for y in range(4) for x in range(4) if before[y][x] != after[y][x]] == [(2, 1)]
    assert before[2][1] == 0 and after[2][1] == 2
    jam, flowing = trace_capture(before), trace_capture(after)
    assert (jam.first_mixed_round, jam.gridlock_round) == (2, 3)
    assert (flowing.first_core_round, flowing.gridlock_round) == (None, None)
    assert (flowing.cycle_start, flowing.period, flowing.cycle_move_count) == (2, 8, 28)
    assert flowing.mean_velocity == Fraction(1, 4)
    identities = trace_labeled(after)
    assert (identities.cycle_start, identities.period) == (2, 16)
    assert all(identities.cycle_moves(label) == 4 for label, _ in identities.species)
    assert all(not find_blocker_cycles(identities.rows(i)) for i in range(len(identities.states)))


@pytest.mark.parametrize("changes", [
    {"width": 0}, {"height": -1}, {"width": True}, {"height": 2.0},
    {"name": "Gridlock"}, {"name": "unknown"}, {"name": None},
    {"by_cars": None}, {"by_cars": []}, {"by_cars": (0, 0, 4, 8)},
    {"by_cars": (False, 0, 4, 8, 16)}, {"by_cars": (0, 0, 4.0, 8, 16)},
    {"by_cars": (0, 0, -1, 8, 16)}, {"by_cars": (0, 0, 25, 8, 16)},
    {"by_cars": (0, 0, 4, 8, 17)}, {"rule": TRAIN},
])
def test_invalid_counts_and_event_metadata_are_rejected(changes):
    valid = EventCounts(2, 2, "gridlock", (0, 0, 4, 8, 16))
    with pytest.raises(ValueError):
        replace(valid, **changes)


def test_raw_event_counts_are_arithmetic_not_a_dynamic_certificate():
    supplied = EventCounts(2, 2, "gridlock", (0, 0, 0, 0, 0))
    assert supplied.probability(Fraction(2, 3)) == 0
    assert analyze_torus(2, 2).event("gridlock").total == 28


def test_integral_census_metadata_uses_unbounded_python_arithmetic():
    # An internally consistent supplied table, not a claimed dynamical census:
    # this exercises large metadata without enumerating 3**40 configurations.
    capacity = tuple(comb(40, k) * 2 ** k for k in range(41))
    events = tuple(EventCounts(np.int64(40), np.int64(1), name,
                               capacity if name == "ringless" else (0,) * 41)
                   for name in EVENT_NAMES)
    census = FiniteCensus(np.int64(40), np.int64(1), events,
                         (np.int64(2 ** 62),) * 40, np.int64(2 ** 62))
    assert type(census.width) is type(census.height) is type(census.states) is int
    assert census.states == 12157665459056928801 == 3 ** 40
    assert all(type(count) is int for count in census.strip_certified_by_k)
    assert type(census.strip_certified_union) is int
    assert sum(census.strip_certified_by_k) == 40 * 2 ** 62


def test_census_rejects_mislabeled_or_inconsistent_events(square3):
    events = list(square3.events)
    events[1] = replace(events[1], name="initial_mixed")
    with pytest.raises(ValueError, match="exact names"):
        replace(square3, events=tuple(events))
    events[1] = replace(square3.events[1], by_cars=square3.event("initial_mixed").by_cars)
    with pytest.raises(ValueError, match="inconsistent event counts"):
        replace(square3, events=tuple(events))
    with pytest.raises(ValueError, match="strip counts"):
        replace(square3, strip_certified_union=True)
    with pytest.raises(ValueError, match="unknown"):
        square3.event("Gridlock")


@pytest.mark.parametrize("p", [-1, Fraction(11, 10), True, 0.5, float("nan"), "1/2", None])
def test_inexact_or_invalid_densities_are_rejected(p, square3):
    for operation in (
        lambda: ring_probability(3, 3, p), lambda: strip_upper_bound(3, 3, p, 2),
        lambda: square3.event("gridlock").probability(p),
        lambda: square3.event("gridlock").derivative(p),
    ):
        with pytest.raises(ValueError):
            operation()


@pytest.mark.parametrize("dimension", [0, -1, True, 2.0, None])
def test_invalid_dimensions_are_rejected(dimension):
    with pytest.raises(ValueError):
        ring_probability(dimension, 2, Fraction(1, 2))
    with pytest.raises(ValueError):
        analyze_torus(2, dimension)


@pytest.mark.parametrize("k", [0, -1, 4, True, 1.5, None])
def test_invalid_strip_width_is_rejected(k):
    with pytest.raises(ValueError):
        strip_upper_bound(3, 2, Fraction(1, 2), k)


@pytest.mark.parametrize("rows", [None, [], [[]], [[0], [0, 1]], [[True]], [[1.0]], [[3]]])
def test_malformed_grids_are_rejected(rows):
    with pytest.raises(ValueError):
        has_full_lane(rows)


def test_train_rule_is_rejected_across_probability_interfaces():
    certificate = make_strip_certificate(STRIP_ROWS, 3, 3)
    for operation in (
        lambda: analyze_torus(2, 2, rule=TRAIN),
        lambda: ring_probability(2, 2, Fraction(1, 2), rule=TRAIN),
        lambda: strip_upper_bound(2, 2, Fraction(1, 2), 1, rule=TRAIN),
        lambda: has_full_lane(STRIP_ROWS, rule=TRAIN),
        lambda: make_strip_certificate(STRIP_ROWS, 3, 3, rule=TRAIN),
        lambda: verify_strip_certificate(STRIP_ROWS, certificate, rule=TRAIN),
    ):
        with pytest.raises(ValueError, match="CLASSIC"):
            operation()


def test_singletons_empty_state_and_explicit_enumeration_budget():
    census = analyze_torus(1, 1)
    assert census.event("gridlock").by_cars == (0, 2)
    assert census.event("eventual_mixed").total == 0
    assert census.strip_certified_by_k == (1,)
    assert census.event("full_lane").probability(Fraction(1, 3)) == ring_probability(1, 1, Fraction(1, 3))
    verify_strip_certificate([[0]], make_strip_certificate([[0]], 0, 1))
    with pytest.raises(ValueError, match="twelve"):
        analyze_torus(4, 4)
