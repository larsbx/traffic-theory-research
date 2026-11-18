"""Independent tagged fixation, exact initial-law Palm weights, and negative controls."""
from dataclasses import replace
from fractions import Fraction
from math import comb

import numpy as np
import pytest

from bml import fixation
from bml.certificates import LabeledOrbit, trace_labeled
from bml.exhaustive import decode
from bml.fixation import (
    FixationCounts, analyze_fixation, ring_palm_probability, trace_fixation, verify_fixation,
)
from bml.model import TRAIN
from bml.probability import has_full_lane, ring_probability


@pytest.fixture(scope="module")
def censuses():
    return {shape: analyze_fixation(*shape) for shape in
            ((1, 1), (1, 2), (2, 1), (3, 2), (2, 3), (2, 2), (3, 3))}


def test_exact_stopped_histogram_and_partial_fixation(censuses):
    census = censuses[2, 2]
    counts = census.counts
    assert counts.stopped_histogram == (
        (1,), (8, 0), (20, 0, 4), (16, 0, 8, 8), (0, 0, 0, 0, 16),
    )
    assert counts.any_stopped_by_cars == (0, 0, 4, 16, 16)
    assert counts.partial_fixation_by_cars == (0, 0, 0, 8, 0)
    assert counts.stopped_tags_by_cars == (0, 0, 8, 40, 64)
    assert counts.gridlock_by_cars == (0, 0, 4, 8, 16)
    assert counts.full_lane_by_cars == (0, 0, 4, 16, 14)
    assert (census.tagged_edges, census.max_labeled_period, census.max_transient) == (177, 4, 0)
    assert census.outside_ring_intermediate == 28


def test_complete_square3_tagged_census(censuses):
    census = censuses[3, 3]
    counts = census.counts
    assert counts.states == 19683
    assert counts.any_stopped_by_cars == (0, 0, 0, 6, 72, 360, 1338, 3276, 2142, 512)
    assert sum(counts.stopped_tags_by_cars) == 52002
    assert sum(counts.partial_fixation_by_cars) == 1755
    assert sum(counts.gridlock_by_cars) == 5951
    assert sum(counts.full_lane_by_cars) == 4214
    assert census.tagged_edges == 162141 and census.outside_ring_intermediate == 9945
    assert (census.max_labeled_period, census.max_transient) == (18, 15)


def test_event_probability_and_car_weighted_probability_are_distinct(censuses):
    counts = censuses[2, 2].counts
    p = Fraction(1, 2)
    palm = counts.palm(p)
    assert (palm.f, palm.q, palm.q_car, palm.delta, palm.r_car) == (
        Fraction(11, 32), Fraction(3, 16), Fraction(9, 32), Fraction(1, 16), Fraction(23, 64),
    )
    assert palm.f != counts.event_probability("any_stopped", p)
    assert palm.q_car != palm.q
    assert palm.delta > 0
    assert palm.q == counts.event_probability("gridlock", p)
    assert counts.palm(Fraction(2, 3)).f == Fraction(14, 27)
    square3 = censuses[3, 3].counts.palm(Fraction(1, 2))
    assert (square3.f, square3.q_car, square3.delta) == (
        Fraction(6007, 32768), Fraction(2281, 16384), Fraction(1445, 32768),
    )


def test_exact_score_covariance_and_ring_bounds_on_small_domains(censuses):
    for (w, h), census in censuses.items():
        counts = census.counts
        for p in (Fraction(1, 7), Fraction(1, 2), Fraction(2, 3), Fraction(1)):
            palm = counts.palm(p)
            ring = counts.event_probability("full_lane", p)
            assert ring == ring_probability(w, h, p)
            assert palm.q_car == palm.score_rhs
            assert palm.f == palm.q + (1 - p) * counts.gridlock_event.derivative(p) / (w * h) + palm.delta
            assert palm.r_car == ring_palm_probability(w, h, p)
            assert 0 <= palm.delta <= palm.r_car <= min(1, ring / p)
            assert 0 <= palm.f <= 1 and 0 <= palm.q_car <= 1
            assert palm.covariance_lhs <= palm.covariance_rhs
            if p == 1:
                assert palm.f == palm.q_car == palm.q == 1
                assert palm.delta == palm.covariance_lhs == palm.covariance_rhs == 0


def test_direct_origin_conditioning_agrees_with_car_weighted_histogram(censuses):
    # Independently sum initial per-configuration iid weights with origin occupied,
    # following the origin identity itself rather than using N/area weighting.
    for p in (Fraction(1, 3), Fraction(1, 2), Fraction(1)):
        stopped_mass = jam_mass = ring_mass = occupied_mass = Fraction()
        for state in decode(np.arange(81), 2, 2):
            rows = state.tolist()
            if not rows[0][0]:
                continue
            orbit = trace_labeled(rows)
            n = len(orbit.species)
            weight = (p / 2) ** n * (1 - p) ** (4 - n)
            occupied_mass += weight
            stopped_mass += weight * (orbit.cycle_moves(0) == 0)
            jam_mass += weight * all(orbit.cycle_moves(label) == 0 for label, _ in orbit.species)
            ring_mass += weight * has_full_lane(rows)
        assert occupied_mass == p
        palm = censuses[2, 2].counts.palm(p)
        assert (stopped_mass / p, jam_mass / p, ring_mass / p) == (palm.f, palm.q_car, palm.r_car)


def test_partial_fixation_requires_neither_global_jam_nor_full_speed():
    trace = trace_fixation([[1, 1], [1, 0]])
    assert trace.full_lane and trace.any_stopped and trace.partial_fixation
    assert not trace.gridlock and not trace.free
    assert trace.stopped_labels == (0, 1)
    assert trace.recurrent_moves == ((0, 0), (1, 0), (2, 2))
    assert trace.period == 2
    balanced = trace_fixation([[1, 1, 1], [1, 0, 0], [2, 0, 0], [2, 2, 2]])
    assert balanced.stopped_count == 7 and balanced.car_count == 8
    assert dict(balanced.speeds)[3] == 1


def test_outside_ring_intermediate_orbits_move_every_identity_forever():
    trace = trace_fixation([[1, 2, 2, 1], [2, 1, 1, 0]])
    assert not trace.full_lane and not trace.any_stopped and not trace.free
    assert (trace.transient, trace.period) == (2, 16)
    assert all(speed == Fraction(1, 4) for _, speed in trace.speeds)
    slow = trace_fixation([[1, 1, 1, 2], [2, 2, 2, 1], [0, 0, 0, 0]])
    assert not slow.full_lane and not slow.any_stopped
    assert (slow.transient, slow.period) == (1, 36)
    assert tuple(moves for _, moves in slow.recurrent_moves) == (4, 4, 4, 9, 9, 9, 9, 36)


def test_joint_empty_species_lanes_do_not_exclude_mixed_fixation():
    rows = [[1, 1, 2], [2, 0, 1], [2, 0, 0]]
    trace = trace_fixation(rows)
    assert not any(cell == 1 for cell in rows[2])
    assert not any(row[1] == 2 for row in rows)
    assert trace.gridlock and trace.stopped_count == 6 and not trace.full_lane


def test_addition_can_remove_fixation_outside_the_ring_event():
    before = [[1, 2, 2, 1], [2, 1, 1, 0], [1, 0, 2, 1], [2, 1, 1, 0]]
    after = [[1, 2, 2, 1], [2, 1, 1, 0], [1, 2, 2, 1], [2, 1, 1, 0]]
    frozen, moving = trace_fixation(before), trace_fixation(after)
    assert not frozen.full_lane and not moving.full_lane
    assert frozen.stopped_count == frozen.car_count == 13
    assert moving.stopped_count == 0 and moving.car_count == 14


def test_permanent_car_does_not_require_its_initial_blocker_to_stay():
    east_rows = [[1, 1, 0], [1, 1, 1], [0, 2, 0]]
    east_orbit = trace_labeled(east_rows)
    assert all(0 not in edge for edge in east_orbit.moved)
    assert 1 in east_orbit.moved[0]
    assert east_orbit.states[0][1] == 1 and east_orbit.states[1][1] == 7
    assert verify_fixation(east_rows, east_orbit).gridlock
    north_rows = [[2, 2, 0], [2, 2, 1], [0, 2, 0]]
    north_orbit = trace_labeled(north_rows)
    assert all(0 not in edge for edge in north_orbit.moved)
    assert north_orbit.states[1][3] == -1  # The E half-step fills this before N tests it.
    assert north_orbit.states[2][3] == 5
    assert verify_fixation(north_rows, north_orbit).gridlock


def test_missing_input_identity_and_same_species_teleport_are_rejected():
    rows = [[1, 1, 2], [2, 0, 1], [2, 1, 0]]
    deleted = [[1, 1, 2], [2, 0, 1], [2, 0, 0]]
    with pytest.raises(ValueError, match="species"):
        verify_fixation(rows, trace_labeled(deleted))
    rows = [[1, 2, 0, 0], [1, 1, 2, 1], [1, 0, 1, 2], [2, 0, 0, 1]]
    orbit = trace_labeled(rows)
    state = list(orbit.states[1])
    left, right = state.index(4), state.index(7)
    state[left], state[right] = state[right], state[left]
    mutant = replace(orbit, states=(orbit.states[0], tuple(state)))
    with pytest.raises(ValueError, match="position changes"):
        verify_fixation(rows, mutant)


def test_train_style_following_is_rejected_even_with_valid_identity_steps():
    orbit = LabeledOrbit(1, 3, ((0, 1), (1, 1)),
                         ((0, 1, -1), (-1, 0, 1), (1, -1, 0)),
                         ((0, 1), (0, 1), (0, 1)), 0)
    with pytest.raises(ValueError, match="production dynamics"):
        verify_fixation([[1, 1, 0]], orbit)


def test_erased_movement_is_rejected_even_when_S_and_J_would_not_change(monkeypatch):
    rows = [[1, 1, 1], [1, 1, 0]]
    real = fixation.trace_labeled
    orbit = real(rows)
    mutant = replace(orbit, moved=tuple(tuple(label for label in edge if label != 3)
                                        for edge in orbit.moved))
    # Both actual and falsified movement records say S=true, J=false; only Z differs.
    assert orbit.cycle_moves(3) > 0 and mutant.cycle_moves(3) == 0
    assert mutant.cycle_moves(4) > 0 and mutant.cycle_moves(0) == 0
    monkeypatch.setattr(fixation, "trace_labeled",
                        lambda candidate, **kwargs: mutant if candidate == rows else real(candidate, **kwargs))
    with pytest.raises(ValueError, match="constant identity positions"):
        analyze_fixation(3, 2)


@pytest.mark.parametrize("changes", [
    {"height": True}, {"width": 2.0}, {"species": None}, {"species": ((True, 1),)},
    {"states": None}, {"states": ()}, {"moved": None}, {"cycle_start": True},
    {"cycle_start": -1}, {"cycle_start": 2}, {"moved": ((2, 2), (2,))},
])
def test_malformed_supplied_orbits_are_rejected(changes):
    rows = [[1, 1], [1, 0]]
    with pytest.raises(ValueError):
        verify_fixation(rows, replace(trace_labeled(rows), **changes))


@pytest.mark.parametrize("changes", [
    {"width": 0}, {"height": True}, {"width": 2.0}, {"rule": TRAIN},
    {"stopped_histogram": None}, {"stopped_histogram": ()},
    {"gridlock_by_cars": None}, {"gridlock_by_cars": (0, 0, 4, 8)},
    {"gridlock_by_cars": (False, 0, 4, 8, 16)},
    {"gridlock_by_cars": (0, 0, 4.0, 8, 16)},
    {"gridlock_by_cars": (0, 0, 4, 8, 17)},
    {"gridlock_by_cars": (0, 0, 4, 7, 16)},
    {"full_lane_by_cars": (0, 0, 4, 0, 14)},
    {"full_lane_by_cars": (0, 0, 5, 16, 14)},
])
def test_invalid_count_metadata_is_rejected(changes, censuses):
    with pytest.raises(ValueError):
        replace(censuses[2, 2].counts, **changes)


@pytest.mark.parametrize("row", [None, (1, 0), (True,), (1.0,), (-1,), (0,), (2,)])
def test_invalid_histogram_rows_are_rejected(row, censuses):
    counts = censuses[2, 2].counts
    with pytest.raises(ValueError):
        replace(counts, stopped_histogram=(row,) + counts.stopped_histogram[1:])


def test_metadata_only_tables_normalize_numpy_integers_without_claiming_dynamics():
    # This deliberately supplied table describes no real CLASSIC census: metadata
    # validation establishes arithmetic consistency, not authenticity of events.
    capacities = tuple(comb(40, n) * 2 ** n for n in range(41))
    histogram = tuple((np.int64(capacity),) + (np.int64(0),) * n
                      for n, capacity in enumerate(capacities))
    zeros = (np.int64(0),) * 41
    counts = FixationCounts(np.int64(40), np.int64(1), histogram, zeros, zeros)
    assert type(counts.width) is type(counts.height) is type(counts.states) is int
    assert counts.states == 12157665459056928801 == 3 ** 40
    assert all(type(value) is int for row in counts.stopped_histogram for value in row)
    assert counts.palm(Fraction(1, 2)).f == 0


@pytest.mark.parametrize("p", [0, -1, Fraction(11, 10), True, 0.5, float("nan"), "1/2", None])
def test_invalid_or_zero_palm_density_is_rejected(p, censuses):
    with pytest.raises(ValueError):
        censuses[2, 2].counts.palm(p)
    with pytest.raises(ValueError):
        ring_palm_probability(2, 2, p)


def test_event_probability_allows_zero_but_rejects_wrong_event_names(censuses):
    counts = censuses[2, 2].counts
    assert all(counts.event_probability(name, 0) == 0 for name in fixation.FIXATION_EVENTS)
    for name in ("S", "Gridlock", None, ["gridlock"]):
        with pytest.raises(ValueError, match="event name"):
            counts.event_probability(name, Fraction(1, 2))


@pytest.mark.parametrize("budget", [0, -1, True, 1.5, None])
def test_invalid_recurrence_budgets_are_rejected(budget):
    with pytest.raises(ValueError):
        trace_fixation([[1, 0, 0]], max_steps=budget)
    with pytest.raises(ValueError):
        analyze_fixation(2, 2, max_steps=budget)


def test_cutoffs_are_unresolved_and_recurrence_boundary_is_included():
    with pytest.raises(ValueError, match="did not recur"):
        trace_fixation([[1, 0, 0]], max_steps=2)
    assert trace_fixation([[1, 0, 0]], max_steps=3).period == 3
    with pytest.raises(ValueError, match="did not recur"):
        analyze_fixation(2, 2, max_steps=1)


@pytest.mark.parametrize("rows", [None, [], [[]], [[0], [0, 1]], [[True]], [[1.0]], [[3]]])
def test_malformed_grids_are_rejected(rows):
    with pytest.raises(ValueError):
        trace_fixation(rows)


def test_singleton_empty_and_rule_boundaries(censuses):
    for rows in ([[1]], [[2]]):
        trace = trace_fixation(rows)
        assert trace.gridlock and trace.any_stopped and trace.full_lane
        assert trace.stopped_count == 1 and not trace.partial_fixation
    empty = trace_fixation([[0]])
    assert empty.free and not empty.any_stopped and not empty.gridlock and not empty.full_lane
    for p in (Fraction(1, 3), Fraction(1)):
        assert censuses[1, 1].counts.palm(p).f == 1
        assert ring_palm_probability(1, 1, p) == 1
        assert ring_palm_probability(1, 2, p) == (1 + p) / 2
        assert ring_palm_probability(2, 1, p) == (1 + p) / 2
    for operation in (
        lambda: analyze_fixation(2, 2, rule=TRAIN),
        lambda: trace_fixation([[0]], rule=TRAIN),
        lambda: verify_fixation([[0]], trace_labeled([[0]]), rule=TRAIN),
        lambda: ring_palm_probability(2, 2, Fraction(1, 2), rule=TRAIN),
    ):
        with pytest.raises(ValueError, match="CLASSIC"):
            operation()
    with pytest.raises(ValueError, match="twelve"):
        analyze_fixation(4, 4)
