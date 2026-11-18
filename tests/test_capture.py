"""Direct blocking certificates, formation observations, and capture controls."""
from dataclasses import replace
from fractions import Fraction

import numpy as np
import pytest

from bml import capture
from bml.capture import find_blocker_cycles, trace_capture, verify_capture, verify_cycle
from bml.certificates import has_blocker_cycle
from bml.exhaustive import decode
from bml.model import TRAIN


# The six core cars follow E,E,N,E,N,N. The extra E at (y,x)=(2,1)
# moves once before it reaches a permanent core obstacle.
CAPTURE = [[1, 1, 2], [2, 0, 1], [2, 1, 0]]
MIXED = find_blocker_cycles(CAPTURE)[0]
BALANCED_PARTIAL = [[1, 1, 1], [1, 0, 0], [2, 0, 0], [2, 2, 2]]
LATER_LOOP = [[2, 2, 1], [1, 1, 0]]


def test_mixed_certificate_captures_with_a_strict_integer_rank():
    assert MIXED.cells == (0, 1, 2, 5, 3, 6)
    assert MIXED.directions == (1, 1, 2, 1, 2, 2)
    assert MIXED.winding == (1, 1)
    assert MIXED.mixed
    verify_cycle(CAPTURE, MIXED, require_mixed=True)
    result = verify_capture(CAPTURE, MIXED)
    assert result.move_budget == 14
    assert result.rounds_to_gridlock == result.total_moves == 1
    assert result.rank_history == (2, 1)
    assert result.final_rows == ((1, 1, 2), (2, 0, 1), (2, 0, 1))
    trace = trace_capture(CAPTURE)
    assert (trace.first_core_round, trace.first_mixed_round, trace.gridlock_round) == (0, 0, 1)
    assert trace.outcome == "gridlock"
    assert trace.mean_velocity == 0


@pytest.mark.parametrize("mutant", [
    replace(MIXED, height=4),
    replace(MIXED, width=3.0),
    replace(MIXED, cells=()),
    replace(MIXED, cells=(0, 1, 2, 5, 3, 0)),
    replace(MIXED, cells=(0, 1, 2, 5, 3, 9)),
    replace(MIXED, cells=(0, 1, 2, 5, 3, -1)),
    replace(MIXED, cells=(0, 1, 2, 5, 3, 6.0)),
    replace(MIXED, cells=(0, 2, 1, 5, 3, 6)),
    replace(MIXED, directions=(2, 1, 2, 1, 2, 2)),
    replace(MIXED, directions=(1, 1, 2, 1, 2)),
    replace(MIXED, directions=(True, 1, 2, 1, 2, 2)),
    replace(MIXED, winding=(1, 0)),
    replace(MIXED, winding=(2, 1)),
    replace(MIXED, winding=(1, True)),
    replace(MIXED, winding=(1,)),
    replace(MIXED, cells=None),
    replace(MIXED, cells=1),
    replace(MIXED, directions=None),
    replace(MIXED, directions=1),
    replace(MIXED, winding=None),
    replace(MIXED, winding=1),
])
def test_forged_cycle_certificate_is_rejected(mutant):
    with pytest.raises(ValueError):
        verify_cycle(CAPTURE, mutant, require_mixed=True)


@pytest.mark.parametrize("replacement", [0, 2])
def test_certificate_is_bound_to_actual_occupied_directions(replacement):
    changed = [row[:] for row in CAPTURE]
    changed[0][0] = replacement
    with pytest.raises(ValueError, match="direction"):
        verify_capture(changed, MIXED)


def test_cycle_checker_rejects_a_nonclosing_directed_path():
    short = replace(MIXED, cells=MIXED.cells[:-1], directions=MIXED.directions[:-1])
    with pytest.raises(ValueError, match="edge"):
        verify_cycle(CAPTURE, short)


def test_monochromatic_core_does_not_certify_whole_system_gridlock():
    core, = find_blocker_cycles(BALANCED_PARTIAL)
    assert core.winding == (1, 0)
    verify_cycle(BALANCED_PARTIAL, core)
    with pytest.raises(ValueError, match="monochromatic"):
        verify_capture(BALANCED_PARTIAL, core)
    with pytest.raises(ValueError, match="winding"):
        verify_capture(BALANCED_PARTIAL, replace(core, winding=(1, 1)))
    trace = trace_capture(BALANCED_PARTIAL)
    assert trace.outcome == "intermediate"
    assert trace.first_core_round == 0
    assert trace.first_mixed_round is trace.gridlock_round is None
    assert trace.period == 3
    assert trace.mean_velocity == Fraction(1, 8)


def test_formation_is_detected_after_an_initially_acyclic_state():
    assert not find_blocker_cycles(LATER_LOOP)
    trace = trace_capture(LATER_LOOP)
    assert trace.outcome == "gridlock"
    assert (trace.first_core_round, trace.first_mixed_round, trace.gridlock_round) == (4, 4, 4)


def test_a_cutoff_is_explicitly_unresolved_and_includes_its_last_snapshot():
    trace = trace_capture(LATER_LOOP, max_steps=3)
    assert trace.outcome == "unresolved"
    assert trace.rounds_observed == 3
    assert trace.gridlock_round is trace.cycle_start is trace.period is None
    assert trace.mean_velocity is None
    assert trace_capture(LATER_LOOP, max_steps=4).gridlock_round == 4
    trace = trace_capture(CAPTURE, max_steps=0)
    assert trace.outcome == "unresolved"
    assert trace.first_core_round == trace.first_mixed_round == 0


def test_exact_recurrence_is_recognized_at_the_cutoff():
    assert trace_capture([[1, 0, 0]], max_steps=2).outcome == "unresolved"
    trace = trace_capture([[1, 0, 0]], max_steps=3)
    assert trace.outcome == "free"
    assert trace.period == 3 and trace.mean_velocity == 1


def test_original_car_nonmonotonicity_is_preserved_in_event_classification():
    before = trace_capture([[0, 2, 2, 1], [2, 0, 2, 1]])
    after = trace_capture([[2, 2, 2, 1], [2, 0, 2, 1]])
    assert before.outcome == "gridlock" and before.gridlock_round == 3
    assert after.outcome == "intermediate" and after.period == 2
    assert after.gridlock_round is None and after.mean_velocity == Fraction(1, 7)


@pytest.mark.parametrize("rows,winding", [([[1]], (1, 0)), ([[2]], (0, 1))])
def test_singleton_dimension_self_cycles_are_monochromatic(rows, winding):
    cycle, = find_blocker_cycles(rows)
    verify_cycle(rows, cycle)
    assert cycle.winding == winding and not cycle.mixed
    assert trace_capture(rows).outcome == "gridlock"


def test_empty_state_remains_free_by_convention():
    assert find_blocker_cycles([[0]]) == ()
    trace = trace_capture([[0]], max_steps=0)
    assert trace.outcome == "free" and trace.mean_velocity == 1
    assert trace.first_core_round is trace.first_mixed_round is trace.gridlock_round is None


@pytest.mark.parametrize("operation", [
    lambda rule: find_blocker_cycles(CAPTURE, rule=rule),
    lambda rule: verify_cycle(CAPTURE, MIXED, rule=rule),
    lambda rule: verify_capture(CAPTURE, MIXED, rule=rule),
    lambda rule: trace_capture(CAPTURE, rule=rule),
])
@pytest.mark.parametrize("rule", [TRAIN, "unknown"])
def test_other_update_rules_are_rejected(operation, rule):
    with pytest.raises(ValueError, match="CLASSIC"):
        operation(rule)


@pytest.mark.parametrize("limit", [-1, 1.5, True])
def test_invalid_trace_budgets_are_rejected(limit):
    with pytest.raises(ValueError, match="nonnegative integer"):
        trace_capture(CAPTURE, max_steps=limit)


def test_capture_comparator_rejects_mutated_production_dynamics(monkeypatch):
    monkeypatch.setattr(capture, "step", lambda state, rule: (state.copy(), 0))
    with pytest.raises(ValueError, match="production dynamics"):
        verify_capture(CAPTURE, MIXED)


def test_identity_substitution_inside_the_core_is_rejected(monkeypatch):
    actual = capture.trace_labeled(CAPTURE)
    altered = tuple(1 if label == 0 else 0 if label == 1 else label
                    for label in actual.states[1])
    mutant = replace(actual, states=(actual.states[0], altered))
    assert mutant.rows(1) == actual.rows(1)
    monkeypatch.setattr(capture, "trace_labeled", lambda *args, **kwargs: mutant)
    with pytest.raises(ValueError, match="identit|position"):
        verify_capture(CAPTURE, MIXED)


def test_replay_cannot_silently_delete_the_noncore_input_car(monkeypatch):
    fewer_cars = [row[:] for row in CAPTURE]
    fewer_cars[2][1] = 0
    wrong_orbit = capture.trace_labeled(fewer_cars)
    monkeypatch.setattr(capture, "trace_labeled", lambda *args, **kwargs: wrong_orbit)
    with pytest.raises(ValueError, match="exact input"):
        verify_capture(CAPTURE, MIXED)


@pytest.mark.parametrize("forge_movers", [False, True])
def test_same_species_noncore_lane_swaps_are_rejected(monkeypatch, forge_movers):
    rows = [[1, 2, 0, 0], [1, 1, 2, 1], [1, 0, 1, 2], [2, 0, 0, 1]]
    cycle = next(cycle for cycle in find_blocker_cycles(rows) if cycle.mixed)
    actual = capture.trace_labeled(rows)
    assert len(actual.states) == 2 and actual.moved == ((8,), ())
    assert 4 not in cycle.cells and 7 not in cycle.cells
    altered = tuple(7 if label == 4 else 4 if label == 7 else label
                    for label in actual.states[1])
    moved = ((8, 4, 7), ()) if forge_movers else actual.moved
    mutant = replace(actual, states=(actual.states[0], altered), moved=moved)
    assert mutant.rows(1) == actual.rows(1)  # Colors and the aggregate rank are unchanged.
    monkeypatch.setattr(capture, "trace_labeled", lambda *args, **kwargs: mutant)
    with pytest.raises(ValueError, match="identit|successor"):
        verify_capture(rows, cycle)


@pytest.mark.parametrize("mutation", [
    lambda orbit: replace(orbit, height=4),
    lambda orbit: replace(orbit, width=4),
    lambda orbit: replace(orbit, species=orbit.species[:-1]),
    lambda orbit: replace(orbit, species=((0, 2),) + orbit.species[1:]),
    lambda orbit: replace(orbit, states=(orbit.states[1],) + orbit.states[1:]),
    lambda orbit: replace(orbit, states=(orbit.states[0], orbit.states[1][:-1])),
    lambda orbit: replace(orbit, states=(orbit.states[0], tuple(
        0 if label == 7 else label for label in orbit.states[1]))),
    lambda orbit: replace(orbit, moved=((7, 7), ())),
    lambda orbit: replace(orbit, moved=((100,), ())),
    lambda orbit: replace(orbit, moved=((), ())),
])
def test_replay_is_bound_to_input_and_valid_individual_edges(monkeypatch, mutation):
    actual = capture.trace_labeled(CAPTURE)
    mutant = mutation(actual)
    monkeypatch.setattr(capture, "trace_labeled", lambda *args, **kwargs: mutant)
    with pytest.raises(ValueError):
        verify_capture(CAPTURE, MIXED)


@pytest.mark.parametrize("h,w,expected", [
    (2, 2, 2), (2, 3, 18), (3, 2, 18),
    (2, 4, 110), (4, 2, 110), (3, 3, 573),
])
def test_exhaustive_mixed_core_capture_against_independent_replay(h, w, expected):
    # In total: all 34,344 configurations, including 831 mixed-core states.
    states = decode(np.arange(3 ** (h * w), dtype=np.int64), h, w)
    mixed_count = 0
    for state in states:
        rows = state.tolist()
        cycles = find_blocker_cycles(rows)
        assert bool(cycles) == has_blocker_cycle(rows)
        for cycle in cycles:
            verify_cycle(rows, cycle)
        mixed = next((cycle for cycle in cycles if cycle.mixed), None)
        if mixed is None:
            continue
        mixed_count += 1
        report = verify_capture(rows, mixed)
        assert report.rounds_to_gridlock <= report.total_moves <= report.move_budget
        assert report.rank_history[0] - report.rank_history[-1] == report.total_moves
    assert mixed_count == expected
