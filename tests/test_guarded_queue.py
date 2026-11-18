"""Guarded finite-time movement and exact initial-law avoidance controls."""
from dataclasses import replace
from fractions import Fraction
from itertools import combinations, product

import numpy as np
import pytest

from bml import guarded_queue
from bml.certificates import trace_labeled
from bml.exhaustive import decode
from bml.guarded_queue import (
    GuardedQueueCertificate, construct_guarded_queue, guarded_queue_bounds, verify_guarded_queue,
)
from bml.model import CLASSIC, EAST, NORTH, TRAIN, half_step, is_fixed, step


def pattern_mask(states, delay, *, all_rows=False):
    """Literal initial pattern test, independent of the module's cell generator."""
    _, height, width = states.shape
    hit = np.zeros(len(states), dtype=bool)
    for row in (range(height) if all_rows else range(1, height, 2)):
        for start in range(width):
            good = states[:, row, (start + delay + 1) % width] == 0
            for offset in range(delay + 1):
                good &= states[:, row, (start + offset) % width] == EAST
            for offset in range(1, delay + 1):
                good &= states[:, (row - 1) % height, (start + offset) % width] == EAST
            hit |= good
    return hit


def probability(states, mask, p):
    cells = states.shape[1] * states.shape[2]
    cars = (states != 0).sum(axis=(1, 2))
    counts = np.bincount(cars[mask], minlength=cells + 1)
    return sum((int(count) * (p / 2) ** n * (1 - p) ** (cells - n)
                for n, count in enumerate(counts)), Fraction())


def test_wrapped_pattern_and_exact_first_move_include_the_endpoint_round():
    cert = GuardedQueueCertificate(4, 3, 3, 0, 2)
    rows = construct_guarded_queue(4, 3, 2, start_x=3, row=0)
    assert rows == ((1, 1, 0, 1), (0, 0, 0, 0), (1, 1, 0, 0))
    checked = verify_guarded_queue(rows, cert)
    assert checked.first_rear_move == 2 and checked.rear_label == 3
    assert len(checked.states) == 4 and len(checked.east_moved) == 3
    assert checked.east_moved == ((1, 9), (0, 8, 9), (3, 8, 9))
    orbit = trace_labeled(rows)
    for t in range(3):
        assert checked.states[t] == orbit.states[t]
        assert checked.east_moved[t] + checked.north_moved[t] == orbit.moved[t]


@pytest.mark.parametrize("width,height", ((2, 2), (3, 2), (2, 3), (3, 3)))
def test_every_small_exterior_and_every_delay_has_the_same_rear_first_move(width, height):
    for delay in range(width - 1):
        cert = GuardedQueueCertificate(width, height, 0, 0, delay)
        fixed = {i: 1 for i in range(delay + 1)}
        fixed[delay + 1] = 0
        fixed.update({(height - 1) * width + i: 1 for i in range(1, delay + 1)})
        free = tuple(i for i in range(width * height) if i not in fixed)
        for values in product(range(3), repeat=len(free)):
            flat = [0] * (width * height)
            for cell, species in fixed.items():
                flat[cell] = species
            for cell, species in zip(free, values):
                flat[cell] = species
            rows = [flat[y * width:(y + 1) * width] for y in range(height)]
            checked = verify_guarded_queue(rows, cert)
            assert checked.first_rear_move == delay
            assert all(checked.east_moved)


@pytest.mark.parametrize("width,height", ((2, 4), (4, 2), (5, 3), (6, 2)))
def test_all_origins_and_maximum_delay_with_a_nontrivial_exterior(width, height):
    exterior = [[(x + 2 * y) % 3 for x in range(width)] for y in range(height)]
    original = [row[:] for row in exterior]
    for delay in {0, width - 2}:
        for row in range(height):
            for start in range(width):
                rows = construct_guarded_queue(width, height, delay, start_x=start,
                                               row=row, exterior=exterior)
                result = verify_guarded_queue(rows, GuardedQueueCertificate(width, height, start, row, delay))
                assert result.first_rear_move == delay
    assert exterior == original


def test_construction_preserves_the_exterior_and_normalizes_numpy_integers():
    exterior = np.array([[2, 2, 2, 2], [0, 1, 2, 0], [2, 2, 2, 2]], dtype=np.int64)
    rows = construct_guarded_queue(np.int64(4), np.uint64(3), np.int64(1), exterior=exterior)
    assert rows == ((1, 1, 0, 2), (0, 1, 2, 0), (2, 1, 2, 2))
    cert = GuardedQueueCertificate(np.int64(4), np.int64(3), np.int64(0), np.int64(0), np.int64(1))
    checked = verify_guarded_queue(rows, cert)
    assert all(type(cell) is int for row in rows for cell in row)
    assert all(type(value) is int for value in vars(checked.certificate).values())
    bounds = guarded_queue_bounds(np.int64(4), np.uint64(3), np.int64(1), np.int64(1))
    assert type(bounds.width) is type(bounds.height) is type(bounds.delay) is int
    assert bounds.p == 1 and isinstance(bounds.p, Fraction)


def test_the_guard_cannot_be_omitted_even_if_only_non_gridlock_is_claimed():
    rows = [[1, 1, 0], [0, 1, 2], [0, 2, 2]]
    following, moves = step(np.array(rows))
    assert int(moves) == 2
    assert following.tolist() == [[1, 2, 1], [0, 1, 2], [0, 0, 2]]
    assert is_fixed(following)
    orbit = trace_labeled(rows)
    assert orbit.cycle_start == 1 and orbit.period == 1 and orbit.cycle_moves(0) == 0
    with pytest.raises(ValueError, match="initial board"):
        verify_guarded_queue(rows, GuardedQueueCertificate(3, 3, 0, 0, 1))


def test_an_initially_empty_guard_cell_can_receive_north_before_it_is_needed():
    rows = [[1, 1, 1, 0], [0, 2, 0, 0], [0, 0, 1, 0]]
    orbit = trace_labeled(rows)
    assert all(0 not in moved for moved in orbit.moved[:3])
    assert orbit.rows(2)[0][1] == NORTH
    with pytest.raises(ValueError, match="initial board"):
        verify_guarded_queue(rows, GuardedQueueCertificate(4, 3, 0, 0, 2))


@pytest.mark.parametrize("species", (EAST, NORTH))
def test_production_actual_movement_counts_are_checked(monkeypatch, species):
    rows = construct_guarded_queue(3, 3, 1)

    def corrupted(state, active, **kwargs):
        after, count = half_step(state, active, **kwargs)
        return after, int(count) + int(active == species)

    monkeypatch.setattr(guarded_queue, "half_step", corrupted)
    with pytest.raises(ValueError, match="production half-step"):
        verify_guarded_queue(rows, GuardedQueueCertificate(3, 3, 0, 0, 1))


@pytest.mark.parametrize("fault", ("swap", "delete", "extra_move", "duplicate_move", "bool_label"))
def test_corrupted_tagged_evidence_is_rejected(monkeypatch, fault):
    rows = construct_guarded_queue(4, 3, 1, exterior=[[1] * 4 for _ in range(3)])
    original = guarded_queue._tagged_half_step

    def corrupted(*args):
        after, moved = original(*args)
        if args[-1] == EAST:
            after = list(after)
            if fault == "swap":
                after[4], after[5] = after[5], after[4]
            elif fault == "delete":
                after[4] = -1
            elif fault == "extra_move":
                moved += (4,)
            elif fault == "duplicate_move":
                moved += moved[:1]
            else:
                after[0] = False
            after = tuple(after)
        return after, moved

    monkeypatch.setattr(guarded_queue, "_tagged_half_step", corrupted)
    with pytest.raises(ValueError):
        verify_guarded_queue(rows, GuardedQueueCertificate(4, 3, 0, 0, 1))


@pytest.mark.parametrize("field,value", [
    ("width", True), ("height", np.bool_(True)), ("delay", 1.0), ("delay", -1),
    ("delay", 2), ("start_x", -1), ("start_x", 3), ("start_x", False),
    ("row", 3), ("row", None), ("width", 0), ("height", 1),
])
def test_bad_certificate_metadata_fails_closed(field, value):
    cert = replace(GuardedQueueCertificate(3, 3, 0, 0, 1), **{field: value})
    with pytest.raises(ValueError):
        verify_guarded_queue(construct_guarded_queue(3, 3, 1), cert)


@pytest.mark.parametrize("rows", (None, [], [[]], [[1], [0, 1]], [[True]], [[1.0]], [[3]]))
def test_bad_boards_are_rejected(rows):
    with pytest.raises(ValueError):
        verify_guarded_queue(rows, GuardedQueueCertificate(3, 3, 0, 0, 1))


def test_grid_dimensions_and_certificate_type_are_bound_to_the_input():
    with pytest.raises(ValueError, match="dimensions"):
        verify_guarded_queue(construct_guarded_queue(3, 2, 1), GuardedQueueCertificate(3, 3, 0, 0, 1))
    with pytest.raises(ValueError, match="GuardedQueueCertificate"):
        verify_guarded_queue([[1, 0], [0, 0]], None)
    with pytest.raises(ValueError, match="exterior dimensions"):
        construct_guarded_queue(3, 3, 1, exterior=[[0, 0], [0, 0]])


@pytest.mark.parametrize("width,height,delay", ((1, 2, 0), (2, 1, 0), (3, 3, 2), (3, 3, True), (3.0, 3, 1)))
def test_invalid_constructor_and_probability_domains(width, height, delay):
    with pytest.raises(ValueError):
        construct_guarded_queue(width, height, delay)
    with pytest.raises(ValueError):
        guarded_queue_bounds(width, height, delay, Fraction(1, 2))


@pytest.mark.parametrize("p", (True, np.bool_(False), 0.5, "1/2", None, Fraction(-1, 2), Fraction(3, 2)))
def test_density_requires_an_exact_rational_in_range(p):
    with pytest.raises(ValueError):
        guarded_queue_bounds(3, 3, 1, p)


def test_train_is_rejected_at_every_public_entry_point():
    rows = construct_guarded_queue(3, 3, 1)
    with pytest.raises(ValueError, match="CLASSIC"):
        construct_guarded_queue(3, 3, 1, rule=TRAIN)
    with pytest.raises(ValueError, match="CLASSIC"):
        verify_guarded_queue(rows, GuardedQueueCertificate(3, 3, 0, 0, 1), rule=TRAIN)
    with pytest.raises(ValueError, match="CLASSIC"):
        guarded_queue_bounds(3, 3, 1, Fraction(1, 2), rule=TRAIN)


def test_cyclic_coefficients_count_literal_disjoint_windows():
    for width in range(2, 10):
        for delay in range(width - 1):
            length = delay + 2
            expected = []
            for k in range(width // length + 1):
                count = 0
                for starts in combinations(range(width), k):
                    cells = [(start + i) % width for start in starts for i in range(length)]
                    count += len(set(cells)) == len(cells)
                expected.append(count)
            assert guarded_queue_bounds(width, 2, delay, Fraction(1, 2)).cyclic_placement_counts == tuple(expected)


@pytest.mark.parametrize("width,height", ((2, 2), (3, 2), (4, 2), (2, 4), (3, 3)))
def test_exact_initial_iid_avoidance_and_early_gridlock_on_complete_domains(width, height):
    states = decode(np.arange(3 ** (width * height)), height, width)
    current = states.copy()
    nonempty = (states != 0).any(axis=(1, 2))
    for delay in range(width - 1):
        hit = pattern_mask(states, delay)
        following, moves = step(current)
        jammed = nonempty & (moves == 0)
        assert not np.any(hit & jammed)
        for p in (Fraction(0), Fraction(1, 10), Fraction(1, 2), Fraction(4, 5), Fraction(1)):
            bounds = guarded_queue_bounds(width, height, delay, p)
            actual_avoidance = probability(states, ~hit, p)
            assert actual_avoidance == bounds.early_gridlock_upper_bound
            assert probability(states, jammed, p) <= actual_avoidance <= bounds.simple_upper_bound
            assert bounds.row_pairs == height // 2
            if p in (0, 1):
                assert bounds.pattern_probability == 0 and bounds.early_gridlock_upper_bound == 1
        current = following


def test_vertical_overlaps_cannot_be_treated_as_independent_row_pairs():
    states = decode(np.arange(3 ** 9), 3, 3)
    actual = probability(states, ~pattern_mask(states, 1, all_rows=True), Fraction(1, 2))
    assert actual == Fraction(15301, 16384)
    assert actual > Fraction(127, 128) ** 9
    assert guarded_queue_bounds(3, 3, 1, Fraction(1, 2)).early_gridlock_upper_bound == Fraction(125, 128)


def test_evolved_configurations_do_not_have_the_initial_iid_pattern_mass():
    states = decode(np.arange(3 ** 9), 3, 3)
    evolved, _ = step(states)
    evolved_pattern = ((evolved[:, 0, 0] == EAST) & (evolved[:, 0, 1] == EAST)
                       & (evolved[:, 0, 2] == 0) & (evolved[:, 2, 1] == EAST))
    actual = probability(states, evolved_pattern, Fraction(1, 2))
    assert actual == Fraction(7, 1024)
    assert guarded_queue_bounds(3, 3, 1, Fraction(1, 2)).pattern_probability == Fraction(1, 128)
