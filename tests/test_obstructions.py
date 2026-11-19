"""Actual-kernel controls for relaxation bounds and candidate-safe-set failures."""
from fractions import Fraction

import numpy as np
import pytest

from bml.capture import find_blocker_cycles, verify_cycle
from bml.exhaustive import decode
from bml.model import CLASSIC, EAST, NORTH, TRAIN, half_step, is_fixed, movers_mask, step
from bml.obstructions import (
    free_by_round_upper_bound, hbk_defects, hbk_increase_fixture,
    horizontal_run_fixture, vacant_cut_fixture,
)


@pytest.mark.parametrize("side", (4, 5, 8, 17, 64))
def test_hbk_defects_increase_under_actual_classic_round(side):
    initial = hbk_increase_fixture(side)
    result, moves = step(initial, CLASSIC)
    expected = np.zeros_like(initial)
    expected[0, 1] = expected[1, 1] = EAST
    expected[1, 0] = expected[1, 2] = NORTH
    assert np.array_equal(result, expected)
    assert int(moves) == 3
    assert hbk_defects(initial.tolist()) == (0, 1)
    assert hbk_defects(result.tolist()) == (0, 2)
    assert np.count_nonzero(initial) == np.count_nonzero(result) == 4


@pytest.mark.parametrize("side", (2, 3))
def test_hbk_zero_set_matches_an_actual_free_cycle(side):
    # An entire side-length round of full movement returns every car to its
    # original position, hence repeats forever by determinism. This oracle
    # evaluates the production kernel and does not reuse the diagonal formula.
    states = decode(np.arange(3 ** (side * side)), side, side)
    population = np.count_nonzero(states, axis=(1, 2))
    current = states.copy()
    full_cycle = np.ones(len(states), dtype=bool)
    for _ in range(side):
        current, moved = step(current, CLASSIC)
        full_cycle &= moved == population
    defects = np.array([hbk_defects(s.tolist()) for s in states])
    zero = (defects == 0).all(axis=1)
    assert np.array_equal(zero, full_cycle)
    assert np.array_equal(current[zero], states[zero])
    # The intermediate half-step uses the opposite phase convention in Eq.11.
    for board in states[zero]:
        after_east, _ = half_step(board, EAST, CLASSIC)
        assert hbk_defects(after_east.tolist(), next_species=NORTH) == (0, 0)
        after_north, _ = half_step(after_east, NORTH, CLASSIC)
        assert hbk_defects(after_north.tolist(), next_species=EAST) == (0, 0)
    # A jam has enough defects to account for at least half its cars. This
    # finite check accompanies the independent edge-count proof in the note.
    frozen = np.array([is_fixed(s) for s in states])
    assert np.all(2 * defects[frozen].sum(axis=1) >= population[frozen])


@pytest.mark.parametrize("side", (2, 4, 6, 8, 16))
def test_jam_defect_bound_is_sharp_on_even_staircases(side):
    for copies in range(1, side // 2 + 1):
        rows = np.zeros((side, side), dtype=np.int8)
        for offset in range(0, 2 * copies, 2):
            for y in range(side):
                rows[y, (y + offset) % side] = EAST
                rows[y, (y + offset + 1) % side] = NORTH
        result, moves = step(rows, CLASSIC)
        assert int(moves) == 0 and np.array_equal(result, rows)
        assert is_fixed(rows)
        assert hbk_defects(rows.tolist()) == (0, copies * side)
        assert 2 * sum(hbk_defects(rows.tolist())) == np.count_nonzero(rows) == 2 * copies * side
        cores = find_blocker_cycles(rows.tolist())
        assert len(cores) == copies
        for core in cores:
            assert core.winding == (1, 1)
            verify_cycle(rows.tolist(), core, require_mixed=True)


@pytest.mark.parametrize("rounds", (0, 1))
def test_run_delay_on_every_three_by_three_exterior(rounds):
    side, x, y = 3, 2, 1
    states = decode(np.arange(3 ** (side * side)), side, side)
    selected = np.ones(len(states), dtype=bool)
    for offset in range(rounds + 2):
        selected &= states[:, y, (x + offset) % side] == EAST
    current = states[selected]
    assert len(current) == 3 ** (side * side - rounds - 2)
    for _ in range(rounds + 1):
        assert np.all(current[:, y, x] == EAST)
        assert not movers_mask(current, EAST, CLASSIC)[:, y, x].any()
        current, _ = step(current, CLASSIC)
    assert np.all(current[:, y, x] == EAST)


@pytest.mark.parametrize("side", (4, 5, 8))
def test_run_delay_on_larger_arbitrary_exteriors(side):
    rng = np.random.default_rng(8194 + side)
    for rounds in range(side - 1):
        initial = rng.integers(0, 3, size=(24, side, side), dtype=np.int8)
        x, y = side - 1, side // 2
        for offset in range(rounds + 2):
            initial[:, y, (x + offset) % side] = EAST
        current = initial
        for _ in range(rounds + 1):
            assert np.all(current[:, y, x] == EAST)
            assert not movers_mask(current, EAST, CLASSIC)[:, y, x].any()
            current, _ = step(current, CLASSIC)


def test_run_rule_and_integer_endpoint_controls():
    # CLASSIC old-state vacancy is essential; TRAIN moves this whole queue.
    initial = horizontal_run_fixture(5, 1)
    assert not movers_mask(initial, EAST, CLASSIC)[0, 0]
    assert movers_mask(initial, EAST, TRAIN)[0, 0]
    # T=L-2 is included: its T+2 run is a complete frozen east row.
    ring = horizontal_run_fixture(5, 3, start_x=4, row=2)
    after, moved = step(ring, CLASSIC)
    assert int(moved) == 0 and np.array_equal(after, ring)
    # A shorter run does not justify the same endpoint. Its rear has started
    # moving in round T once a length-(T+1) queue has had T rounds to clear.
    short = np.zeros((5, 5), dtype=np.int8)
    short[0, :2] = EAST
    after_one, _ = step(short, CLASSIC)
    assert movers_mask(after_one, EAST, CLASSIC)[0, 0]


def _iid_weight_sum(selected: np.ndarray, populations: np.ndarray, p: Fraction, cells: int):
    by_cars = np.bincount(populations[selected], minlength=cells + 1)
    return sum((int(count) * (p / 2) ** n * (1 - p) ** (cells - n)
                for n, count in enumerate(by_cars)), Fraction())


@pytest.mark.parametrize("side", (2, 3))
def test_run_probability_bound_against_complete_initial_iid_space(side):
    states = decode(np.arange(3 ** (side * side)), side, side)
    populations = np.count_nonzero(states, axis=(1, 2))
    # Free forever from a snapshot iff all cars move in each of the next L
    # rounds. The latter returns the state exactly and can be checked directly.
    current = states.copy()
    for rounds in range(side - 1):
        trial = current.copy()
        free_from_here = np.ones(len(states), dtype=bool)
        for _ in range(side):
            trial, moved = step(trial, CLASSIC)
            free_from_here &= moved == populations
        length = rounds + 2
        no_run = np.ones(len(states), dtype=bool)
        for y in range(side):
            for start in range(0, side - length + 1, length):
                no_run &= ~(states[:, y, start:start + length] == EAST).all(axis=1)
        assert not (free_from_here & ~no_run).any()
        for p in (Fraction(0), Fraction(1, 10), Fraction(1, 2), Fraction(2, 3), Fraction(1)):
            bound = free_by_round_upper_bound(side, p, rounds)
            # Exact identity for disjoint initial cylinders, and an inequality
            # for the dynamically defined event, are separate checks.
            assert _iid_weight_sum(no_run, populations, p, side * side) == bound
            assert _iid_weight_sum(free_from_here, populations, p, side * side) <= bound
        current, _ = step(current, CLASSIC)


def test_vacant_winding_cut_can_become_a_mixed_jam_in_one_round():
    initial, cycle = vacant_cut_fixture()
    assert len(cycle) == len(set(cycle)) == 8
    assert all(initial[y, x] == 0 for x, y in cycle)
    east_steps = south_steps = 0
    for (x, y), (xx, yy) in zip(cycle, cycle[1:] + cycle[:1]):
        if (xx, yy) == ((x + 1) % 4, y):
            east_steps += 1
        else:
            assert (xx, yy) == (x, (y - 1) % 4)
            south_steps += 1
    assert (east_steps, south_steps) == (4, 4)  # winding (1,-1)
    assert find_blocker_cycles(initial.tolist()) == ()
    result, moved = step(initial, CLASSIC)
    assert result.tolist() == [
        [1, 2, 0, 0], [0, 1, 2, 0], [0, 0, 1, 2], [2, 0, 0, 1],
    ]
    assert int(moved) == 4
    assert is_fixed(result)
    cores = find_blocker_cycles(result.tolist())
    assert len(cores) == 1 and cores[0].winding == (1, 1)
    assert len(cores[0].cells) == np.count_nonzero(result) == 8
    verify_cycle(result.tolist(), cores[0], require_mixed=True)
    unchanged, next_moves = step(result, CLASSIC)
    assert np.array_equal(unchanged, result) and int(next_moves) == 0


@pytest.mark.parametrize("bad", (True, -1, 2.5, "4"))
def test_nonnatural_domains_rejected(bad):
    with pytest.raises(ValueError):
        hbk_increase_fixture(bad)
    with pytest.raises(ValueError):
        horizontal_run_fixture(5, bad)
    with pytest.raises(ValueError):
        free_by_round_upper_bound(bad, Fraction(1, 2), 0)
    with pytest.raises(ValueError):
        hbk_defects([[0, 0], [0, 0]], next_species=bad)


@pytest.mark.parametrize("bad", (True, -1, 0.5, "1/2", Fraction(3, 2)))
def test_density_must_be_an_exact_probability(bad):
    with pytest.raises(ValueError):
        free_by_round_upper_bound(5, bad, 1)


def test_scope_and_shape_guards():
    for side, rounds in ((1, 0), (4, 3)):
        with pytest.raises(ValueError):
            free_by_round_upper_bound(side, Fraction(1, 2), rounds)
    with pytest.raises(ValueError):
        free_by_round_upper_bound(5, Fraction(1, 2), 1, rule=TRAIN)
    with pytest.raises(ValueError):
        hbk_increase_fixture(3)
    with pytest.raises(ValueError):
        horizontal_run_fixture(4, 1, row=4)
    with pytest.raises(ValueError):
        horizontal_run_fixture(4, 1, start_x=4)
    for rows in ([[0, 0, 0], [0, 0, 0]], [[0]], [[0, 3], [0, 0]], [[0, True], [0, 0]]):
        with pytest.raises(ValueError):
            hbk_defects(rows)
    with pytest.raises(ValueError):
        hbk_defects([[0, 0], [0, 0]], next_species=3)
