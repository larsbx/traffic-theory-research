"""Direct-path semantics, independent exact cycles, and conditional probability bounds."""
from dataclasses import replace
from fractions import Fraction
from itertools import product
from math import comb

import numpy as np
import pytest

from bml import path_core
from bml.certificates import trace_labeled
from bml.exhaustive import decode
from bml.model import EAST, NORTH, TRAIN, half_step, step
from bml.path_core import (
    analyze_path_core, core_count, direct_path_count, direct_path_mask,
    maximal_frozen_core, path_mass_gridlock_upper_bound, population_event_upper_bound,
    scalar_path_mask,
)
from bml.probability import has_full_lane, ring_probability


@pytest.fixture(scope="module")
def censuses():
    return {side: analyze_path_core(side, side, steps=side - 1) for side in (2, 3)}


def test_edge_count_and_repeated_vertex_boundaries():
    rows = [[EAST, EAST, 0]]
    assert direct_path_mask(rows, 0) == ((True, True, False),)
    assert direct_path_mask(rows, 1) == ((True, False, False),)
    assert direct_path_mask(rows, 2) == ((False, False, False),)
    # N=2: N-1 edges can be an acyclic chain, whereas N edges identify the core.
    assert direct_path_count(rows, 1) > core_count(rows) == 0
    assert direct_path_mask(rows, 3) == maximal_frozen_core(rows)
    assert direct_path_count(rows, 0) == 2
    for steps in (0, 1, 3, 10 ** 50):
        assert direct_path_mask([[EAST, EAST, EAST]], steps) == ((True, True, True),)
        assert direct_path_mask([[0]], steps) == ((False,),)
        for species in (EAST, NORTH):
            assert direct_path_mask([[species]], steps) == ((True,),)
            assert scalar_path_mask([[species]], steps) == ((True,),)
    assert core_count([[0]]) == 0
    assert core_count([[EAST]]) == core_count([[NORTH]]) == 1


def test_core_includes_feeders_and_is_maximal_among_forward_closed_subsets():
    # The north car feeds into a full east row; it is in the core but on no cycle.
    rows = [[EAST, EAST, EAST], [NORTH, 0, 0]]
    assert maximal_frozen_core(rows) == ((True, True, True), (True, False, False))
    # Enumerate every candidate subset independently on every 2x2 board. Union
    # of all occupied forward-closed subsets must equal the pruner's core.
    for flat in product(range(3), repeat=4):
        rows = [flat[:2], flat[2:]]
        union = set()
        for bits in range(16):
            subset = {i for i in range(4) if bits & (1 << i)}
            valid = True
            for i in subset:
                if flat[i] == 0:
                    valid = False
                    break
                y, x = divmod(i, 2)
                target = 2 * y + (x + 1) % 2 if flat[i] == EAST else 2 * ((y + 1) % 2) + x
                if target not in subset:
                    valid = False
                    break
            if valid:
                union |= subset
        expected = tuple(tuple(2 * y + x in union for x in range(2)) for y in range(2))
        assert maximal_frozen_core(rows) == expected
        for steps in range(7):
            assert direct_path_mask(rows, steps) == scalar_path_mask(rows, steps)
        assert direct_path_mask(rows, 3) == direct_path_mask(rows, 4) == expected


def test_core_persists_through_each_half_step_with_same_species():
    for rows in ([[EAST, EAST, EAST], [NORTH, 0, 0]],
                 [[1, 1, 2], [2, 0, 1], [2, 1, 0]],
                 [[1, 1], [1, 0]]):
        board = np.asarray(rows, dtype=np.int8)
        core = np.asarray(maximal_frozen_core(rows))
        for species in (EAST, NORTH):
            after, _ = half_step(board, species)
            assert np.array_equal(after[core], board[core])
            assert np.all(np.asarray(maximal_frozen_core(after.tolist()))[core])
            board = after


def test_exact_terminal_cycle_mean_excludes_transient_prefix_and_is_basin_weighted():
    # 0 has a large transient observation; 1,2 form a cycle; 3 reaches that
    # same cycle; 4 is a different fixed point. Uniform attractor weighting
    # would also give the wrong initial-law expectation.
    means, cycles, period, transient = path_core._terminal_averages(
        (1, 2, 1, 0, 4), ((1000, 2, 8, 10000, 1), (9, 0, 1, 8, 0)))
    assert means == ((Fraction(5), Fraction(5), Fraction(5), Fraction(5), Fraction(1)),
                     (Fraction(1, 2),) * 4 + (Fraction(0),))
    assert (cycles, period, transient) == (2, 2, 2)
    assert sum(means[0], Fraction()) / 5 == Fraction(21, 5)


def test_exact_small_census_and_stopped_original_tags(censuses):
    small, square = censuses[2], censuses[3]
    assert small.counts.states == 81 and square.counts.states == 19683
    assert small.counts.final_core_by_cars == (0, 0, 8, 40, 64)
    assert small.counts.gridlock_by_cars == (0, 0, 4, 8, 16)
    assert (small.colored_cycles, small.tagged_edges, small.core_growth_states) == (49, 177, 0)
    assert small.recurrent_path_nonjam_ringless_states == 28
    assert square.counts.initial_core_by_cars == (0, 0, 0, 18, 234, 1296, 4068, 7848, 8874, 4608)
    assert square.counts.final_core_by_cars == (0, 0, 0, 18, 252, 1530, 7200, 21780, 16614, 4608)
    assert square.counts.gridlock_by_cars == (0, 0, 0, 6, 36, 180, 798, 2538, 1881, 512)
    assert square.counts.recurrent_path_by_cars == (
        0, 0, 0, Fraction(261, 4), 918, 5262, Fraction(529119, 35), Fraction(208269, 8), 17388, 4608)
    assert (square.colored_cycles, square.max_colored_period, square.max_colored_transient) == (2644, 12, 15)
    assert (square.tagged_edges, square.max_labeled_period, square.max_labeled_transient) == (162141, 18, 15)
    assert square.core_growth_states == 5121
    assert square.recurrent_path_without_core_states == square.recurrent_path_nonjam_ringless_states == 9387
    assert sum(square.counts.final_core_by_cars) == 52002


def test_three_by_three_pushforward_polynomial_rejects_evolved_iid(censuses):
    counts = censuses[3].counts
    assert counts.path_polynomial("initial") == (0, 0, 0, 1, 0, 0, 0, 0, 0, 0)
    assert counts.path_polynomial("one_round") == (
        0, 0, 0, Fraction(3, 2), Fraction(-9, 16), Fraction(9, 32),
        Fraction(-5, 16), Fraction(3, 32), 0, 0)
    # Exact coefficient identity, not an assertion drawn from sampled p values:
    # H1-p^3 = p^3(1-p)(16-2p+7p^2-3p^3)/32.
    difference = tuple(after - before for after, before in zip(
        counts.path_polynomial("one_round"), counts.path_polynomial("initial")))
    factor = (Fraction(1, 2), Fraction(-1, 16), Fraction(7, 32), Fraction(-3, 32))
    expanded = [Fraction()] * 10
    for k, coefficient in enumerate(factor):
        expanded[k + 3] += coefficient
        expanded[k + 4] -= coefficient
    assert difference == tuple(expanded)
    # The remaining factor is >0 on [0,1]: 16-2p>=14 and 7p^2-3p^3>=0.
    low = counts.evaluate(Fraction(1, 5))
    assert low.initial_path_mass == Fraction(1, 125)
    assert low.one_round_path_mass == Fraction(3491, 312500)
    assert low.recurrent_path_mass == Fraction(114171737, 13125000000)
    assert low.one_round_path_mass > low.initial_path_mass
    assert low.recurrent_path_mass != low.initial_path_mass


def test_short_recurrent_paths_do_not_imply_stopped_tags():
    rows = [[NORTH, EAST, EAST], [0, 0, 0], [0, 0, 0]]  # Ternary code 14.
    orbit = trace_labeled(rows)
    assert orbit.cycle_start == 0 and orbit.period == 8
    assert orbit.rows(0) == orbit.rows(4) and orbit.states[0] != orbit.states[4]
    assert not has_full_lane(rows)
    assert all(orbit.cycle_moves(label) > 0 for label, _ in orbit.species)
    counts = tuple(direct_path_count(orbit.rows(i), 2) for i in range(orbit.period))
    assert counts == (1, 0, 1, 0) * 2
    assert Fraction(sum(counts), orbit.period) == Fraction(1, 2)
    assert all(core_count(orbit.rows(i)) == 0 for i in range(orbit.period))


def test_delayed_new_core_invalidates_finite_prefix_as_late_time_input():
    # All cars move before the prescribed time, then the whole population is
    # frozen. The initial empty core does not bound the eventual core.
    for side in (4, 6, 10):
        delay = (side - 2) // 2
        board = np.zeros((side, side), dtype=np.int8)
        for i in range(side):
            assert not board[i, (i - delay) % side]
            board[i, (i - delay) % side] = EAST
            assert not board[(i - delay) % side, (i + 1) % side]
            board[(i - delay) % side, (i + 1) % side] = NORTH
        for _ in range(delay):
            assert core_count(board.tolist()) == 0
            board, moved = step(board)
            assert int(moved) == 2 * side
        assert core_count(board.tolist()) == 2 * side
        following, moved = step(board)
        assert not moved and np.array_equal(board, following)


def _population_fill_oracle(area, p, budget, minimum):
    # Independent primal construction: spend the budget on lowest populations
    # first. The implementation instead minimizes the dual cutoff inequalities.
    answer = Fraction()
    remaining = Fraction(budget)
    for n in range(minimum, area + 1):
        capacity = Fraction(comb(area, n)) * p ** n * (1 - p) ** (area - n)
        take = min(capacity, remaining / n)
        answer += take
        remaining -= n * take
    return answer


def test_population_envelope_matches_independent_primal_at_all_breakpoints():
    for area in range(1, 10):
        for minimum in {1, (area + 1) // 2, area}:
            for p in (Fraction(0), Fraction(1, 5), Fraction(1, 2), Fraction(2, 3), Fraction(1)):
                spent = Fraction()
                budgets = {Fraction(0), Fraction(area + 1)}
                for n in range(minimum, area + 1):
                    cost = n * comb(area, n) * p ** n * (1 - p) ** (area - n)
                    budgets |= {spent, spent + cost / 2, spent + cost}
                    spent += cost
                for budget in budgets:
                    actual = population_event_upper_bound(area, p, budget, minimum_population=minimum)
                    assert actual == _population_fill_oracle(area, p, budget, minimum)
                    assert isinstance(actual, Fraction) and 0 <= actual <= 1


def test_population_late_time_wrapper_and_density_endpoints():
    for side in range(1, 7):
        area = side * side
        for mass in (Fraction(0), Fraction(1, 20), Fraction(1), Fraction(2)):
            assert path_mass_gridlock_upper_bound(side, side, 0, mass) == 0
            assert path_mass_gridlock_upper_bound(side, side, 1, mass) == min(mass, 1)
            assert path_mass_gridlock_upper_bound(side, side, Fraction(1, 3), mass) == (
                population_event_upper_bound(area, Fraction(1, 3), area * mass,
                                             minimum_population=side))
        assert path_mass_gridlock_upper_bound(side, side, Fraction(1, 3), 0) == 0
    assert population_event_upper_bound(4, Fraction(1, 2), 10, minimum_population=2) == Fraction(11, 16)


def test_normalized_core_event_gap_and_population_bounds(censuses):
    for side, census in censuses.items():
        for p in (Fraction(0), Fraction(1, 5), Fraction(1, 2), Fraction(2, 3), Fraction(1)):
            value = census.counts.evaluate(p)
            q, core, normalized = value.gridlock_probability, value.final_core_mass, value.normalized_final_core_mass
            assert value.initial_core_mass <= core <= value.recurrent_path_mass
            assert value.gridlock_root_mass <= core <= normalized
            assert 0 <= normalized - q <= value.full_lane_nonjam_probability <= ring_probability(side, side, p)
            assert q <= value.core_population_upper_bound <= value.path_population_upper_bound <= 1
            if p == 0:
                assert q == core == normalized == value.recurrent_path_mass == 0
            if p == 1:
                assert q == core == normalized == value.recurrent_path_mass == 1
    half = censuses[3].counts.evaluate(Fraction(1, 2))
    assert half.normalized_final_core_mass == Fraction(476101, 3670016)
    assert half.gridlock_probability == Fraction(12613, 131072)
    assert half.normalized_final_core_mass - half.gridlock_probability == Fraction(122937, 3670016)
    assert half.final_core_mass == Fraction(6007, 65536)
    assert half.gridlock_root_mass == Fraction(2281, 32768)
    assert half.core_population_upper_bound == Fraction(64815, 262144)
    assert half.path_population_upper_bound == Fraction(29764839, 73400320)


def test_direct_fixed_origin_initial_law_integration_uses_initial_weights(censuses):
    # This computes a fixed root after one round directly, without the census's
    # all-root division by area or its population-layer aggregation.
    p = Fraction(1, 5)
    initial = decode(np.arange(3 ** 9), 3, 3)
    following, _ = step(initial)
    total = Fraction()
    for before, after in zip(initial, following):
        n = int(np.count_nonzero(before))
        if scalar_path_mask(after.tolist(), 2)[0][0]:
            total += (p / 2) ** n * (1 - p) ** (9 - n)
    assert total == censuses[3].counts.evaluate(p).one_round_path_mass


def test_census_detects_wrong_production_edges(monkeypatch):
    original = path_core.classify_all

    def mutant(*args, **kwargs):
        classification = original(*args, **kwargs)
        successors = classification.f.copy()
        successors[1] = 1  # A moving isolated car is falsely held in place.
        return replace(classification, f=successors)

    monkeypatch.setattr(path_core, "classify_all", mutant)
    with pytest.raises(AssertionError, match="colored edge"):
        analyze_path_core(2, 2, steps=1)


@pytest.mark.parametrize("steps", [-1, True, 1.5, None, "2"])
def test_invalid_edge_counts_are_rejected(steps):
    for action in (lambda: direct_path_mask([[1]], steps), lambda: scalar_path_mask([[1]], steps),
                   lambda: analyze_path_core(2, 2, steps=steps)):
        with pytest.raises(ValueError):
            action()


@pytest.mark.parametrize("rows", [None, [], [[]], [[1], [1, 0]], [[True]], [[1.0]], [[3]]])
def test_malformed_grids_are_rejected(rows):
    for action in (lambda: direct_path_mask(rows, 0), lambda: scalar_path_mask(rows, 0),
                   lambda: maximal_frozen_core(rows)):
        with pytest.raises(ValueError):
            action()


@pytest.mark.parametrize("value", [True, -1, Fraction(-1, 3), 0.25, "1/4", None])
def test_invalid_nonexact_bound_inputs_are_rejected(value):
    with pytest.raises(ValueError):
        population_event_upper_bound(4, Fraction(1, 2), value)
    with pytest.raises(ValueError):
        path_mass_gridlock_upper_bound(2, 2, Fraction(1, 2), value)


@pytest.mark.parametrize("p", [True, -1, Fraction(3, 2), 0.25, "1/4", None])
def test_invalid_densities_are_rejected(p, censuses):
    with pytest.raises(ValueError):
        population_event_upper_bound(4, p, 1)
    with pytest.raises(ValueError):
        censuses[2].counts.evaluate(p)


def test_invalid_domain_rule_and_recurrence_budget_are_rejected():
    for area in (0, -1, True, 3.0):
        with pytest.raises(ValueError):
            population_event_upper_bound(area, Fraction(1, 2), 1)
    for minimum in (0, 5, True, 1.0):
        with pytest.raises(ValueError):
            population_event_upper_bound(4, Fraction(1, 2), 1, minimum_population=minimum)
    for action in (lambda: direct_path_mask([[1]], 0, rule=TRAIN),
                   lambda: scalar_path_mask([[1]], 0, rule=TRAIN),
                   lambda: maximal_frozen_core([[1]], rule=TRAIN),
                   lambda: path_mass_gridlock_upper_bound(2, 2, Fraction(1, 2), 1, rule=TRAIN),
                   lambda: analyze_path_core(2, 2, steps=1, rule=TRAIN)):
        with pytest.raises(ValueError, match="CLASSIC"):
            action()
    for budget in (0, -1, True, 1.5):
        with pytest.raises(ValueError):
            analyze_path_core(2, 2, steps=1, max_steps=budget)
    with pytest.raises(ValueError, match="did not recur"):
        analyze_path_core(2, 2, steps=1, max_steps=1)
    with pytest.raises(ValueError, match="twelve"):
        analyze_path_core(4, 4, steps=0)


def test_count_metadata_validation_and_numpy_integer_normalization(censuses):
    base = censuses[2].counts
    normalized = replace(base, width=np.int64(2), height=np.int64(2), steps=np.int64(1))
    assert type(normalized.width) is type(normalized.height) is type(normalized.steps) is int
    for changes in ({"width": True}, {"steps": -1}, {"rule": TRAIN},
                    {"initial_path_by_cars": None}, {"final_core_by_cars": (0,)},
                    {"initial_path_by_cars": (False, 0, 16, 64, 64)},
                    {"initial_path_by_cars": (0, 0, 16, 64, 65)},
                    {"recurrent_path_by_cars": (0, 0, 16.0, 64, 64)},
                    {"final_core_by_cars": (0, 0, 7, 40, 64)},
                    {"gridlock_by_cars": (0, 1, 4, 8, 16)}):
        with pytest.raises(ValueError):
            replace(base, **changes)
    for time in (None, 0, "t=1", ["initial"]):
        with pytest.raises(ValueError):
            base.path_polynomial(time)
