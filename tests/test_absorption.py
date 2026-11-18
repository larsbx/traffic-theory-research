"""Independent trace, finite-graph, and initial-weight absorption controls."""
from dataclasses import replace
from fractions import Fraction
from itertools import product

import numpy as np
import pytest

from bml.absorption import (
    HIT, SAFE, UNRESOLVED, VERDICTS, certificate_from_code,
    complete_cutoff_census, decode_board, encode_board, make_certificate,
    partial_probability_bounds, verify_certificate,
)
from bml.exhaustive import JAM, classify_all
from bml.model import TRAIN, step


def scalar_decode(width, height, code):
    return tuple((code // 3 ** i) % 3 for i in range(width * height))


def scalar_encode(flat):
    return sum(cell * 3 ** i for i, cell in enumerate(flat))


def scalar_step(width, height, flat):
    """Independent complete-snapshot source/destination update, with no NumPy."""
    state = tuple(flat)
    for species in (1, 2):
        moves = []
        for source, car in enumerate(state):
            y, x = divmod(source, width)
            target = (y * width + (x + 1) % width if species == 1
                      else ((y + 1) % height) * width + x)
            if car == species and state[target] == 0:
                moves.append((source, target))
        following = list(state)
        for source, target in moves:
            following[source], following[target] = 0, species
        state = tuple(following)
    return state


def scalar_trace(width, height, code, cutoff):
    current = scalar_decode(width, height, code)
    codes = [code]
    for _ in range(cutoff):
        current = scalar_step(width, height, current)
        codes.append(scalar_encode(current))
    target = any(current) and scalar_step(width, height, current) == current
    repeat = next((i for i, state in enumerate(codes[:-1]) if state == codes[-1]), None)
    verdict = "hit" if target else "safe" if repeat is not None else "unresolved"
    return tuple(codes), verdict, repeat if verdict == "safe" else None


@pytest.mark.parametrize("width,height", ((1, 1), (1, 3), (3, 1), (2, 2), (3, 2)))
def test_complete_small_trace_contract_against_independent_scalar_kernel(width, height):
    for code in range(3 ** (width * height)):
        for cutoff in (0, 1, 4):
            cert = certificate_from_code(width, height, code, cutoff)
            codes, verdict, repeat = scalar_trace(width, height, code, cutoff)
            assert (cert.states, cert.verdict, cert.repeat_index) == (codes, verdict, repeat)
            verify_certificate(width, height, cert)


def test_empty_fixed_state_and_nonempty_jam_are_separate():
    empty0 = make_certificate([[0, 0], [0, 0]], 0)
    empty1 = make_certificate([[0, 0], [0, 0]], 1)
    full0 = make_certificate([[1, 1], [1, 1]], 0)
    assert empty0.verdict == "unresolved"
    assert empty1.verdict == "safe" and empty1.repeat_index == 0
    assert full0.verdict == "hit" and full0.repeat_index is None
    with pytest.raises(ValueError, match="nonempty jam"):
        verify_certificate(2, 2, replace(empty1, verdict="hit", repeat_index=None))


def test_safe_recurrence_includes_intermediate_motion():
    cert = certificate_from_code(4, 2, 3860, 2)
    assert cert.states == (3860, 4340, 3860)
    assert cert.verdict == "safe"
    moves = [int(step(decode_board(4, 2, code))[1]) for code in cert.states[:-1]]
    population = int(np.count_nonzero(decode_board(4, 2, cert.initial_code)))
    assert 0 < sum(moves) < 2 * population
    # The positive recurrent movement certifies no jam, not full speed.
    verify_certificate(4, 2, cert)


def test_late_jam_is_unresolved_at_an_earlier_cutoff():
    rows = [[1, 2, 2, 1], [2, 1, 1, 0], [1, 0, 2, 1], [2, 1, 1, 0]]
    early = make_certificate(rows, 1)
    late = make_certificate(rows, 3)
    assert early.verdict == "unresolved"
    assert late.verdict == "hit"
    with pytest.raises(ValueError, match="nonempty jam/recurrence"):
        verify_certificate(4, 4, replace(early, verdict="safe", repeat_index=0))


def test_every_trace_edge_is_verified_not_just_the_endpoint():
    valid = certificate_from_code(4, 2, 3860, 2)
    forged = replace(valid, states=(3860, 3860, 3860))
    with pytest.raises(ValueError, match="trace edge 0->1"):
        verify_certificate(4, 2, forged)
    with pytest.raises(ValueError, match="recurrence index"):
        verify_certificate(4, 2, replace(valid, repeat_index=1))
    with pytest.raises(ValueError, match="recurrence index"):
        verify_certificate(4, 2, replace(valid, repeat_index=2))
    with pytest.raises(ValueError, match="cutoff"):
        verify_certificate(4, 2, replace(valid, cutoff=3))
    with pytest.raises(ValueError, match="dimensions"):
        verify_certificate(2, 4, valid)


def test_large_single_board_encoding_never_uses_int64_for_its_code():
    rows = [[0] * 8 for _ in range(8)]
    rows[7][7] = 1
    code = encode_board(rows)
    assert code == 3 ** 63 and code > 2 ** 63
    assert np.array_equal(decode_board(8, 8, code), rows)
    cert = certificate_from_code(8, 8, code, 8)
    assert all(type(state) is int for state in cert.states)
    assert cert.verdict == "safe" and cert.terminal_code == code
    verify_certificate(8, 8, cert)
    with pytest.raises(ValueError, match="board range"):
        decode_board(8, 8, 3 ** 64)


@pytest.mark.parametrize("rows", ([[3]], [[-1]], [[1.0]], [[True, 0]], [], [[0], [0, 1]]))
def test_invalid_species_and_board_shapes_are_not_coerced(rows):
    with pytest.raises(ValueError):
        make_certificate(rows, 1)


@pytest.mark.parametrize("bad", (True, -1, 0.5, "2"))
def test_invalid_cutoffs_are_not_coerced(bad):
    with pytest.raises(ValueError, match="cutoff"):
        make_certificate([[0]], bad)
    cert = make_certificate([[0]], 1)
    with pytest.raises(ValueError, match="cutoff"):
        verify_certificate(1, 1, replace(cert, cutoff=bad))


def test_rule_boundary_rejects_train_at_every_entry_point():
    cert = make_certificate([[1]], 0)
    with pytest.raises(ValueError, match="CLASSIC"):
        make_certificate([[1]], 0, rule=TRAIN)
    with pytest.raises(ValueError, match="CLASSIC"):
        verify_certificate(1, 1, replace(cert, rule=TRAIN))
    with pytest.raises(ValueError, match="CLASSIC"):
        verify_certificate(1, 1, cert, rule=TRAIN)
    with pytest.raises(ValueError, match="CLASSIC"):
        partial_probability_bounds(1, 1, [cert], Fraction(1, 2), rule=TRAIN)
    with pytest.raises(ValueError, match="CLASSIC"):
        complete_cutoff_census(1, 1, [1], rule=TRAIN)


@pytest.mark.parametrize("p", (0, 1, True, 0.5, Fraction(-1, 2), Fraction(3, 2)))
def test_probability_requires_a_valid_exact_fraction(p):
    with pytest.raises(ValueError, match="exact Fraction"):
        partial_probability_bounds(1, 1, [], p)


def test_partial_support_keeps_all_omitted_and_unresolved_mass():
    p = Fraction(1, 2)
    empty = make_certificate([[0, 0], [0, 0]], 1)
    full = make_certificate([[1, 1], [1, 1]], 0)
    unknown = make_certificate([[1, 0], [0, 0]], 0)
    bounds = partial_probability_bounds(2, 2, [empty, full, unknown], p)
    assert bounds.hit_mass == Fraction(1, 256)
    assert bounds.safe_mass == Fraction(1, 16)
    assert bounds.observed_unresolved_mass == Fraction(1, 32)
    assert bounds.covered_mass == Fraction(25, 256)
    assert bounds.omitted_mass == Fraction(231, 256)
    assert bounds.lower == Fraction(1, 256)
    assert bounds.upper == Fraction(15, 16)
    assert bounds.unresolved == bounds.upper - bounds.lower
    assert bounds.unresolved == bounds.omitted_mass + bounds.observed_unresolved_mass
    none = partial_probability_bounds(2, 2, [], p)
    assert (none.lower, none.upper, none.unresolved) == (0, 1, 1)


def test_partial_weight_zero_endpoints_and_duplicate_initial_states():
    empty1 = make_certificate([[0, 0], [0, 0]], 1)
    empty2 = make_certificate([[0, 0], [0, 0]], 2)
    p0 = partial_probability_bounds(2, 2, [empty1], Fraction(0))
    assert p0.lower == p0.upper == p0.unresolved == 0
    assert p0.omitted_mass == 0  # Unlisted boards all have initial probability zero.
    with pytest.raises(ValueError, match="duplicate initial"):
        partial_probability_bounds(2, 2, [empty1, empty2], Fraction(1, 2))
    full = [make_certificate([list(flat[:2]), list(flat[2:])], 0)
            for flat in product((1, 2), repeat=4)]
    p1 = partial_probability_bounds(2, 2, full, Fraction(1))
    assert p1.lower == p1.upper == 1 and p1.unresolved == 0


def test_distinct_initial_preimages_are_weighted_separately_after_coalescence():
    census = complete_cutoff_census(3, 2, [1])
    snapshot = census.snapshot(1)
    hits = np.flatnonzero(snapshot.verdicts == HIT)
    by_terminal = {}
    pair = None
    for initial in hits:
        terminal = int(snapshot.terminal_codes[initial])
        if terminal in by_terminal:
            pair = (by_terminal[terminal], int(initial))
            break
        by_terminal[terminal] = int(initial)
    assert pair is not None
    certs = [certificate_from_code(3, 2, code, 1) for code in pair]
    assert certs[0].initial_code != certs[1].initial_code
    assert certs[0].terminal_code == certs[1].terminal_code
    p = Fraction(1, 3)
    expected = sum((p / 2) ** sum(bool(x) for x in scalar_decode(3, 2, code)) *
                   (1 - p) ** sum(x == 0 for x in scalar_decode(3, 2, code))
                   for code in pair)
    bounds = partial_probability_bounds(3, 2, certs, p)
    assert bounds.lower == bounds.covered_mass == expected
    assert bounds.safe_mass == 0 and bounds.upper == 1


@pytest.mark.parametrize("width,height", ((1, 1), (1, 3), (3, 1), (2, 2), (3, 2), (3, 3)))
def test_complete_census_bounds_against_full_orbit_classifier(width, height):
    cutoffs = (0, 1, 2, 4, 8, 16, 32)
    census = complete_cutoff_census(width, height, cutoffs)
    truth = classify_all(height, width)
    assert np.array_equal(census.successors, truth.f)
    assert np.array_equal(census.initial_car_counts, truth.n_east + truth.n_north)
    jam = truth.cls == JAM
    previous = None
    for snapshot in census.snapshots:
        assert np.all(jam[snapshot.verdicts == HIT])
        assert not np.any(jam[snapshot.verdicts == SAFE])
        if previous is not None:
            assert np.all(snapshot.verdicts[previous.verdicts == HIT] == HIT)
            assert np.all(snapshot.verdicts[previous.verdicts == SAFE] == SAFE)
            assert np.all(previous.verdicts[snapshot.verdicts == UNRESOLVED] == UNRESOLVED)
        for p in (Fraction(0), Fraction(1, 5), Fraction(1, 2), Fraction(2, 3), Fraction(1)):
            counts = np.bincount(census.initial_car_counts[jam], minlength=width * height + 1)
            exact = sum((int(n) * (p / 2) ** k * (1 - p) ** (width * height - k)
                         for k, n in enumerate(counts)), Fraction())
            bounds = snapshot.probability_bounds(p)
            assert bounds.lower <= exact <= bounds.upper
            assert bounds.covered_mass == 1 and bounds.omitted_mass == 0
            assert bounds.upper - bounds.lower == bounds.unresolved
            if previous is not None:
                old = previous.probability_bounds(p)
                assert old.lower <= bounds.lower <= bounds.upper <= old.upper
        previous = snapshot
    assert census.snapshot(32).counts[UNRESOLVED] == 0


def test_complete_census_selected_rows_match_independent_traces():
    for width, height in ((2, 2), (3, 2)):
        census = complete_cutoff_census(width, height, [0, 1, 4, 8])
        for snapshot in census.snapshots:
            for code in range(census.states):
                codes, verdict, _ = scalar_trace(width, height, code, snapshot.cutoff)
                assert int(snapshot.terminal_codes[code]) == codes[-1]
                assert VERDICTS[int(snapshot.verdicts[code])] == verdict


def test_census_and_verified_certificate_weights_agree_on_complete_support():
    census = complete_cutoff_census(2, 2, [0, 2, 4])
    for snapshot in census.snapshots:
        certs = [certificate_from_code(2, 2, code, snapshot.cutoff)
                 for code in range(census.states)]
        for p in (Fraction(0), Fraction(1, 2), Fraction(1)):
            assert partial_probability_bounds(2, 2, certs, p) == snapshot.probability_bounds(p)


def test_cutoff_sixteen_does_not_close_the_three_by_three_census():
    census = complete_cutoff_census(3, 3, [16, 32])
    assert census.snapshot(16).counts[UNRESOLVED] == 72
    early = census.snapshot(16).probability_bounds(Fraction(1, 2))
    late = census.snapshot(32).probability_bounds(Fraction(1, 2))
    assert early.unresolved > 0 and early.lower < early.upper
    assert late.unresolved == 0
    assert late.lower == late.upper == Fraction(12613, 131072)


def test_census_guards_and_metadata_do_not_certify_supplied_counts():
    for args in ((4, 3, [0]), (1, 1, []), (1, 1, [0, 0]), (1, 1, [True])):
        with pytest.raises(ValueError):
            complete_cutoff_census(*args)
    with pytest.raises(ValueError, match="max_cells"):
        complete_cutoff_census(1, 1, [0], max_cells=13)
    snapshot = complete_cutoff_census(1, 1, [1]).snapshot(1)
    forged = replace(snapshot, by_cars=((0, 2), (0, 0), (0, 0)))
    with pytest.raises(ValueError, match="partition"):
        forged.probability_bounds(Fraction(1, 2))
    with pytest.raises(KeyError):
        complete_cutoff_census(1, 1, [1]).snapshot(2)
