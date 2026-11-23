"""Independent finite-law and geometric controls for disjoint-strip capacity."""
from dataclasses import replace
from fractions import Fraction

import numpy as np
import pytest

from bml.capacity import (
    StripCapacity, capacity_bound_terms, capacity_upper_bound,
    make_capacity_certificate, verify_capacity_certificate,
)
from bml.exhaustive import JAM, classify_all, decode
from bml.model import TRAIN, step
from bml.probability import make_strip_certificate, strip_upper_bound


def strict_capacity_example():
    rows = [[0] * 8 for _ in range(8)]
    for y in range(8):
        rows[y][0] = 1
    rows[0][1] = 1
    for x, ys in ((2, (0, 1)), (3, (2, 3)), (6, (4, 5)), (7, (6, 7))):
        for y in ys:
            rows[y][x] = 2
    return rows


def test_capacity_can_exceed_every_single_strip_test():
    rows = strict_capacity_example()
    certificate = make_capacity_certificate(rows, 2)
    assert certificate.starts == (0, 4)
    assert certificate.east_rows == (2, 1, 1, 1, 1, 1, 1, 1)
    assert certificate.north_columns == (0, 0, 2, 2, 0, 0, 2, 2)
    assert sum(n // certificate.k for n in certificate.east_rows) == 1
    # No cyclic run of north-empty columns is longer than max east-row count.
    for k in range(1, 9):
        for start in range(8):
            with pytest.raises(ValueError):
                make_strip_certificate(rows, start, k)
    # The transposed/species-swapped version has no north-empty column at all.
    dual = [[{0: 0, 1: 2, 2: 1}[rows[x][y]] for x in range(8)] for y in range(8)]
    for k in range(1, 9):
        for start in range(8):
            with pytest.raises(ValueError):
                make_strip_certificate(dual, start, k)
    state = np.array(rows, dtype=np.int8)
    for _ in range(24):
        verify_capacity_certificate(state.tolist(), certificate)
        state, _ = step(state)


def test_arbitrary_disjoint_cyclic_strips_and_partition_offsets():
    rows = [[0, 0, 2, 0], [1, 0, 0, 0]]
    certificate = make_capacity_certificate(rows, 3, offset=3)
    assert certificate.starts == (3,)
    verify_capacity_certificate(rows, certificate)
    # The public verifier accepts a valid subset, without requiring a partition.
    empty = [[0] * 5 for _ in range(2)]
    verify_capacity_certificate(empty, StripCapacity(5, 2, 2, (4, 2), (0, 0), (0,) * 5))


@pytest.mark.parametrize("changes", [
    {"width": 9}, {"height": True}, {"k": 0}, {"k": True}, {"k": 1.5},
    {"starts": (0, 0)}, {"starts": (0, 1)}, {"starts": (0, 8)},
    {"starts": (False, 4)}, {"starts": [0, 4]}, {"starts": None},
    {"starts": (0, 2)}, {"starts": (0,)}, {"starts": ()},
    {"east_rows": (1,) * 8}, {"east_rows": (False,) * 8},
    {"east_rows": None}, {"north_columns": (0,) * 8},
])
def test_forged_capacity_metadata_is_rejected(changes):
    rows = strict_capacity_example()
    certificate = make_capacity_certificate(rows, 2)
    with pytest.raises(ValueError):
        verify_capacity_certificate(rows, replace(certificate, **changes))


def test_monochromatic_cycles_and_empty_boundary():
    with pytest.raises(ValueError, match="full north"):
        make_capacity_certificate([[2, 0], [2, 0]], 1, offset=1)
    with pytest.raises(ValueError, match="exceed row capacity"):
        make_capacity_certificate([[1, 1], [0, 0]], 1)
    verify_capacity_certificate([[0]], make_capacity_certificate([[0]], 1))
    with pytest.raises(ValueError):
        make_capacity_certificate([[1]], 1)
    with pytest.raises(ValueError):
        make_capacity_certificate([[2]], 1)


@pytest.mark.parametrize("width,height", [(1, 1), (1, 2), (2, 1), (2, 2), (3, 2)])
def test_exact_marginal_laws_against_direct_initial_state_weights(width, height):
    size = 3 ** (width * height)
    states = decode(np.arange(size), height, width)
    classification = classify_all(height, width)
    for p in (Fraction(0), Fraction(1, 7), Fraction(1, 2), Fraction(2, 3), Fraction(1)):
        n = (states != 0).sum(axis=(1, 2))
        weights = [(p / 2) ** int(cars) * (1 - p) ** (width * height - int(cars)) for cars in n]
        jam = sum((weight for weight, kind in zip(weights, classification.cls) if kind == JAM), Fraction())
        for k in range(1, width + 1):
            east_rows = (states == 1).sum(axis=2)
            north_columns = (states == 2).sum(axis=1)
            capacity = (east_rows // k).sum(axis=1)
            supply = sum((north_columns[:, j * k:(j + 1) * k] == 0).all(axis=1).astype(int)
                         for j in range(width // k))
            full_north = (north_columns == height).any(axis=1)
            for threshold in range(1, width // k + 1):
                direct = tuple(sum((weight for weight, yes in zip(weights, mask) if yes), Fraction())
                               for mask in (capacity >= threshold, supply < threshold, full_north))
                assert capacity_bound_terms(width, height, p, k, threshold) == direct
                assert jam <= capacity_upper_bound(width, height, p, k, threshold)


def test_public_certificate_soundness_on_every_2_by_2_state():
    classification = classify_all(2, 2)
    for code, state in enumerate(decode(np.arange(81), 2, 2)):
        for k in (1, 2):
            for offset in (0, 1):
                try:
                    certificate = make_capacity_certificate(state.tolist(), k, offset=offset)
                except ValueError:
                    continue
                verify_capacity_certificate(state.tolist(), certificate)
                assert classification.cls[code] != JAM


def test_exact_terms_clamping_and_endpoints():
    terms = capacity_bound_terms(3, 2, Fraction(1, 2), 1, 2)
    assert terms == (Fraction(1909, 4096), Fraction(833, 2048), Fraction(721, 4096))
    assert sum(terms) == Fraction(2148, 2048)
    assert capacity_upper_bound(3, 2, Fraction(1, 2), 1, 2) == 1
    for p, expected in ((0, 0), (1, 1)):
        for k in range(1, 9):
            for threshold in range(1, 8 // k + 1):
                assert capacity_upper_bound(8, 8, p, k, threshold) == expected


@pytest.mark.parametrize("side,p,best_parameters,one_parameters", [
    (8, Fraction(1, 40), (1, 5), (2, 1)),
    (12, Fraction(1, 18), (2, 2), (3, 1)),
])
def test_threshold_above_one_strictly_improves_all_single_strip_bounds(
    side, p, best_parameters, one_parameters,
):
    bounds = [(capacity_upper_bound(side, side, p, k, threshold), k, threshold)
              for k in range(1, side + 1) for threshold in range(1, side // k + 1)]
    best = min(bounds)
    one = min(item for item in bounds if item[2] == 1)
    old = min(strip_upper_bound(side, side, p, k) for k in range(1, side + 1))
    assert best[1:] == best_parameters and one[1:] == one_parameters
    assert best[0] < one[0] < old
    if side == 8:
        assert best[0] < Fraction(1, 100) < Fraction(1, 40) < one[0]
    else:
        assert best[0] < Fraction(1, 5) < one[0]


@pytest.mark.parametrize("args", [
    (0, 2, Fraction(1, 2), 1, 1), (2, True, Fraction(1, 2), 1, 1),
    (2, 2, 0.5, 1, 1), (2, 2, True, 1, 1),
    (2, 2, Fraction(-1), 1, 1), (2, 2, Fraction(2), 1, 1),
    (2, 2, Fraction(1, 2), 0, 1), (2, 2, Fraction(1, 2), 3, 1),
    (2, 2, Fraction(1, 2), True, 1), (2, 2, Fraction(1, 2), 1, 0),
    (2, 2, Fraction(1, 2), 1, 3), (2, 2, Fraction(1, 2), 1, True),
    (2, 2, Fraction(1, 2), 1, 1.5),
])
def test_invalid_probability_inputs(args):
    with pytest.raises(ValueError):
        capacity_bound_terms(*args)


@pytest.mark.parametrize("operation", [
    lambda: make_capacity_certificate([[0]], 1, rule=TRAIN),
    lambda: verify_capacity_certificate([[0]], StripCapacity(1, 1, 1, (0,), (0,), (0,)), rule=TRAIN),
    lambda: capacity_upper_bound(2, 2, Fraction(1, 2), 1, 1, rule=TRAIN),
    lambda: make_capacity_certificate([[0]], 1, offset=True),
    lambda: make_capacity_certificate([[0]], 1, offset=1),
    lambda: make_capacity_certificate([[False]], 1),
])
def test_rule_and_input_boundaries(operation):
    with pytest.raises(ValueError):
        operation()
