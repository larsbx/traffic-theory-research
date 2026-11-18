"""Finite regressions for the CLASSIC blocker-cycle lower-bound argument.

These checks exercise the existing Python extractor and its preconditions.
They are not a proof of G1 or a refinement of Lean's existence proof. In
particular, an occupied-target cycle does not certify zero TRAIN movement.
"""
from __future__ import annotations

import numpy as np
import pytest

from bml.exhaustive import decode
from bml.model import CLASSIC, TRAIN, EAST, NORTH, blocker_cycle, step


SHAPES = [(h, w) for h in range(1, 10) for w in range(1, 10) if h * w <= 9]


def check_cycle_certificate(s, cycle):
    """Check a proposed simple occupied-target loop without using blocker()."""
    assert s.ndim == 2
    h, w = s.shape
    assert h > 0 and w > 0
    assert cycle, "a cycle must have positive length"
    assert len(cycle) == len(set(cycle)), "a simple cycle has distinct sites"
    assert all(0 <= y < h and 0 <= x < w for y, x in cycle)
    assert all(s[y, x] in (EAST, NORTH) for y, x in cycle)
    east_steps = 0
    north_steps = 0
    for i, (y, x) in enumerate(cycle):
        if s[y, x] == EAST:
            expected = (y, (x + 1) % w)
            east_steps += 1
        else:
            expected = ((y + 1) % h, x)
            north_steps += 1
        assert cycle[(i + 1) % len(cycle)] == expected, "wrong oriented edge or missing closure"
    assert east_steps + north_steps == len(cycle)
    assert east_steps % w == 0 and north_steps % h == 0
    assert east_steps // w + north_steps // h > 0
    assert min(w, h) <= len(cycle) <= int(np.count_nonzero(s))


@pytest.mark.parametrize("h,w", SHAPES)
def test_every_nonempty_classic_frozen_state_has_a_valid_simple_cycle(h, w):
    """Exhaust every input state; inspect certificates for the zero-move subset."""
    states = decode(np.arange(3 ** (h * w), dtype=np.int64), h, w)
    following, moved = step(states, CLASSIC)
    occupied = np.count_nonzero(states, axis=(1, 2))
    frozen_indices = np.flatnonzero((moved == 0) & (occupied > 0))
    assert len(frozen_indices) > 0
    for index in frozen_indices:
        s = states[index]
        assert np.array_equal(following[index], s)
        check_cycle_certificate(s, blocker_cycle(s))


def test_blocker_extractor_discards_the_noncyclic_prefix():
    # The first car is a north car feeding into a full east row. It is not
    # itself on the recurrent blocker cycle, which consists of three sites.
    s = np.array([[NORTH, 0, 0], [EAST, EAST, EAST], [0, 0, 0]], dtype=np.int8)
    assert step(s, CLASSIC)[1] == 0
    cycle = blocker_cycle(s)
    check_cycle_certificate(s, cycle)
    assert set(cycle) == {(1, 0), (1, 1), (1, 2)}
    assert (0, 0) not in cycle


@pytest.mark.parametrize("cycle", [
    [],
    [(0, 0), (0, 1), (0, 2), (0, 0)],  # repeated endpoint is not a distinct site
    [(0, 0), (0, 2), (0, 1)],            # reverse edges
    [(0, 0), (0, 1)],                    # a path is not a closed cycle
    [(0, 0), (0, 1), (0, 3)],            # out of bounds
    [(0, 0), (0, 1), (1, 0)],            # includes a hole
])
def test_certificate_checker_rejects_malformed_loops(cycle):
    s = np.array([[EAST, EAST, EAST], [0, 0, 0]], dtype=np.int8)
    with pytest.raises(AssertionError):
        check_cycle_certificate(s, cycle)


@pytest.mark.parametrize("shape", [(0, 1), (1, 0), (0, 0), (1, 1), (2, 3)])
def test_zero_dimensions_or_empty_state_cannot_supply_a_car_cycle(shape):
    with pytest.raises(AssertionError):
        check_cycle_certificate(np.zeros(shape, dtype=np.int8), [(0, 0)])


@pytest.mark.parametrize("s", [
    np.array([[EAST]], dtype=np.int8),
    np.array([[NORTH]], dtype=np.int8),
    np.array([[EAST, EAST, EAST]], dtype=np.int8),
    np.array([[NORTH], [NORTH], [NORTH]], dtype=np.int8),
])
def test_full_ring_cycle_does_not_certify_a_train_jam(s):
    # The occupancy is unchanged under both rules, but every TRAIN car moves.
    # This rules out using occupancy equality or a geometric blocker cycle as
    # the premise for the CLASSIC no-movement theorem under the TRAIN rule.
    classic, classic_moves = step(s, CLASSIC)
    train, train_moves = step(s, TRAIN)
    assert np.array_equal(classic, s) and np.array_equal(train, s)
    assert classic_moves == 0
    assert train_moves == int(np.count_nonzero(s)) > 0
    check_cycle_certificate(s, blocker_cycle(s))
