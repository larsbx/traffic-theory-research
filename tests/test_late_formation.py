"""Vectorized mixed-cycle detector vs the per-state finder in bml.capture."""
import numpy as np
import pytest

from bml.capture import find_blocker_cycles
from bml.late_formation import formation_times, mixed_cycle_present, sample
from bml.model import step


@pytest.mark.parametrize("seed", range(6))
def test_detector_matches_capture_finder(seed):
    rng = np.random.default_rng(seed)
    for h, w in [(2, 3), (3, 3), (3, 5), (4, 4), (5, 6), (6, 6)]:
        for p in (0.4, 0.6, 0.8, 0.95):
            u = rng.random((60, h, w))
            batch = np.where(u < p / 2, 1, np.where(u < p, 2, 0)).astype(np.int8)
            want = [any(c.mixed for c in find_blocker_cycles(b.tolist())) for b in batch]
            assert mixed_cycle_present(batch).tolist() == want


def test_formation_time_is_first_appearance_and_cycle_persists():
    """A mixed cycle is present at round t  ⟺  0 ≤ T_M ≤ t (first appearance, then permanent)."""
    L, B, horizon = 8, 40, 200
    T = formation_times(L, 0.6, B, horizon, seed=1)
    s = sample(np.random.default_rng(1), B, L, 0.6)
    for t in range(horizon + 1):
        assert (mixed_cycle_present(s) == ((T >= 0) & (T <= t))).all()
        s = step(s)[0]
