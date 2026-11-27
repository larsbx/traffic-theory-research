"""Internal consistency of the recorded cut-rank experiment on the finite Kuramoto model.

The numbers come from `scripts/swarm_cut_rank.py`, which needs a checkout of
larsbx/finite-swarm-dynamics. This test only checks the committed record."""
import json
from pathlib import Path

DATA = Path(__file__).resolve().parents[1] / "docs/research/data/2026-11-27-swarm-cut-rank.json"


def test_cut_rank_record():
    report = json.loads(DATA.read_text())
    assert report["schema"] == "swarm.cut-rank.v1" and len(report["swarm_commit"]) == 40
    assert [(c["p"], c["oscillators"]) for c in report["cases"]] == [
        (7, 2), (7, 3), (11, 2), (11, 3), (13, 2), (13, 3)]
    for case in report["cases"]:
        p, m, n = case["p"], case["oscillators"], case["unit_group_order"]
        assert n == (p + 1 if p % 4 == 3 else p - 1)
        assert [r["kappa"] for r in case["by_coupling"]] == list(range(1, p))
        for r in case["by_coupling"]:
            assert r["states"] == n ** m and r["sparse_states"] == (n ** m if 2 * m <= n else 0)
            assert r["sparse_states_locking"] <= r["states_locking"] <= r["states"]
            fixed = r["states"] - r["moving_states"]
            for sign in ("1", "-1"):
                # the step hypothesis holds exactly at the fixed states
                assert r["moving_states_with_step"][sign] == 0
                assert r["step_holds"][sign] == fixed
                assert r["step_and_release_hold"][sign] <= fixed
            assert fixed <= r["states_locking"]
