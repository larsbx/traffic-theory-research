# BML probability layer (Mathlib)

A separate Lake package for statements about the iid initial law. It imports the
Mathlib-free CLASSIC kernel in [`../lean`](../lean/README.md) and uses Mathlib for finite sums
and products over ℚ. The kernel package does not depend on it.

- Lean `v4.34.1`, Mathlib pinned at `d13f23b723b8a846827a245b89c10fc7d3f11612`, the pin used by
  `formal/general` in [larsbx/finite-swarm-dynamics](https://github.com/larsbx/finite-swarm-dynamics).
- `BMLProb/Weight.lean`: `cellWeight`, `weight`, `prob`; product formula for cell-by-cell
  events, total weight one, monotonicity, union bound, disjoint unions and differences.
- `BMLProb/Thin.lean`: independence of columns, the weight of "a full north column and every
  north car in one", the lower bound `jamProb_lower_bound` (the thin-torus bound `L_W ≤ q_W`
  is `thin_lower_bound`), and the coarse upper bound `jamProb_upper_bound`.
- `ProbAudit.lean`: checks that the listed theorems exist and use only `propext`,
  `Quot.sound` and `Classical.choice`.

```sh
cd formal/prob
lake exe cache get      # prebuilt Mathlib
lake build
lake env lean ProbAudit.lean
```

Scope: exact rational weights on a fixed finite torus. There are no limits, no real numbers
and no measure theory. The statements and what they leave open are in the
[swarm-links note](../../docs/research/2026-11-27-swarm-dynamics-links.md#1-a-shared-mathlib-pin-and-the-first-iid-bounds-in-lean)
and blueprint B10.5.
