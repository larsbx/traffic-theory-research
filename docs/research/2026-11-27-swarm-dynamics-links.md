# BML and finite swarm dynamics: what transfers

**Research note — 27 November 2026. Comparison with
[larsbx/finite-swarm-dynamics](https://github.com/larsbx/finite-swarm-dynamics) at commit
`a81e00e5`. One new Lean result (§1), one reformulation of proved results (§2), one negative
experiment (§3). No novelty claim.**

Both programs study deterministic synchronous maps on finite state spaces with exact
arithmetic and a kernel-checked core. They differ in the interaction. Swarm agents change
heading and never exclude each other. BML cars never change heading and interact only by
exclusion. So jams, blocker cycles and the gap condition have no swarm counterpart, and the
swarm repository's ordered-ℚ contraction results have no BML counterpart. The swarm repository
is also deliberately non-probabilistic, so it says nothing about the open fixed-density
question. Three things do transfer.

## 1. A shared Mathlib pin, and the first iid bounds in Lean

The swarm repository's `formal/general` package runs on Lean 4.34.1 with Mathlib pinned at
`d13f23b7`. The BML kernel in `formal/lean` is on the same Lean version and is Mathlib-free.
The new package [`formal/prob`](../../formal/prob/README.md) depends on both: it imports the
kernel-checked BML theorems and uses Mathlib only for finite sums and products over ℚ. The
kernel package and its audits are unchanged.

For a finite index set ι, `prob p A` is the total weight of the configurations `ι → Cell` in
`A`, each cell being empty, east or north with weights 1 − p, p/2, p/2. Write
`q_{w,h}(p) = prob p EventuallyJammed` on the w×h torus (`jamProb`). For 0 ≤ p ≤ 1, h ≥ 1 and
w ≥ 1, with a = (p/2)^h and c = (1 − p/2)^h:

| Lean theorem | Statement |
|---|---|
| `prob_forall`, `prob_true` | An event imposed cell by cell has product weight; total weight is 1. |
| `prob_forall_column` | An event imposed on every column has the w-th power of the one-column weight. |
| `prob_plug_no_lone` | P(some full north column, and every north car in one) = (a + c)^w − c^w. |
| `jamProb_lower_bound` | (a + c)^w − c^w ≤ q_{w,h}(p). |
| `thin_lower_bound` | h = 2: (1 − p + p²/2)^w − (1 − p/2)^{2w} ≤ q_{w,2}(p), the bound L_W of Theorem A. |
| `prob_exists_fullNorthColumn` | P(some full north column) = 1 − (1 − a)^w. |
| `jamProb_upper_bound` | q_{w,h}(p) ≤ P(#east ≥ w) + 1 − (1 − a)^w. |

The lower bound is the lower half of Theorem A of the
[thin-torus note](2026-11-21-thin-torus-nonmonotonicity.md), now at every height. The upper
bound is coarser than Theorem A's: it uses only "a jam with fewer than w east cars needs a full
north column", not the gap condition, and leaves the binomial tail P(#east ≥ w) as an event
weight. Neither bound decays in w at fixed h and p, so they do not give Theorem P.
`tests/test_thin.py::test_iid_bounds_any_height` checks the two identities and both bounds by
exact enumeration on 2×3, 2×4, 3×2 and 3×3 at p = 1/5, 1/2, 9/10, 1.

Still open for Theorem A: the weight Γ_W of the gap condition as a renewal sum (the rest of
blueprint B10.5), which needs the gap event as a predicate on initial states.

## 2. Gridlock obstructions as coverage of lane cycles

The swarm repository's leader-placement test (`docs/LEADER_PLACEMENT.md`) calls a class
c ∈ H₁(K) *covered* by a vertex set S if no cycle representing c avoids the closed
neighbourhood of S. The BML obstruction theorems have this form on a simpler complex.

**Lane complexes.** An east car never leaves its row and a north car never leaves its column
(`east_carTrace_row`, `north_carTrace_column`). So the space available to east traffic is the
disjoint union K_E of the h row circles, and to north traffic the union K_N of the w column
circles. H₁(K_E) is free on the rows and H₁(K_N) on the columns. There are no 2-cells, so the
only representative of a row class is the row itself, and a set S of cells covers it exactly
when S meets that row. The linear test `z = J_S y + ∂₂ b` of the swarm repository reduces to
this, since ∂₂ = 0.

**The proved results in this language.** Call a set of cells *pinned* if its occupants never
move again; a `BlockingCore` (occupied and closed under each car's forward cell) is pinned.

| Statement | Lean theorem |
|---|---|
| A pinned set covering every row class and every column class forces gridlock within the movement budget. | `RouteCover.jammed_by_movementBudget` |
| A nonempty blocking core covers every row and column class, unless a full monochromatic lane exists. | `BlockingCore.routeCover_or_full_lane` |
| A full north column covers every row class at once. If the column classes carry no moving traffic, gridlock follows. | `eventuallyJammed_of_north_in_full_columns` (B10.4) |
| An uncovered row class carrying a car and a hole, with no north car in the row, never jams. | `EastMixedRow.never_jam` |
| In a jam with no full north column the east cars meet every column class. | `jam_east_every_column` (B10.2) |
| A blocker cycle in a frozen state is a closed monotone walk on the torus, with class (i, j) ≠ 0 in H₁(T²; ℤ) and length iW + jH ≥ min(W, H). | `blocker_closed_winding`, `blocker_closed_length_lower_bound` (G1) |

The last row uses the torus itself, not the lane complexes: blocker cycles mix the two
species, and their classes live in H₁(T²). On two rows the classes (0, 1) and (1, j) are the
plug and the winding cycle of B10.2.

**What this does not give.** It is a common vocabulary for results already proved, not a new
theorem. The coverage test has content beyond "S meets every lane" only when lanes share
cells and 2-cells exist, which is the street-network setting. There the relation to the R2
trap certificates is the following, and it is weaker than an equivalence:

- An R2 trap (`BML/RouteTrap.lean`) is a greatest fixed point of a closure operator on
  vehicles. It is order-theoretic and depends on the current occupancy. On the torus with
  one option per car it is a blocking core.
- Coverage is a property of a set of cells and the lane graph only. If the undirected lane
  graph minus S has H₁ = 0, it has no directed cycle, so no circulation survives outside S.
  The converse fails: a graph can have undirected cycles and no directed ones. A homological
  test is therefore sufficient for "S stops all circulation" and not necessary.

No such test is implemented or proved here.

## 3. The cut-rank argument does not apply to the finite Kuramoto model

The sparse speed-one proofs (`BML.Train.Diagonals.half_eventual_stable`, and the CLASSIC
analogue in `BML/SparseDynamics.lean`) work on labels with classes in the cyclic group ℤ_N,
which has no order. They need two hypotheses: each label's class stays or moves one step back
(*step*), and an occupied class with an empty successor stays occupied (*release*). With
2m ≤ N labels, every class is then eventually constant. The order comes from cutting the cycle
at a permanently empty class.

The swarm repository's finite Kuramoto model has phases on the blue unit conic over F_p, a
cyclic group of order n = p ± 1, and no ordered energy. So the question is whether the same
argument proves phase locking there. It does not. `scripts/swarm_cut_rank.py` enumerates every
state of m = 2 and m = 3 all-to-all oscillators over F₇, F₁₁, F₁₃, for every coupling
κ ∈ F_p^×, identity natural rotors and no lag, using the swarm repository's exact reference
implementation:

- **Step fails in every moving state.** In none of the states that change does every phase
  index stay or move one class in a common direction. This holds for both orientations of ℤ_n
  and every κ: 0 of 48 moving states (F₇, m = 2), 0 of 480 (F₇, m = 3), 0 of 120 (F₁₁ and F₁₃,
  m = 2), 0 of 1656 (F₁₁ and F₁₃, m = 3).
- **The reason is structural for m = 2.** The coupling `det(u_i, u_j)` is antisymmetric, so
  two oscillators rotate by opposite parameters. The cut-rank argument needs motion relative
  to the common frame to be one-sided.
- **The conclusion also fails.** Sparse states (2m ≤ n) do not all lock: over F₇ with m = 2
  between 16 and 32 of the 64 states reach a fixed point, depending on κ. For F₁₁ with m = 3
  the range over κ is 72 to 1728 of 1728, so some couplings do lock every state, by a
  mechanism this argument does not explain.

The argument applies to phase models whose relative motion is one-sided and local, such as a
rule where an oscillator advances with the common drift unless the next phase class is
occupied. That is the TRAIN rule on a ring, not the determinant-coupled model. The numbers are
in [`data/2026-11-27-swarm-cut-rank.json`](data/2026-11-27-swarm-cut-rank.json);
`tests/test_swarm_link.py` checks the file's internal consistency. The enumeration is finite
evidence for these fields, sizes and weights only.
