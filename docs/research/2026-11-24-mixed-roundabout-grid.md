# A grid with a variable share of roundabouts

**Research note — 24 November 2026.** The [roundabout note](2026-11-24-roundabout-bml.md)
replaced every BML intersection by a roundabout. Here an arbitrary set R of intersections are
roundabouts and the rest keep the BML signal, so the share ρ = |R|/WH is a parameter. BML is
R = ∅ and roundabout BML is R = everything.

**Main result (Theorem MX-G).** Let r_y be the number of roundabouts in row y and c_x the number
in column x. A gridlock with exactly n cars exists if and only if

> min( W + min_y r_y , H + min_x c_x ) ≤ n ≤ WH + 2|R|.

The least gridlock is always one straight street, the one with the fewest roundabouts. So the
relationship to the share ρ depends on placement, and exactly so (Corollary MX-E): with
k = |R| roundabouts the least gridlock ranges from min(W,H), as in BML, up to
min(W + ⌊k/H⌋, H + ⌊k/W⌋) ≈ (1+ρ)·min(W,H) when they are spread evenly. A random placement is
asymptotically as good as the best one (Corollary MX-P).

**Free flow** behaves differently. Proposition MX-F bounds it by a time budget at each junction,
and exhaustive enumeration shows the capacity is **not monotone** in R: on the 3×3 torus no
roundabout allows 6 free cars, every single roundabout allows 5, and eight roundabouts allow 7.
A Monte Carlo sweep (§6) shows the same shape for gridlock from random traffic: mixed grids
jam at lower density than either pure grid.

MX-0, MX-G, MX-E, MX-P and MX-F have complete prose proofs. The capacity census is finite
data, the sweep is simulation, and nothing is formalized in Lean. No novelty is claimed.

Code: [`bml/mixed.py`](../../bml/mixed.py). Tests: [`tests/test_mixed.py`](../../tests/test_mixed.py).
Replay: [`scripts/check_mixed.py`](../../scripts/check_mixed.py). Sweep:
[`scripts/mixed_ratio_sweep.py`](../../scripts/mixed_ratio_sweep.py) →
[`data/2026-11-24-mixed-ratio-sweep.json`](data/2026-11-24-mixed-ratio-sweep.json).

## 0. The model

**Cells.** Every intersection v = (x,y) has a **junction cell** c(v), holding · or E or N. If
v ∈ R it also has the private quadrants a(v) (E only) and b(v) (N only) of the roundabout note.
There are WH + 2|R| cells.

**Routes.**

- E: c(x,y) → [a(x+1,y) if (x+1,y) ∈ R] → c(x+1,y);
- N: c(x,y) → [b(x,y) if (x,y) ∈ R] → c(x,y+1).

**Tick.** Time runs in ticks t = 0, 1, 2, …. In one tick every car moves whose next cell is
empty at the start of the tick and which is not held by a signal. The junction cell of a
**signal** intersection admits E cars only in even ticks and N cars only in odd ticks. A
roundabout has no signal; if an E car in a(v) and an N car both want c(v), exactly one moves
(yield on entry lets the E car go).

**Reductions**, both tested: with R = ∅ the ticks 2t and 2t+1 are the E and N half-steps of
BML; with R everything each tick is the roundabout step.

**A modelling choice that matters.** The signal gates entry to its junction cell, so a car
waits for green in the cell before it. For an N car leaving a roundabout that cell is the
private b. For an E car it is the roundabout's shared cell c, because the roundabout's private
E cell lies on its entry side. An E car therefore holds a roundabout for two ticks when the
next intersection east is a signal. §4 and §5 depend on this choice; §§1–3 do not.

## 1. Lemma MX-0 (gridlock)

**Claim.** No car moves in two consecutive ticks ⟺ every car's next cell is occupied. Such a
state never changes. A **gridlock** is such a state with at least one car.

*Proof.* (⇐) is immediate. (⇒) Suppose some car has an empty next cell z. Among the cars with
next cell z, in at least one of the two ticks one of them is not held by a signal: at a signal
junction each species is admitted in one of the two ticks, and a roundabout cell admits both
always. In that tick a car enters z, namely that car or the winner of the merge. ∎

## 2. Theorem MX-G (the least gridlock is a straight street)

**Claim.** A gridlock with exactly n cars exists ⟺ n_min(R) ≤ n ≤ WH + 2|R|, where

> n_min(R) = min( W + min_y r_y , H + min_x c_x ).

*Proof.* *Lower bound.* In a gridlock, map each car to the car in its next cell. Iterating
reaches a cycle of distinct occupied cells. Between consecutive junction cells the cycle
follows an E route or an N route; say it does so α and β times. It closes on the torus, so
W | α and H | β, and α + β ≥ 1.

- If β = 0, the cycle follows E routes only, so it is a whole row y: W junction cells and the
  r_y cells a(·,y). It has W + r_y cars.
- If α = 0, it is a whole column x, with H + c_x cars.
- Otherwise α ≥ W and β ≥ H, so it has at least W + H junction cells.

Since r_y ≤ W and c_x ≤ H, we have n_min(R) ≤ min(2W, 2H) ≤ W + H. So every cycle has at
least n_min(R) cars.

*Construction.* Fill every cell of a cheapest street with its species: each car is blocked by
the next, which gives n_min(R) cars. The directed graph on cells, with an edge from each cell
to its successor under either species, is strongly connected: every private cell leads to a
junction cell, and junction cells reach every cell by E and N routes. So while some cell is
empty, a route path from an empty cell to an occupied one has a last empty cell z, whose
successor under some species σ is occupied. Put a σ car in z. It is blocked, and the state is
again a gridlock by MX-0. Repeat until all WH + 2|R| cells are full. ∎

**Endpoints.** R = ∅ gives min(W,H) ≤ n ≤ WH, which is G1. R everything gives
2·min(W,H) ≤ n ≤ 3WH, which is RB-G.

## 3. How the least gridlock depends on the share of roundabouts

**Corollary MX-E (extremes over placements).** Among all R with |R| = k,

- the largest n_min is min( W + ⌊k/H⌋ , H + ⌊k/W⌋ );
- the smallest n_min is min( W + max(0, k − W(H−1)) , H + max(0, k − H(W−1)) ).

*Proof.* *Largest.* Some row has at most ⌊k/H⌋ roundabouts and some column at most ⌊k/W⌋,
which gives the bound. It is attained by laying the k roundabouts row after row, ⌊k/H⌋ or
⌈k/H⌉ per row, each row continuing cyclically at the column where the previous one stopped:
the k roundabouts then occupy consecutive positions round the cycle of columns, so each column
holds ⌊k/W⌋ or ⌈k/W⌉ (`balanced`). *Smallest.* The other H−1 rows hold at most W(H−1)
roundabouts, so every row has r_y ≥ k − W(H−1), and likewise for columns. Filling all other
rows first, or all other columns first, attains whichever term is smaller. ∎

In terms of ρ = k/WH on an L×L torus: the best placement gives n_min = L + ⌊ρL⌋, and the worst
gives n_min = L until ρ > 1 − 1/L. **One street without roundabouts returns the least gridlock
to BML's value, whatever the share.** Raising it needs roundabouts on every street.

**Corollary MX-P (random placement).** Let each intersection be a roundabout independently
with probability ρ.

- If H ≥ 2W, then n_min = W + min_y r_y, and P(n_min ≥ W + j) = P(Bin(W,ρ) ≥ j)^H exactly.
- On the L×L torus, n_min/L → 1 + ρ in probability as L → ∞.

*Proof.* If H ≥ 2W, every column costs at least H ≥ 2W ≥ W + r_y, so rows decide, and the row
counts are independent Bin(W,ρ). On the square, n_min ≤ L + r_0 and r_0/L → ρ. For the other
direction, Hoeffding's inequality and a union bound over the 2L streets give
P(some street has fewer than (ρ−ε)L roundabouts) ≤ 2L·exp(−2ε²L) → 0. ∎

**Scope of §§2–3.** n_min is the size of the smallest gridlock that can exist. It is an
extremal quantity and says nothing about how likely random traffic is to reach a gridlock; for
that see §6.

## 4. Proposition MX-F (a time budget at every junction)

A configuration is **free** if from tick 0 on no car is ever delayed by another car, so that
cars wait only for signals. Every free car covers one block per two ticks on average. Let E_y
be the number of E cars in row y and N_x the number of N cars in column x.

**Claim.** In a free configuration, for every intersection v = (x,y),

> (E_y / 2W)·(2 + σ_E(v)) + (N_x / 2H)·(2 + σ_N(v)) ≤ 1,

where σ_E(v) = 1 if the next intersection east of v is a signal, σ_N(v) = 1 if v and the next
intersection north of v are both signals, and both are 0 otherwise.

*Proof.* Once a free car has passed a signal, it enters every junction cell on its street in
ticks of the parity that its signals admit, two ticks per block, and its timetable is
periodic. On a street without signals it moves in every tick. A car leaving a junction cell waits there one extra
tick exactly when its next cell is a signal junction: this is the case σ_E(v) = 1 for E cars.
For N cars it happens only at a signal v whose northern neighbour is a signal, because at a
roundabout the N car moves on to b(v) and waits there. So a visit occupies c(v) for 1 + σ
ticks. A cell vacated in one tick cannot be entered in that tick, so each visit is followed by
an empty tick, and visits use 2 + σ ticks each, disjointly. Each E car of row y visits c(v)
once per 2W ticks and each N car of column x once per 2H ticks. ∎

**Corollary (one signal caps a street).** In a free configuration a row that contains a signal
carries at most ⌊2W/3⌋ E cars, and a row of roundabouts at most W. A column with two
consecutive signals carries at most ⌊2H/3⌋ N cars. With R = ∅ and with R everything the
budget gives the upper bounds n ≤ 2WH/3 of Theorem F and n ≤ WH of RB-C.

The budget is necessary and not sufficient: on 3×3 with one roundabout it allows more than
the true capacity 5.

## 5. Free-flow capacity is not monotone in R

`free_levels` enumerates every free configuration of a placement from the dynamics.
`scripts/check_mixed.py` does this for **every** placement on five small tori. The table gives
the smallest and largest capacity over the placements with k roundabouts.

| k | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|---|---|---|
| 3×3 | 6 | 5 | 4–5 | 4–7 | 4–6 | 4–6 | 4–8 | 6–7 | 7 | 9 |
| 4×2 | 4 | 4 | 4–5 | 4–5 | 4–6 | 5–6 | 6–7 | 7 | 8 | |
| 3×2 | 3 | 3 | 3–4 | 3–4 | 4–5 | 5 | 6 | | | |
| 2×2 | 2 | 2 | 2–3 | 3 | 4 | | | | | |

So on 3×3 the first roundabout lowers the capacity, the mean over placements stays below the
BML value 6 until k = 7, and the last signal still costs two cars (7 against 9). On 3×3 BML
reaches its ceiling because 3 | g, and one roundabout breaks the period-3 pattern that does
so. On the other three boards, where BML is below its ceiling, the minimum never falls below
the BML value. These are exact facts about these boards only; no general capacity formula for
mixed R is proved here.

## 6. Monte Carlo: gridlock from random traffic against the share

Not a proof. L = 24, each intersection a roundabout with probability ρ, each cell occupied
with probability p, 40 runs of 6,000 ticks per point, one seed. A run counts as gridlocked if
no car can move at the end.

| ρ | highest p with no gridlocked run | lowest p with ≥ half the runs gridlocked | the same, in cars per intersection |
|---|---|---|---|
| 0 | 0.34 | 0.46 | 0.45 |
| 0.25 | 0.14 | 0.22 | 0.34 |
| 0.5 | 0.10 | 0.18 | 0.36 |
| 0.75 | 0.10 | 0.18 | 0.45 |
| 1 | 0.38 | 0.50 | 1.50 |

The grid of p has step 0.04. In this model a mixed grid jams at a markedly lower density than
BML, per cell and per intersection, and the all-roundabout grid holds about three times as
many cars per intersection as BML before jamming. One size and one seed support no claim
about a limit, and 6,000 ticks may undercount slow jams.

A likely contributor is the modelling choice of §0: an E car waiting for a signal sits in the
shared cell of the roundabout behind it and blocks the crossing N stream. This was not tested.
A variant with a link cell between intersections would remove it, and is the natural next
model to compare.

## 7. Summary: what the share of roundabouts does

| quantity | dependence on R | status |
|---|---|---|
| least gridlock n_min | W or H plus the fewest roundabouts on a street | proved (MX-G) |
| n_min at share ρ | from min(W,H) to ≈ (1+ρ)·min(W,H); random placement → (1+ρ)L | proved (MX-E, MX-P) |
| most cars in gridlock | WH(1 + 2ρ) | proved (MX-G) |
| free flow on one street | ≤ 2/3 per junction if the street has a signal, ≤ 1 if none | proved (MX-F) |
| free-flow capacity | not monotone; lowest at intermediate shares on 3×3 | exhaustive on 4 tori |
| gridlock from random traffic | earliest at intermediate shares, L = 24 | simulation |

**Evidence.** The tests compare n_min with the girth of the blocker graph for every placement
on eight boards up to 4×2 and 3×3, and with exhaustive enumeration of all states on boards with
at most four intersections. The construction is replayed at every admissible count on random
placements up to 5×5. MX-E is checked against all placements up to 4×4, MX-P against exact
enumeration on four boards, and MX-F on every free configuration of every placement up to
3×2. The largest board in the capacity census has nine intersections.
