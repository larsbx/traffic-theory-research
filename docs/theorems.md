# When does BML gridlock switch? — what is proved here, and what stays open

**Model.** Let W,H ≥ 1. The torus is 𝕋 = ℤ_W × ℤ_H. A configuration is s : 𝕋 → {·, E, N}. One step is
an **E half-step** followed by an **N half-step**:

- E half-step: every E car whose east cell (x+1, y) is empty moves into it, all at once;
- N half-step: the same for N cars and their north cell (x, y+1).

Move eligibility uses the state **before that half-step**: a car cannot follow another car
into a cell that the latter vacates during the same half-step. This is Model I in
[Biham–Middleton–Levine 1992][BML], p. 2. The step map f is deterministic and conserves
n_E and n_N. Notation: n = n_E + n_N. Extrema below range over **all species allocations**;
they do not impose equal numbers of E and N cars.

Throughout the CLASSIC discussion below, these are `bml.model.CLASSIC`
updates. Section 5b explicitly changes the rule to `bml.model.TRAIN`.

Every orbit is eventually periodic, and its terminal cycle is one of three kinds:

| kind | definition |
|---|---|
| **gridlock** (JAM) | some car exists and no car moves on the cycle |
| **free flow** (FREE) | every car moves at every step |
| **intermediate** (MIXED) | anything else: mean velocity strictly between 0 and 1 |

The empty configuration is classified FREE by convention, although it is also a fixed point.
Here “already free” means every car moves at every full step starting now; “eventually FREE”
allows a transient. A fixed car count admits eventual FREE exactly when it admits an
already-free configuration, because car counts are conserved and one can start on the
terminal cycle. This equivalence concerns **existence**, not every initial configuration.

**Verification boundary.** The prose proofs below are distinct from the Lean theorems and
bounded computational checks. [The formal coverage register](../formal/README.md) identifies
the statements currently checked by Lean, the actual Quint replay bounds, and the remaining
G1/G2/R/F obligations. A bounded table does not prove a universal statement.

The `BML` library supplies the finite-torus kernel, species transport bijections,
G1/F arithmetic components, and the strong non-monotonicity theorem below. The
[companion Traffic suite](../formal/traffic-layer.md) independently supplies the
fixed-point/blocking equivalence, Wang recoding, and staircase constructions.
Its finite-walk winding theorem assumes modular closure. Extracting an actual
simple blocker cycle and linking its closure and distinct-car count to the
arithmetic results remain obligations; no general bridge between the two Lean
libraries is being assumed.

The `BML` and `Traffic` suites use **CLASSIC** old-state vacancy semantics.
The separate [`BML.Train` Lean and `Train.qnt` Quint layer](../formal/TRAIN.md)
implements TRAIN queue and full-ring movement. Its Lean proofs now include the
complete Theorem T in §5b, numeric conservation, and the distinction between
fixed occupancy and zero movement. A full single-species TRAIN ring rotates
while its occupancy is unchanged, so G0's fixed-point criterion cannot be
transferred to that rule. The additional 3×4 non-monotonicity witness remains
Python-only; the complete CLASSIC G1/G2/R/F arguments retain their stated
prose/bounded-evidence boundaries.
The sparse-square TRAIN speed-one result in §5c is also fully kernel-checked,
including the actual diagonal dynamics and numerical movement conclusion.

## 0. The open problem, stated precisely

Let μ_p be the i.i.d. measure where a cell is E w.p. p/2, N w.p. p/2 and empty otherwise.

**Research conjecture.** There is a p_c ∈ (0,1) such that
- P_{μ_p}(gridlock on the L×L torus) → 0 as L → ∞ for p < p_c;
- the same probability → 1 for p > p_c.

This is an **unresolved target**, not a result proved here or a verbatim formulation from
the 1992 paper. That paper explicitly leaves open whether its finite-size transition
locations converge to a positive value or to zero (pp. 4–5). Intermediate phases also
require care when proposing a single sharp threshold. Primary-source checks give:

| result | statement |
|---|---|
| [Angel–Holroyd–Martin][AHM], *Electron. Comm. Probab.* 10 (2005), Theorems 1–2 | On ℤ², for p sufficiently close to 1, every car moves only finitely often a.s. The finite-torus theorem also gives eventual gridlock with probability tending to 1 as both dimensions grow and their ratio converges in (0,∞). |
| [Austin–Benjamini][AB], arXiv:math/0607759v3 (2006), Propositions 1, 6, 8 | Prop 1: eventual speed one below N/2 cars. Prop 6: a stuck configuration of m cars exists ⟺ m ≥ 2N. **Different update rule (resolved in §5b):** their written rule moves same-species queues together and rotates a full ring (the *train rule*, `bml.model.TRAIN`). That explains 2N against the CLASSIC kernel's N. Prop 6 is re-proved and extended to rectangles in §5b. The full TRAIN Prop 1 Lean proof is described in §5c. Its proposed CLASSIC transfer (§2) remains unproved. |
| [Hertzberg Rabinovich–Biham–Katzav][HBK], arXiv:2601.01180v2 (2026) | Square lattices: free-flowing periodic states are the zero set of a distance D = D∥ + D⊥, and the zero set persists. The full text studies relaxation with numerical fits; it does not prove our fixed-positive-density probability target. |
| [D'Souza][DS], *Phys. Rev. E* 71 (2005), 066112 | Numerical stable intermediate phases and dependence on lattice aspect ratio. |
| [Yashina–Tatashev][YT], arXiv:2311.17120 (2023), Theorem 1 | For deterministic fixed directions and both species present, perpetual free motion requires gcd(W,H) ≥ 3; this overlaps a consequence of Lemma R. |

The AHM paper starts with the opposite first species; interchanging coordinates and species
gives the same iid law and the same fixation statement for our phase convention.

The [tagged-fixation reduction](research/2026-11-18-tagged-fixation-and-gridlock.md)
gives a further exact deterministic theorem for this CLASSIC kernel. Let `J`
mean eventual nonempty global jam, `S` mean that some original car moves only
finitely often, and `R` mean an initially full E-row or N-column. Then
`S = J union R`, with a complete Lean proof. Write `q_L(p) = Pr_p(J)`.
For `p > 0`, let `f_L(p)` be the probability that the original car at a specified
site eventually stops, conditioned on that site being occupied. The separate
prose probability argument proves

\[
|f_L(p)-q_L(p)|\le
\frac{1}{2L}\sqrt{\frac{1-p}{p}}+L(p/2)^{L-1}.
\]

Thus the two probabilities have the same fixed-positive-density limits whenever
those limits exist. This reduction does not establish their existence or a
positive sharp critical density; full movement and infinite-volume fixation
remain distinct questions.

Below are exact **extremal existence thresholds** on each finite torus. They do not settle
the complete deterministic question of which car counts force eventual free flow, or the
probability of gridlock at fixed positive density.

## 1. Lemma G0 (gridlock = fixed point)

**Claim.** For a **nonempty** configuration, its terminal cycle has velocity 0 ⟺ the orbit
reaches a fixed point. For every configuration, including the empty one,

> s is fixed ⟺ every E car's east cell is occupied and every N car's north cell is occupied.

*Proof.*
1. The N half-step preserves exactly the set of E-occupied cells. If an E car moves from a
   cell z, that cell cannot receive another E in the same half-step, because z was occupied
   when eligibility was computed. The N half-step cannot restore an E at z. Consequently
   f(s) = s implies that no E car moved.
2. The N half-step therefore starts from s itself. The same source-vacancy argument shows
   that if an N car moved, its source would change. Thus f(s) = s also implies no N moves.
3. No moves occur exactly when both local blocking conditions hold. Conversely, those
   conditions make both half-steps the identity.
4. On a finite recurrent cycle, zero mean velocity for a nonempty configuration means zero
   moves on every edge, since move counts are nonnegative. The cycle is then a fixed point.
   A reached fixed point persists and has zero moves. ∎

## 2. Theorem G1 (least gridlock): a gridlock with n cars exists ⟺ min(W,H) ≤ n ≤ WH

*Proof of ≥.* Let s be fixed with n ≥ 1. Define the blocker map β on cars:
- β(c) = the car in the east cell of c, if c is an E car;
- β(c) = the car in the north cell of c, if c is an N car.

β is well defined by G0, and it maps a finite set to itself, so it has a cycle c₀ → c₁ → … → c_{ℓ−1} → c₀.

- Each β-step is a unit step (1,0) or (0,1).
- So the cycle is a closed lattice loop on 𝕋 with a E-steps and b N-steps.
- (a, b) ≡ (0, 0) in ℤ_W × ℤ_H with a, b ≥ 0 and a + b = ℓ ≥ 1. Hence W ∣ a and H ∣ b, not both zero.

Its cars are distinct, so n ≥ ℓ = a + b ≥ min(W, H).

*Construction (tightness, every n in range).* Fill a shortest line (a row of W E cars, or a column
of H N cars). Then stack cars of the other species behind it, line by line: each new car is blocked by
the one in front, and the last by the full line (`extremal.gridlock_with`).

*Corollary.* With 0 < n < min(W,H), no configuration ever gridlocks and every orbit has
positive asymptotic velocity. The empty state is FREE by convention. G1 is the exact
threshold for gridlock *existence* and holds for every aspect ratio. It does not establish
eventual free flow for all configurations below that threshold. ∎

*Proposed CLASSIC transfer of Austin–Benjamini Prop 1 (not a verified import).*

The paper's written rule is TRAIN, and §5c treats that actual rule. The following
argument is a proposed extension to CLASSIC; the TRAIN proof does not itself
establish it.
- Their proof tracks empty arcs of time-corrected NW–SE diagonals. It uses only two facts:
  cars advance at most one diagonal per step, and a diagonal with an empty diagonal above it
  always releases at least one car.
- The second fact also holds here. Its E cars move first into the empty diagonal, unobstructed;
  if it has none, every N car moves.
- So m < N/2 should force eventual speed one under this kernel too, which is stronger than the
  corollary above on square tori.
- Random tests up to 14×14 under both rules agree (`tests/test_train_rule.py`).
  This CLASSIC transfer still has no complete Lean proof.

## 3. Theorem G2 (no forced gridlock below full density)

**Claim.** If WH ≥ 2 and 0 ≤ n < WH, some n-car configuration never gridlocks.

*Proof.* If n = 0, use the empty configuration, which is not gridlock. Otherwise say W ≥ 2;
if not, swap the roles of E/rows and N/columns.

1. Use E cars only. Then the rows evolve independently, as one-lane rings.
2. Fill rows so that some row holds between 1 and W−1 cars. If n ≢ 0 (mod W), filling greedily
   leaves a partial row. If n ≡ 0 (mod W) and n > 0, then n ≤ WH − W, so an empty row exists;
   move one car into it.
3. In a ring with a car and a hole, the car directly behind a hole always moves. So the row never
   freezes. ∎

Hence the deterministic switch is *not* at any density below 1: every n < WH is unforced.

## 4. Non-monotonicity

Adding one car can turn an orbit that gridlocks into one that never does. Exhaustively
(`data/exhaustive.json`) this happens on every torus with W, H ≥ 2 up to 16 cells; for example
6 612 960 (state, cell, species) triples on 4×4.

The smallest recorded witness (2×2) is a full E row plus one E car in the other row.
There is also a stronger 4×2 witness, with rows listed in increasing y and entries 0/1/2
meaning empty/E/N:

| configuration | rows | behavior |
|---|---|---|
| s, code 3858 | `[[0,2,2,1],[2,0,2,1]]` | Reaches the fixed state `[[2,1,2,0],[1,2,2,0]]` after three full steps. |
| s′, code 3860 | `[[2,2,2,1],[2,0,2,1]]` | Add an N at (x,y)=(0,0). Alternates with `[[2,0,2,1],[2,2,2,1]]`, code 4340. |

In s′ the **original** N car initially at (x,y)=(1,0) moves every full step forever.
The **added** N car at (0,0) never moves. This is not a case of adding an independent
circulating car. [The witness data](../data/formal-witnesses.json) are checked by an
independent labeled-car replay, which detects recurrence of identities as well as colors,
and compared against the NumPy dynamics. The Lean layer also checks the concrete orbit
and its indefinite two-cycle; the coverage register states the identity boundary precisely.
No claim of minimality or novelty is made.

**Census of genuine witnesses** (`bml.nonmonotone`, identity-tracking replay over every
gridlocking x and every single-car addition y). A pair counts as *genuine* if some original
car of x moves infinitely often in y:

| H×W | 2×2, 2×3, 3×2, 3×3 | 2×4 | 2×5 | 3×4 | 4×3 |
|---|---|---|---|---|---|
| genuine un-jamming pairs | **0** | 24 | 460 | 17 952 | 18 108 |

On every torus with ≤ 6 cells (apart from 1×n, which never un-jams), un-jamming is only ever the
added car itself; the 4×2 witness above lives on the smallest torus where a genuine pair occurs.

On 3×4, one added E car keeps **all seven** original cars moving forever. Without it they all
freeze. Rows below are printed north to south, `>` = E and `^` = N:

```
x (freezes completely)      y = x + E car at (x,y)=(0,0)
^^>.                        ^^>.
>>.^                        >>.^
...>                        >..>
```

This is pinned in `tests/test_nonmonotone.py` by NumPy identity replay only; it is not in
`data/formal-witnesses.json` or Lean.

Consequence: "gridlock" is not an increasing event under adding cars. So no monotone coupling in
p gives the threshold for free, and a sharp-threshold argument (e.g. Friedgut–Kalai) cannot be
applied naively.

## 5. Lemma R (rigidity of free flow) and Theorem F (densest free flow)

Let g = gcd(W, H) and φ(x, y) = x + y mod g.

**Lemma R.** s flows freely forever ⟺ all three of the following hold:
1. no E car has an E car directly east of it;
2. no N car has an N car directly north of it;
3. for every N car q and E car e: φ(q) − φ(e) ∉ {0, 1} (mod g).

*Proof.* In free flow every car moves at every step, so the motion is rigid:
e(t) = e + (t, 0) and q(t) = q + (0, t). Write d = q − e. For all t:
- the E move needs e + (t+1, 0) ≠ q + (0, t), i.e. d ∉ (1, 0) + G;
- the N move needs q + (0, t+1) ≠ e + (t+1, 0), i.e. d ∉ G (this also forbids overlap);

where G = ⟨(1, −1)⟩ ≤ ℤ_W × ℤ_H. Same-species collisions are rigid-invariant: conditions 1 and 2.

The kernel of φ contains G, and |ker φ| = WH/g = lcm(W, H) = |G|. So G = ker φ, and the two
conditions read φ(d) ∉ {0, 1}. Conversely, if 1–3 hold, the rigid motion is consistent at every
half-step. ∎

(Checked exhaustively on all tori with ≤ 9 cells and on random states up to 8×8; see
`tests/test_extremal.py`.)

**Theorem F.** Let n_free(W,H) be the largest car count that admits free flow, and V(g) = ⌊(g + ⌊g/3⌋)/2⌋. Then

- for g = 1: n_free = max( H⌊W/2⌋, W⌊H/2⌋ );
- for g ≥ 2: n_free = (WH/g) · V(g).

Free flow exists for exactly the n with 0 ≤ n ≤ n_free.

*Proof of ≤.*
1. Let A = φ(E cars) and B = φ(N cars) ⊆ ℤ_g. Lemma R gives B ∩ (A ∪ (A+1)) = ∅.
2. If g = 1, this forces a single species, and condition 1 (or 2) caps each row at ⌊W/2⌋
   (or each column at ⌊H/2⌋).
3. If A = ℤ_g, then B = ∅ and n ≤ H⌊W/2⌋ ≤ WH/2 ≤ (WH/g)V(g). The case B = ℤ_g is symmetric.
4. Otherwise the cyclic word over ℤ_g with letters A / B / · splits after each "·" into blocks
   Bˢ Aʳ · of length ℓ = s + r + 1. An A-run cannot be followed by B (since B ∩ (A+1) = ∅); maximal
   runs do the rest. There is at least one blank in this case: a cyclic word containing both
   A and B with no blank necessarily has a forbidden A→B transition; if only one letter
   appears with no blank, it occupies the whole circle, already handled in step 3.
5. Count cars per block:
   - In each row the cells of an A-run form W/g horizontal segments of length r, each holding at
     most ⌈r/2⌉ E cars (condition 1).
   - Likewise each B-run gives H/g vertical segments per column, at most ⌈s/2⌉ N cars each.
6. So n ≤ (WH/g) Σ_blocks (⌈s/2⌉ + ⌈r/2⌉).
7. Each term is ≤ (ℓ + ε)/2, where ε = 1 iff s and r are both odd. That needs ℓ ≥ 3, so the
   number k of such blocks is ≤ ⌊g/3⌋. Integrality then gives Σ ≤ ⌊(g + ⌊g/3⌋)/2⌋ = V(g).

*Construction.* For g ≥ 2, label the classes with k blocks (N, E, ·) followed by blocks (E, ·).
Here k ∈ {⌊g/3⌋, ⌊g/3⌋ − 1} is chosen so that k ≡ g (mod 2). For g = 1, alternate cars along the
better direction. Fewer cars: delete cars, since conditions 1–3 are closed under deletion. ∎

(Verified by simulation for all W, H ≤ 12, and against the exhaustive data for WH ≤ 16.)

On L×L: n_free = L · ⌊(L + ⌊L/3⌋)/2⌋, so the densest free flow has density → **2/3**, attained
exactly when 3 ∣ L (L = 3m gives V = 2m). For W, H coprime, free flow is
single-species, with density ≤ 1/2.

The formula simplifies to V(g) = ⌊2g/3⌋: write g = 3m+r for r ∈ {0,1,2}.
Thus for g ≥ 2 the maximal density is ⌊2g/3⌋/g, attaining 2/3 exactly when 3 ∣ g.
The g = 1 branch remains separate.

**Prior art.** The square-density value 2/3 is already stated in footnote [7] of
[BML 1992][BML]; it is not a novelty claim here. The mixed-species obstruction at g < 3
also appears in [Yashina–Tatashev, Theorem 1][YT]. Whether the complete rectangular floor
formula appears earlier remains unestablished by the present source check.

## 5b. The train rule: Austin–Benjamini Prop 6 on rectangles

Under the **train rule** (`bml.model.TRAIN`), a maximal line of same-species cars moves together
if the cell ahead of its head is empty; a full single-species ring rotates as well.
This is the queue movement rule written by [Austin–Benjamini][AB]. The east
half-step is followed by the north half-step, with simultaneous movement within
each phase. An unchanged occupancy pattern need not mean zero movers.

**Theorem T.** Under the train rule on W×H with W,H≥2, a nonempty stuck
configuration of n cars exists ⟺ W+H≤n≤WH. If a dimension is one, no nonempty
stuck configuration exists. Consequently the same equivalence holds for all
positive W,H: the numerical interval is empty in the singleton case.

**Formal status.** This entire equivalence, including the construction at every
allowed n and the singleton boundary, is kernel-checked in
[`Train/Threshold.lean`](../formal/lean/Train/Threshold.lean).
`BML.Train.noMoves_population_iff` states it directly using zero movement in
the two successive half-steps. `jam_population_iff_positive` uses the equivalent
nonempty `Jam` predicate. These statements use the actual executable TRAIN
kernel and its occupied-coordinate population, not an assumed static
certificate or a bounded enumeration. The [TRAIN register](../formal/TRAIN.md)
gives the proof inventory and separately scoped cross-language evidence.

*Proof of ≥* (Austin–Benjamini's square argument extended to rectangles).
Suppose s is stuck and n≥1.

1. A column with N cars but no E car would release its N cars: either a line ends at a hole, or the
   column is full and rotates. So every column with a car contains an E car.
2. If some column x had no E car, it would be empty by step 1. Then the E cars of column x−1 would
   move, so column x−1 has no E car either. Inducting leftwards, there are no E cars at all, and
   then no cars at all by step 1, contradicting n ≥ 1.
3. So every column has an E car, and symmetrically every row has an N car: n ≥ W + H.

*Construction, every n in the interval.* Put k=n−(W+H). Start at (0,0) and
follow the closed staircase with word E^(W−1) N^(H−1) E N. It winds once in each
direction and has W+H distinct occupied cells. Each car faces its successor:
E cars occupy y=0,x<W−1 and the top-right corner (W−1,H−1); N cars occupy the
right column below that corner and (0,H−1).

For every other interior coordinate x<W−1,1≤y≤H−1, define

\[
j=x(H-1)+(H-1-y).
\]

Place an N car exactly when j≤k. The j=0 car already belongs to the core;
indices 1,…,k add exactly k cars. Their north targets are occupied, since the
ordering fills each column downwards from its top, and the top car points
around to the bottom-row E car. The fixed E cars still have occupied targets.
Every row contains an N and every column an E, so no homogeneous ring can
rotate. Thus the configuration is TRAIN-stuck with
W+(H−1)+(k+1)=W+H+k=n cars. The capacity condition is precisely
k<(W−1)(H−1), equivalent to n≤WH under n≥W+H.

This is the coordinate formula used by Lean `stuckConfig` and Python
`extremal.train_stuck_with`. Lean proves the exact count through an explicit
duplicate-free listing and proves zero movement through the queue/ring kernel.
For singleton dimensions, the necessary W+H lower bound exceeds capacity WH,
which proves impossibility. ∎

**Finite implementation checks.** The Python tests check all allowed
constructor populations for 2≤W,H≤8 and the existence equivalence exhaustively
through WH≤12. The separate TRAIN Quint checker compares all 3,720 boards on
the 14 ordered rectangles with WH≤6, 74 larger targeted cases, and 96 constructor
boards; its 24 named tests and mutation controls have their own bounded scope.
The Lean/Python acceptance domain includes all 784 constructor boards for
2≤W,H≤8. Consult source-bound run receipts for completed acceptance at a given
revision. These finite comparisons support the implementations; the all-size
mathematical theorem comes from Lean's proof.

**Same question, two rules.** The least frozen car count is min(W, H) under CLASSIC (G1) and
W + H under the train rule (T). On N×N these are N and Austin–Benjamini's 2N.
The 21 Wang tile types in the tiling note encode occupied directed targets,
which suffice for CLASSIC freezing. A TRAIN jam additionally excludes full E
rows and full N columns. There is no claimed TRAIN Wang encoding. The separate
square speed-one statement is described next.

## 5c. The train rule: eventual speed one below N/2 on squares

**Formal status:** the full theorem is kernel-checked in
[`Train/SpeedOne.lean`](../formal/lean/Train/SpeedOne.lean), using the proved
cyclic argument, actual diagonal dynamics, and numerical movement
characterization. Its public statement assumes only the square domain,
positive side length, and strict population bound.

**Proposition S (Austin–Benjamini Proposition 1).** Let N>0 and let s be any
TRAIN configuration on an N×N torus. If `2 * population s < N`, then

\[
\exists T\;\forall t\ge T:\quad
\operatorname{totalMoveCount}(\operatorname{torusStep}^{t}(s))
=\operatorname{population}(s).
\]

`totalMoveCount` adds east moves and north moves in the following half-step.
Lean's `fullSpeed_iff_all_phases_move` proves that this equals the population
exactly when every car moves in its own phase. Thus the conclusion asserts
eventual speed one, rather than merely perpetual positive movement. It
includes the empty configuration and imposes no species balance. The public
theorem names are `BML.Train.sparse_square_eventually_fullSpeed` and
`BML.Train.sparse_square_moves_equal_population`.

*Proof route.* [Austin–Benjamini, pp. 2–3][AB] uses corrected diagonals; the
formal argument works with adjacent empty pairs instead of maximal arcs.

1. Label the initial cars and track each through both phases. The corrected
   tag is `x+y−t mod N`, where t counts full cycles. A moving car keeps its tag;
   a blocked car moves one tag backwards. Transport covers every current car.
2. An occupied physical diagonal followed by an empty one releases at least
   one car in the next full cycle. If an east car is present, it can move;
   otherwise north cars can move because the east phase cannot fill their
   target diagonal from that source diagonal.
3. The condition 2m<N guarantees two adjacent empty tags at every time. If
   no such pair existed, the m occupied tags and their predecessors would
   cover all N tags, contradicting N>2m. Tags may coincide without harming
   the count.
4. Every empty pair at t+1 was already empty at t: occupants of its old second
   site have nowhere to go, and release would keep some corrected tag at its
   old first site if that site were occupied. Thus pair sets decrease. A finite
   descending-family argument gives one pair that stays empty forever.
5. Cut the cyclic order at a permanent vacancy. Each car's natural-number
   rank drops when it is blocked and otherwise stays fixed. Its attained
   minimum gives eventual tag stability. The finite list of initial cars
   has a common eventual time; the actual movement equivalence and count
   conservation give the displayed conclusion.

The generic cyclic argument is proved as
`BML.Train.Diagonals.sparse_eventual_stable`; `Train/DiagonalDynamics.lean`
discharges its release and step hypotheses from the actual TRAIN kernel. See the
[TRAIN register](../formal/TRAIN.md#sparse-squares-eventual-speed-one) for the
module boundaries and evidence scope.

The statement is **square-only**. Replacing N by min(W,H) is false: one east
and one north car on a 5×7 torus satisfy 2m<min(W,H), but rigid free trajectories
would produce a future east-target/north-position collision by the Chinese
remainder theorem. No rectangular speed-one theorem, effective stabilization
time, random-density threshold, or CLASSIC transfer is claimed here.

The finite acceptance domain consists of all 1,305 low-population states
on N=1,…,5, closed under the actual successor map. Its criterion is that every
terminal cycle has full actual movement on every edge. Eight further orbit
certificates contribute 53 transition rows, including positive examples on
6×6, 7×7, and 8×8. The 5×7 two-car counterexample has transient 1 and period
15, with 29 moves in 30 car-step opportunities on its terminal cycle. Ten
additional Quint tests and six adversarial controls check the clock, phase
counts, recurrence, domain completeness, and theorem scope. The
[TRAIN register](../formal/TRAIN.md#eventual-speed-one-acceptance) records the
exact domains and commands; source-bound receipts distinguish completed
acceptance from the all-size Lean proof.

## 6. CLASSIC extremal existence diagram (every finite torus)

| car count n | gridlock possible | gridlock forced | free flow possible |
|---|---|---|---|
| n = 0 | no | no | yes (vacuously) |
| 0 < n < min(W,H) | no (G1) | no | yes iff n ≤ n_free |
| min(W,H) ≤ n ≤ n_free | yes | no | yes |
| n_free < n < WH | yes | no (G2) | no (F); MIXED or JAM only |
| n = WH | yes | yes | no |

As a density on L×L, the gridlock-existence threshold is 1/L → 0 and the free-flow-existence
threshold → 2/3. Gridlock is not forced at any count below full occupancy. The earlier
statement that “free flow is forced at no density” was false: for W,H ≥ 2 every one-car
configuration moves freely forever. That claim also conflated an initially free state with
eventual free flow.

What G1 does imply is that, for any fixed positive density and all sufficiently large square
tori, a jammed configuration exists at the corresponding integer car count. A density alone
therefore cannot force free flow for every configuration in that asymptotic regime. These
extremal facts do not determine the probabilities of the competing outcomes under μ_p.

## 7. Empirical context (not a proof)

`python -m bml.montecarlo 32 4000` (32 samples per p, μ_p, 4000 steps):

- the jammed fraction rises from 0.03 at p = 0.400 to 0.81 at p = 0.450;
- the mean velocity drops from 0.76 to 0.09 over the same range.

The output is in `data/montecarlo_L32_T4000.txt`. Finite-size estimates of the switch drift with L
and T, so this does not estimate p_c.

## 8. Why an initial-loop bound does not prove a low-density phase

Let C₀ be the event that a simple directed occupied blocking loop already exists at time zero
on the L×L torus. Such a loop has length ℓ ≥ L by G1's winding argument and at most L²
distinct cells. At most L²·2^ℓ rooted direction words can describe it. For any word that does
describe a simple loop, its prescribed orientations occur with probability (p/2)^ℓ under μ_p.
A union bound gives, for 0 ≤ p < 1,

\[
\Pr(C_0) \le L^2\sum_{\ell=L}^{L^2}p^\ell
\le \frac{L^2p^L}{1-p}.
\]

This tends to zero for **every fixed p < 1**, including the high-density regime where AHM's
finite-torus theorem proves eventual gridlock with probability tending to one. Thus absence
of an initial simple blocker loop is not an obstruction to later gridlock.

An explicit 3×2 example starts at `[[2,2,1],[1,1,0]]`, code 125. Every blocker chain initially
ends at the hole, but after four full steps it reaches the frozen state `[[1,2,0],[2,1,1]]`.
The [certificate](../data/formal-witnesses.json) checks both graph conditions and the full
orbit. The counting argument above is a prose derivation, not a Lean theorem.

The unresolved probability estimate must control **loop formation during evolution**.
The evolved distribution is not the initial iid measure, so its orientation probabilities
cannot be multiplied as if independent. Reusing the same time-zero bound at all later
times, or taking an unproved union over unbounded time, does not close this gap.

## 8b. Persistent cores and capture

The [freezing and nucleation note](research/2026-11-18-freezing-gridlock-nucleation.md)
separates existence, formation, capture, and limiting basin probability. It
specializes the mixed-winding blocking mechanism in Angel–Holroyd–Martin's
proof of Theorem 2: a persistent occupied core meeting every row and column
forces all cars to stop within

`M = n_E*(W-1) + n_N*(H-1)`

full steps, and bounds every finite prefix of future car moves by M. A simple
occupied blocker cycle containing both directions supplies such a core by
winding around both torus coordinates. A monochromatic cycle alone need not
capture the whole system.

`BML/Capture.lean` proves core persistence and the universal actual-kernel
capture theorem from explicit row/column obstacle witnesses. The winding-to-
coverage construction is still prose mathematics, checked by `bml.capture`
on finite certificates. Independent labeled replay verifies core identities,
individual motion, rank decrease, and the bound against the production model.
See the [coverage register](../formal/README.md) for the exact boundary.

The remaining probability problem is the formation of a suitable structure.
The theorem supplies a capture bound after a certificate appears; it does not
locate a critical density or establish that a mixed cycle is necessary for
all possible global jams.

## 8c. Probability reductions and a shrinking no-gridlock window

Let J be eventual nonempty global gridlock, M eventual appearance of a mixed
direct blocker cycle, and R the presence of a full eastbound row or northbound
column initially. Conservation of species counts in each lane and the cycle
argument give the exact deterministic identity

`M = J intersect R-complement`.

The [probability note](research/2026-11-18-probabilistic-gridlock-bounds.md)
proves this identity, including why a full monochromatic lane prevents a mixed
cycle. Under the iid law on an L×L torus,

\[
0\le \Pr_p(J)-\Pr_p(M)\le2L(p/2)^L\le2L\,2^{-L}.
\]

Thus the two eventual probabilities have the same limiting behavior, uniformly
over density sequences. Their common fixed-positive-density threshold remains
unproved.

The note also proves a conserved-strip obstruction. If k consecutive columns
have no N cars, every row has fewer than k E cars, and no column is full N,
then no future nonempty jam is possible. An exact finite iid bound yields

\[
p_LL\le(2-\varepsilon)\log\log L
\quad\Longrightarrow\quad
\Pr_{p_L}(J)\longrightarrow0
\qquad(0<\varepsilon<2).
\]

This is a shrinking-density no-gridlock theorem in prose. It does not prove
eventual perfect free flow or a nonjamming interval at fixed positive density.
In fact, for every fixed p>0 the probability of even one N-free column tends
to zero, so the strip method cannot be extended to fixed p merely by improving
its tail estimates.

`BML/Lanes.lean` proves the underlying CLASSIC numerical species and lane-count
invariants, full-lane persistence and backward reflection, and invariance of
north-free cyclic strips. `bml.probability` supplies exact rational finite probabilities and
checked strip certificates; its census compares independently detected eventual
mixed cycles with the orbit classifier. The probability laws and analytic
limits are not claimed as Lean theorems. The note additionally proves both
jam/free-flow representatives in typical conserved lane classes and a
finite-time isolation bound showing that the size and time limits need not
commute.

**Finite iid monotonicity.** On every torus with W·H ≤ 16, the jam fraction among n-car
configurations is nondecreasing in n. So q(p) = P_p(J) is nondecreasing in p, exactly, by a
Bernstein-coefficient certificate. Each difference b_{n+1} − b_n equals (jam-creating minus
jam-destroying single-car additions)/(number of pairs), so configurationwise non-monotonicity
is outweighed level by level. See the
[finite iid monotonicity note](research/2026-11-18-finite-iid-monotonicity.md). The fixed-count
fraction is *not* monotone in general: exactly, b₇ < b₆ on 2×11, 2×12 and 2×14, while monotonicity
of q itself is open there. This settles nothing asymptotically.

## 9. Next targets

The [dated open questions and proof roadmap](research/2026-11-18-open-questions-and-proof-roadmap.md)
updates this list after the TRAIN and lane-invariant merges. It records PR #7's
pending G1/G2 and coset proofs, PR #12's CLASSIC sparse-flow blueprint, the new
TRAIN periodic-family argument, and the remaining probability, projection and
verification questions. Its references include the full [HBK] v2 study and
distinguish its free-state characterization from an iid attraction theorem.

1. **Continue the CLASSIC Lean proof layer.** G0 and the concrete recurrent witnesses have
   kernel-checked coverage; the separate TRAIN threshold T is fully proved. Complete
   extraction of a simple CLASSIC blocker cycle and its torus
   winding, the all-count constructions of G1/G2, the coset identity G = ker φ, and the
   rigidity/optimization implications of R/F. See the precise [coverage register](../formal/README.md).
2. **Control formation of blocking loops under μ_p.** Section 8 gives the initial counting
   bound and explains the missing dynamical estimate. Do not treat a finite-time simulation
   or an iid count at time zero as an eventual-probability bound.
3. **Literature and novelty.** The Austin–Benjamini rule correspondence is resolved (§5b).
   Still open: search for the complete rectangular formula; read the full text of [HBK]; and
   formalise the Prop 1 transfer of §2. The 2/3 value and the gcd obstruction already have prior
   literature.
4. **Why is un-jamming trivial on tori with ≤ 6 cells?** Is there a structural reason (§4)?
5. Extend the exhaustive tables to 4×5 (3²⁰ ≈ 3.5·10⁹ states). That needs a symmetry quotient
   (translations × species-preserving symmetries).

## References checked on 2026-11-18

- [BML] O. Biham, A. A. Middleton, D. Levine, *Self Organization and a Dynamical Transition
  in Traffic Flow Models*, Physical Review A 46 (1992), R6124–R6127. Model I, pp. 2–3;
  finite-size uncertainty, pp. 4–5; extremal observation, footnote [7].
- [AHM] O. Angel, A. E. Holroyd, J. B. Martin, *The Jammed Phase of the
  Biham–Middleton–Levine Traffic Model*, Electronic Communications in Probability 10
  (2005), 167–178. Theorems 1–2. DOI: 10.1214/ECP.v10-1148.
- [AB] T. D. Austin, I. Benjamini, *For what number of cars must self organization occur
  in the Biham–Middleton–Levine traffic model from any possible starting configuration?*,
  arXiv:math/0607759v3 (2006). Read the movement rules together with Propositions 1 and 6.
- [DS] R. M. D'Souza, *Coexisting phases and lattice dependence of a cellular automaton
  model for traffic flow*, Physical Review E 71 (2005), 066112. DOI: 10.1103/PhysRevE.71.066112.
- [YT] M. V. Yashina, A. G. Tatashev, *Necessary condition for self-organization in the
  BML model with stochastic direction choice*, arXiv:2311.17120 (2023), Theorem 1 for q=0.
- [HBK] G. Hertzberg Rabinovich, O. Biham, E. Katzav, *Structure and dynamics in the
  low-density phase of a two-dimensional cellular automaton model of traffic flow*,
  arXiv:2601.01180 (2026). Abstract only.

[BML]: https://arxiv.org/pdf/cond-mat/9206001
[AHM]: https://arxiv.org/pdf/math/0504001
[AB]: https://arxiv.org/pdf/math/0607759
[DS]: https://doi.org/10.1103/PhysRevE.71.066112
[YT]: https://arxiv.org/pdf/2311.17120
[HBK]: https://arxiv.org/abs/2601.01180
