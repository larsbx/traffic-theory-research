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
the statements currently checked by Lean, the actual Quint replay bounds, and the
remaining formal obligations beyond the completed deterministic capacity theorems. A bounded table does not prove a universal statement.

The `BML` library supplies the finite-torus kernel, numerical species-count
conservation, the complete G1 and G2 exact-count theorems, the full F capacity
and exact-count constructions, and the strong non-monotonicity theorem below. Its G1 proof extracts
an actual simple occupied blocker cycle, proves torus winding, and bounds the
cycle length by the executable car count. Conservation then rules out a jam
at any future time below `min(W,H)` cars. Executable row/column prefix
constructions have proved counts at every `min(W,H) ≤ n ≤ WH`, completing
sufficiency and the equivalent existence theorem for orbits reaching a jam.
G2 supplies a configuration at every `n < WH` that never reaches a nonempty
jam. For positive n, a mixed single-species lane retains a car, a hole, and an
eligible mover under every iterate; n = 0 uses the empty fixed point.
Together with full-occupancy blocking, this proves that gridlock is forced
exactly at `n = WH` among feasible populations. The
[companion Traffic suite](../formal/traffic-layer.md) independently supplies the
fixed-point/blocking equivalence, Wang recoding, and staircase constructions.
Its finite-walk winding theorem assumes modular closure; the separate `BML`
proof does not require an unproved bridge between the two Lean libraries.
The geometric coset identity used by R is formalized on the actual cyclic
coordinates, with signed and bounded forward witnesses. Lemma R now connects
those witnesses to the actual traffic kernel: the static conditions are
equivalent to every car moving in every round from time zero. It also proves
a finite moving-window criterion and return after `lcm(W,H)` rounds. The
packing upper bound, maximizing constructions, and every smaller population
in F are also proved for the actual kernel. The same capacity characterizes
existence of eventual free flow by population conservation.

The `BML` and `Traffic` suites use **CLASSIC** old-state vacancy semantics.
The separate [`BML.Train` Lean and `Train.qnt` Quint layer](../formal/TRAIN.md)
implements TRAIN queue and full-ring movement. Its Lean proofs now include the
complete Theorem T in §5b, numeric conservation, and the distinction between
fixed occupancy and zero movement. A full single-species TRAIN ring rotates
while its occupancy is unchanged, so G0's fixed-point criterion cannot be
transferred to that rule. The additional 3×4 non-monotonicity witness remains
Python-only; the CLASSIC packing theorem F has its own complete Lean proof
and separately scoped finite construction checks.
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
| [Austin–Benjamini][AB], arXiv:math/0607759v3 (2006), Propositions 1, 6, 8 | Prop 1: eventual speed one below N/2 cars. Prop 6: a stuck configuration of m cars exists ⟺ m ≥ 2N. **Different update rule (resolved in §5b):** their written rule moves same-species queues together and rotates a full ring (the *train rule*, `bml.model.TRAIN`). That explains 2N against the CLASSIC kernel's N. Prop 6 is re-proved and extended to rectangles in §5b. The full TRAIN Prop 1 Lean proof is described in §5c. The separate CLASSIC proof is kernel-checked for positive rectangles (§2 and blueprint B7). |
| [Hertzberg Rabinovich–Biham–Katzav][HBK], arXiv:2601.01180v2 (2026); Phys. Rev. E 113, 014127 | Same CLASSIC half-steps (blocking read from the start of each half-step), square L×L tori, equal species densities. Free-flowing periodic (FFP) states are described by four features: no adjacent same-species pairs along their direction, single-species counter-diagonals, and an adjacent-diagonal condition. On squares (g = L) these are our Lemma R conditions. The paper **asserts** that D = D∥ + D⊥ vanishes exactly on FFP states, and that the densest FFP state has L²/3 cars per species when 3 ∣ L, i.e. total density 2/3. Its appendix **proves** only one-step invariance of D = 0. Convergence of random states to FFP below p_c, τ⊥ ∝ L for p ≲ 0.125, and the fit D⊥ ~ t^{−1.1} e^{−t/τ⊥} are numerical. It gives no attraction or basin theorem, no derived p_c, no gcd condition and no rectangles. Lemma R and Theorem F here prove the characterization and the capacity for every rectangle, in Lean. |
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

**Lean boundary.** G1 is complete for every positive W,H, including singleton
dimensions. `BML.jam_has_simple_blocker_cycle` and
`BML.jam_carCount_lower_bound` prove necessity. `BML.gridlockWith` constructs a
jam at each admissible exact count, with freezing and numerical count proved
separately in `AllCounts.lean`. `BML.jam_carCount_iff` assembles the exact
interval, and `BML.exists_eventual_jam_with_count_iff` proves the same interval
for the existence of an orbit reaching a jam. `BML.few_cars_never_jam` excludes
a jam at every iterate below the minimum. The positive-asymptotic-velocity
consequence via eventual periodicity remains outside the current Lean proof.

The Lean constructor anchors its full line at the last row or column and fills
a prefix of reverse row/column ranks. The rank bijections prove that exactly n
sites are occupied, including a partial final line. This construction differs
in ordering from `extremal.gridlock_with`; its actual compiled output is checked
against Python CLASSIC dynamics for every admissible count on W,H≤12, without
asserting equality between the two constructors.

*CLASSIC transfer of Austin–Benjamini Proposition 1.*

The paper's written rule is TRAIN, treated in §5c. The CLASSIC result B7–B7.6
is separately proved in Lean for all positive rectangles. If `2m ≤ g`,
where `g = gcd(W,H)`, all cars eventually move in every complete CLASSIC
round. In each finite prefix there are at most `g−2` blocks per original
car and at most `m(g−2)` rounds containing a block. The proof uses actual
two-phase transport, corrected diagonal classes, and empty pairs that
persist backwards. See [blueprint B7](../formal/blueprint.md#b7-classic-low-density-speed-one).

*Prior art and movement semantics.* [Kozlov–Tatashev–Yashina][KTY] is a 2023
preprint. Its Theorem 1 already includes the equality threshold on rectangular
tori of arbitrary dimension. Here `m` counts all particles; `q = 0` fixes their
types. Section 1 specifies ECA184 within each type, and §2 evaluates a type's
vacant destination after the earlier types have moved. With east first and
north second, these stated rules match the CLASSIC pre-phase vacancy test.
This is a source-level comparison; the Lean proofs derive movement directly
from the executable kernel and do not import the paper as an axiom.

The related published article by [Yashina–Tatashev][YT24], *Mathematical
Methods in the Applied Sciences* 47 (2024), 14341–14352, also states the
inclusive gcd threshold in its abstract. Its two-author journal citation
is distinct from the three-author KTY preprint. The preprint's theorem gives
finite expected stabilization time; the explicit blockage and lcm deadlines
below are proved within this Lean development, without a claim of priority.

B7.6 now proves the equality case, preserving the same bound `m(g−2)`:

- **Alternating state.** `corrected_alternating_of_no_emptyPair` uses exact
  finite-list saturation to prove alternating singleton occupied classes.
  `corrected_alternating_allMove` checks every car's actual movement; the
  singleton condition prevents an east car from filling a north target.
  `corrected_alternating_step` and
  `corrected_no_emptyPair_perpetual_allMove` prove preservation and all future
  rounds' movement.
- **The final blocked round.** An empty pair at time `T` leaves its first
  class vacant through `T+1`, even if the pair disappears. The positive-rank
  argument therefore counts the transition into alternation as well. No
  additional `+1` is needed in the `g−2` per-tag bound.
- **Elapsed time.** `low_density_speed_one_deadline` gives permanent movement
  by `lcm(W,H) * m * (g−2)` complete east-then-north rounds under `2m ≤ g`.
  The natural-number subtraction includes the empty board and `g = 2`
  single-car states, whose deadline is zero.
- **Finite controls.** The replay checks 75,716 inclusive sparse boards on
  16 ordered shapes, including 61,608 equality boards. Blocked prefixes
  on 2×2, 3×3 and 4×4 with one car above the admitted population prevent
  accidentally certifying states outside the theorem's hypotheses.

See the [B7.6 source and verification note](research/2026-11-21-classic-inclusive-sparse-flow.md)
for theorem interfaces, dependency changes, and the acceptance scope.

## 3. Theorem G2 (no forced gridlock below full density)

**Claim.** For every positive W,H and every 0 ≤ n < WH, some n-car configuration
never gridlocks. This includes n = 0 on the 1×1 torus.

*Proof.* If n = 0, use the empty configuration, which is not gridlock. Otherwise say W ≥ 2;
if not, swap the roles of E/rows and N/columns.

1. Use E cars only. Then the rows evolve independently, as one-lane rings.
2. Fill rows so that some row holds between 1 and W−1 cars. If n ≢ 0 (mod W), filling greedily
   leaves a partial row. If n ≡ 0 (mod W) and n > 0, then n ≤ WH − W, so an empty row exists;
   move one car into it.
3. A mixed ring has a car-to-hole boundary, so at least one car moves. Cars persist, and each
   filled hole leaves a hole at the moving car's source. Thus the row keeps both a car and a
   hole and never freezes. ∎

Hence the deterministic switch is *not* at any density below 1: every n < WH is unforced.

**Lean boundary.** G2 is complete, with the actual numerical count and an
unbounded-time conclusion. `BML.nonGridlockWith` fills a column-major prefix
with east cars when W ≥ 2, or a north-only prefix when W = 1.
`BML.nonGridlockWith_carCount` proves its exact population using rank
bijections. `BML.nonGridlockWith_never_jam` and
`BML.exists_never_jam_with_count` prove that no full-step iterate is `Jam`.
The proof in [`Lanes.lean`](../formal/lean/BML/Lanes.lean) preserves a mixed
row or column under the actual synchronous phases, then uses cyclic
reachability from [`Ring.lean`](../formal/lean/BML/Ring.lean) to find an
eligible mover at every time. The empty case is handled separately: the
empty fixed point is not a nonempty jam.

**Forced-gridlock boundary.** For positive W,H and a feasible population
`0 ≤ n ≤ WH`, [`BML.forced_eventual_jam_iff`](../formal/lean/BML/GridlockThresholds.lean)
proves

\[
\bigl(\forall s,\ |s|=n\ \Longrightarrow
  \exists t\in\mathbb{N},\ \operatorname{Jam}(f^t(s))\bigr)
\quad\Longleftrightarrow\quad n=WH.
\]

At full occupancy every target is occupied, so every configuration is already
a nonempty jam at time zero. Below full occupancy the G2 constructor disproves
the universal claim. The feasibility assumption is necessary: when n > WH,
there are no n-car configurations, making the universal statement vacuous.
On the 1×1 torus, n = 0 is the empty non-jam and n = 1 is already jammed under
CLASSIC. G2 proves absence of a nonempty jam, not that every car moves at every
step or that the orbit eventually reaches free flow.

The separate G2 trace gate is scoped to every positive W,H≤12, every `n < WH`,
and times `0 ≤ t ≤ 2 max(W,H)`. Its finite implementation comparisons are
separate from the all-time invariant proof; consult the source-bound run
receipt for completed acceptance at a given revision.

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

On 2×2, 2×3, 3×2 and 3×3, un-jamming is only ever the added car itself. The boundary is side
length, not cell count: 3×3 has 9 cells and only trivial pairs, while 2×4 (8 cells) already has
genuine ones. Theorem U below gives the complete classification.

**Theorem U (genuine un-jamming).** Call a pair (x, y = x + one car) *genuine* if x eventually
gridlocks, y never does, and some original car of x moves infinitely often in y. On the W×H
torus:

1. if min(W, H) = 1, adding a car never turns a gridlocking configuration into a
   non-gridlocking one;
2. if W, H ∈ {2, 3}, un-jamming pairs exist but none is genuine;
3. if min(W, H) ≥ 2 and max(W, H) ≥ 4, genuine pairs exist.

*Proof of 1.* Say H = 1. Every N car's north cell is itself, so it never moves, and nothing can
enter its cell.
- If x has an N car, y has the same permanent obstacle. The E cars of the single ring then pile
  up behind it, so y gridlocks.
- If x has no N car, x is a single-species ring. Such a ring gridlocks only when it is full, so
  no car can be added.

W = 1 is symmetric. (`tests/test_nonmonotone.py` also checks every addition on 1×n and n×1,
n ≤ 8.)

*Proof of 2.* This is a finite enumeration: the identity-tracking census above covers every
gridlocking x and every single-car addition on these four tori.

*Proof of 3 (gated column, W ≥ 4).* Use columns C₀, C₁, C₂ and C_{W−1}, which are distinct
because W ≥ 4. Let x be:
- C₀: N cars in rows 1…H−1, with a hole at row 0;
- C₁: a single N car at row 0;
- C₂: full N;
- C_{W−1}: full E;
- every other cell empty.

Let y be x plus an N car at (0, 0).

*y never gridlocks.* In y, C₀ and C₂ are full N rings, so their cars never move and nothing
enters them. E cars reach C₁ only from C₀, which never contains one. So C₁ holds only its
original N car and H − 1 ≥ 1 holes, and that car moves at every round forever.

*x gridlocks.*
1. Cars never change their lane of travel. E cars move only from C_{W−1} into C₀ and from C₀
   into C₁. Out of C₁ they are blocked forever by C₂, which stays full of N cars that never move.
   So each E car moves at most twice, and on the terminal cycle of x no E car moves.
2. Fix that cycle. Suppose C₁ held no E car on it. Then its N car would move at every round.
   - Every cell of C₁ would be empty at some east phase. So no E car of C₀ could stay blocked,
     and C₀ would hold no E car either.
   - C₀ would then be H − 1 N cars and one hole, and that hole passes every row. So no E car of
     C_{W−1} could stay blocked, and C_{W−1} would be empty.
   - All H E cars would then be in C₁, a contradiction. So C₁ holds an E car on the cycle.
3. If C₀ held no E car on the cycle, the same hole argument would empty C_{W−1}. Then C₁ would
   hold all H E cars plus its N car, which is H + 1 > H cells.
4. So both C₀ and C₁ contain a permanent E obstacle, and their N cars stop moving. In a ring
   with a permanent obstacle, a car moving forever would have to pass through it. C_{W−1}'s
   E cars and C₂ are stationary as well.
5. The cycle is therefore a nonempty fixed point: x gridlocks.

*Gated row, H ≥ 4.* Exchange rows with columns and E with N:
- R₀: E cars in columns 1…W−1, with a hole at column 0;
- R₁: a single E car at column 0;
- R₂: full E;
- R_{H−1}: full N.

y adds an E car at (0, 0). The same argument applies verbatim with the species swapped, and it
does not use the order of the two phases. ∎

**Lean classification.** `BML.Gated.genuine_unjamming_iff` proves the
dimension criterion using the CLASSIC kernel and actual tagged transport.
The singleton argument and both gated families are proved directly. The
small-torus exclusion uses exhaustive certificates checked by the Lean
kernel. [Formal proof guide](../formal/blueprint.md#b8-theorem-u-genuine-un-jamming-classification)

**Evidence.**
- `bml.nonmonotone.gated_witness` builds both families. `tests/test_nonmonotone.py` checks them
  exactly on every shape with sides 2–10 and max side ≥ 4: Floyd cycle detection for x and y,
  plus identity replay for the original mover.
- A random search additionally certified genuine witnesses on all 45 such shapes up to 8×8. On
  many of them every original car revives, for example all 20 on 6×6.

The gate needs four distinct lanes: the gate, the free lane, the blocker and the feeder. That
explains why the smallest genuine examples need a side of length 4. Case 2 rules out any other
mechanism on 3×3 by enumeration, not by a structural argument.

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

**Lean coverage: the coset identity and Lemma R are proved.** For
positive W,H, let `D = BML.diagonalStep W H`, which applies the actual
`cyclicNext` to x and `cyclicPrev` to y, and let `L = lcm(W,H)`.
`BML.diagonalShift_exists_iff` proves, for arbitrary torus points p,q,

\[
\exists t\in\mathbb{Z}:\ p+(t,-t)=q
\quad\Longleftrightarrow\quad \varphi(p)=\varphi(q).
\]

The signed translation is a proved action, and `BML.iterate_diagonalStep`
identifies its natural-time values with iteration of D. The origin form,
`BML.diagonal_kernel_iff`, is exactly `G = ker φ` as an equivalence of point
membership. The proof derives Bézout coefficients and the compatible signed
congruences in [`Congruence.lean`](../formal/lean/BML/Congruence.lean), then
connects them to the actual coordinates in
[`Cosets.lean`](../formal/lean/BML/Cosets.lean).

[`CosetTimes.lean`](../formal/lean/BML/CosetTimes.lean) reduces signed witnesses
modulo L and proves the equivalent forward-time statements

\[
\varphi(p)=\varphi(q)
\quad\Longleftrightarrow\quad
\exists\,0\le t<L:\ D^t(p)=q
\quad\Longleftrightarrow\quad
\exists\,1\le t\le L:\ D^t(p)=q.
\]

Starting at the actual east neighbor of p instead gives the class
`(φ(p)+1) mod g`, including g=1. These statements supply the two geometric
encounter classes and the nonnegative/positive time windows used in the prose
proof. D is an auxiliary action on positions, not `torusStep` on traffic
configurations. [`Rigid.lean`](../formal/lean/BML/Rigid.lean) supplies the
bridge: when every car moves in each preceding actual round, east occupancy
and north occupancy are precisely their respective coordinate translates.
North movement is evaluated after the east half-step.

[`FreeFlow.lean`](../formal/lean/BML/FreeFlow.lean) proves both directions
of Lemma R for every positive W,H, including singleton axes and the empty
state. Its `StaticFree` predicate is exactly conditions 1–3 above, with the
cross-species exclusions stated as φ(q)≠φ(e) and φ(q)≠(φ(e)+1) mod g.
For sufficiency, the static conditions imply movement in both phases and are
preserved by the actual full step. Induction gives movement forever. For
necessity, the bounded coset encounters rule out each forbidden pair under
the rigid-prefix theorem; the same-species conditions follow already at t=0.

The proof gives the finite criterion

\[
\operatorname{StaticFree}(s)
\quad\Longleftrightarrow\quad
\forall\,0\le t<L:\ \operatorname{AllMove}(f^t(s))
\quad\Longleftrightarrow\quad
\forall\,t\ge0:\ \operatorname{AllMove}(f^t(s)).
\]

`lemmaR_finite_lt` uses the first L rounds; `lemmaR_finite` also provides
the inclusive window t≤L. If a static condition fails, some round t<L has
a blocked car. If the conditions hold, `freeFlow_returns_lcm` proves
`f^L(s)=s`, and `freeFlow_periodic` proves repetition after L at every time.
The least configuration period may be smaller than L. This differs from
the auxiliary diagonal action on a single position, whose least period is L.

Perpetual free flow here starts at time zero. The separate theorem
`eventually_allMove_iff_reaches_staticFree` identifies eventual permanent
full movement with eventual entry into the static-free set. It supplies no
claim that every configuration reaches that set and no uniform entry-time
bound. The class packing, maximizing constructions, and complete attainable
population spectrum of F are now proved in `BML/FreeMaximum.lean` and its
supporting modules.

The separate coset gate exports successors, phase classes, and east translates
for all 6,084 positions on the 144 ordered rectangles with W,H≤12. Its declared
scope reconstructs a complete cycle from each position, totaling 283,526 orbit
visits, and checks each of the same-class and east-translated relations on
422,500 ordered pairs. These are finite coordinate checks, with 12 rejection
controls; source-bound receipts record successful runs. They do not enumerate
traffic configurations. Lemma R has its own kernel proof and separate finite
traffic acceptance checks.

The R gate, `scripts/check_freeflow.py`, compares actual Lean decisions of
`StaticFree` and `AllMove` and both phase traces on every initial state of
every ordered positive rectangle with WH≤9: 93,387 states on 23 rectangles,
covering 622,362 full transitions in their lcm windows. It uses NumPy phase
comparisons and an independent scalar orbit oracle that rejects blockage
from time zero. It also checks rigid moving prefixes, lcm closure of
static-free states, coverage, and corrupted-output controls. This is its
declared finite domain; source-bound receipts record which checks passed
at a given revision.

**Theorem F.** Let n_free(W,H) be the largest car count that admits free flow, and V(g) = ⌊(g + ⌊g/3⌋)/2⌋. Then

- for g = 1: n_free = max( H⌊W/2⌋, W⌊H/2⌋ );
- for g ≥ 2: n_free = (WH/g) · V(g).

Free flow exists for exactly the n with 0 ≤ n ≤ n_free.

*Proof of ≤.* If g=1, the phase map is constant, so Lemma R forbids mixed
species. Double counting adjacent pairs bounds each east-only row by ⌊W/2⌋
and each north-only column by ⌊H/2⌋.

Now let g≥2 and M=WH/g. Every phase fiber has M cells: east shift bijects
successive fibers, and the g equal fibers partition the torus. Let aᵢ,bᵢ be
the species counts in class i, and cᵢ=aᵢ+bᵢ. Same-species adjacency and the
shift bijections give

\[
c_i\le M,\qquad a_i+a_{i+1}\le M,\qquad b_i+b_{i+1}\le M.
\]

The cross-species conditions give aᵢ=0 or bᵢ=0, and aᵢ=0 or bᵢ₊₁=0.
These five constraints imply cᵢ+cᵢ₊₁+cᵢ₊₂≤2M. If aᵢ>0, the first two north
counts vanish. If aᵢ=aᵢ₊₁=0, the first two east counts vanish. In the remaining
case, aᵢ=0<aᵢ₊₁, the last two north counts vanish. In each case an adjacent
same-species cap and one total-class cap suffice.

If a class is empty, rotate it to the last position and write g=3q+r.
Group the first 3q entries into triples. The total is at most 2qM for r=0
or 1, and at most (2q+1)M for r=2, because the final entry is zero. This is
M⌊2g/3⌋. If no class is empty, any positive east count forces a positive east
count in the next class, so cyclic propagation forces a single species.
Summing adjacent caps gives 2n≤gM≤2M⌊2g/3⌋ for g≥2. This proves the upper bound.

*Construction.* For g≥2, fill phase classes according to `N E ·` triples
and `E ·` pairs. When g=3q, use q triples; when g=3q+2, use q triples and
one pair; when g=3q+1≥4, use q−1 triples and two pairs. Each pattern has
exactly ⌊2g/3⌋ occupied classes, every E class is followed by an empty class,
and every N class by an E class, including the cyclic seam. Thus Lemma R
holds and the total is M⌊2g/3⌋. For g=1, alternate cars along the direction
with larger capacity, leaving an unpaired last coordinate empty on odd lanes.
Deleting any subset of cars preserves all static conditions, giving every
smaller population. ∎

**Lean proof.** `staticFree_carCount_le_freeMax` proves the upper bound for
actual configurations. `maxFreeConfig` attains it, and `freeWith` retains
exactly n cars whenever n≤freeMax. The theorems
`exists_staticFree_with_count_iff`, `exists_perpetual_allMove_with_count_iff`,
and `exists_eventual_allMove_with_count_iff` prove the same population
spectrum in all three formulations. Eventual necessity uses actual car-count
conservation; sufficiency chooses a free board with transient zero. This does
not assert that every board below the maximum eventually becomes free.

The separate `scripts/check_free_max.py` acceptance gate evaluates the actual
Lean constructor for all 3,334 attainable-count cases on the 144 rectangles
with sides 1…12. Its complete lcm windows contain 146,348 transitions. It
checks both phase snapshots and move counts against independent scalar
updates, the exact formula and populations, static conditions, lcm closure,
complete coverage, and 22 rejection controls. Source-bound receipts identify
successful runs. The historical WH≤16 tables and independent max-plus DP
checks remain separate computational evidence.

On L×L: n_free = L · ⌊(L + ⌊L/3⌋)/2⌋, so the densest free flow has density → **2/3**, attained
exactly when 3 ∣ L (L = 3m gives V = 2m). For W, H coprime, free flow is
single-species, with density ≤ 1/2.

The formula simplifies to V(g) = ⌊2g/3⌋: write g = 3m+r for r ∈ {0,1,2}.
Thus for g ≥ 2 the maximal density is ⌊2g/3⌋/g, attaining 2/3 exactly when 3 ∣ g.
The g = 1 branch remains separate.

**Prior art.** The square-density value 2/3 is already stated in footnote [7] of
[BML 1992][BML]; it is not a novelty claim here. The mixed-species obstruction at g < 3
also appears in [Yashina–Tatashev, Theorem 1][YT]. Whether the complete rectangular floor
formula appears earlier remains unestablished.
- **Search of 2026-11-21:** general web searches for the maximal free-flow count on W×H tori
  in terms of gcd(W,H), and for the BML density bound 2/3.
- **Also read:** the Kozlov–Tatashev–Yashina line of work ([KTY], [YT]).
- **Found:** only the 2/3 square value, the gcd ≥ 3 obstruction for mixed free flow, and the
  m ≤ gcd/2 sufficient condition (B7 and B7.6). None of these sources states the complete
  floor formula (W·H/g)·⌊2g/3⌋.

A search can only show a statement was not found, not that it is new.

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

## 5c. The train rule: eventual speed one up to N/2 on squares

**Formal status:** the full theorem is kernel-checked in
[`Train/SpeedOne.lean`](../formal/lean/Train/SpeedOne.lean), using the proved
cyclic argument, actual diagonal dynamics, and numerical movement
characterization. Its public statement assumes only the square domain,
positive side length, and the population bound `2m ≤ N`.

**Proposition S (Austin–Benjamini Proposition 1, with the boundary case).** Let N>0 and let s be any
TRAIN configuration on an N×N torus. If `2 * population s ≤ N`, then

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
theorem names are `BML.Train.half_square_eventually_fullSpeed` and
`BML.Train.half_square_moves_equal_population`; the strict `sparse_square_*`
statements of Proposition 1 are corollaries.

*Proof route.* [Austin–Benjamini, pp. 2–3][AB] uses corrected diagonals; the
formal argument works with adjacent empty pairs instead of maximal arcs.

1. Label the initial cars and track each through both phases. The corrected
   tag is `x+y−t mod N`, where t counts full cycles. A moving car keeps its tag;
   a blocked car moves one tag backwards. Transport covers every current car.
2. An occupied physical diagonal followed by an empty one releases at least
   one car in the next full cycle. If an east car is present, it can move;
   otherwise north cars can move because the east phase cannot fill their
   target diagonal from that source diagonal.
3. Suppose first that 2m<N. This guarantees two adjacent empty tags at every time. If
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

6. If 2m=N and some time T has no adjacent empty pair, counting saturates:
   an occupied tag with an occupied successor would leave a cover of all N
   tags by 2m−1 entries. So occupied and empty tags alternate at T. Release
   keeps each occupied tag occupied, so T+1 alternates too, and a car falling
   back one tag would create two adjacent occupied tags. Every car therefore
   keeps its tag from T onward. If no such T exists, steps 4–5 apply.

The generic cyclic argument is proved as
`BML.Train.Diagonals.half_eventual_stable`; `Train/DiagonalDynamics.lean`
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

The table concerns feasible populations `0 ≤ n ≤ WH`. “Gridlock forced” means
that every configuration at that count eventually reaches a nonempty jam.
The G1 existence interval and the G2/full-occupancy forced boundary are proved
in Lean, together with the exact free-flow formula F and its constructions
at every attainable population.

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
[finite iid monotonicity note](research/2026-11-18-finite-iid-monotonicity.md). Exhaustively for W·H ≤ 22, every 24-cell shape and 5×5, q(p) is strictly increasing. The fixed-count
fraction is *not* monotone in general: exactly, b₇ < b₆ on 2×11, 2×12 and 2×14. On 2×11 and 2×12, q itself is still strictly
increasing (exact certificate). This settles nothing asymptotically.

**Theorem M (thin-torus non-monotonicity).** For every W ≥ 24, q(p) is *not* monotone on the
2×W and W×2 tori. The argument has two parts:
- **Structure.** A jam with fewer than W long-axis cars needs a plug, a short line of two short-axis cars.
  Plugs never form or dissolve. Every lone short-axis car must be caught by a queue, so each gap
  between plugs needs at least as many long-axis cars as its farthest lone car's distance.
- **Bounds.** This gives exact bounds L_W ≤ q ≤ U_W. Exact certificates give L_W(p₁) > U_W(p₂)
  for 24 ≤ W ≤ 79, and a renewal bound covers all W ≥ 80.

See the [thin-torus note](research/2026-11-21-thin-torus-nonmonotonicity.md),
`bml.thin`, `data/thin-nonmonotone.json` and `scripts/thin_certificates.py`. Monte Carlo with
exact classification suggests that 2×15 (30 cells) is already non-monotone and 2×14 is not.
The smallest non-monotone torus is unknown; it has between 23 and 48 cells.

**Theorem P (no jammed phase on thin tori).** For every fixed p < 1, q_{2×W}(p) ≤ C·W·ρ^W with
ρ < 1, so the jam probability tends to 0 and the thin-torus critical density is p_c = 1.
- A blocking cycle other than a plug winds once around the torus and carries exactly W long-axis
  cars. That has probability ≤ (p(2−p))^W.
- With a plug present, the gap condition is necessary, and its probability decays by the renewal
  bound.

Explicit rates for p ≤ 49/50 are certified exactly. This contrasts with [AHM], where squares jam
with probability → 1 at high density. See §5 of the
[thin-torus note](research/2026-11-21-thin-torus-nonmonotonicity.md).

## 9. Next targets

The [dated open questions and proof roadmap](research/2026-11-18-open-questions-and-proof-roadmap.md)
records the state after the TRAIN and lane-invariant merges, including PR #7's
G1/G2 and coset work, PR #12's CLASSIC sparse-flow blueprint, and the remaining
probability, projection, and verification questions. Its references include
the full [HBK] v2 study and distinguish its free-state characterization from an
iid attraction theorem. The coverage below describes this branch's compiled results.

1. **Continue the CLASSIC Lean proof layer.** G0, numerical conservation, complete G1/G2,
   the feasible-population forced-gridlock boundary, the geometric coset identity B2,
   the actual-kernel free-flow characterization R, the complete F capacity and
   exact-count constructions, and the concrete recurrent witnesses have kernel-checked
   coverage. R includes a finite lcm-window criterion and lcm return; F includes
   static, perpetual, and eventual existence spectra. The separate TRAIN threshold T
   and sparse-square speed-one theorem are fully proved. CLASSIC B7 proves eventual
   full movement and bounds blocked rounds under `2m ≤ gcd(W,H)`. B7.6 now
   formalizes the inclusive case from the actual kernel (§2); the threshold
   is prior art in [KTY].
   See the precise [coverage register](../formal/README.md).
2. **Control formation of blocking loops under μ_p.** Section 8 gives the initial counting
   bound and explains the missing dynamical estimate. Do not treat a finite-time simulation
   or an iid count at time zero as an eventual-probability bound.
   The [late-formation measurements](research/2026-11-21-late-formation.md) show the size of
   the gap. At p ≤ 0.5 no mixed cycle formed within log L rounds (about 1,380 formations,
   L ≤ 128), and formation takes order L rounds or longer near the threshold. At p ≥ 0.9 it is
   logarithmic, the same order as the proven guarded-barrier delay. Evidence only.

3. **Literature and novelty.** The Austin–Benjamini rule correspondence is resolved (§5b).
   The 2/3 value and the gcd obstruction have prior literature, and the sparse speed-one bound
   is prior art in [KTY] (m ≤ gcd/2). The search for the complete rectangular capacity formula
   (§5) found no earlier statement. The scope of [HBK] is recorded in §0: an asserted
   square-lattice FFP characterization and L²/3 capacity, with numerical relaxation results.
   A **systematic web and arXiv search on 2026-11-28** covered:
   - thin (2×n) and narrow tori;
   - monotonicity of the jam probability in density;
   - rectangular and gcd-dependent free-flow capacity;
   - rigorous low-density results.

   It found no earlier statement of Theorem F's rectangular formula, Theorem M, Theorem P, or any
   result specific to two-row tori.
   - **Rigorous work found:** [AHM] (jamming near p = 1), [AB] (fewer than L/2 cars),
     [BGI] (a single-junction variant, with a phase transition) and [KTY]/[YT].
   - **Numerical and physical studies:** [BML], [DS], [LD] (periodic intermediate states on
     coprime rectangles) and [OM] (honeycomb lattice), which prove none of these statements.

   This is a search outcome, not a novelty claim. Still open: a library-database
   (MathSciNet/zbMATH) check.
4. ~~Why is un-jamming trivial on small tori?~~ Resolved by Theorem U (§4): genuine un-jamming
   exists iff min(W,H) ≥ 2 and max(W,H) ≥ 4. Lean formalisation: blueprint B8.
5. ~~Extend the exhaustive tables to 4×5.~~ Done for every shape with W·H ≤ 22, including 4×5
   in 14 s, and for all 24-cell shapes and 5×5 (`data/exhaustive-24-25.json`). The tool is `bml/native/classify.c`, which uses a translation quotient, bitmask
   dynamics and Floyd cycle detection; the tables are in `data/exhaustive-17-22.json`. G1 and F
   hold on all of them. Reflections are not symmetries, because they reverse the flow.

## References checked on 2026-11-18

- [KTY] V. V. Kozlov, A. G. Tatashev, M. V. Yashina, *Sufficient Loading Conditions for Self-organization in the n-dimensional Version of BML Model with Stochastic Direction Choice*, arXiv:2310.02291v1 (2023), preprint. Theorem 1 includes `m ≤ d/2`; §§1–2 specify ECA184 and ordered type phases, with fixed types at `q = 0`. Checked 2026-11-21 against the PDF.
- [YT24] M. V. Yashina, A. G. Tatashev, *Loading conditions for self-organization in the BML model with stochastic direction choice*, Mathematical Methods in the Applied Sciences 47 (2024), 14341–14352. DOI: 10.1002/mma.10276. Publisher abstract and publication metadata checked 2026-11-21; full journal text was not available through the retrieval used.

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
- [BGI] I. Benjamini, O. Gurel-Gurevich, R. Izkovsky, *The Biham–Middleton–Levine traffic
  model for a single junction*, arXiv:math/0703201 (2007). A single row and column with one
  shared cell; self-organization and a phase transition in that variant. Found 2026-11-28.
- [LD] N. J. Linesch, R. M. D'Souza, *Periodic states, local effects and coexistence in the BML
  traffic jam model*, Physica A 387 (2008), 6170–6176; arXiv:0709.3604. Exactly periodic intermediate states on coprime
  (Fibonacci) rectangles; numerical. Found 2026-11-28.
- [OM] L. E. Olmos, J. D. Muñoz, *Traffic gridlock on a honeycomb city*, arXiv:1610.07438
  (2016). BML on a honeycomb network; numerical, with a single percolation-like transition.
  Found 2026-11-28.
- [YT] M. V. Yashina, A. G. Tatashev, *Necessary condition for self-organization in the
  BML model with stochastic direction choice*, arXiv:2311.17120 (2023), Theorem 1 for q=0.
- [HBK] G. Hertzberg Rabinovich, O. Biham, E. Katzav, *Structure and dynamics in the
  low-density phase of a two-dimensional cellular automaton model of traffic flow*,
  arXiv:2601.01180v2 (2026); Phys. Rev. E 113, 014127 (2026). Full text (arXiv HTML v2) read
  2026-11-21: update rule Eqs. (2)–(3); FFP features §IV; distance Eqs. (6)–(13);
  Appendix B (one-step invariance of D = 0); Figs. 2–4 (relaxation fits).

[BML]: https://arxiv.org/pdf/cond-mat/9206001
[AHM]: https://arxiv.org/pdf/math/0504001
[AB]: https://arxiv.org/pdf/math/0607759
[DS]: https://doi.org/10.1103/PhysRevE.71.066112
[YT]: https://arxiv.org/pdf/2311.17120
[HBK]: https://arxiv.org/abs/2601.01180
[KTY]: https://arxiv.org/abs/2310.02291
[YT24]: https://doi.org/10.1002/mma.10276
[BGI]: https://arxiv.org/abs/math/0703201
[LD]: https://arxiv.org/abs/0709.3604
[OM]: https://arxiv.org/abs/1610.07438
