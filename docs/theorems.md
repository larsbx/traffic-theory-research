# When does BML gridlock switch? — what is proved here, and what stays open

**Model.** The torus is 𝕋 = ℤ_W × ℤ_H. A configuration is s : 𝕋 → {·, E, N}. One step is
an **E half-step** followed by an **N half-step**:

- E half-step: every E car whose east cell (x+1, y) is empty moves into it, all at once;
- N half-step: the same for N cars and their north cell (x, y+1).

"Empty" means empty at the start of the half-step. This is the **classical rule** of Biham,
Middleton and Levine, also used by Angel–Holroyd–Martin: "every ↑ which currently has a 0
immediately to its North … moves into this space". Under this rule, a full ring of cars is frozen.

Austin–Benjamini use a different rule, the **train rule**: a maximal line of same-species cars
moves together if the cell ahead of its head is empty, so a full ring rotates. Results do not
transfer between the two rules automatically; §5b treats the train rule. Code: `bml.model.CLASSIC`
and `bml.model.TRAIN`.

The step map f is deterministic and conserves n_E and n_N. Notation: n = n_E + n_N.

Every orbit is eventually periodic, and its terminal cycle is one of three kinds:

| kind | definition |
|---|---|
| **gridlock** (JAM) | some car exists and no car moves on the cycle |
| **free flow** (FREE) | every car moves at every step |
| **intermediate** (MIXED) | anything else: mean velocity strictly between 0 and 1 |

## 0. The open problem, stated precisely

Let μ_p be the i.i.d. measure where a cell is E w.p. p/2, N w.p. p/2 and empty otherwise.

**Conjecture (BML 1992).** There is a p_c ∈ (0,1) such that
- P_{μ_p}(gridlock on the L×L torus) → 0 as L → ∞ for p < p_c;
- the same probability → 1 for p > p_c.

This is **open**. Austin–Benjamini also record that it may fail outright: there may be no
p_c ∈ (0,1) at all, with the switch p_c(N) drifting slowly to 0. What is proved
(checked against the papers on 2026-11-18):

| source | rule | statement |
|---|---|---|
| Angel–Holroyd–Martin, [*Electron. Comm. Probab.* 10 (2005) 167–178](https://arxiv.org/abs/math/0504001) | classical | **Thm 1:** on ℤ², there is p₁ < 1 such that for p ≥ p₁, a.s. no car moves infinitely often. **Thm 2:** the same holds a.a.s. on m×n tori with m, n → ∞ and m/n converging in (0, ∞). p₁ is not computed; Austin–Benjamini report that it comes out very close to 1. |
| Austin–Benjamini, [arXiv:math/0607759](https://arxiv.org/abs/math/0607759) (2006) | train | **Prop 1:** on N×N, fewer than N/2 cars always attain speed one. **Prop 6:** a stuck configuration of m cars exists ⟺ m ≥ 2N. **Prop 8:** n log n random cars of each colour a.a.s. never get stuck. **Q7** (open): for which N/2 ≤ m < 2N can speed stay below 1 forever? |
| D'Souza, [*Phys. Rev. E* 71, 066112 (2005)](https://arxiv.org/abs/cond-mat/0402351) | classical | numerical: intermediate phases coexist with free flow and jam; bifurcation points depend on lattice size and aspect ratio |

Below, the **worst-case** (deterministic) switch is settled exactly on every finite torus. It also
gives a structural obstruction (§4) to the most naive route to the probabilistic one.

## 1. Lemma G0 (gridlock = fixed point)

**Claim.** An orbit's terminal cycle has velocity 0 ⟺ the orbit reaches a fixed point. Moreover,

> s is fixed ⟺ every E car's east cell is occupied and every N car's north cell is occupied.

*Proof.*
1. (⇐ for the first claim) A fixed point has no moves.
2. (⇒) If no car moves on the cycle, then f = id on it, so the period is 1.
3. For the characterisation: if s is fixed, the E half-step moves nothing. That holds iff every
   E car is blocked in s. The N half-step then acts on s itself, and moves nothing iff every
   N car is blocked in s. ∎

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

*Corollary.* With n < min(W,H) cars no configuration ever gridlocks: every orbit has positive
asymptotic velocity. G1 is the exact threshold for gridlock *existence*, for every aspect ratio. ∎

*Comparison with Austin–Benjamini.*
- Their Prop 6 (stuck ⟺ m ≥ 2N) is for the train rule. Under the classical rule a full row is
  already a gridlock, so the threshold halves to N.
- Their Prop 1 proof (empty arcs of time-corrected diagonals) only uses two facts: cars move at most
  one diagonal per step, and a diagonal with an empty diagonal above it always releases a car.
  The second fact also holds under the classical rule. The E cars on it move first, unobstructed;
  if there are none, every N car moves.
- So **Prop 1 transfers to the classical rule**: m < N/2 ⇒ speed one, which is stronger than this
  corollary on square tori. This transfer is our derivation; random tests up to 14×14 under both
  rules agree (`tests/test_train_rule.py`).

## 3. Theorem G2 (no forced gridlock below full density)

**Claim.** If WH ≥ 2 and 0 ≤ n < WH, some n-car configuration never gridlocks.

*Proof.* Say W ≥ 2; otherwise swap the roles of E/rows and N/columns.

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

**Trivial vs genuine.** In the smallest witness (2×2: a full E row plus one E car) only the new car
circulates. Call a pair (x, y = x + car) *genuine* if some original car of x moves infinitely often
in y. Tracking car identities (`bml.nonmonotone`):

| torus | 2×2, 2×3, 3×2, 3×3 | 2×4 | 2×5 | 3×4 | 4×3 |
|---|---|---|---|---|---|
| genuine un-jamming pairs | **0** | 24 | 460 | 17 952 | 18 108 |

On 3×4 (rows printed north to south, `>` = E, `^` = N), one added car keeps **all seven**
original cars moving forever, cars that all freeze without it:

```
x (freezes completely)      y = x + E car at (0,0) (all 8 cars move forever)
^^>.                        ^^>.
>>.^                        >>.^
...>                        >..>
```

(Pinned in `tests/test_nonmonotone.py`.)

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
   runs do the rest.
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

*Prior art (partial check, 2026-11-18).*
- Hertzberg Rabinovich–Biham–Katzav ([arXiv:2601.01180](https://arxiv.org/abs/2601.01180), square
  lattices) characterise free-flowing periodic states as the zero set of a distance
  D = D∥ + D⊥, with D∥ for same-type and D⊥ for cross-type interactions. That is likely
  equivalent to Lemma R, but only the abstract was checked.
- Neither that abstract nor Benjamini–Gurel-Gurevich–Izkovsky
  ([arXiv:math/0703201](https://arxiv.org/abs/math/0703201)) mentions a maximal free-flow density,
  the 2/3 limit, or the gcd(W, H) dependence. Theorem F is not claimed as novel.

## 5b. The train rule: Austin–Benjamini Prop 6 on rectangles

**Theorem T.** Under the train rule on W×H with W, H ≥ 2, a stuck configuration of n cars exists
⟺ W + H ≤ n ≤ WH.

*Proof of ≥* (their argument, verbatim for rectangles). Suppose s is stuck and n ≥ 1.

1. A column with N cars but no E car would release its N cars: either a line ends at a hole, or the
   column is full and rotates. So every column with a car contains an E car.
2. If some column x had no E car, it would be empty by step 1. Then the E cars of column x−1 would
   move, so column x−1 has no E car either. Inducting leftwards, there are no E cars at all, and
   then no cars at all by step 1, contradicting n ≥ 1.
3. So every column has an E car, and symmetrically every row has an N car: n ≥ W + H.

*Construction.* Take the closed staircase of winding (1,1): from cell i, step east iff
i·W mod (W+H) < W. This gives exactly W east steps, spread so that each row gets ⌈W/H⌉ < W of them.
Mark a cell E if the path leaves it eastwards, N otherwise.
- Every E line ends at an N car, and every N line at an E car.
- No row is a full E ring and no column a full N ring.

So it is stuck with W + H cars. Then add blocked cars one at a time
(`extremal.train_stuck_with`, checked for all n and all 2 ≤ W, H ≤ 8; exhaustively ⟺ for WH ≤ 12). ∎

**Same question, two rules.** The least frozen car count is min(W, H) under the classical rule
(G1) and W + H under the train rule (T).

## 6. The worst-case phase diagram (exact, every finite torus)

| car count n | gridlock possible | gridlock forced | free flow possible |
|---|---|---|---|
| 0 < n < min(W,H) | no (G1) | no | yes iff n ≤ n_free |
| min(W,H) ≤ n ≤ n_free | yes | no | yes |
| n_free < n < WH | yes | no (G2) | no (F); MIXED or JAM only |
| n = WH | yes | yes | no |

As a density on L×L, the gridlock-existence threshold is 1/L → 0 and the free-flow-existence
threshold → 2/3. Neither forced gridlock nor forced flow occurs strictly inside (0, 1). So the BML
switch is a purely *typical-case* phenomenon, and any proof of p_c must be genuinely probabilistic.

## 7. Empirical context (not a proof)

`python -m bml.montecarlo 32 4000` (32 samples per p, μ_p, 4000 steps):

- the jammed fraction rises from 0.03 at p = 0.400 to 0.81 at p = 0.450;
- the mean velocity drops from 0.76 to 0.09 over the same range.

The output is in `data/montecarlo_L32_T4000.txt`. Finite-size estimates of the switch drift with L
and T, so this does not estimate p_c.

## 8. Next targets

1. **Formalise** G0, G1, G2, Lemma R, F and T in Lean. The blocker-cycle argument and the
   coset lemma G = ker φ are the substance.
2. **Quantitative G1 under μ_p.** Bound P(a closed E/N blocking loop exists at time 0 or later).
   Loops need ≥ L cars on one monotone cycle, which suggests a first-moment/Peierls bound for small p.
   Austin–Benjamini's Prop 8 is the train-rule template; the classical analogue is weaker, because a
   single full line suffices to freeze.
3. **Austin–Benjamini Q7 under the classical rule**: for which N/2 ≤ m can speed stay below 1 forever?
   The exhaustive tables already answer this for WH ≤ 16 (`n_mixed`, `n_jam_min`).
4. **Why are tori with WH ≤ 6 trivially non-monotone?** Is there a structural reason, or are they
   just too small?
5. Extend the exhaustive tables to 4×5 (3²⁰ ≈ 3.5·10⁹ states). That needs a symmetry quotient
   (translations × species-preserving symmetries).
