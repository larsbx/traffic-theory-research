# When does BML gridlock switch? — what is proved here, and what stays open

**Model.** The torus is 𝕋 = ℤ_W × ℤ_H. A configuration is s : 𝕋 → {·, E, N}. One step is
an **E half-step** followed by an **N half-step**:

- E half-step: every E car whose east cell (x+1, y) is empty moves into it, all at once;
- N half-step: the same for N cars and their north cell (x, y+1).

The step map f is deterministic and conserves n_E and n_N. Notation: n = n_E + n_N.

**Formalization status.** The [Lean and Quint layer](../formal/README.md) proves
G0's full-cycle fixed-point characterization using actual simultaneous updates
(`Traffic.fullStep_fixed_iff_frozen` and `Traffic.frozen_iff_targets`). It also
proves the winding arithmetic under an explicit modular-closure hypothesis.
G1, G2, Lemma R, and Theorem F below remain informal arguments and executable
checks; the current Lean layer does not prove those results or conservation.

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

This is **open**. What is proved in the literature:

| result | statement |
|---|---|
| Angel–Holroyd–Martin, *Electron. Comm. Probab.* 10 (2005) | on ℤ², for p sufficiently close to 1, every car moves only finitely often a.s. |
| Austin–Benjamini, arXiv:math/0607759 (2006) | on the N×N torus, fewer than N/2 cars always self-organise into free flow |
| D'Souza, *Phys. Rev. E* 71 (2005) | numerically, stable intermediate states exist |

These attributions are from memory and have not yet been re-checked against the papers.

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
asymptotic velocity. On square tori, Austin–Benjamini's free-flow result is stronger for n < N/2.
G1 is the exact threshold for gridlock *existence*, and it holds for every aspect ratio. ∎

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

The smallest witness (2×2) is a full E row plus one E car in the other row. That example is trivial:
the new car itself circulates. Finding witnesses in which the *original* cars' fate changes is an
open item.

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

I have not yet checked whether Theorem F already appears in the literature.

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

1. **Extend the formal layer** from G0 to G1, G2, Lemma R and F in Lean. The
   blocker-cycle existence/closure bridge and the coset lemma G = ker φ remain.
2. **Quantitative G1 under μ_p.** Bound P(a closed E/N blocking loop exists at time 0 or later).
   Loops need ≥ L cars on one monotone cycle, which suggests a first-moment/Peierls bound for small p.
   This is the gap that Austin–Benjamini closes only below N/2 cars.
3. **Non-trivial non-monotonicity witnesses**, where the added car's own motion is not the cause.
4. Extend the exhaustive tables to 4×5 (3²⁰ ≈ 3.5·10⁹ states). That needs a symmetry quotient
   (translations × species-preserving symmetries).
