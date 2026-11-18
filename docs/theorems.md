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
| [Austin–Benjamini][AB], arXiv:math/0607759v3 (2006), Proposition 1 | States eventual speed one below N/2 cars. **Model correspondence is unresolved:** its written queue-movement rule and Proposition 6's minimum frozen count 2N do not match this unrestricted synchronous kernel, where a full E row is frozen at N cars. We do not import its statements as verified theorems of this kernel. |
| [D'Souza][DS], *Phys. Rev. E* 71 (2005), 066112 | Numerical stable intermediate phases and dependence on lattice aspect ratio. |
| [Yashina–Tatashev][YT], arXiv:2311.17120 (2023), Theorem 1 | For deterministic fixed directions and both species present, perpetual free motion requires gcd(W,H) ≥ 3; this overlaps a consequence of Lemma R. |

The AHM paper starts with the opposite first species; interchanging coordinates and species
gives the same iid law and the same fixation statement for our phase convention.

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

## 6. Extremal existence diagram (every finite torus)

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

## 9. Next targets

1. **Continue the Lean proof layer.** G0 and the concrete recurrent witnesses now have
   kernel-checked coverage. Complete extraction of a simple blocker cycle and its torus
   winding, the all-count constructions of G1/G2, the coset identity G = ker φ, and the
   rigidity/optimization implications of R/F. See the precise [coverage register](../formal/README.md).
2. **Control formation of blocking loops under μ_p.** Section 8 gives the initial counting
   bound and explains the missing dynamical estimate. Do not treat a finite-time simulation
   or an iid count at time zero as an eventual-probability bound.
3. **Reconcile literature semantics and novelty.** Resolve the Austin–Benjamini update-rule
   correspondence and search for the complete rectangular formula. The 2/3 value and the
   gcd obstruction already have prior literature; the stronger non-monotonicity witness
   above closes the earlier local example gap.
4. Extend the exhaustive tables to 4×5 (3²⁰ ≈ 3.5·10⁹ states). That needs a symmetry quotient
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

[BML]: https://arxiv.org/pdf/cond-mat/9206001
[AHM]: https://arxiv.org/pdf/math/0504001
[AB]: https://arxiv.org/pdf/math/0607759
[DS]: https://doi.org/10.1103/PhysRevE.71.066112
[YT]: https://arxiv.org/pdf/2311.17120
