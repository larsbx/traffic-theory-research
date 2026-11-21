# The jam probability is not monotone on thin tori

**Research note — 21 November 2026. Theorem with exact certificates; no novelty claim.**

The [finite iid monotonicity note](2026-11-18-finite-iid-monotonicity.md) proves that the iid
jam probability q(p) = P_p(J) is strictly increasing in p on every torus with W·H ≤ 22, on every
24-cell shape and on 5×5. It leaves open whether this holds on every finite torus. It does not:

> **Theorem M.** For every W ≥ 24, the iid jam probability q of the CLASSIC 2×W torus (and of
> the W×2 torus) is not monotone on [0, 1]. Some p₁ < p₂ have q(p₁) > q(p₂).

The cause is a rigidity of thin tori. On a torus two cells high, a jam with fewer than W cars
needs a column holding two north cars, a **plug**. Plugs can neither form nor dissolve. Every
other north car must be caught by a queue reaching back from a plug, and long queues are
improbable. So q rises to about e⁻²/W near p = 2/W, then falls exponentially in W at moderate p,
and rises again only near p = 1.

Throughout: CLASSIC rule, rows y ∈ {0, 1}, columns x ∈ ℤ_W. E cars move (x, y) → (x+1, y), and
N cars move (x, y) → (x, 1−y). The iid law μ_p puts nothing, E or N in each cell with
probabilities 1 − p, p/2 and p/2. J is eventual nonempty gridlock.

## 1. Structure

A column is a **plug** if both its cells hold N cars, **lone** if it holds exactly one N car, and
**open** otherwise. The **gap** of a plug at column x₀ is the run of non-plug columns
x₀ − 1, x₀ − 2, … up to the next plug to the west; a column x₀ − d of the gap has **distance**
d. For a gap, E_gap is its number of E cars and d_max the largest distance of a lone column in
it (0 if there is none). A configuration satisfies the **gap condition** if it has a plug and
E_gap ≥ d_max in every gap.

**Lemma 1 (invariants).** E cars keep their row and N cars their column. So the N count of every
column is invariant, and with it the set of plug columns. The cars of a plug never move, and no E
car ever enters a plug column, so every E car stays in its row and in its gap.

*Proof.* The first sentence is the update rule. A plug's two N cars each target the other's
cell, which stays occupied. An E car could enter a plug column only into an occupied cell. ∎

**Lemma 2 (blocking cycles).** In a fixed point every car has an occupied forward cell (G0).
Following each car to the car ahead of it defines a map on a finite set, so every forward orbit
ends in a cycle. A simple cycle with a east steps and b north steps has a ≡ 0 (mod W),
b ≡ 0 (mod 2), and a + b cars. If a = 0, the cycle lies in one two-cell column, so b = 2 and the
column is a plug. Otherwise it has at least W cars. **So in a fixed point with fewer than W cars
every blocking cycle is a plug.** ∎

**Lemma 3 (necessity).** If a configuration with n < W cars jams, it satisfies the gap condition.

*Proof.* Let y be the nonempty fixed point it reaches.
1. **There is a plug.** By Lemma 2, y has a plug, and by Lemma 1 the initial configuration has
   the same plug columns, hence the same gaps.
2. **The chain from the farthest lone column.** Take a gap with d = d_max ≥ 1, attained at the
   lone column c = x₀ − d. In y the lone N car of c is blocked, so the other cell of c holds a
   car, which is an E car because c holds one N car. Follow the orbit of that E car under the
   blocker map. An east step advances one column; a north step stays in its column. The orbit
   ends in a cycle, which is a plug (Lemma 2), and the first plug column east of c is x₀. So the
   orbit has a car in every column c, c+1, …, x₀ − 1.
3. **Counting the cars there.** Every lone column of the gap lies in this range. Its N car is
   blocked in y, so it holds two cars. The range therefore holds at least d + ℓ cars of y, where
   ℓ is the number of lone columns of the gap.
4. **Conclusion.** These cars lie in the gap: by Lemma 1 they are the gap's E cars and its ℓ lone
   N cars. So E_gap + ℓ ≥ d + ℓ. ∎

**Lemma 4 (sufficiency).** A configuration with a plug and no lone column jams.

*Proof.* All N cars are in plugs and never move. In each row, every gap is a path of cells
ending at a permanently occupied plug cell. E cars move only forward along their path, so the
sum of their positions measured from the path starts rises with every move and is bounded.
Finitely many moves occur. Afterwards nothing moves, which is a nonempty fixed point. ∎

All four lemmas use only the fixed-point structure, the invariants and a potential argument. None
depends on which species moves first. With axes and species exchanged they hold on W×2, and
μ_p is symmetric in the species, so everything below holds for W×2 as well.
`tests/test_thin.py` checks Lemmas 3 and 4:
- on every state of 2×3, 2×4, 2×5 and their transposes;
- on 12,000 random sparse states of 2×9, 2×14 and their transposes.

## 2. Exact bounds

**Theorem A.** For every W ≥ 3 and p ∈ [0, 1],

\[
L_W(p)=\Bigl(1-p+\tfrac{p^2}{2}\Bigr)^{W}-\Bigl(1-\tfrac p2\Bigr)^{2W}\;\le\;q_W(p)\;\le\;
P(\mathrm{Bin}(2W,p)\ge W)+\Gamma_W(p)=U_W(p),
\]

where Γ_W(p) = μ_p(gap condition).

*Proof.* Under μ_p the columns are iid: plug with probability a = (p/2)², N-free with
probability c = (1 − p/2)². By Lemma 4, q is at least the probability that every column is a
plug or N-free, minus the probability that all are N-free, which is (a + c)^W − c^W. By Lemma 3,
q ≤ P(n ≥ W) + μ_p(gap condition). ∎

**Computing Γ.** Gap contents are iid columns conditioned to be non-plug, so Γ is a renewal sum:
- **Gap probabilities.** G(g) is the probability that g iid non-plug columns satisfy
  E ≥ d_max. A dynamic programme over (E so far, d_max so far) computes it. G does not depend on
  W.
- **Blocks.** With blocks b_l = a·G(l−1) (a plug and its gap), the linear sequences satisfy
  c₀ = 1 and c_m = Σ_l b_l c_{m−l}.
- **Cyclic sum.** Counting the block that covers column 0 gives Γ_W = Σ_{l=1}^{W} l·b_l·c_{W−l}.

In `bml.thin` all of this is exact integer arithmetic over the common denominator (2·den p)^{2W}.
`tests/test_thin.py` checks:
- L_W and Γ_W against brute-force enumeration of every state on 2×3, 2×4 and 2×5;
- G against enumeration of gap contents;
- L ≤ q ≤ U against the exact q of all 18 thin shapes in the exhaustive tables (2×3 to 12×2).

The bounds are tight at low density and loose at moderate density. Monte Carlo estimates from
`bml/native/thin_mc.c` (exact Floyd classification, 4·10⁶ samples):

| torus | p | L_W(p) | q (Monte Carlo) | U_W(p) |
|---|---|---|---|---|
| 2×24 | 0.085 | 0.00602 | 0.00684 | 0.00717 |
| 2×24 | 0.245 | 0.00111 | 0.00349 | 0.00583 |
| 2×30 | 0.068 | 0.00475 | 0.00529 | 0.00547 |
| 2×30 | 0.265 | 0.00020 | 0.00106 | 0.00237 |
| 2×50 | 0.040 | 0.00279 | 0.00298 | 0.00302 |
| 2×50 | 0.285 | 6.1·10⁻⁷ | 1.6·10⁻⁵ | 8.3·10⁻⁵ |

## 3. Proof of Theorem M

**24 ≤ W ≤ 79: exact certificates.** For each W, `data/thin-nonmonotone.json` stores rationals
p₁ < p₂ with L_W(p₁) > U_W(p₂), checked in exact arithmetic. Then q(p₁) ≥ L(p₁) > U(p₂) ≥ q(p₂).
- At W = 24: p₁ = 17/200, p₂ = 49/200, with L = 0.00602 against U = 0.00583.
- At W = 79: p₁ = 1/40, p₂ = 59/200, with L = 0.00175 against U = 4.8·10⁻⁷.

**W ≥ 80: one certificate for all.**

*Lower side.* Since 1 − p + p²/2 ≥ e^{−p} and ln(1 − x) ≤ −x − x²/2,

\[
L_W(2/W)\ \ge\ e^{-2}\bigl(1-e^{-1/W}\bigr)\ \ge\ e^{-2}\Bigl(\frac1W-\frac1{2W^2}\Bigr).
\]

*Renewal bound.* Let β(z) = Σ_{g≥0} a·G(g)·z^{g+1}. If β(z) < 1 for some z > 1, then
c_m ≤ z^{−m}/(1 − β(z)) for every m, because all terms are nonnegative and Σ c_m z^m = 1/(1 − β_W(z)) ≤ 1/(1 − β(z)). Hence

\[
\Gamma_W\le W c_W\le \frac{W z^{-W}}{1-\beta(z)} .
\]

*Bounding β.* For g ≥ K, use the exponential-moment bound: for θ ≥ 1, 1{E ≥ d} ≤ θ^{E−d}.
Summing over the position d of the farthest lone column factorises over columns and gives

\[
G(g)\le s^g+\frac{w_L}{w}\sum_{d=1}^{g} r^d s^{g-d},\qquad
b=1-p+\tfrac{p\theta}{2},\ s=b^2,\ w_L=pb,\ w=s+w_L,\ r=w/\theta ,
\]

which sums in closed form when sz < 1 and rz < 1. Take p₂ = 7/20, θ = 7/5 and z = 117/100. With
the first K = 60 terms of G exact and this tail, β(z) ≤ 0.7036 exactly.

*Combining.* By Chernoff, P(Bin(2W, p₂) ≥ W) ≤ x^W with x = 4p₂(1 − p₂). It suffices that

\[
W x^{W}+\frac{W^2 z^{-W}}{1-\beta(z)}\ <\ e^{-2}\Bigl(1-\frac1{2W}\Bigr).
\]

- **At W = 80** this holds exactly: 0.118 < 0.1345, with e⁻² bounded below by a rational from its
  series.
- **For W ≥ 80** the left side does not increase, since (1 + 1/W)x ≤ 1 and (1 + 1/W)² ≤ z, while
  the right side increases.
- **The order of the two densities** is right: 2/W < p₂.

So q(2/W) > q(7/20) for every W ≥ 80.

`scripts/thin_certificates.py` rechecks all 56 finite certificates and the asymptotic one in
about 3 seconds. The tests include negative controls: the bounds certify nothing at W = 23, and
the asymptotic inequality fails at W = 60.

## 4. Below 24, and what the curve looks like

At W ≤ 23 the two bounds do not separate. Monte Carlo (exact classification, 4·10⁶ samples per
point, `bml.native.thin_jam_count`) gives the shape of q there:

| torus | q(0.10) | q(0.20) | q(0.30) | q(0.40) | q(0.50) | largest drop on the grid |
|---|---|---|---|---|---|---|
| 2×12 | 0.01088 | 0.01844 | 0.02142 | 0.02499 | 0.03256 | none |
| 2×13 | 0.01078 | 0.01695 | 0.01843 | 0.02047 | 0.02660 | none |
| 2×14 | 0.01047 | 0.01517 | 0.01565 | 0.01684 | 0.02170 | none |
| 2×15 | 0.01025 | 0.01366 | 0.01339 | 0.01387 | 0.01732 | q(0.225) − q(0.350) = 6σ |
| 2×16 | 0.00990 | 0.01228 | 0.01125 | 0.01123 | 0.01390 | q(0.175) − q(0.350) = 18σ |
| 2×17 | 0.00969 | 0.01095 | 0.00950 | 0.00906 | 0.01128 | q(0.150) − q(0.350) = 31σ |
| 2×18 | 0.00925 | 0.00982 | 0.00796 | 0.00739 | 0.00907 | q(0.150) − q(0.400) = 45σ |
| 2×19 | 0.00895 | 0.00868 | 0.00666 | 0.00592 | 0.00724 | q(0.150) − q(0.400) = 59σ |
| 2×20 | 0.00846 | 0.00771 | 0.00556 | 0.00474 | 0.00564 | q(0.125) − q(0.400) = 72σ |
| 2×21 | 0.00808 | 0.00682 | 0.00460 | 0.00378 | 0.00452 | q(0.125) − q(0.400) = 83σ |
| 2×22 | 0.00776 | 0.00608 | 0.00383 | 0.00306 | 0.00359 | q(0.100) − q(0.425) = 92σ |
| 2×23 | 0.00736 | 0.00525 | 0.00318 | 0.00243 | 0.00281 | q(0.100) − q(0.400) = 100σ |

The grid is p = 0.05, 0.075, …, 0.6; σ is the combined standard error of the two estimates.
- **2×12 to 2×14:** no decrease on the grid. This agrees with the exact certificate on 2×12.
- **2×15:** a 6σ decrease, between p = 0.225 and 0.35.
- **2×16 to 2×23:** an unmistakable decrease.

So the smallest non-monotone 2×W torus is very likely 2×15 (30 cells). That is evidence, not a
proof: 3³⁰ states is beyond exhaustive classification, and the bounds of §2 are too loose there.
The data are `data/thin-monte-carlo.json` (`scripts/thin_sweep.py`, fixed seeds).

The mechanism is visible at fixed car count too. Exactly,
b_n ≥ Σ_k C(W,k)·C(2W−2k, n−2k)/(C(2W,n)·2ⁿ), the fraction of n-car configurations whose N cars
all sit in k ≥ 1 plugs. Its k = 1 term is C(n,2)/((2W−1)·2ⁿ), which decreases in n for n ≥ 4.
This is a plausible source of the b₆ > b₇ dips on 2×11, 2×12 and 2×14, but the lower bound alone
does not prove them.

## 5. What this does and does not show

- **Monotonicity fails for some finite tori.** Exact monotonicity of q holds on every torus
  checked, up to 25 cells,
  and fails on 2×W from 48 cells on. The smallest counterexample is not known; §4 suggests it is
  2×15.
- **The failure is thin-torus rigidity, not a density threshold.** On 2×W at fixed p < 1/2,
  q_W(p) → 0 exponentially as W grows (the renewal bound). Low-density jams there are single
  initial coincidences. Nothing here bears on squares, where blocking cycles can form
  dynamically, or on p₋ > 0.
- **Only Lemmas 1–4 and the bounds are proved in prose.** The certificates are exact computer
  arithmetic. The Lean obligations are blueprint B10.
