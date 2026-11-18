# Finite iid monotonicity of the jam probability

**Research note — 18 November 2026.** The [roadmap](2026-11-18-open-questions-and-proof-roadmap.md#52-questions-that-remain)
asks whether the iid-averaged jam probability q_L(p) is monotone in the density p. The
[probability note](2026-11-18-probabilistic-gridlock-bounds.md#6-non-monotonicity-configurations-and-probabilities-are-different)
disproves monotonicity configuration by configuration, and for the mixed-cycle event M. It
leaves q_L itself open. This note settles the finite-size question exactly for every torus
with W·H ≤ 16 and reports Monte Carlo evidence beyond that. It makes no asymptotic claim and
no novelty claim.

CLASSIC rule throughout. The iid law μ_p puts E, N or nothing in each cell with probabilities
p/2, p/2 and 1 − p. J is eventual nonempty gridlock; F is eventual free flow.

## 1. Bernstein form

Let c_n be the number of n-car configurations in J, and b_n = c_n / (C(N,n)·2^n) the jam
fraction among n-car configurations (N = W·H). Then

\[
q(p)=\sum_n c_n\,(p/2)^n(1-p)^{N-n}=\sum_{n=0}^{N} b_n\binom Nn p^n(1-p)^{N-n},
\]

which is q in Bernstein form. Differentiating,

\[
q'(p)=N\sum_{n=0}^{N-1}(b_{n+1}-b_n)\binom{N-1}{n}p^n(1-p)^{N-1-n}.
\]

**Certificate.** If b is nondecreasing in n, every Bernstein coefficient of q′ is ≥ 0, so
q is nondecreasing on [0, 1]. The converse fails in general: q can increase while b dips.
Monotonicity of b is therefore the stronger statement. It says that the jam probability
increases with the car count n, for a uniformly random configuration with n cars and fair
species.

## 2. An exact identity: creating versus destroying jams

Pick a uniform n-car configuration x, a uniform empty cell and a fair species, and let y be
x plus that car. Every (n+1)-car configuration arises from exactly n + 1 such triples, so y
is uniform among (n+1)-car configurations. Hence

\[
b_{n+1}-b_n=\frac{\#\{(x,y):x\notin J,\ y\in J\}-\#\{(x,y):x\in J,\ y\notin J\}}{\binom Nn 2^n\cdot 2(N-n)} .
\]

So b is nondecreasing exactly when, at every level n, single-car additions that **create** a
jam are at least as numerous as those that **destroy** one. §4 of
[theorems.md](../theorems.md#4-non-monotonicity) shows that destroying additions exist, even
ones that revive every original car. The identity measures how much creation outweighs them.

## 3. Theorem (finite, exact)

> On every torus with W·H ≤ 16 (all 50 ordered shapes), b_n is nondecreasing in n.
> Hence q(p) = P_p(J) is nondecreasing on [0, 1]. The same holds for the event
> "never reaches free flow" (jam or intermediate recurrent motion).

*Evidence.* This is a finite enumeration, not a prose proof.
- The classifier was rerun on every state of every one of the 50 shapes, 298,822,278
  configurations in all. The per-n jam counts reproduce `data/exhaustive.json` exactly,
  including the 10–16-cell records that the
  [formal register](../../formal/README.md#finite-evidence-scopes) had marked as not rerun.
- The creating and destroying addition counts per level are in `data/jam-additions.json`.
  The identity of §2 holds exactly at every level of every shape.
- `tests/test_iid.py` checks the Bernstein form and q′, the certificate for J and for "not F",
  and the identity, all in exact rational arithmetic.

**Margins.** Creation dominates comfortably on squares. On 4×4, the largest ratio of
destroying to creating additions at any level is about 0.31 (n = 6). Thin tori come closest:
the extreme is 2×8 at n = 4, with 9,552 destroying against 11,776 creating additions (ratio
0.81). Shapes 1×n are degenerate: their jams are a single full lane, so destroying additions
never occur.

The tests check the ratio ≤ 1 on every shape and level. The quoted extremes come from
`data/jam-additions.json`.

## 4. Beyond 16 cells: Monte Carlo (evidence only)

_Pending: filled in from the paired estimator in §2 (random x and a random addition), with
jam detected as reaching a fixed point within T steps and rechecked at 2T._

## 5. What this does and does not show

- It answers the roadmap's monotonicity question for these finite sizes only. Nothing here
  implies monotonicity of q_L for large L, or the existence of a threshold.
- Configurationwise non-monotonicity (§4 of theorems.md, and the 13→14-car square
  counterexample in the probability note) is fully compatible with monotone averages. The
  identity of §2 is the bookkeeping that reconciles the two.
- The mixed-cycle probability m_3(p) decreases near p = 1 (probability note, §6), while q_3
  is increasing. The difference is the full-lane event R, which is in J but not in M.
- A proof strategy suggested by §2: show that jam-creating additions dominate
  jam-destroying ones level by level, for instance with an injection from destroying
  additions into creating ones. No such injection is known. Since the margin reaches 0.81 on
  2×8, it cannot be a crude one.
