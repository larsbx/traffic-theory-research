# Finite iid monotonicity of the jam probability

**Research note — 18 November 2026.** The [roadmap](2026-11-18-open-questions-and-proof-roadmap.md#52-questions-that-remain)
asks whether the iid-averaged jam probability q_L(p) is monotone in the density p. The
[probability note](2026-11-18-probabilistic-gridlock-bounds.md#6-non-monotonicity-configurations-and-probabilities-are-different)
disproves monotonicity configuration by configuration, and for the mixed-cycle event M. It
leaves q_L itself open. This note settles the finite-size question exactly for every torus
with W·H ≤ 16 and for 2×9: q is nondecreasing there. It also shows exactly that the stronger
fixed-count statement fails on 2×11, 2×12 and 2×14. It makes no asymptotic claim and no novelty
claim.

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

> On every torus with W·H ≤ 16 (all 50 ordered shapes), and on 2×9 (18 cells), b_n is
> nondecreasing in n.
> Hence q(p) = P_p(J) is nondecreasing on [0, 1]. The same holds for the event
> "never reaches free flow" (jam or intermediate recurrent motion).

*Evidence.* This is a finite enumeration, not a prose proof.
- The classifier was rerun on every state of every one of the 50 shapes, 298,822,278
  configurations in all. The per-n jam counts reproduce `data/exhaustive.json` exactly,
  including the 10–16-cell records that the
  [formal register](../../formal/README.md#finite-evidence-scopes) had marked as not rerun.
- The creating and destroying addition counts per level are in `data/jam-additions.json`.
  The identity of §2 holds exactly at every level of every shape.
- 2×9 (3¹⁸ ≈ 3.9·10⁸ states, about 8 minutes) was classified exactly. Its per-level jam and
  intermediate counts are in `data/exhaustive-2x9.json`, and both fractions are nondecreasing.
  Thin tori are the closest cases at 16 cells (§3, Margins), so 2×9 is the most informative
  single extension that fits in memory.
- `tests/test_iid.py` checks the Bernstein form and q′, the certificate for J and for "not F",
  and the identity, all in exact rational arithmetic.

**Margins.** Creation dominates comfortably on squares. On 4×4, the largest ratio of
destroying to creating additions at any level is about 0.31 (n = 6). Thin tori come closest:
the extreme is 2×8 at n = 4, with 9,552 destroying against 11,776 creating additions (ratio
0.81). Shapes 1×n are degenerate: their jams are a single full lane, so destroying additions
never occur.

The tests check the ratio ≤ 1 on every shape and level. The quoted extremes come from
`data/jam-additions.json`.

## 4. Beyond 16 cells: the fraction monotonicity fails on thin tori

**Monte Carlo (evidence).** The paired estimator of §2 samples a uniform n-car configuration
x and a uniform single-car addition y. Jam is detected as reaching a fixed point within T
steps and rechecked at 2T; no sample changed between T and 2T. The results:
- **Squares and wide rectangles:** no significant negative difference. The smallest z-scores
  over all levels were 6×6: +2.65, 3×9: +0.38, and 5×5: −0.58 (1 creating against 2
  destroying additions).
- **Thin 2×W tori**, with 400k pairs per level: odd levels are comfortably positive, but even
  levels approach ties and then reverse.

| torus | n = 4 | n = 6 | n = 8 |
|---|---|---|---|
| 2×10 | +7.33 | +0.83 | +9.58 |
| 2×12 | +2.24 | **−2.85** | −0.20 |
| 2×14 | +0.61 | **−4.83** | **−3.65** |

(z-scores of creating minus destroying additions)

**Exact counterexample.** `bml.levels` computes a single level's jam count exactly. It uses
translation invariance, jam_n = (N/n)·#{jamming configurations with a car at cell 0}, and
classifies each configuration by Floyd cycle detection: a configuration jams iff the cycle its
orbit reaches is a fixed point. There is no time horizon. The counter reproduces the
exhaustive counts on 2×8, 3×4, 4×3 and 3×3 (`tests/test_iid.py`).

| torus | b₆ | b₇ | b₇ ≥ b₆? |
|---|---|---|---|
| 2×10 | 95/3264 ≈ 0.029105 | 7379/248064 ≈ 0.029746 | yes (levels 5–8 all nondecreasing) |
| **2×11** | 3561/144704 ≈ 0.024609 | 12181/496128 ≈ 0.024552 | **no** |
| 2×12 | 45685/2153536 ≈ 0.021214 | 38251/1845888 ≈ 0.020722 | **no** |
| 2×14 | 4729/287040 ≈ 0.016475 | 147133/9472320 ≈ 0.015533 | **no** |

So **b₇ < b₆ on 2×11, 2×12 and 2×14**. At 22 cells, 2×11 is the smallest torus where a
decrease is known. 2×10 has none at levels 5–8, but its other levels and other 20–21-cell
shapes were not checked. For a uniformly random configuration, the jam probability is
not monotone in the car count in general. The counts are in
`data/level-counterexample.json`, and §3's theorem is sharp in this sense: it holds up to 16
cells and on 2×9, and fails by 22 cells.

**Still open at these sizes.** Whether the iid probability q(p) is nondecreasing. A dip in b
makes one Bernstein coefficient of q′ negative, but q′ can stay positive everywhere. Deciding
it exactly needs every level of 2×11, which is 3²² ≈ 3.1·10¹⁰ states, beyond the exhaustive
method.

## 5. What this does and does not show

- It answers the roadmap's monotonicity question for W·H ≤ 16 and 2×9 only. The stronger
  fixed-count monotonicity fails on 2×11 (§4), so no proof can establish it in general. Nothing here
  implies monotonicity of q_L for large L, or the existence of a threshold.
- Configurationwise non-monotonicity (§4 of theorems.md, and the 13→14-car square
  counterexample in the probability note) is fully compatible with monotone averages. The
  identity of §2 is the bookkeeping that reconciles the two.
- The mixed-cycle probability m_3(p) decreases near p = 1 (probability note, §6), while q_3
  is increasing. With M = J ∩ Rᶜ, the gap q_3 − m_3 is P_p(J ∩ R), the probability of jams that
  start with a full lane. It is not P_p(R): R is not contained in J. A full east row plus one
  lone east car elsewhere circulates forever.
- §2 suggested proving monotonicity by showing that jam-creating additions dominate
  jam-destroying ones level by level. §4 shows that this is false on 2×11, so that route
  cannot prove monotonicity of q in general. A proof for q would have to use the averaging
  over n built into the iid law.
- On thin 2×W tori the decrease appears at the step n = 6 → 7 on widths 11, 12 and 14, and
  the Monte Carlo z-scores are worst at even n. Why this level is special is not understood.
  The data alone don't support a parity rule: width 11 is odd.
