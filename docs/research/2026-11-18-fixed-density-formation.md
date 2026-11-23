# Fixed-density bounds for CLASSIC mixed-cycle formation

**Research note — 18 November 2026. Prepared for review; no novelty claim.**

This continues PR #13 at integrated head
`07b6f117de5700b0c1803687361b733a43da3605`, including its original probability
note at `0ff1c2b40bd310995c427dd2c718d8401f203fbb`. The update rule is always
CLASSIC: synchronous east, then synchronous north. The initial cells have the
independent law `(0,E,N)=(1-p,p/2,p/2)`. A jam is nonempty.

Write `A_t` for the event that a mixed simple direct-blocker cycle is present
at full-round time `t`, and `M` for eventual occurrence. Such cycles persist,
so `A_t` increases with `t` and `M` is their union. PR #13 proves in prose
that `M=J intersect R-complement`, where `J` is eventual gridlock and `R` is
an initially full E-row or N-column. In particular,

\[
0\le q_L(p)-\Pr_p(M)\le 2L(p/2)^L.
\]

**What changes.** We obtain a fixed-density exponential upper bound on
initial mixed cycles, a finite-time extension using distinct original car
identities, and an exact transfer formula for a prescribed winding cycle
formed after one round. The latter disproves independence of the evolved
cells by an exponentially growing probability ratio. An additional obstruction
rules out an autonomous capture seed supported on a fixed finite block.
These results do **not** prove `p_->0`, a positive critical density, or a sharp
transition. The one-round lower bound below tends to zero with size.

**Follow-up:** [certified eventual-gridlock bounds](2026-11-18-certified-absorption-bounds.md)
now instantiate the safe-certificate route with universal Lean soundness and
exact finite initial-weight intervals. The
[relaxation obstructions](2026-11-18-relaxation-obstructions.md) show why fixed
burn-in, a vacant winding cut, and pointwise HBK defect descent do not close
the argument; they give a separate conditional late expected-defect criterion.

**Evidence boundary.** `BML/Formation.lean` proves the local preimage equivalence
for the actual kernel, simultaneous staircase formation, and construction of
an occupied successor-closed core. Probability integration, winding geometry,
the bounds, and limits below have prose proofs. The finite census checks one
round on all 43,046,721 states of the 4x4 torus; it does not enumerate their
eventual basins. No new Quint probability theorem is asserted.

## 1. Initial cycles are exponentially rare at every fixed p below one

Let `L>=2`. A simple mixed cycle of length `ell` has `a` east and `b` north
steps, with `a,b` positive multiples of `L`. Consequently `ell>=2L` and
`ell<=L^2`. At initial time the probability of any specified such cycle is
exactly `(p/2)^ell`, regardless of all exterior cells.

There are at most

\[
\frac{L^2}{kL}\sum_{j=1}^{k-1}\binom{kL}{jL}
\]

simple mixed cycles of length `kL`: choose a starting site and direction
word, then divide by the `kL` distinct roots of each simple cycle. Some words
repeat a vertex or close too early; keeping them only increases the bound.
A union bound gives

\[
\Pr_p(A_0)\le
\min\!\left\{1,
 L^2\sum_{k=2}^{L}\frac1{kL}
       \sum_{j=1}^{k-1}\binom{kL}{jL}(p/2)^{kL}\right\}.
\tag{1}
\]

Bounding the word count by `2^ell` and including every integer length at least
`2L` yields, for `0<=p<1`,

\[
\boxed{\Pr_p(A_0)\le
       \min\{1,\; Lp^{2L}/[2(1-p)]\}.}
\tag{2}
\]

Thus initial **direct** mixed cycles are exponentially rare for every fixed
`p<1`. This does not contradict Angel–Holroyd–Martin (AHM): their enlarged
blocking paths include replacement dependencies beyond direct occupied
successor edges. Their high-density theorem concerns eventual fixation,
not presence of an initial direct cycle [1]. In their high-density regime,
PR #13's event identity and (2) imply

\[
\Pr_p(M\setminus A_0)\longrightarrow1.
\tag{3}
\]

Hence an initial-direct-cycle estimate cannot be used as an upper bound on
eventual formation, even in a regime with a proved gridlock theorem.

## 2. A finite-time upper bound without an evolved iid assumption

Fix an integer `T>=0` and put `K=min(T+1,L)`. For a specified cycle of length
`ell` at time `T`, trace each of its distinct cars to time zero. An E-car
originates in the same row, at one of at most `K` westward positions; an N-car
originates in the same column, at one of at most `K` southward positions.
Different cars have distinct origins. There are at most `K^ell` assignments;
discarding assignments with coincident origins leaves only injective ones.
For each injective assignment, the required initial species have probability
`(p/2)^ell` under the actual initial law. The dynamic requirements can only
reduce that probability. Therefore

\[
\Pr_p(\text{specified cycle at }T)\le K^\ell(p/2)^\ell.
\]

Count cycles as in (1), with `p` replaced by `b=pK`. Since cycles persist,
this bounds formation **by** `T`, rather than just first formation exactly
at `T`. In particular, if `b<1`,

\[
\boxed{\Pr_p(A_T)\le
       \min\{1,\; Lb^{2L}/[2(1-b)]\},\qquad b=p\min(T+1,L).}
\tag{4}
\]

The winding-restricted sum analogous to (1) is often sharper and is computed
with exact rational arithmetic in `bml/formation.py`. The car-trace bijections
already formalized in `BML/Capture.lean` justify distinct original identities;
the counting/probability argument (4) remains a prose proof.

For each fixed `p>0` and fixed `T` satisfying `p(T+1)<1`, (4) tends to zero.
This controls early **capture-core formation**, which is different from PR
#13's bound on early complete gridlock. It does not control formation after
arbitrarily long transients. In particular, `T` cannot grow without bound at
fixed `p` in this estimate. There is no exchange of time and size limits.

## 3. An exact one-round winding-capture probability

Take `L>=4`. For each `y` modulo `L`, define

\[
B_y=(y,y),\quad C_y=(y+1,y),\quad A_y=(y-1,y),\quad
D_y=(y+1,y-1),\quad Q_y=(y+2,y)=D_{y+1}.
\]

Let `H_t` be the specified staircase event: every `B_y` contains E and every
`C_y` contains N at time `t`. These sites form the simple cycle
`B_y -> C_y -> B_(y+1)`, of winding `(1,1)`. Thus `H_1` implies `A_1` and
eventual global capture. Initially,

\[
\Pr_p(H_0)=(p/2)^{2L}.
\tag{5}
\]

Here is an exact predicate for `H_1` involving only initial cells. For every
`y`, require both

\[
\begin{split}
E_y={}&[B_y=E,\ C_y\ne0]\ \lor\ [B_y=0,\ A_y=E],\\
N_y={}&[C_y=N]\ \lor\
 [D_y=N,\ ((C_y=0,\ B_y\ne E)\lor(C_y=E,\ Q_y=0))].
\end{split}
\tag{6}
\]

**Proof of equivalence.** `E_y` is exactly the condition that `B_y` is E
after the east phase, and the north phase preserves E. If all `E_y` hold,
the north target of `C_y` is `B_(y+1)`, occupied by E after the east phase.
Thus an N initially at `C_y` stays. Otherwise an N can enter from `D_y`
precisely when `C_y` is empty after the east phase. That happens either when
it was empty and no E at `B_y` enters, or when its E moves into initially
empty `Q_y`. This gives `N_y`. Conversely all these conditions force the
two desired species after the complete round. This proof uses synchronous
phase snapshots; replacing them with asynchronous moves would change it.

The local equivalence and simultaneous formation are Lean-checked. Once the
staircase is formed, `staircaseCore` constructs a persistent blocking core.
Its winding and the geometric row/column cover give capture by the argument
of PR #13; that cover instantiation is not claimed as a new Lean theorem.

### Integrating the initial cells exactly

Put `u=p/2`, `v=1-p`, `a=u^2(1+v)`, and `b=u v^2`. Conditional on
`D_y=d,D_(y+1)=e`, summing the independent initial values of `A_y,B_y,C_y`
in (6) gives

\[
g(d,e)=a+\mathbf1_{d=N}\bigl(b+a\mathbf1_{e=0}\bigr).
\tag{7}
\]

All `A,B,C,D` sites are distinct when `L>=4`: they lie on four distinct
diagonals `x-y=-1,0,1,2`. Conditional on the `D` values, the remaining
three-site row groups are disjoint. The appearance of `D_(y+1)` in (7)
must be retained; multiplying unconditional row probabilities would be wrong.

With alphabet `(0,E,N)` and weights `w=(v,u,u)`, set

\[
T_{d,e}=g(d,e)w_e,\qquad
T=\begin{pmatrix}
va&ua&ua\\
va&ua&ua\\
v(2a+b)&u(a+b)&u(a+b)
\end{pmatrix}.
\]

Summing the cyclic sequence of initial `D` values proves the **exact** formula

\[
\boxed{\Pr_p(H_1)=h_L(p)=\operatorname{tr}(T^L).}
\tag{8}
\]

For rational `p` this is rational, with no Monte Carlo error. A rank-two
reduction acts on functions `c+k*1_(d=N)` by the matrix

\[
\begin{pmatrix}a&au\\ b+av&ub\end{pmatrix}.
\]

Its trace is `r=u^2(1+v+v^2)` and determinant is `-d`, where `d=u v a^2`.
Consequently the trace sequence satisfies

\[
h_0=2,\quad h_1=r,\quad h_j=rh_{j-1}+dh_{j-2}.
\tag{9}
\]

The initial indices in (9) are algebraic traces, not statements about tori of
side zero or one. Formula (8) describes the specified event only for `L>=4`.

Since `d>=0`, (9) implies `h_L>=r^L`. For every fixed `0<p<1`,

\[
\boxed{\frac{\Pr_p(H_1)}{\Pr_p(H_0)}
\ge[1+(1-p)+(1-p)^2]^L>1.}
\tag{10}
\]

At every full-round time, each individual site's E and N marginal is still
`u`: initial translation invariance is preserved, and each species' total
count is conserved. If the evolved cells were independent, the probability
in (8) would be `u^(2L)`. Thus (10) is an all-size counterexample to that
independence assumption, with an exponentially growing discrepancy.

### A finite-size lower bound on actual global capture

Translate the four-diagonal initial support by offsets `1,5,9,...`, using
`floor(L/4)` copies. Their initial supports are disjoint, so these **initial
preimage events** are independent. Every successful copy forms a winding
capture cycle at round one, regardless of exterior values. Therefore

\[
\boxed{q_L(p)\ge\Pr_p(A_1)\ge
1-[1-h_L(p)]^{\lfloor L/4\rfloor}.}
\tag{11}
\]

This is a genuine initial-iid finite-size bound at fixed positive density.
It assumes neither monotonicity in particle count nor independence of evolved
cells. Its limitation is explicit: `g(d,e)<=u` (indeed `2a+b=u`), so each
row sum of `T` is at most `u`. Thus `h_L<=3u^L`. Even the union of all `L`
translated prescribed staircases has probability at most `3L u^L -> 0`.
The right side of (11) also tends to zero. These capture structures do not
prove a positive limiting gridlock probability at any fixed `p`.

## 4. What a block argument still has to prove

A cylinder event specifying at most `m` initial sites cannot force eventual
gridlock for every exterior assignment on all large tori. To see this, take
`L>m` and set every unspecified site empty. There are fewer than `L` cars.
Any nonempty jam would contain a simple blocker cycle, whose nonzero winding
requires at least `L` distinct cars. Conservation rules this out. Thus no
fixed finite pattern is an autonomous global-capture droplet. A spatial
block proof needs connected certificates across the torus, or an explicit
condition on the exterior. AHM's enlarged blocking paths and connected
renormalized blocks are consistent with this obstruction [1].

Here is a precise conditional route for finite-state inequalities. Let `U_L`
be a set of states satisfying

1. `F(U_L)` is contained in `U_L`;
2. `U_L` contains no mixed cycle.

Suppose, under the actual initial product law, one can bound

\[
\Pr_p(F^{T_L}(s)\notin U_L\cup A)\le\varepsilon_L,
\]

where `A` is the set of states containing a mixed cycle. Then

\[
\boxed{q_L(p)\le 2L(p/2)^L+\Pr_p(A_{T_L})+\varepsilon_L.}
\tag{12}
\]

**Proof.** If `F^(T_L)(s)` belongs to `U_L`, forward invariance and disjointness
exclude every later mixed cycle. Persistence also excludes an earlier one.
If it belongs to `A`, count it in `A_(T_L)`. All remaining eventual formations
belong to the error event. Add the initial ring exception. No later
configuration is treated as iid.

On a completely enumerated finite graph, forward closure and disjointness
of `U_L` are decidable, and its time-`T_L` preimage probability is an exact
initial-weight sum. A cutoff with moving but unresolved trajectories is not
such a safe set. Formula (12) would advance fixed-density nonjamming if both
its formation term and error term were proved to vanish for fixed `p>0`.
Neither small-torus enumeration nor (4), whose nontrivial time horizon is
bounded at fixed `p`, establishes that missing estimate.

Conserved lane profiles alone cannot supply `U_L`: PR #13 constructs jammed
and permanently free representatives in typical profiles at every fixed
`p<2/3`. A valid safe-set argument must retain information beyond lane counts
and estimate its initial-law preimage mass.

## 5. Exact finite evidence and reproduction

For one specified staircase on the complete 4x4 initial state space, the
counts by number of cars are:

| Cars | Initial specified cycle | Specified cycle after one round |
| ---: | ---: | ---: |
| 0–7 | 0 | 0 |
| 8 | 1 | 81 |
| 9 | 16 | 792 |
| 10 | 112 | 3,272 |
| 11 | 448 | 7,568 |
| 12 | 1,120 | 10,800 |
| 13 | 1,792 | 9,792 |
| 14 | 1,792 | 5,536 |
| 15 | 1,024 | 1,792 |
| 16 | 256 | 256 |
| Total | 6,561 | 39,889 |

Each state in car-count layer `n` receives weight `(p/2)^n(1-p)^(16-n)`.
For `p=1/2`, the initial probability is `1/65536`, and the exact round-one
probability is `6647/33554432`: a ratio of `6647/512`, approximately `12.98`.
For the uniform ternary law `p=2/3`, the latter probability is
`39889/43046721`. These agree with (8), rather than assuming it in the census.
Numerical agreement verifies the stated finite domain; the all-size formula
uses the integration proof above.

```sh
python -m pytest -q tests/test_formation.py
python scripts/check_formation.py --report .artifacts/formation-replay.json
cd formal/lean
lake build BML
lake env lean Audit.lean
```

The report checks (6) pointwise against the production kernel on all 4x4
states and compares exact iid weights with the transfer recurrence. Tests
also use an independent scalar kernel, arbitrary-exterior positive controls,
all 243 local assignments for conditional integration, and complete 2x2/3x3
transition maps to check (1)/(4). The report binds its results to unchanged
source hashes before and after execution. These are distinct verification
scopes and are not one shared theorem.

The fixed-density problem remains open. The concrete progress is an exact
dynamic capture calculation, early-formation bounds, and proved barriers to
three tempting shortcuts: counting only initial direct cycles, assigning an
iid law after a round, and amplifying an autonomous fixed-block droplet.

## References

1. Omer Angel, Alexander E. Holroyd, James B. Martin, **The Jammed Phase of the
   Biham–Middleton–Levine Traffic Model**, ECP 10 (2005), 167–178.
   [Primary paper](https://arxiv.org/pdf/math/0504001v2).
   Theorems 1–2, the enlarged blocking paths in Section 2, and the torus proof
   in Section 3 are the relevant prior results. Their north-then-east order is
   conjugate to ours by swapping coordinates and species, preserving the law.
2. [PR #13 probability note](2026-11-18-probabilistic-gridlock-bounds.md): event
   identity, ring comparison, capture argument, and lane-profile counterexamples.
