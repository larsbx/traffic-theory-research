# A limitation of deterministic lane-profile certificates

**Research note — 18 November 2026.** At every fixed density \(0<p<1\),
the conserved lane counts of a square CLASSIC BML system admit a completely
jammed representative with probability tending to one. Consequently, every
sound deterministic certificate that uses only those counts to rule out
eventual gridlock has acceptance probability tending to zero. The bounds
below make this limitation quantitative. They do not bound the probability
that the actual random initial state eventually jams. No novelty claim is
made.

**Proof status.** The construction and probability arguments below have
self-contained mathematical proofs. The accompanying Lean file,
[`BML/Profiles.lean`](../../formal/lean/BML/Profiles.lean), formalizes the
actual CLASSIC representative, its exact numerical lane counts, and the
deterministic rejection of admissible profiles by any predicate that soundly
excludes already jammed configurations. Section 5 names the public exports
and explains that scope. The probability estimates are prose mathematics,
not probability theorems in Lean. Consult the
[formal coverage register](../../formal/README.md) for validation status.

## 1. What information a lane profile retains

Use an \(L\times L\) torus, \(L\ge1\), with coordinates \((x,y)\)
modulo \(L\). East is \(+x\), north is \(+y\). A full CLASSIC round
updates all E-cars synchronously and then all N-cars synchronously. A car
moves only if its destination was empty at the start of its half-step. These
are the rules in [`bml/model.py`](../../bml/model.py), rather than the
repository's different TRAIN rule.

For a state \(s\), write

\[
r_y(s)=\#\{x:s(x,y)=E\},\qquad
c_x(s)=\#\{y:s(x,y)=N\},\qquad
\Pi(s)=((r_y)_y,(c_x)_x).
\]

The profile \(\Pi\) records each E-row count and each N-column count.
These counts are conserved by every full round. They retain the species and
the locations of the lanes, but discard the positions of cars within them.

A **jam** is a nonempty configuration in which every car's successor cell
is occupied. Let \(J_L\) be the set of initial states whose actual CLASSIC
trajectory eventually reaches a jam. The empty state is excluded from
\(J_L\). For a profile \(\pi\), let

\[
\Gamma(\pi)=\{s:\Pi(s)=\pi\}.
\]

Call \(\pi\) **jam-realizable** when \(\Gamma(\pi)\) contains an
already jammed state. This is a statement about a representative in a
conserved class. It does not assert that another state in that class can
reach that representative, or that its orbit reaches any jam.

## 2. A jammed representative for every positive bounded profile

### Theorem 1: exact realization under a sum bound

Suppose the integer vectors \(r,c\) satisfy

\[
r_y\ge1,\quad c_x\ge1,\quad r_y+c_x\le L
\quad\text{for every }x,y.
\]

Equivalently, all counts are positive and
\(\max_y r_y+\max_x c_x\le L\). Then there is a nonempty jammed
configuration with exactly this profile.

**Construction.** At \((x,y)\), put E when
\((y-x\bmod L)<r_y\), put N when
\(0<(x-y\bmod L)\le c_x\), and leave the cell empty otherwise. The
residues in these inequalities are represented by integers in
\(\{0,\ldots,L-1\}\).

**Proof.** Positivity and the sum bound imply \(L\ge2\) and
\(r_y,c_x\le L-1\). The E-sites in row \(y\) are precisely

\[
(y-j,y),\qquad 0\le j<r_y,
\]

and the N-sites in column \(x\) are precisely

\[
(x,x-i),\qquad 1\le i\le c_x.
\]

Within a lane these indices give distinct sites. An overlap would require
\(i+j\equiv0\pmod L\), but

\[
1\le i+j\le c_x+r_y-1\le L-1,
\]

which is impossible. Thus the two prescriptions are disjoint, and they
realize all requested counts exactly. Equality in the sum bound is allowed;
the strict inequality in the E-index range supplies the needed final minus
one.

An E-car with \(j>0\) is blocked by the E-car with index \(j-1\) in
the same row. The front E-car \((y,y)\) is blocked by the N-car
\((y+1,y)\), which is the \(i=1\) car in column \(y+1\). This car
exists because that column's N-count is positive.

An N-car with \(i>1\) is blocked by the N-car with index \(i-1\) in
the same column. The front N-car \((x,x-1)\) is blocked by the E-car
\((x,x)\), which exists because row \(x\)'s E-count is positive.
Every E-car is therefore blocked during the E half-step, and every N-car is
still blocked during the N half-step. The configuration is nonempty and
jammed. ∎

Every specified count is at most \(L-1\), so the representative has neither
a full E-row nor a full N-column. In fact, every configuration with this
profile has the same absence of full monochromatic lanes. The obstruction
therefore persists when those special ring configurations are excluded.

The construction requires no equality between the total numbers of the two
species. It strengthens the jammed half of the narrower construction in
[Proposition 7 of the probability note](2026-11-18-probabilistic-gridlock-bounds.md#proposition-7-two-states-for-every-profile-in-a-specified-range).
The free-flowing representative proved there has its own stronger hypotheses;
no extension of that free-flow claim is inferred here.

## 3. The certificate class and the exact finite bound

For each \(L\), a **sound deterministic profile-only nonjamming
certificate** is any predicate \(C_L\) on profiles satisfying

\[
C_L(\Pi(s))\quad\Longrightarrow\quad s\notin J_L
\qquad\text{for every initial configuration }s.
\]

There is no restriction on the predicate's computational complexity. It can
use the entire ordered pair of lane-count vectors. It must, however, give the
same answer for every state with the same profile, and acceptance must rule
out eventual nonempty gridlock for all of those states.

Let \(F_L\) be the event that the sampled profile has no jammed
representative. Every such certificate satisfies

\[
\{C_L(\Pi(s))\}\subseteq F_L.
\]

Indeed, accepting a jam-realizable profile would also accept its jammed
representative, which already belongs to \(J_L\) at time zero. In
particular, the bound below controls every sound predicate at once; it is
not tied to a chosen algorithm. Some profiles in \(F_L\) may still contain
states that jam later, so \(F_L\) itself is not asserted to be a sound
nonjamming certificate.

Sample the initial cells independently with probabilities
\((1-p,p/2,p/2)\) for empty, E, N. Put

\[
u=p/2,\quad X\sim\operatorname{Bin}(L,u),\quad
m=\lfloor L/2\rfloor,\quad
z=(1-u)^L,\quad t_m=\Pr(X\ge m+1).
\]

### Theorem 2: a finite uniform bound over all certificates

For every \(L\ge1\), \(p\in[0,1]\), and sound \(C_L\),

\[
\boxed{
\Pr(C_L(\Pi(s)))\le\Pr(F_L)
\le\min\left\{1,\,2\left[1-(1-z-t_m)^L\right]\right\}
\le\min\{1,\,2L(z+t_m)\}.}
\]

**Proof.** If every E-row count and every N-column count lies in
\([1,m]\), their maximum sum is at most \(2m\le L\), so Theorem 1
gives a jammed representative. Therefore \(F_L\) requires at least one
count outside this interval.

Each E-row count has the law of \(X\). Its two disjoint bad cases are
zero, with probability \(z\), and greater than \(m\), with probability
\(t_m\). Different E-rows use disjoint initial sites, so the probability
that at least one E-row is bad is exactly \(1-(1-z-t_m)^L\). The same
formula holds for the family of N-columns. Union bound these two families
and then, if desired, union bound the \(2L\) individual lanes. Independence
between an E-row and an N-column is neither true in general nor used.
Finally, any probability is at most one. ∎

The upper tail is \(X\ge\lfloor L/2\rfloor+1\), not
\(X\ge\lfloor L/2\rfloor\). Counts equal to the cap are admissible.
For \(L=1\), the sufficient interval is empty and the bound remains
valid, although uninformative.

### Unequal caps and a shared-cell refinement

The finite bound can be improved without changing the construction. For
positive integers \(a,b\) with \(a+b\le L\), let
\(t_a=\Pr(X\ge a+1)\) and \(t_b=\Pr(X\ge b+1)\). Repeating the
proof with E-row counts at most \(a\) and N-column counts at most \(b\)
gives

\[
\Pr(F_L)\le
\min\{1,\,2-(1-z-t_a)^L-(1-z-t_b)^L\}.
\]

One may minimize over these fixed choices of caps. Increasing a cap only
improves this bound, so it suffices to consider \(a+b=L\). For odd
\(L\ge3\), choosing \(a=(L-1)/2\), \(b=(L+1)/2\) improves the
symmetric-cap estimate by allowing one family to use the extra site. No
claim that one particular pair optimizes every finite instance is needed.

A different refinement tests the sum condition directly. For a fixed row
\(y\) and column \(x\), their common site contributes one to
\(r_y+c_x\) if it is occupied and zero if it is empty. It cannot
contribute two. Every other relevant cell contributes an independent
Bernoulli variable with parameter \(u\). Consequently

\[
r_y+c_x\ \stackrel{d}{=}\ Y+B,
\qquad Y\sim\operatorname{Bin}(2L-2,u),\quad
B\sim\operatorname{Bernoulli}(p),
\]

with \(Y\) and \(B\) independent. Put

\[
T=(1-p)\Pr(Y\ge L+1)+p\Pr(Y\ge L).
\]

This is exactly the probability that this pair violates \(r_y+c_x\le L\).
Theorem 1 fails to apply only if a lane count is zero or some pair violates
the sum bound. Union bounding the \(L^2\) pairs therefore gives another
valid estimate:

\[
\boxed{
\Pr(F_L)\le
\min\{1,\,2[1-(1-z)^L]+L^2T\}.}
\]

This calculation uses independence only among distinct initial cells. No
independence among the \(L^2\) pair events is assumed. The minimum of any
of the displayed upper bounds remains a valid upper bound.

## 4. Fixed-density consequences and their limits

Fix \(0<p<1\). Write

\[
D(1/2\Vert u)
=\frac12\log\frac{1}{4u(1-u)}
=\frac12\log\frac{1}{p(2-p)}>0.
\]

For completeness, the exponential-moment bound at
\(a=\log[(1-u)/u]>0\) yields

\[
\Pr(X\ge L/2)
\le e^{-aL/2}(1-u+ue^a)^L
=[4u(1-u)]^{L/2}.
\]

Since \(m+1>L/2\), this also bounds \(t_m\). Theorem 2 gives

\[
\boxed{
\Pr(C_L(\Pi(s)))\le\Pr(F_L)
\le\min\left\{1,\,
2L\left[(1-p/2)^L+[p(2-p)]^{L/2}\right]\right\}
\longrightarrow0.}
\]

Both exponential bases are strictly below one. Thus the probability that
the observed profile rules out every already jammed representative is
exponentially small, up to the displayed polynomial factors. The failure
probability of every sound deterministic profile-only certificate is at
least one minus this bound.

The shared-cell estimate can improve the rate. For \(L\ge2\),
\(T\le\Pr(Y\ge L)\le\Pr(Y\ge L-1)\). Applying the same
exponential-moment argument to the \(2L-2\) trials of \(Y\) gives

\[
\Pr(F_L)\le
\min\left\{1,\,
2L(1-p/2)^L+L^2[p(2-p)]^{L-1}\right\}.
\]

The convergence is also uniform when \(p\) ranges over any fixed compact
interval \([a,b]\subset(0,1)\): the first bound is at most
\(2L[(1-a/2)^L+[b(2-b)]^{L/2}]\).

None of these estimates implies \(q_L(p)=\Pr(J_L)\to1\), nor does it
rule out \(q_L(p)\to0\). They concern the existence of a jammed state
somewhere in the same conserved profile class. That representative might
have a very small basin, and the sampled state need not reach it. Under the
initial iid law with \(0<p<1\), every state in a fixed profile class has
the same initial probability, because the profile fixes the total counts of
both species. A single jammed representative therefore need not give a
useful lower bound on the conditional probability of eventual gridlock.

The obstruction applies to universal deterministic nonjamming conclusions
based solely on lane counts. It does not prevent probability estimates for
the fraction of a profile class that jams, certificates that use actual car
positions, or arguments that control future motion. It also does not assert
that typical profiles contain free-flowing states at every \(p<1\); the
previous two-representative result proves that additional statement only
under its own hypotheses.

Finally, the sparse nonjamming theorems in the
[probability note](2026-11-18-probabilistic-gridlock-bounds.md#3-an-explicit-sparse-density-nonjamming-bound)
concern densities tending to zero. There is no conflict between those
results and the present limitation at fixed positive density. Neither
establishes a positive critical density, a sharp threshold, or existence of
all fixed-density large-torus limits.

## 5. Evidence boundary

The deterministic Lean layer uses the actual CLASSIC torus directions and
update. Its main public exports are:

| Export | Scope |
| --- | --- |
| `laneProfileJam` | The explicit E/N configuration used in Theorem 1. |
| `laneProfileJam_counts` | Exact numerical E-row counts and N-column counts. |
| `laneProfileJam_jam` | The representative is a nonempty actual-kernel jam. |
| `laneProfileJam_no_moves`, `laneProfileJam_fixed` | No actual movement occurs, and a full round leaves the state unchanged. |
| `laneProfileJam_no_full_lane` | No full E-row or full N-column is present. |
| `exists_jam_with_lane_profile` | A jam exists with the prescribed positive profile and pairwise sum bound. |
| `exists_jam_with_lane_profile_of_caps` | The same existence result using separate caps whose sum is at most \(L\). |
| `exists_jam_with_same_lane_profile` | A supplied configuration satisfying the profile hypotheses has a jammed representative with exactly its lane counts. |
| `admissible_profile_cannot_certify_no_jam` | Every profile predicate that universally excludes already jammed states rejects these admissible profiles. |

The last theorem's soundness premise is exclusion of an already jammed
configuration. A certificate that soundly excludes eventual gridlock, as
defined in Section 3, satisfies this premise because every already jammed
state belongs to \(J_L\). The formal result therefore supplies the
deterministic obstruction used here; it does not formalize the random
initial law, the finite probability bounds, or their asymptotics.

The computational entry points are [`bml/profiles.py`](../../bml/profiles.py),
[`tests/test_profiles.py`](../../tests/test_profiles.py), and
[`scripts/check_profiles.py`](../../scripts/check_profiles.py). The completed
constructor census checks every positive ordered profile pair satisfying the
sum condition on the following sides:

| Square side | Admissible ordered profile pairs checked |
| --- | ---: |
| 2 | 1 |
| 3 | 15 |
| 4 | 386 |
| 5 | 16,090 |
| **Total** | **16,492** |

Every witness is bound to the exact requested lane counts by the public
verifier, which checks both actual production half-steps for zero movement.
An independent tagged replay also certifies a period-one state with no tag
movement. Nine additional nonuniform profiles on sides 8, 16, and 31 are
targeted checks, separate from the exhaustive domains. In total, 16,501
witnesses pass both checks.

A separate scalar enumeration covers all 19,767 initial states on sides
1, 2, and 3. At each of \(p=0,1/5,1/2,2/3,1\), exact product-law
weights verify that both bounds dominate the probability of failure of the
sufficient profile condition, and that the entire specified row/column pair
distribution equals \(\operatorname{Bin}(2L-2,p/2)+
\operatorname{Bernoulli}(p)\). This gives 15 density/domain evaluations and
75 individual pair-mass checks. These are checks of the profile obstruction
and the initial law, not an enumeration of eventual traffic basins.

Negative controls reject a moving board with the same admissible profile,
stale or malformed counts, violated positivity or sum conditions, and TRAIN.
A further control distinguishes the correct shared-cell law from the false
\(\operatorname{Bin}(2L,p/2)\) model. At \(L=64,p=1/2\), exact fractions
give a shared-cell pair bound below \(1/100000\), while the symmetric-cutoff
bound exceeds \(1/10000\); these remain bounds on certificate acceptance.
The focused regression suite passes 55 tests.

From the repository root, reproduce the focused tests and source-bound census
with:

```sh
python -m pytest -q tests/test_profiles.py
python scripts/check_profiles.py --report .artifacts/profiles-replay.json
```

The completed JSON receipt records matching before/after source hashes,
separate exhaustive and targeted scopes, exact probability evaluations, and
the negative controls. Finite constructor checks can falsify an
implementation error, but do not replace the universal representative proof.

The initial-product-law calculations and all asymptotic conclusions require
the separate arguments above. They make no iid assumption about evolved
configurations and no assumption that eventual gridlock is monotone under
adding cars.
