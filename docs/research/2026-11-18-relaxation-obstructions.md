# Relaxation obstructions and a late-defect criterion for CLASSIC BML

**Research note — 18 November 2026. No novelty claim.**

The [fixed-density formation note](2026-11-18-fixed-density-formation.md)
reduces a possible low-density argument to reaching an explicit invariant safe
set, with high probability under the **initial** iid law. This note tests three
tempting shortcuts and supplies a weaker, quantitative alternative to proving
entry into permanent free flow.

Throughout, \(F\) is one CLASSIC east-then-north round on an \(L\times L\)
torus. Coordinates are \((x,y)\), east increases \(x\), and north increases
\(y\), modulo \(L\). Initial cells have probabilities
\((1-p,p/2,p/2)\) for empty, east and north. No later state is assigned an iid
law. A jam is nonempty and has zero movement; the empty state is free.

The universal queue delay and the finite vacant-cut counterexample below are
proved in [BML/Delay.lean](../../formal/lean/BML/Delay.lean). The iid
integration, logarithmic consequence, defect estimates and analytic limits
are prose proofs. The four-car defect counterexample has an all-size coordinate
proof and finite Python checks. None establishes a positive critical density.

## 1. The HBK defects and their phase convention

Hertzberg Rabinovich, Biham and Katzav define two nonnegative defects in
Eqs. (8) and (11) of [HBK]. Their zero set characterizes permanent free flow;
Appendix B proves its invariance. The convergence results are numerical.
Their suggestion of a Lyapunov function concerns a possible coarse-grained
mean-field description, not a proved monotonicity theorem for the microscopic
kernel.

Write \(e_n(s)\) and \(n_n(s)\) for the numbers of east and north cars on
the counter-diagonal \(x+y=n\pmod L\). At a full-round boundary, immediately
before the east phase, use the **raw integer defects**

\[
\begin{aligned}
d_\parallel(s)
&=\sum_{x,y}\mathbf1_{s(x,y)=E=s(x+1,y)}
 +\sum_{x,y}\mathbf1_{s(x,y)=N=s(x,y+1)},\\
d_\perp(s)
&=\sum_{n\in\mathbb Z_L}\min\{e_n(s),n_n(s)\}
 +\sum_{n\in\mathbb Z_L}\min\{e_n(s),n_{n+1}(s)\},\\
V(s)&=d_\parallel(s)+d_\perp(s).
\end{aligned}
\tag{1}
\]

Immediately after the east phase, the second sum in \(d_\perp\) instead
uses \(\min\{n_n,e_{n+1}\}\), because north moves next. The implementation
[bml/obstructions.py](../../bml/obstructions.py) makes this phase argument
explicit. It uses raw integers and assumes no finite-size normalization
identity for their initial expectations.

## 2. A sparse counterexample to pointwise descent

For every \(L\ge4\), leave all sites empty except

| Species | Before the round | After the round |
| --- | --- | --- |
| East | \((1,0),(0,1)\) | \((1,0),(1,1)\) |
| North | \((0,0),(2,0)\) | \((0,1),(2,1)\) |

The east car at \((1,0)\) is blocked by the north car at \((2,0)\). The
other east car moves to \((1,1)\). Both north destinations are then empty,
so both north cars move. This proves the displayed transition using the
actual two phase snapshots.

There are no like-species adjacent pairs before or after. Initially the east
diagonal counts are \(e_1=2\), and the north counts are \(n_0=n_2=1\).
Only the cross-diagonal term \(\min(e_1,n_2)=1\) contributes. Afterward,
\(e_1=e_2=n_1=n_3=1\); the same-diagonal term at \(1\) and the
cross-diagonal term from \(2\) to \(3\) each contribute one. Hence

\[
\boxed{(d_\parallel,d_\perp)(s)=(0,1),\qquad
       (d_\parallel,d_\perp)(F(s))=(0,2).}
\tag{2}
\]

Thus \(d_\perp\), \(V\), and any positive rescaling of \(d_\perp\) plus
a nonnegative multiple of \(d_\parallel\) increase on this example. This
also includes the paper's displayed scaling
\(D=2d_\parallel/(Lp)^2+d_\perp/(L^2p)\) for \(p>0\). Since the example
has only four cars, its global density \(4/L^2\) tends to zero. Restricting
to an arbitrarily small positive upper bound on global density does not make
these quantities pointwise nonincreasing.

This does not refute an averaged drift inequality under a specified evolved
law, a potential with additional information, or a bound over a different
time scale. It also does not contradict [HBK]'s proved invariance at zero.

## 3. A universal queue delay and its initial-iid probability

Let \(\tau_{\rm ff}(s)\) be the least integer \(U\ge0\) such that every
car moves in every round \(t\ge U\); set it to infinity when no such \(U\)
exists. Time \(t\) denotes the configuration \(F^t(s)\) before the east
phase of round \(t\). The empty state has \(\tau_{\rm ff}=0\).

### A run of \(T+2\) cars excludes full movement in round \(T\)

Suppose the initial sites
\((x_0,y_0),(x_0+1,y_0),\ldots,(x_0+T+1,y_0)\) all contain east cars.
Their rear car remains blocked in every round \(0\le t\le T\), whatever
the exterior does.

To prove this, observe that one CLASSIC round preserves all but the front
site of any east run. Every other car has an occupied destination in the
old east-phase snapshot, so stays; the north phase preserves east cars.
Induction leaves the initial first \(r-t\) sites east after \(t\) rounds
when the initial run has length \(r\). Taking \(r=T+2\) leaves the first
two sites east at time \(T\). The rear car therefore cannot move in that
round, and

\[
\tau_{\rm ff}(s)>T.
\tag{3}
\]

This is a statement about the original car, not a replacement occupying its
site. The Lean theorems `BML.eastRun_delay`, `eastRun_blocked_until`,
`eastRun_rear_trace` and `eastRun_settling_after` prove the kernel statements;
`torus_eastRun_delay` specializes to the actual finite-torus update. The
kernel proof does not require distinct sites. Distinctness is imposed next
for the probability calculation. TRAIN queues do not obey this delay rule.

### Exact finite-size upper bound on early free flow

Assume \(0\le T\le L-2\), put \(r=T+2\), and choose the disjoint blocks

\[
\{(jr+i,y):0\le i<r\},\qquad
0\le y<L,\quad 0\le j<\lfloor L/r\rfloor.
\]

There are \(K=L\lfloor L/(T+2)\rfloor\) blocks. Each is all east with
probability \((p/2)^{T+2}\). These events are independent because their
**initial supports** are disjoint. Any successful block excludes even one
full-movement round at time \(T\). Consequently

\[
\boxed{\Pr_p(\tau_{\rm ff}\le T)
 \le\Pr_p(\text{all cars move in round }T)
 \le\left[1-(p/2)^{T+2}\right]^{L\lfloor L/(T+2)\rfloor}.}
\tag{4}
\]

The right-hand side is the exact probability that none of the selected
initial blocks is all east; it is only an **upper bound** on the dynamically
defined events. The endpoint \(T=L-2\) is included, where each block is a
complete east row. Replacing \(T+2\) by \(T+1\) would be incorrect: with
empty space ahead, the rear of a run of length \(T+1\) can begin moving in
round \(T\).

### A logarithmic lower obstruction on settling time

Fix \(0<p\le1\), write \(u=p/2\), and choose

\[
0<c<\frac{2}{\log(2/p)},\qquad T_L=\lfloor c\log L\rfloor.
\]

For all sufficiently large \(L\), \(T_L+2\le L\). Since
\(1-z\le e^{-z}\), \(\lfloor L/r\rfloor\ge L/(2r)\) for \(1\le r\le L\),
and \(u^{T_L+2}\ge u^2L^{-c\log(1/u)}\), (4) gives

\[
\Pr_p(\tau_{\rm ff}\le\lfloor c\log L\rfloor)
\le\exp\!\left[
-\frac{u^2 L^{2-c\log(1/u)}}{2(c\log L+2)}\right]
\longrightarrow0.
\tag{5}
\]

Thus with probability tending to one,
\(\tau_{\rm ff}\ge\lfloor c\log L\rfloor+1\). This asserts neither
eventual free flow nor an optimal constant: infinite settling times also
satisfy this lower bound.

### Why a fixed burn-in cannot reach the HBK safe set with high probability

Let \(U=\{s:V(s)=0\}\). Every state in \(U\) has full movement, and its
future stays in \(U\). Equation (4) therefore gives
\(\Pr_p(F^T(s)\in U)\to0\) for every fixed \(p>0\) and fixed \(T\).
For the times satisfying \(p(T+1)<1\), the earlier formation note also gives
\(\Pr_p(A_T)\to0\). Here \(A\) is the set of states containing a mixed
capture cycle, and \(A_T=\{s:F^T(s)\in A\}\). The safe-set error for this
particular choice therefore obeys

\[
\Pr_p(F^T(s)\notin U\cup A)
\ge1-\Pr_p(F^T(s)\in U)-\Pr_p(A_T)\longrightarrow1.
\tag{6}
\]

The fixed-time formation bound and the free-flow zero set therefore cannot
complete that argument together. A larger explicit invariant safe set, or
control at a time growing with \(L\), is needed. This is not an obstruction
to the safe-set method in general.

## 4. A vacant winding cut is not an invariant safety certificate

Consider the following \(4\times4\) state, with rows listed in increasing
\(y\). Its actual CLASSIC successor is displayed alongside it:

\[
s=\begin{pmatrix}
0&0&0&E\\0&E&N&N\\0&E&0&0\\N&N&0&E
\end{pmatrix},\qquad
F(s)=\begin{pmatrix}
E&N&0&0\\0&E&N&0\\0&0&E&N\\N&0&0&E
\end{pmatrix}.
\tag{7}
\]

The initial state has the simple vacant east/south cycle

\[
(0,0),(1,0),(2,0),(2,3),(2,2),(3,2),(0,2),(0,1),(0,0).
\]

It has four east and four south steps, hence winding \((1,-1)\). Yet one
round, with two east and two north moves, produces a nonempty jam. Its eight
cars form the mixed occupied cycle \(E(y,y)\to N(y+1,y)\to E(y+1,y+1)\),
of winding \((1,1)\).

The theorem `BML.DelayWitness.vacant_cycle_does_not_prevent_jam` checks this
specific initial cut and actual jam in Lean; `after_has_no_vacant_cycle`
also rules out every vacant east/south cycle afterward. The ternary codes
are `18626220 -> 15826840`, using the repository's row-major encoding.
Thus the existence of such a vacant winding cut at one time does not define
a forward-invariant safe set. A useful cut certificate would need stronger
conditions that survive the two phase updates.

## 5. A weaker sufficient target: late expected defect density

Reaching \(V=0\) with high probability would establish permanent full flow.
For the narrower target of avoiding complete gridlock, one can instead use
the fact that a jam must retain many defects.

### A jam with \(m\) cars has \(V\ge m/2\)

In a frozen configuration, let \(a,b,c,d\) count occupied directed edges of
types \(E\to E,E\to N,N\to E,N\to N\), respectively. Every car has
exactly one such edge, so

\[
m=a+b+c+d,\qquad \#E=a+b,\qquad d_\parallel=a+d.
\]

The north successor map is injective, so distinct \(N\to E\) edges have
distinct east targets. Therefore \(c\le\#E=a+b\). For each diagonal
\(n\), the \(E\to N\) edges from \(n\) have distinct east sources and
distinct north targets on \(n+1\); their number is at most
\(\min(e_n,n_{n+1})\). Summing gives \(b\le d_\perp\). Thus

\[
\boxed{m\le2a+2b+d\le2(d_\parallel+d_\perp)=2V.}
\tag{8}
\]

The constant is sharp even at every fixed limiting density. For even
\(L\ge2\), choose \(1\le k\le L/2\). For each
\(a\in\{0,2,\ldots,2(k-1)\}\), put east cars at \((y+a,y)\) and north
cars at \((y+a+1,y)\), for \(y\in\mathbb Z_L\). Each translate is a
successor-closed staircase. The translates occupy disjoint pairs of
\(x-y\) classes, so their union is a jam with \(m=2kL\).

All east cars lie on even \(x+y\) classes and north cars on odd ones.
Each translate supplies two east cars to every even class and two north
cars to every odd class. Thus \(d_\parallel=0\), each of the \(L/2\)
east-to-north class pairs contributes \(2k\), and

\[
V=kL=m/2.
\]

For any fixed \(p\in(0,1]\), taking \(k=\lfloor pL/2\rfloor\) along
sufficiently large even \(L\) gives \(m/L^2=2k/L\to p\), with equality
in (8). The even-\(L\) condition matters. These deterministic examples
make no statement about their iid basin probabilities.

### Converting an expected defect estimate into an eventual-jam bound

Fix \(p>0\). Let \(M\) be the initial population and let \(\tau_J\) be
the first time of nonempty gridlock. Here \(M\sim\operatorname{Bin}(L^2,p)\), and
population is conserved. The elementary binomial lower-tail estimate is

\[
\Pr_p(M<pL^2/2)\le e^{-pL^2/8}.
\tag{9}
\]

For completeness, exponential Markov with \(\lambda=\log2\) bounds the
left side by
\(\exp[pL^2(\lambda/2-1/2)]\le\exp(-pL^2/8)\); this uses
\((1-p+p e^{-\lambda})^{L^2}\le\exp[pL^2(e^{-\lambda}-1)]\)
and \(\log2\le3/4\). No assumption on the evolved cell law enters.

On \(\{\tau_J\le t,\ M\ge pL^2/2\}\), the time-\(t\) state is still a
jam and (8) gives \(V(F^t(s))\ge pL^2/4\). Therefore, for every \(t\ge0\),

\[
\Pr_p(\tau_J\le t)
\le e^{-pL^2/8}+\frac{4}{pL^2}\,
      \mathbb E_{s\sim\mu_{L,p}}[V(F^t(s))].
\tag{10}
\]

Taking time to infinity **at fixed \(L\)** yields

\[
\boxed{q_L(p)\le e^{-pL^2/8}
 +\frac{4}{pL^2}\liminf_{t\to\infty}
       \mathbb E_{s\sim\mu_{L,p}}[V(F^t(s))].}
\tag{11}
\]

Indeed, the probabilities on the left of (10) increase to \(q_L(p)\), so
the inequality holds along a subsequence attaining the liminf on the right.
For each fixed \(p>0\), the sufficient research target is consequently

\[
\boxed{\lim_{L\to\infty}\;
\liminf_{t\to\infty}
\frac{\mathbb E_{s\sim\mu_{L,p}}[V(F^t(s))]}{L^2}=0
\quad\Longrightarrow\quad q_L(p)\to0.}
\tag{12}
\]

The order of limits is part of the claim. Proving a small value at one early
time, or a limit with \(L\) taken first, does not establish (12). All
expectations integrate initial iid samples followed by the actual dynamics.
Equation (2) prevents replacing this missing estimate by pointwise descent.

This target permits a subextensive positive number of defects, including
moving recurrent states, and therefore asks less than full-flow entry. In
contrast, \(\mathbb E[V(F^{T_L})]=o(1)\) would imply entry into \(V=0\)
with high probability by the integer-valued Markov bound. Small **defect
density** alone does not imply such entry.

One may also use the long-time Cesaro mean
\(\overline V_L(s)=\lim_{K\to\infty}K^{-1}\sum_{t<K}V(F^t(s))\).
It exists because each finite deterministic orbit is eventually periodic.
On the jam event it is at least \(M/2\), so the right side of (11) remains
an upper bound if its liminf expectation is replaced by
\(\mathbb E[\overline V_L]\). This is convenient for exact finite-orbit
certificates; a size-uniform estimate under the initial law is still needed.

## 6. Evidence and reproduction

Run the focused executable checks from the repository root:

    python -m pytest -q tests/test_obstructions.py

They use the actual `bml.model.CLASSIC` kernel. They check the four-car
transition on five square sizes; the HBK zero set against a complete free
orbit on every \(2\times2\) and \(3\times3\) board; the phase convention;
(8) on every jam in those domains; and equality for every
\(1\le k\le L/2\) on five even staircase sizes.
They exhaust every \(3\times3\) exterior of the specified length-two and
length-three runs, exercise larger arbitrary exteriors, distinguish TRAIN,
and check the exact initial-iid sum and bound (4) on the complete small domains.
The vacant-cut witness is replayed, its winding is checked, and its final
mixed blocker cycle is verified independently of the displayed matrix.

These are finite executable checks. The all-size queue statement separately
has its Lean proof, and the all-size four-car and counting statements have
the prose proofs above. Probability integration and analytic limits are not
claimed as Lean or Quint theorems. In particular, neither the obstruction
fixtures nor (11) supplies the missing late-defect estimate in (12).

## Sources and related records

- [HBK] G. Hertzberg Rabinovich, O. Biham and E. Katzav, *Structure and dynamics
  in the low-density phase of a two-dimensional cellular automaton model of
  traffic flow*, Physical Review E **113** (2026), 014127.
  [Primary full text, arXiv:2601.01180v2](https://arxiv.org/html/2601.01180v2);
  [published DOI](https://doi.org/10.1103/y7qy-6z9t).
  Equations (8), (11), Sections VI–VIII and Appendix B delimit the definition,
  numerical convergence evidence, proposed interpretation and proved zero-set
  invariance used here.
- [Fixed-density formation](2026-11-18-fixed-density-formation.md): early-time
  mixed-cycle bounds and the conditional invariant-safe-set inequality.
- [Probability reductions](2026-11-18-probabilistic-gridlock-bounds.md):
  nonempty gridlock, conserved populations and lanes, and the distinction
  between finite-time and eventual events.
- [Open questions and proof roadmap](2026-11-18-open-questions-and-proof-roadmap.md):
  the separate CLASSIC and TRAIN obligations.

[HBK]: https://arxiv.org/html/2601.01180v2
