# Probabilistic gridlock bounds for CLASSIC BML

**Research note — 18 November 2026.** This note proves several partial results
about random initial states on square tori. It does **not** prove a positive
critical density, sharpness of a transition, or convergence of the jam
probability at every fixed density. No novelty claim is made.

The results separate three issues: a deterministic certificate for capture,
the probability of forming that certificate, and the order of the time and
size limits. They strengthen the distinctions in the earlier
[freezing and nucleation note](2026-11-18-freezing-gridlock-nucleation.md).

**Proof status.** The accompanying Lean lane layer covers conservation of
the actual CLASSIC E-count in each row and N-count in each column, together
with equivalences between initial and later full E-rows, full N-columns,
and north-free strips. The event identity, mixed-cycle geometry, strip-crossing
argument, constructions, probability estimates, and asymptotic conclusions
below have mathematical prose proofs. The later
[profile note](2026-11-18-lane-profile-obstruction.md) generalizes the jammed
representative and connects it to a universal actual-kernel Lean construction;
the free-flow representative and probability conclusions remain prose results.
The [capacity note](2026-11-18-disjoint-strip-capacity.md) strengthens the
finite strip bound using several disjoint strips. Theorem 6a below sharpens
the asymptotic sparse window using the original strip estimate.
Consult the [formal coverage register](../../formal/README.md) for the exact
machine-checked statements and validation status. Finite exhaustive checks
can verify finite statements and detect mistakes; they do not prove the
large-size limits below.

## 1. Model, events, and the existing high-density theorem

Work on \(\mathbb Z_L^2\), with \(L\ge1\). Coordinates are \((x,y)\),
east is \(+x\), and north is \(+y\). A full round consists of a synchronous
E half-step followed by a synchronous N half-step. Under **CLASSIC**, a car
moves precisely when its destination is empty at the start of its half-step.
In particular, a full monochromatic lane is frozen. These are the rules in
[`bml/model.py`](../../bml/model.py); the repository's TRAIN rule is a different
dynamical system and is not used here.

Let \(F\) be the full-round map. The initial state has the product law

\[
\mu_{L,p}(E)=\mu_{L,p}(N)=p/2,\qquad
\mu_{L,p}(0)=1-p,
\]

independently at every site. Counts fluctuate under this law. Results for an
ensemble conditioned on exact counts require their own probability argument.

A **jam** is a nonempty configuration in which every car's next cell is
occupied. It remains unchanged forever. Define

\[
\tau_J(s)=\inf\{t\ge0:F^t(s)\text{ is a jam}\},\qquad
J_L=\{\tau_J<\infty\},\qquad q_L(p)=\mu_{L,p}(J_L).
\]

The infimum of the empty set is \(\infty\). The empty configuration is not
a jam. This convention is essential: otherwise several statements below
would already fail at \(p=0\).

Angel, Holroyd, and Martin prove that there is \(p_1\in(0,1)\) such that, for
every fixed \(p\ge p_1\), eventual fixation has probability tending to one
on \(m\times n\) tori as both dimensions diverge and
\(m/n\to a\in(0,\infty)\) [1, Theorem 2]. Consequently
\(q_L(p)\to1\) in that regime: the probability of an initially empty torus
vanishes. Their infinite-lattice theorem instead asserts that each car moves
only finitely often and each site eventually stabilizes. It does not give a
common finite stopping time for the infinite system [1, Theorem 1]. Their
N-then-E order maps to ours by interchanging coordinates and species, which
preserves the symmetric iid law. No numerical value of \(p_1\) is imported
here.

The 2026 study [2] characterizes free-flowing periodic states using a distance
\(D\), proves invariance once \(D=0\), and studies convergence through
numerical decay fits. It does not supply the missing fixed-positive-density
iid attraction or sharp-threshold theorem used nowhere in this note.

## 2. Mixed-cycle formation is exactly gridlock outside the ring event

A **direct blocker edge** goes from an occupied cell to the next cell in its
car's direction, provided that cell is occupied. A **mixed simple cycle** is
a directed cycle of distinct cells containing both E and N cars. Let

\[
M_L=\{\text{a mixed simple blocker cycle occurs at some full-round time}\},
\]

and let \(R_L\) be the event that the initial configuration contains a full
E-row or a full N-column.

### Lemma 1: permanence and capture

A direct blocker cycle is permanent. If it is mixed, it forces eventual
global gridlock.

**Proof.** Every E-car on the cycle has an occupied cycle destination during
the E half-step, so none moves. The N-cars then have occupied cycle
destinations too. Induction over half-steps proves permanence.

Lift the cycle's steps to \(\mathbb Z^2\). If there are \(a\) east steps
and \(b\) north steps, closure implies \(a=uL\), \(b=vL\) for
nonnegative integers \(u,v\). A mixed cycle has \(u,v\ge1\). Its east
steps traverse every column residue, and its north steps traverse every row
residue. The permanent core therefore meets every row and column.

Every E-car remains in its original row and cannot pass its row's permanent
obstacle. It makes at most \(L-1\) further moves. The same bound holds for
each N-car in its column. If there are \(n_E,n_N\) cars, at most
\((n_E+n_N)(L-1)\) individual moves remain. A full round with no individual
moves is already a jam; every round before that makes at least one move.
Thus a jam is reached within the same bound on subsequent full rounds.
Nonemptiness is conserved. ∎

Mixed cyclic blocking-path capture is already present in AHM's proof of
Theorem 2 [1, numbered arXiv p. 12]. Their paths include additional dependency
patterns. The direct-cycle argument above states the specialization needed
here, without a claim of priority.

### Proposition 2: the exact event identity

\[
\boxed{M_L=J_L\cap R_L^c.}
\]

**Proof.** Lemma 1 gives \(M_L\subseteq J_L\). A full initial E-row stays
full of the same E-cars forever. A mixed cycle must visit every row, but once
its forward traversal enters this row it stays there forever, following E
successors. Such a cycle cannot contain N-cars. A full initial N-column
excludes mixed cycles by the corresponding argument. Thus
\(M_L\subseteq R_L^c\).

Conversely, suppose \(J_L\) occurs and \(R_L\) does not. In the eventual
jam, follow successors from any occupied cell. The occupied set is finite and
successors remain occupied, so a cell repeats and produces a simple directed
cycle. If it were pure E, it would fill a row: successive east steps first
return after traversing all \(L\) columns. E-count in that row is conserved,
so the row was full of E-cars initially, contradicting \(R_L^c\). A pure
N-cycle similarly contradicts conservation of N-count in its column.
Therefore the cycle is mixed, proving \(M_L\). ∎

Conservation used here follows directly from the update: an E move changes
two cells in the same row, removing and inserting one E-car; N moves neither
create nor destroy E-cars. The N-column statement is symmetric. This proof
also explains why an initially full lane reflects any full lane found later.

### Corollary 3: a uniform probability comparison

For every \(L\ge1\) and \(p\in[0,1]\),

\[
\Pr(R_L)=2\left[1-\left(1-(p/2)^L\right)^L\right]
\]

and

\[
0\le q_L(p)-\Pr(M_L)
\le\Pr(R_L)\le2L(p/2)^L\le2L\,2^{-L}.
\]

**Proof.** Full E-row events are independent across the \(L\) rows, each
with probability \((p/2)^L\). Full N-column events have the same union
probability. The two unions are disjoint: an E-row and N-column would require
both species at their intersection. This proves the exact formula. The event
identity and a union bound give the inequalities. ∎

The final error tends to zero uniformly in \(p\), including sequences
\(p=p_L\). A limiting probability or threshold proved for one event would
therefore transfer to the other. The comparison supplies no formation
probability by itself.

## 3. An explicit sparse-density nonjamming bound

### Lemma 4: an empty strip obstructs every possible jam

Fix \(1\le k\le L\). Suppose some \(k\) consecutive columns contain no
N-cars, every row contains fewer than \(k\) E-cars, and no column is full of
N-cars. Then \(J_L\) is impossible.

**Proof.** The N-free columns stay N-free, and the row and column counts are
conserved. If a jam arose, extract a simple blocker cycle as in Proposition 2.
A pure E-cycle needs \(L\ge k\) E-cars in one row, and a pure N-cycle needs
a full N-column; both are excluded. A mixed cycle winds horizontally and
must cross the strip. Within its N-free columns the cycle can take only east
steps, so crossing requires \(k\) distinct E-cars in the same row. This
contradicts the row-count bound. The argument includes \(k=1\) and \(k=L\).
∎

### Proposition 5: a finite probability estimate

For every integer \(1\le k\le L\),

\[
\boxed{
q_L(p)\le
L\Pr\!\left[\operatorname{Bin}(L,p/2)\ge k\right]
+\left[1-(1-p/2)^{Lk}\right]^{\lfloor L/k\rfloor}
+L(p/2)^L.}
\]

**Proof.** Union bound the probability that some E-row count is at least
\(k\), giving the first term. Partition as many columns as possible into
\(\lfloor L/k\rfloor\) fixed disjoint blocks of width \(k\). Each block
is N-free with probability \((1-p/2)^{Lk}\), independently across these
blocks. The middle term is exactly the probability that none of these chosen
blocks is N-free; it bounds the probability that no suitable strip exists
anywhere. The last term bounds the chance of a full N-column. Outside these
three bad events Lemma 4 excludes gridlock. Independence between the three
bad events is neither asserted nor needed. ∎

### Theorem 6: a shrinking-density regime

For every fixed \(0<\varepsilon<2\),

\[
\boxed{
p_L L\le(2-\varepsilon)\log\log L\text{ for all sufficiently large }L
\quad\Longrightarrow\quad q_L(p_L)\longrightarrow0.}
\]

All logarithms are natural.

**Proof.** Put \(\eta=\varepsilon/2\),
\(\lambda_L=p_L L/2\le(1-\eta)\log\log L\), and choose a constant
\(1<a<1/(1-\eta)\). Set

\[
k_L=\left\lceil a\frac{\log L}{\log\log L}\right\rceil.
\]

Eventually \(1\le k_L\le L\) and \(k_L>\lambda_L\). For a binomial
variable of mean \(\lambda\), the exponential-moment estimate
\(\mathbb E e^{tX}\le\exp[\lambda(e^t-1)]\), with
\(t=\log(k/\lambda)>0\), gives
\(\Pr(X\ge k)\le(e\lambda/k)^k\). If \(\lambda=0\), the relevant
tail is zero. Otherwise

\[
\log\left[L(e\lambda_L/k_L)^{k_L}\right]
\le(1-a+o(1))\log L\longrightarrow-\infty,
\]

because
\(\log(e\lambda_L/k_L)\le-\log\log L+
2\log\log\log L+O(1)\). This controls the first term.

For the second term let \(\theta_L=(1-\lambda_L/L)^{Lk_L}\) and
\(r_L=\lfloor L/k_L\rfloor\). Taylor's estimate for \(\log(1-z)\)
at \(z=0\) gives

\[
\log\theta_L=-\lambda_L k_L+
O(\lambda_L^2 k_L/L),\qquad
\lambda_L^2 k_L/L\longrightarrow0.
\]

It follows that
\(\theta_L\ge L^{-a(1-\eta)-o(1)}\), and hence

\[
r_L\theta_L\ge L^{1-a(1-\eta)-o(1)}\longrightarrow\infty.
\]

Thus \((1-\theta_L)^{r_L}\le e^{-r_L\theta_L}\to0\). Finally,
\(L(p_L/2)^L=L(\lambda_L/L)^L\to0\). Apply Proposition 5. ∎

This is a nonjamming theorem, not a proof of eventual perfect free flow.
Its allowed densities tend to zero. It therefore establishes no positive
lower bound for a critical density.

### Theorem 6a: an additive improvement of the sparse window

The same finite strip estimate gives the stronger implication

\[
\boxed{
p_L L\le 2\log\log L-4\log\log\log L-2
\text{ for all sufficiently large }L
\quad\Longrightarrow\quad q_L(p_L)\longrightarrow0.}
\]

All logarithms are natural, and the displayed upper bound is positive for
sufficiently large \(L\). No fixed positive subtraction from its right-hand
side is required.

**Proof.** Put

\[
t=\log L,\quad s=\log t,\quad g=\log s,\quad
\lambda=p_L L/2,\quad
\Lambda=s-2g-1,\quad \beta=g/s,\quad d=\Lambda+\beta,
\]

and choose the integer strip width

\[
k=\left\lceil\frac{t}{d}\right\rceil.
\]

The hypothesis gives \(0\le\lambda\le\Lambda\). Eventually
\(s/2\le\Lambda<d<s\), \(1\le k\le L\), and
\(k>e\Lambda\). We also have \(k\le t/d+1\). If \(\lambda=0\),
the initial state is empty almost surely and \(q_L(0)=0\). It therefore
suffices to give uniform bounds on the remaining indices, where
\(\lambda>0\).

For the first term of Proposition 5, the binomial exponential-moment estimate
used in Theorem 6 gives \(\Pr[\operatorname{Bin}(L,\lambda/L)\ge k]
\le(e\lambda/k)^k\). Since \(k\ge t/d\) and
\(\log[t/(e\Lambda d)]>0\) eventually,

\[
\begin{aligned}
\log\left[L(e\lambda/k)^k\right]
&\le t-\frac{t}{d}\log\frac{t}{e\Lambda d}\\
&=\frac{t}{d}\left[d-s+1+\log\Lambda+\log d\right]\\
&=\frac{t}{d}\left[\beta+\log(\Lambda/s)+\log(d/s)\right].
\end{aligned}
\]

Use \(\log(1-x)\le-x\) on
\(\Lambda/s=1-(2g+1)/s\) and
\(d/s=1-(2g+1-\beta)/s\). For sufficiently large \(s>1\), both
arguments belong to \((0,1)\), and the bracket is at most

\[
\beta-\frac{4g+2-\beta}{s}
=-\frac{3g+2}{s}+\frac{g}{s^2}
\le-\frac{2g}{s}.
\]

Thus the first term is at most
\(\exp[-2gt/(sd)]\le\exp[-2gt/s^2]\), which tends to zero.

For the empty-strip term, set
\(n=\lfloor L/k\rfloor\) and
\(\theta=(1-\lambda/L)^{Lk}\). Eventually \(L/k\ge2\), so
\(n\ge L/(2k)\). Also \(\lambda/L\le1/2\), and
\(\log(1-z)\ge-z-2z^2\) for \(0\le z\le1/2\) gives

\[
\log\theta\ge-\Lambda k-e_L,
\qquad e_L=2\Lambda^2k/L\longrightarrow0.
\]

The error tends to zero because \(\Lambda\le s\) and
\(k\le2t/s+1\), so \(e_L=O(st/L+s^2/L)\). Keeping the ceiling and
floor errors explicitly,

\[
\begin{aligned}
\log(n\theta)
&\ge t-\log(2k)-\Lambda k-e_L\\
&\ge\frac{\beta t}{d}-\log(2k)-\Lambda-e_L\\
&\ge\frac{gt}{s^2}-O(s)\longrightarrow\infty.
\end{aligned}
\]

Here \(\log k=O(s)\), and \(gt/s^2\) dominates \(s\), since
\(t=e^s\). Therefore
\((1-\theta)^n\le\exp(-n\theta)\to0\).

Finally, the full-column term is bounded by
\(L(\Lambda/L)^L\to0\), because \(\Lambda=O(\log\log L)\).
All three terms in Proposition 5 vanish. The bounds depend only on the
displayed envelope \(\Lambda\), so indices with smaller positive
\(\lambda\), together with the already handled zero-density indices,
give the claimed convergence for the full sequence. ∎

Theorem 6 remains a simpler leading-order consequence: for every fixed
\(\varepsilon>0\), eventually
\((2-\varepsilon)\log\log L\le
2\log\log L-4\log\log\log L-2\).
The improved envelope divided by \(L\) still tends to zero. This is a
stronger shrinking-density nonjamming result, with no implication of a
nonjamming phase at any fixed positive density or of eventual perfect free
flow.

## 4. Conserved lane profiles can contain both outcomes

Let \(r_y\) be the number of E-cars in row \(y\), and \(c_x\) the
number of N-cars in column \(x\). A **lane profile** specifies both vectors.
These counts are conserved, but they do not generally determine the outcome.

The subsequent [profile note](2026-11-18-lane-profile-obstruction.md) proves
that a jammed representative exists for every positive profile with
\(\max r+\max c\le L\), and that such profiles occur with high probability
at every fixed \(0<p<1\). The two-representative result below retains its
stronger hypotheses for the free-flow construction.

### Proposition 7: two states for every profile in a specified range

Let \(L\ge3\), \(K=\lfloor L/3\rfloor\), and suppose

\[
1\le r_y\le K\quad\text{for every row},\qquad
1\le c_x\le K\quad\text{for every column}.
\]

There is a jammed configuration with this profile, and there is a configuration
with this same profile in which every car moves on every eligible half-step
forever.

**Jammed construction and proof.** In row \(y\), put E-cars at
\((y-j,y)\) for \(0\le j<r_y\). In column \(x\), put N-cars at
\((x,x-i)\) for \(1\le i\le c_x\), using coordinates modulo \(L\).
An overlap would require \(i+j\equiv0\pmod L\), whereas
\(1\le i+j\le2K-1<L\). Therefore the placements are disjoint and give
the requested counts.

Each E with \(j>0\) is blocked by the E with index \(j-1\). The front E
at \((y,y)\) is blocked by the \(i=1\) N in column \(y+1\), which is
present since every \(c_x\ge1\). Each N with \(i>1\) is blocked by the
N with index \(i-1\). The front N at \((x,x-1)\) is blocked by the E at
\((x,x)\), present since every \(r_y\ge1\). All cars are blocked.

**Free-flow construction and proof.** Use the phase
\(\phi(x,y)=x+y\pmod L\) and sets

\[
A=\{1,4,\ldots,3K-2\},\qquad
B=\{0,3,\ldots,3K-3\}.
\]

In each row choose exactly \(r_y\) sites whose phases lie in \(A\); in
each column choose exactly \(c_x\) sites whose phases lie in \(B\).
There are \(K\) choices in each lane, and \(A\cap B=\varnothing\), so
the choices realize the profile without overlap. In \(\mathbb Z_L\),

\[
(A+1)\cap(A\cup B)=\varnothing,
\qquad
(B+1)\cap\bigl(B\cup(A+1)\bigr)=\varnothing.
\]

These identities hold because the displayed representatives and their
one-step shifts stay in \(0,\ldots,3K-1\subseteq0,\ldots,L-1\), and
\(B+1=A\). The first identity lets every E-car move. The second then lets
every N-car move. At the end of the round both phase supports have shifted
by one. A common translation preserves both disjointness identities, so
induction proves free flow forever. ∎

### Corollary 8: typical profiles at fixed density

For each fixed \(0<p<2/3\), an iid initial state has, with probability
tending to one, a lane profile containing both a jammed and a free-flowing
representative.

**Proof.** Write \(u=p/2\in(0,1/3)\). Each of the \(2L\) lane counts
has distribution \(\operatorname{Bin}(L,u)\). Its probability of zero is
\((1-u)^L\). To bound the upper tail, choose a fixed
\(u<v<1/3\). Eventually \(K/L>v\). For a sufficiently small fixed
\(t>0\),
\(\log(1-u+ue^t)-tv<0\), since its derivative at zero is \(u-v<0\).
The exponential-moment bound therefore gives
\(\Pr(X>K)\le\Pr(X\ge vL)\le e^{-bL}\) for some \(b>0\).
A union bound over the \(2L\) lanes tends to zero. Apply Proposition 7. ∎

This is an existence statement within typical invariant classes. It gives
no positive lower bound on the conditional probability of either basin.
One specially constructed representative can have a vanishing share of its
class. The result consequently does not contradict a probabilistic phase
transition.

## 5. Finite-time isolation and limits that do not commute

### Proposition 9: an explicit bound on early global gridlock

Let \(T\ge0\) be an integer with \(T+2\le L\). Define

\[
A_T=\frac{(T+1)(T+2)}2,\qquad
K_{L,T}=\left\lfloor\frac L{T+2}\right\rfloor
          \left\lfloor\frac L{T+1}\right\rfloor.
\]

Then

\[
\boxed{
\Pr_p(\tau_J\le T)
\le\left[1-\frac p2(1-p)^{A_T}\right]^{K_{L,T}}.}
\]

**Proof.** Consider the initial event consisting of an E-car at \((0,0)\)
and empty cells in the triangle

\[
S_T=\{(x,y):1\le x\le T+1,\;-(x-1)\le y\le0\}.
\]

Its \(A_T\) cells are distinct and do not include the seed. We claim that
the seed moves during rounds \(0,1,\ldots,T\). Inductively, at the start
of round \(t\le T\) it is at \((t,0)\), with target \((t+1,0)\).
An E-car occupying that target could have originated only at row-zero
positions \(x\in[1,t+1]\), since each E-car has made at most \(t\) moves.
An N-car there could have originated only in column \(t+1\), at
\(y\in[-t,0]\), since each N-car has made at most \(t\) moves. All such
initial sites belong to \(S_T\) and are empty. These statements are modulo
\(L\); the specified ranges have length below \(L\), so they list every
possible origin without a missing wraparound case. Cars cannot change
species or move faster than one step per round. The target is therefore
empty, proving the induction. A move in round \(T\) excludes
\(\tau_J\le T\), because a jam is absorbing.

The event has probability \(w_T=(p/2)(1-p)^{A_T}\) and fits in a rectangle
of width \(T+2\) and height \(T+1\). Pack \(K_{L,T}\) disjoint such
rectangles into the torus, translating the event into each. Their initial
site sets are disjoint, so the events are independent. Early gridlock
requires all of them to fail, giving the bound. ∎

### Corollary 10: a growing observation time

For fixed \(0<p<1\) and

\[
0<c<\frac2{\sqrt{-\log(1-p)}},\qquad
T_L=\lfloor c\sqrt{\log L}\rfloor,
\]

we have \(\Pr_p(\tau_J\le T_L)\to0\).

**Proof.** Put \(b=-\log(1-p)>0\). Then
\(A_{T_L}=(c^2/2)\log L+O(\sqrt{\log L})\), so
\(w_{T_L}=L^{-bc^2/2+o(1)}\). Also
\(K_{L,T_L}=L^{2+o(1)}\). The strict condition on \(c\) gives
\(K_{L,T_L}w_{T_L}\to\infty\), and Proposition 9 is at most
\(\exp[-K_{L,T_L}w_{T_L}]\to0\). ∎

This lower bound on the time of gridlock allows \(\tau_J=\infty\).
It is not a statement that every trajectory eventually jams, nor a bound
on the time to reach free flow or an intermediate periodic orbit.

For any fixed \(p\in[p_1,1)\) in AHM's high-density regime, let
\(Q_L(T)=\Pr_p(\tau_J\le T)\). At each fixed \(L\), increasing the
time limit exhausts the eventual-jam event, so
\(\lim_{T\to\infty}Q_L(T)=q_L(p)\). AHM and Proposition 9 now give
the explicit noncommutation

\[
\boxed{
\lim_{L\to\infty}\lim_{T\to\infty}Q_L(T)=1,
\qquad
\lim_{T\to\infty}\lim_{L\to\infty}Q_L(T)=0.}
\]

The second identity follows because every fixed finite \(T\) has
\(w_T>0\) and \(K_{L,T}\to\infty\). Thus even a regime with a rigorous
eventual-jam theorem can look unjammed when a fixed cutoff precedes the
large-size limit.

## 6. Non-monotonicity: configurations and probabilities are different

### A square counterexample outside the exceptional ring event

Use \(0,E,N=0,1,2\), with rows in increasing \(y\). Start from

```text
[[1,2,2,1],
 [2,1,1,0],
 [1,0,2,1],
 [2,1,1,0]]
```

and add one N-car at \((x,y)=(1,2)\). Neither initial state has a full
E-row or a full N-column. The original has 13 cars and jams at round 3;
the new state has 14 cars and never jams.

Here is a complete finite orbit certificate. Each entry lists the four rows
separated by `/`; the move count is for the next full round. Applying the
two explicitly defined half-steps to each entry gives the next entry.

| Original round | State | Next moves |
| --- | --- | ---: |
| 0 | `1221 / 2110 / 1021 / 2110` | 6 |
| 1 | `1201 / 0121 / 2101 / 2121` | 3 |
| 2 | `1221 / 1120 / 2011 / 2101` | 1 |
| 3 | `1221 / 1120 / 2011 / 2011` | 0 |

At round 2 a mixed cycle already follows the coordinates
\((0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(0,2),(0,3)\), then closes.
The round-3 state has every destination occupied.

| Round after insertion | State | Next moves |
| --- | --- | ---: |
| 0 | `1221 / 2110 / 1221 / 2110` | 4 |
| 1 | `1201 / 2121 / 1201 / 2121` | 2 |
| 2 | `1221 / 2101 / 1221 / 2101` | 4 |
| 3 | `1021 / 2211 / 1021 / 2211` | 4 |
| 4 | `2121 / 0211 / 2121 / 0211` | 2 |
| 5 | `2121 / 1210 / 2121 / 1210` | 4 |
| 6 | `2101 / 1221 / 2101 / 1221` | 4 |
| 7 | `2211 / 1021 / 2211 / 1021` | 4 |
| 8 | `0211 / 2121 / 0211 / 2121` | 2 |
| 9 | `1210 / 2121 / 1210 / 2121` | 4 |

The next state equals round 2. Determinism therefore certifies an occupancy
cycle of period 8 after a transient of 2. The cycle has 28 individual moves,
so it cannot be a jam; its average moves per car per full round are
\(28/(14\cdot8)=1/4\). Lemma 1 also excludes a mixed cycle anywhere on
this infinite trajectory. No claim about the movement of each particular
car identity is needed for this certificate.

This disproves configurationwise increasingness of both \(J_L\) and
\(M_L\), even outside \(R_L\). It does **not** disprove monotonicity of
the iid average \(q_L(p)\), which remains a separate question.

### A finite iid probability need not be increasing for the mixed event

The complete finite-graph enumeration in
[`bml/probability.py`](../../bml/probability.py), with regression checks in
[`tests/test_probability.py`](../../tests/test_probability.py), gives the
following numbers of initial states in \(M_3\), among
\(\binom9n2^n\) states with \(n\) cars:

| Number of cars \(n\) | States in \(M_3\) | Fraction \(b_n\) |
| --- | ---: | ---: |
| 0–5 | 0 | 0 |
| 6 | 384 | \(1/14\) |
| 7 | 1,872 | \(13/32\) |
| 8 | 1,062 | \(59/128\) |
| 9 | 174 | \(87/256\) |

These are finite enumeration data, not an asymptotic theorem. Given those
counts, the iid probability is exactly the Bernstein polynomial

\[
m_3(p)=\sum_{n=0}^9 b_n\binom9n p^n(1-p)^{9-n}.
\]

Differentiating at \(p=1\) leaves only the last two coefficients:

\[
m_3'(1)=9(b_9-b_8)=-279/256<0.
\]

Thus even iid mixed-cycle probability decreases for some densities near one
at this finite size. Replacing \(J_L\) by \(M_L\) does not automatically
produce an increasing event or an increasing finite iid probability. The
uniform comparison in Corollary 3 remains valid; it is an asymptotic
approximation and does not prove monotonicity of either family.

## 7. Exact remaining obligations for a critical-density theorem

One can state the target without assuming configurationwise monotonicity or
existence of \(\lim_L q_L(p)\) at every density. Define

\[
p_- = \sup\{a\in[0,1]:
       \forall p\in(0,a),\ q_L(p)\to0\},
\]

\[
p_+ = \inf\{a\in[0,1]:
       \forall p\in(a,1],\ q_L(p)\to1\}.
\]

The defining sets are nonempty: \(a=0\) makes the first requirement
vacuous, and \(a=1\) makes the second vacuous. AHM puts \(p_1\) in the
second set. Moreover

\[
0\le p_-\le p_+\le p_1<1.
\]

To prove the middle inequality, suppose a lower interval endpoint from the
first set exceeded an upper interval endpoint from the second. A density
strictly between them would have limiting jam probability both zero and
one, a contradiction. Taking supremum and infimum gives the result.

The equality \(p_-=p_+=p_c\) would establish a threshold: for any
\(p<p_c\), some endpoint in the first set exceeds \(p\), and for any
\(p>p_c\), some endpoint in the second set is below \(p\). A **positive**
critical density additionally requires \(p_->0\). Nothing in these
definitions prescribes behavior at \(p=p_c\). Eventual perfect free flow
below \(p_c\), a limiting velocity jump, and a critical-window scale are
further claims requiring further proofs.

The new sparse theorem does not prove \(p_->0\), because its densities
vanish. Its mechanism also cannot be extended to fixed \(p>0\) simply by
optimizing \(k\): an N-free column has probability \((1-p/2)^L\), so
the probability of any N-free column is at most
\(L(1-p/2)^L\to0\). Every N-free strip requires such a column.

Likewise, the lane-profile theorem does not estimate basin probabilities,
and the finite-time theorem supplies a delay rather than eternal avoidance
of capture. A successful fixed-density argument must control formation or
avoidance of a winding capture structure over times increasing with \(L\).
The event identity identifies precisely which formation event suffices,
up to a uniformly negligible exception. It does not estimate that event's
probability. Even a proof of monotonicity of all the \(q_L\) would still
leave convergence with size, positivity, and sharpness to establish.

## References and evidence boundaries

1. Omer Angel, Alexander E. Holroyd, and James B. Martin, **The Jammed Phase
   of the Biham–Middleton–Levine Traffic Model**, Electronic Communications
   in Probability 10 (2005), 167–178.
   [DOI](https://doi.org/10.1214/ECP.v10-1148);
   [arXiv:math/0504001v2](https://arxiv.org/abs/math/0504001v2);
   [full paper](https://arxiv.org/pdf/math/0504001v2).
   Theorems 1–2 give the high-density results. The mixed cyclic blocking-path
   capture observation is in the proof of Theorem 2, numbered arXiv p. 12.

2. Gilad Hertzberg Rabinovich, Ofer Biham, and Eytan Katzav, **Structure and
   dynamics in the low-density phase of a two-dimensional cellular automaton
   model of traffic flow**, Physical Review E 113 (2026), 014127.
   [DOI](https://doi.org/10.1103/y7qy-6z9t);
   [arXiv:2601.01180v2](https://arxiv.org/abs/2601.01180v2);
   [full text](https://arxiv.org/html/2601.01180v2).
   Section VI studies decay by numerical fits; Appendix B proves persistence
   of the zero-distance free-flowing set. Those are distinct from an iid
   fixed-density basin-probability theorem.

The constructions and probability bounds in this note are proved above.
The explicit orbit table is a finite reproducible certificate. The
\(3\times3\) coefficient table is an exact finite enumeration result whose
scope is that lattice only. Reproduce the advertised finite domains, exact
iid probabilities, and separate verifier controls using
[`scripts/check_probability.py`](../../scripts/check_probability.py):

```bash
python scripts/check_probability.py --report .artifacts/probability-census.json
```

The report binds its results to source hashes before and after the run.
Its all-width census checks vectorized strip predicates; it records individual
public certificate-verifier controls separately. Repository validation
receipts and the formal coverage register, rather than this prose note,
identify which code and formal statements were checked in a particular run.
