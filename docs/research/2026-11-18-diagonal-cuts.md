# Diagonal cuts bound the time to the first CLASSIC mixed cycle

This continues the [one-round formation calculation](2026-11-18-fixed-density-formation.md).
On a square torus the earlier ancestor count requires \(p(T+1)<1\) at a fixed time to give
decay with side length. A different bound applies for every fixed \(0<p<1\)
and through \(T\) of order \(\sqrt{\log L}\). It controls formation of the
mixed blocker cycle itself. The probability of formation after this time
remains the obstruction to a positive critical-density theorem.
The [guarded-queue bound](2026-11-18-protected-queue-gridlock-delay.md) gives a
logarithmic delay for complete gridlock, which can occur after the first
mixed cycle forms.

## Model and bound

Use the CLASSIC east-then-north round \(F\) on \(\mathbb Z_L^2\). The initial
cells are independent, taking values \(0,E,N\) with probabilities
\(1-p,p/2,p/2\). Let \(A_T\) be the event that there is a simple mixed
direct-blocker cycle in \(F^T(s)\). At a snapshot an E or N car points to
its immediate forward cell. A path follows this arrow while the next site
is occupied. A cycle with both species persists and captures the board, so
\(A_T\) is also the event that such a cycle has appeared by round \(T\).
The [event identity](2026-11-18-probabilistic-gridlock-bounds.md) relates its
eventual occurrence to gridlock outside the initial full-lane event.

For \(L\ge2\) and integer \(T\ge0\), set

\[
 b=3T+1,\qquad K=\max\left\{0,\left\lfloor\frac{L-2T-1}{b}\right\rfloor\right\},
\qquad
w_T(p)=(1-p)^{(T+1)(5T+2)/2}(1-p/2)^{T(T+1)}.
\]

Then

\[
\boxed{\Pr_p(A_T)\le \min\left\{1,\frac{Lp}{2}(1-w_T(p))^K\right\}.}
\tag{1}
\]

The proof works with the initial law throughout. It uses the spatial order
of sites exposed by one deterministic path and permits arbitrary correlations
at time \(T\).

## Exploring one blocker path

Write \(H(x,y)=x+y\) for the height on the integer lift. Both directions
increase \(H\) by one. Fix a starting site with lift \(z_0\), and follow the
arrows in the snapshot \(F^T(s)\), lifting the path to \(\mathbb Z^2\). To learn
the color at a queried vertex \(z\), reveal the initial cells in the box
\(z+[-T,T]^2\), projecting every site back to the torus. Indeed, one east
half-step reads the site and its horizontal neighbors, and one north
half-step reads three vertically consecutive results of the east phase.
Induction gives the radius \(T\) box for \(T\) rounds. Query sets and path
directions are determined from previously read values. For a given transcript
of this procedure, the unqueried initial cells still have their original
independent laws. Each particular transcript imposes only the recorded values
at recorded sites, since those values determine all query addresses.

Suppose the path survives through vertex \(z\) at index \(j\), whose color is
already known. All read sites have lifted heights in
\([H(z_0)-2T,H(z)+2T]\). Let \(d\) be the unit step dictated by that color. The
possible vertices after another \(b\) edges lie in the segment

\[
S=\{z+d+(i,b-1-i) : 0\le i<b\}.
\]

For \(q\in S\), any E-car at \(q\) in the snapshot must originate at
\(q-(r,0)\) for some \(0\le r\le T\). An N-car must originate at
\(q-(0,r)\) for such an \(r\). This follows from one-cell transport per
round, preservation of species, and the invariance of its lane. Demand that
each possible E origin contain no E initially and each possible N origin
contain no N initially. The demand makes the entire segment empty at
time \(T\), regardless of other cells, so the path cannot survive through
index \(j+b\).

These origin sites have lifted heights between \(H(z)+b-T\) and \(H(z)+b\).
The lower endpoint is \(H(z)+2T+1\), strictly above the read sites. If
\(j+b+2T<L\), both sets of heights lie in one interval of integer length
less than \(L\). Thus their height residues are disjoint on the square
torus. This is where the bound on \(K\) enters. With at least one admissible
trial, \(L\ge 5T+2\). At a given origin height all candidate sites occupy
an interval of at most \(b+T<L\) consecutive horizontal coordinates, so
the projections at that height are distinct as well.

At height \(H(z)+b-r\) the horizontal ranges of the E and N origins, relative
to \(z+d\), are \([-r,b-1-r]\) and \([0,b-1]\) respectively. Exactly
\(b-r\) sites must forbid both species and \(2r\) must forbid just one. Hence
the counts over the entire segment are

\[
 \sum_{r=0}^T(b-r)=\frac{(T+1)(5T+2)}2,
 \qquad \sum_{r=0}^T 2r=T(T+1).
\]

The cut demands have conditional probability exactly \(w_T(p)\) for every
surviving transcript. The next probe need not read those cells in advance.
Continue to follow the path, revealing a stencil when it is needed. The
same argument applies at indices \(j=0,b,\ldots,(K-1)b\). Iterated
conditioning gives a factor at most \(1-w_T(p)\) per trial, even though the
probes follow an adaptive path. Initial translation invariance and conserved
total population give \(\Pr_p(F^T(s)(z_0)\ne0)=p\). Therefore the probability
of surviving from a particular root through index \(Kb\) is at most
\(p(1-w_T(p))^K\). When \(K=0\), this is the marginal statement alone.

## From paths to winding cycles

Use the \(L\) roots with \(H=0\bmod L\). A simple mixed cycle winds positively
in both directions and has length \((a+c)L\) with \(a,c\ge1\). It therefore
visits the root layer at least twice at distinct vertices. The occupied paths
from those vertices survive through index \(Kb<L\) whenever \(K>0\). If
\(K=0\) the two vertices are occupied. Markov's inequality on the number of
surviving roots gives (1).

On the infinite lattice, the argument has no wraparound restriction. At each
fixed \(T\), the length of an occupied direct path from a specified root has
an exponential tail from the same conditional probes. In particular, for
\(p<1\) there are almost surely no infinite direct paths at any finite
round. Angel–Holroyd–Martin's high-density theorem uses a graph of blocking
dependencies that also includes replacements by cars from another lane.
Its blocking paths can exist initially while our finite-time estimate holds
for direct paths. [Angel–Holroyd–Martin, Sections 2–3](https://arxiv.org/pdf/math/0504001v2).

## A growing time horizon at fixed density

For \(0<p<1\) define

\[
 C(p)=\tfrac52\log\frac1{1-p}+\log\frac1{1-p/2}.
\]

Choose \(0<c<C(p)^{-1/2}\) and \(T_L=\lfloor c\sqrt{\log L}\rfloor\). Then
\(w_{T_L}(p)=L^{-C(p)c^2+o(1)}\) and \(K=L^{1+o(1)}\), so

\[
 \Pr_p(A_{T_L})\le \frac{Lp}{2}\exp[-K w_{T_L}(p)]\longrightarrow0.
\tag{2}
\]

The same conclusion holds uniformly for \(0\le p\le p_0<1\) if
\(c<C(p_0)^{-1/2}\), since \(w_T(p)\) decreases in \(p\). No ordering of
the actual events in density is needed. The sufficient condition behind (2)
is \(K w_T(p)-\log L\to+\infty\).

Write \(\tau_M=\inf\{T:A_T\text{ occurs}\}\) with \(\inf\varnothing=\infty\).
The remaining event is explicit:

\[
 q_L(p)\le 2L(p/2)^L+\Pr_p(A_{T_L})+\Pr_p(T_L<\tau_M<\infty).
\tag{3}
\]

In the fixed high-density regime of Angel–Holroyd–Martin with \(p<1\), the
last term tends to one by their torus theorem, the full-lane comparison, and
(2). To establish a nonjamming interval, a further estimate must show that
this term tends to zero at some range of small fixed densities. [Angel–Holroyd–Martin, Theorem 2](https://arxiv.org/pdf/math/0504001v2).

### A tagged formulation of the late event

Let \(D_T=\{T<\tau_M<\infty\}\), let \(O\) be initial occupation of one
specified site, and let \(R\) be the initial full-lane event. On \(O\), write
\(X\) for eventual stopping of the car originally at that site. The
tagged fixation theorem gives, on \(O\cap R^c\), equivalence between \(X\)
and eventual global gridlock. Combining that theorem with the mixed-cycle
identity yields

\[
 \Pr_p(D_T\mid O)=\Pr_p(X, R^c, A_T^c\mid O).
\]

The left side samples an initially occupied site and so weights states by
their population. With \(N\) the initial number of cars, translation symmetry
implies \(\Pr_p(D_T\mid O)=\mathbb E[N\mathbf1_{D_T}]/(pL^2)\) for \(p>0\).
Under the binomial law of \(N\), Cauchy–Schwarz gives

\[
 \left|\Pr_p(D_T\mid O)-\Pr_p(D_T)\right|
 \le\sqrt{\frac{(1-p)\Pr_p(D_T)(1-\Pr_p(D_T))}{pL^2}}
 \le\frac{1}{2L}\sqrt{\frac{1-p}{p}}.
\]

Thus a vanishing probability of eventual stopping for that initial car on
\(R^c\cap A_{T_L}^c\) would control the late term at fixed density. At the
horizon in (2), this conditioning excludes a vanishing fraction of boards
even given \(O\). The estimate still requires information on all future
motion of the tag, as a long wait can occur without fixation.
[Tagged fixation and global gridlock](2026-11-18-tagged-fixation-and-gridlock.md).

## Initial queues delay full movement

The existing Lean theorem `torus_eastRun_delay` says that an initial row
of \(T+2\) consecutive E-cars leaves its rear car blocked in round \(T\).
Counting disjoint runs for \(T+2\le L\) gives the following bound from
equation (4) of the [relaxation note](2026-11-18-relaxation-obstructions.md).

\[
 \Pr_p(\text{every car moves in the round starting at }T)
 \le \left(1-(p/2)^{T+2}\right)^{L\lfloor L/(T+2)\rfloor}.
\tag{4}
\]

At fixed \(p>0\) this tends to zero even at \(T=\lfloor a\log L\rfloor\) for
any \(0<a<2/\log(2/p)\). In particular (2) and (4) imply that, at the
diagonal-cut horizon, the snapshot typically has neither a mixed core nor
full movement. An argument using an invariant set entered at that horizon
must cover configurations with queues. Perfect free flow alone cannot
supply the required mass.

## Verification

`BML/Locality.lean` proves box dependence for the actual CLASSIC torus kernel,
disjoint projections for lifted height gaps strictly between zero and \(L\),
and emptiness from excluding the species' initial origins. The conditional
probability, winding count, and limit arguments above are mathematical proofs
in prose.

`tests/test_diagonal_cuts.py` embeds all \(3^9\) one-round stencils across a
torus seam and compares two exterior completions. It exhausts the \(3^9\)
assignments of a one-round cut in each direction and verifies that the four
admissible assignments clear its endpoints under three exterior completions.
The tests also enumerate finite candidate origin sets against every admissible
checkpoint in seven geometries, check an explicit wraparound collision beyond
the proved range, and compare exact probabilities on the complete 2x2 and
3x3 initial domains at \(T=0\). Longer-time controls exercise cuts in the
production kernel. These checks validate local and finite claims.

```sh
python -m pytest -q tests/test_diagonal_cuts.py
cd formal/lean
lake build BML
lake env lean Audit.lean
```
