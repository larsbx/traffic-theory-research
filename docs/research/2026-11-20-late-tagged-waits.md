# Late mixed-cycle formation and tagged waits in CLASSIC BML

A smaller guarded probe excludes first formation through a longer
logarithmic window, including part of the late event left by the previous
initial-law bounds. A finite tag wait also gives an exact test of whether a
tag will move again. The resulting conditional lap formula identifies the
estimate still needed beyond the improved cutoff.
[Diagonal cuts](2026-11-18-diagonal-cuts.md) ·
[Guarded barriers](2026-11-19-guarded-barrier-formation.md).

Use the CLASSIC east-then-north round map \(F\) on the square torus of side
\(L\ge2\). The initial cell law is \((1-p,p/2,p/2)\) for vacant, E, and N.
Let \(A_T=\{\tau_M\le T\}\), where \(\tau_M\) is the first full-round snapshot
with a mixed direct-blocker cycle and is infinity when none appears. Such
cycles persist. Let \(R\) denote an initial full monochromatic lane, \(O\)
occupation of the tag's initial site, and \(X\) eventual fixation of that
original tag. On \(O\cap R^c\), \(X\) is equivalent to eventual mixed-cycle
formation. [Tagged fixation](2026-11-18-tagged-fixation-and-gridlock.md) ·
[Mixed-cycle event identity](2026-11-18-probabilistic-gridlock-bounds.md).

## A smaller fresh guarded probe

At time \(T\ge1\), explore a snapshot's direct blocker path from a lifted
root \(z_0\) by revealing the radius-\(T\) initial box at each queried vertex.
Suppose the path is occupied at index \(j\) with lift \(z=(x,y)\) and known
step \(d\in\{(1,0),(0,1)\}\). Both coordinates along the path are
nondecreasing, so every exposed site has a lift in

\[
 [z_{0,x}-T,x+T]\times[z_{0,y}-T,y+T].
\]

Place the guarded L with southwest corner \(z+d\) and northeast corner
\((X,Y)=(x+T+1,y+T+1)\). Its horizontal leg is above the entire revealed
rectangle, its vertical leg is to the right, and its shifted guard is
above the rectangle. The extended N queue and its top hole are also to
the right. The two wall lengths sum to \(2T+1\). With the extra main N
queue and its shifted guard, the initial prescription specifies exactly
\(4T+1\) cars of prescribed species and one vacant site.

On the lift the prescription is disjoint from the revealed rectangle.
The coordinate spans of their union are at most \(j+2T+1\) and
\(j+3T+1\), since each coordinate has advanced at most \(j\) from the root.
When \(j+3T+1<L\), reduction modulo \(L\) is injective on the union. This
proves that the footprint uses distinct, unqueried initial sites even at
a seam. The deterministic guarded-barrier result supplies both walls and
the vacancy at time \(T\). Starting at \(z+d\), any direct path that reaches
either wall is directed along it to the vacant corner. The path stops by
index \(j+2T+2\).

Conditional on a surviving path transcript, the unrevealed initial cells
have their original independent law. The transcript is determined by the
values at its adaptively chosen query addresses. The new footprint, chosen
using the known step \(d\), has conditional weight

\[
 \delta=(1-p)(p/2)^{4T+1}.
\]

Write \(s=2T+2\) and \(K=\max(0,\lfloor (L-T)/s\rfloor)\). For
\(j=0,s,\ldots,(K-1)s\), the strict span requirement holds, since
\((K-1)s+3T+1=Ks+T-1\le L-1\). At each trial, the conditional probability
of surviving the next stride is at most \(1-\delta\). Translation
invariance and population conservation give a root occupancy marginal of
\(p\) at time \(T\). Therefore a given root's probability of surviving
through \(Ks\) edges is at most \(p(1-\delta)^K\). Every simple mixed cycle
winds in both coordinates and supplies at least two distinct surviving
roots on the layer \(x+y=0\bmod L\). Counting those roots gives

\[
 \boxed{\Pr_p(A_T)\le U(L,p,T):=\min\{1,(Lp/2)(1-\delta)^K\}.}
 \tag{1}
\]

At \(T=0\), use the elementary vacancy probe at stride one, which gives
\(U(L,p,0)=\min(1,Lp^L/2)\). The argument applies to a local exploration
transcript. Conditioning separately on a global basin event such as
\(A_{T_0}^c\) can restrict unqueried cells. To bound the finite band
\(\{T_0<\tau_M\le T\}\), use its inclusion in \(A_T\).

At fixed \(0<p<1\), take \(T=\lfloor c\log L\rfloor\) with
\(0<c<1/(4\log(2/p))\). Then \(\delta=L^{-4c\log(2/p)+o(1)}\) and
\(K=L^{1+o(1)}\). It follows that \(K\delta-\log L\to+\infty\), so (1)
tends to zero. The previous sufficient coefficient was
\(1/(6\log(2/p))\). The new result bounds a strictly larger finite band
after the original \(\sqrt{\log L}\) cutoff and after the earlier
logarithmic cutoff.

Taking the better of (1) and the diagonal-cut bound also gives a uniform
\(T=\lfloor c\log L/\log\log L\rfloor\) horizon over \(0\le p\le p_0<1\)
for every \(0<c<1/4\). For \(p\le1/T\) and \(T\ge2\), the diagonal-cut
certificate weight is at least \(e^{-6T-9}\), and its trial count is of
order \(L/T\). For \(1/T\le p\le p_0\), the new weight is at least
\((1-p_0)(2T)^{-(4T+1)}=L^{-4c+o(1)}\), with trial count again of order
\(L/T\). In both cases the product of trial count and weight dominates
\(\log L\) uniformly.

## A finite wait certifies permanent stopping

Suppose a tag remains at site \(z\) for \(2m\) consecutive full-round
snapshots, for an integer \(m\ge1\). Its successor at every attempt is
occupied. At an E tag's attempts those observations can switch from E to
N at most once. An N blocker that moved would leave the cell vacant at
the next E attempt, since another N cannot replace it in the same N phase.
For an N tag, use the phase after E and before N. Its successor observations
can switch from N to E at most once. An E blocker that moves leaves the
target vacant in the very phase where the N tag observes it. In either
case the \(2m-1\) attempts contain \(m\) consecutive observations of one
color. For an N tag, a successor observed as N in the middle snapshot is
N at the preceding full boundary, and a successor observed as E is E at
the following boundary. Thus the successor has a constant species for
\(m\) full snapshots within the original window.

Apply this argument \(d\) times within successively shorter subwindows.
If the original tag stays at the same site for \(2^d\) consecutive
snapshots, an occupied blocker path from it with \(d\) edges exists in
some snapshot in that window. With \(d=M\), the conserved population, the
path's \(M+1\) occupied vertices include a repeat. The set of vertices
reached from the root is then an occupied successor-closed core. The core
is permanent under the CLASSIC kernel and includes the tag's site.
Conservation of tagged transport shows the same original tag is present
there and cannot move later. Hence on any finite positive rectangle,

\[
 \boxed{\text{no tag move in the next }B(M)=2^M-1\text{ rounds}
   \quad\Longleftrightarrow\quad
   \text{no future move of that tag}.}
 \tag{2}
\]

The statements apply at every starting round with an occupied tag. On
\(R^c\), the core supplies an obstacle on every horizontal or vertical
route. It contains a mixed cycle because the only monochromatic cycles
are full lanes, whose absence is conserved. Thus any wait in (2) that
starts at round \(u\) certifies \(\tau_M\le u+B(M)\). A mixed cycle already
present at \(u\) prevents the tag from completing a full lap after \(u\)
because the tag cannot pass a permanent obstacle in its lane. For \(u\ge T\),
on \(O\cap R^c\cap A_T^c\), failure to make \(L\) actual moves in the
\(LB(M)\) rounds starting at \(u\) lies between \(\{\tau_M\le u\}\) and
\(\{\tau_M\le u+LB(M)\}\) under event inclusion. To see the latter, fewer
than \(L\) moves across \(L\) intervals of length \(B(M)\) leaves at least
one entire interval with no move.

## A conditional estimate after the cutoff

Write \(G_T=R^c\cap A_T^c\), with \(\Pr_p(G_T\mid O)>0\). At round \(T\)
start counting moves of the original tag. Let \(S_j\) be the first
boundary by which \(jL\) actual moves have occurred since \(T\), or
infinity if the count is never reached. In particular \(S_0=T\). On
\(S_j<\infty\), define the conditional failure probability

\[
 r_j=\Pr_p\big(\text{fewer than }L\text{ tag moves in the }LB(M)
   \text{ rounds starting at }S_j\mid O,G_T,S_j<\infty\big).
\]

Equation (2) guarantees that the next move, if it exists, occurs within
\(B(M)\) rounds of the current boundary. Consequently each reached
\(S_j\) is at most \(T+jLB(M)\), and failure in the displayed finite test
is equivalent to \(S_{j+1}=\infty\). The population is initial data and
\(M\le L^2\) gives a uniform finite horizon for fixed \(j,L\).

The events \(\{S_j<\infty\}\) are nested, and their intersection is exactly
the event of infinitely many moves. The chain rule, followed by continuity
from above, therefore gives

\[
 \boxed{\begin{aligned}
 \Pr_p(T<\tau_M<\infty\mid O)
   &=\Pr_p(G_T\mid O)\left(1-\prod_{j\ge0}(1-r_j)\right)\\
   &\le \Pr_p(G_T\mid O)\min\left\{1,\sum_{j\ge0}r_j\right\}.
 \end{aligned}}
 \tag{3}
\]

After a zero-probability survivor event, all remaining factors can be
set to one because the product is already zero. If \(\Pr_p(G_T\mid O)=0\),
the late probability on the left is zero. Each factor is a finite conditional probability given
the initial law and the appropriate survivor event. The proof does not
require the successive laps or their environments to be independent.

The occupied-path lemma also gives a shorter conditional test. For any
integer \(d\ge1\), put \(b_d=2^d-1\) and let \(P_d(t)\) denote the existence
of an occupied \(d\)-edge blocker walk from the tag's position at time
\(t\). On a failed lap, at least one of the first \(L\) intervals of length
\(b_d\) after \(S_j\) has no move. Applying the lemma to that interval gives

\[
 r_j\le\Pr_p\big(\exists 0\le u\le Lb_d:\ P_d(S_j+u)
   \mid O,G_T,S_j<\infty\big).
\]

Thus choosing \(d=O(\log L)\) gives a polynomial-length observation window
for this upper bound. Recurrent moving orbits can still have blocker paths,
so this estimate needs conditional tail control to be summable over laps.

For an earlier cutoff \(T_0\le T\), the initial Palm comparison turns
(1) and (3) into the following bound.
[Initial Palm comparison](2026-11-18-diagonal-cuts.md#a-tagged-formulation-of-the-late-event).

\[
 \Pr_p(T_0<\tau_M<\infty)\le U(L,p,T)
   +\frac{1}{2L}\sqrt{\frac{1-p}{p}}
   +\Pr_p(G_T\mid O)\min\left\{1,\sum_{j\ge0}r_j\right\}.
 \tag{4}
\]

At the improved logarithmic cutoff, the first two terms vanish for fixed
\(p\in(0,1)\). A sufficient next estimate is summability with a bound
tending to zero for each small fixed \(p\), for example
\(r_j\le a_L(p)b_p(j)\) with \(a_L(p)\to0\) and \(\sum_j b_p(j)<\infty\).
This summability estimate remains open. At fixed high density \(p<1\) in
the regime of Angel, Holroyd and Martin, the torus eventually jams with
probability tending to one. The full-lane term and (1) vanish there, so
the conditional failure probability in (3) instead tends to one. The
missing estimate must use the small initial density and the actual
evolved conditional law. [Angel–Holroyd–Martin, Theorem 2](https://emis.de/ft/41517).

## Controls for regeneration and late capture

An exact 3×3 example in increasing \(y\) order is

```text
N E N
E E N
. . .
```

The north tag at the origin moves in rounds 2, 3, and 4, completing a lap
after cutoff 1. The first mixed cycle appears at time 6, and all cars
stop. The initial board has no full monochromatic lane. Thus one full
lap can exclude a cycle at the start of that lap but cannot certify a
regeneration for all later rounds.

Even **all cars moving for order \(L\) rounds** is compatible with late
capture at every prescribed limiting density \(0<p<1/2\), with both
species equally represented. Choose integers \(k\ge1\) and \(T\ge1\) with
\(4(k-1)+2T+1\le L-1\). Fill whole \(x-y\bmod L\) classes as follows:

\[
 \mathcal E=\{0,2,\ldots,2(k-1)\},\qquad
 \mathcal N=\{2(k-1)+2T+1+2j:0\le j<k\}.
\]

All other cells are vacant. While free, E classes shift by \(+t\) and N
classes by \(-t\). Same-species classes are cyclically nonadjacent.
For \(a\in\mathcal E\), \(b\in\mathcal N\), the difference \(b-a\) is in
\([2T+1,L-1]\). A source overlap or cross-species obstruction in round
\(t<T\) would require \(b-a\equiv 2t,2t+1\), or \(2t+2\pmod L\).
Thus every car moves in those \(T\) rounds. At time \(T\), the last E
class and first N class are at residues \(c\) and \(c+1\). Their cars
form a mixed staircase \(E\to N\to E\) winding once in each direction.
There cannot have been an earlier permanent cycle, so \(\tau_M=T\).

The population is \(2kL\) with exactly \(k\) E-cars per row and \(k\)
N-cars per column. For fixed \(p<1/2\), take \(k=\lfloor pL/2\rfloor\)
and \(T=\lfloor aL\rfloor\) with \(0<a<(1-2p)/2\). The construction then
applies for all large \(L\). The same lane counts admit a perpetual
free-flow board. Use the first \(2k\) even \(x+y\bmod L\) classes, assigning
the first \(k\) to E and the others to N. The used classes are cyclically
nonadjacent and shift together by one in each free round, which preserves
both phases' movement conditions. Translating either board can put an
N tag at the origin. Its initial \(T\) actual moves are identical in the
two examples. These prescribed boards are deterministic controls under
matching density and lane counts. Their existence gives no order-one iid
lower bound on the late probability at small density.

## Verification and scope

- **Lean.** `BML/Waiting.lean` proves the finite successor subwindow,
  occupied path, permanent core, route-cover and original-tag statements
  for the actual kernel. `BML/Locality.lean` proves injectivity of the
  projection on short coordinate rectangles. `BML/Barrier.lean` supplies
  the previously proved deterministic guarded barrier.
- **Written proofs.** The adaptive probability calculation, the
  logarithmic limits, the lap probability estimate, and the balanced
  delayed-capture construction are proved above.
- **Finite replay.** `tests/test_late_fixation.py` checks all 19,764 initial
  2×2 and 3×3 boards through exact labeled recurrence, matches their
  162,318 colored transitions against the production map, and checks waits
  and finite lap tests. On 3×3 with cutoff 1, 2,412 boards first form a mixed
  cycle later. In 104 of them the origin is occupied and its tag completes
  a lap after the cutoff before eventually stopping. Additional controls
  exercise seams, a reused site beyond the admissible probe count,
  protected queues, and the balanced delayed-capture family.

At cutoff 1 on 3×3, exact initial-weight sums give the following values.

| Initial density \(p\) | \(\Pr_p(1<\tau_M<\infty)\) | \(\Pr_p(X\mid O,G_1)\) |
| --- | ---: | ---: |
| \(1/5\) | \(3051/12500000\) | \(303/342269\) |
| \(1/2\) | \(297/8192\) | \(607/9363\) |
| \(9/10\) | \(52612659/320000000\) | \(1982452077/3254192201\) |

```sh
python -m pytest -q tests/test_late_fixation.py
cd formal/lean
lake build
lake env lean Audit.lean
```

The result extends the part of the late event that can be bounded and
gives a finite test for each conditional lap. The all-time estimate at
small fixed density, and hence a positive nonjamming interval, remains open.
