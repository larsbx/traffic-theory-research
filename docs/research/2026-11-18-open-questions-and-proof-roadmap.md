# Open questions and proof roadmap

**Research review — 18 November 2026.** This note records the questions left
after the TRAIN formalization and the BML/tiling review. It distinguishes
missing repository proofs from unresolved research questions. New arguments
below carry no claim of novelty.

**Repository snapshot:** main
[`eca166097bafb910a1d9e81bca7ee6bbb175687d`](https://github.com/larsbx/traffic-theory-research/commit/eca166097bafb910a1d9e81bca7ee6bbb175687d).
PR status in this note is a dated snapshot, not a continuously updated assertion.
The [formal register](../../formal/README.md), [TRAIN register](../../formal/TRAIN.md),
and [Traffic register](../../formal/traffic-layer.md) give the detailed scopes.

**Subsequent deterministic follow-up — 19 November 2026:** the current
[blueprint](../../formal/blueprint.md) records B0–B7 as kernel-checked,
including the CLASSIC rigidity, maximal free-flow capacity, and rectangular
sparse-speed results formerly pending below. The elapsed-time conversion in
§3 is now formalized for CLASSIC: when `2m < g = gcd(W,H)`, permanent full
movement holds from round `lcm(W,H) * m(g−2)` onward, and the state is
`StaticFree` at that deadline. See `low_density_speed_one_deadline` and
`low_density_staticFree_deadline` in
[BML/SparseSpeed.lean](../../formal/lean/BML/SparseSpeed.lean).
The original status table and priorities below retain their dated snapshot.
Equality, rectangular TRAIN speed one, and the fixed-positive-density
probability problem remain separate obligations.

**Subsequent probability follow-up:** the
[tagged-fixation note](2026-11-18-tagged-fixation-and-gridlock.md) adds a complete
Lean proof that some original car eventually stops iff global jam occurs or an
initial full monochromatic lane exists. Its prose Palm calculation connects
one tagged car's fixation probability to global jam probability with an
explicit vanishing error. This supplies an alternative core-to-route-cover
proof without cycle extraction; the fixed-positive-density questions in §5
remain unresolved. The status table below retains its original pinned snapshot.

**Further probability follow-up:** the
[profile obstruction](2026-11-18-lane-profile-obstruction.md) now has a Lean
construction of ringless jams with arbitrary positive profiles satisfying
\(\max r+\max c\le L\). Its prose probability consequence rules out
high-probability, universally sound nonjamming certificates based solely on
conserved lane counts at any fixed \(0<p<1\). The
[capacity bound](2026-11-18-disjoint-strip-capacity.md) improves finite
empty-strip estimates, and Theorem 6a of the probability note sharpens the
sparse window to \(p_LL\le2\log\log L-4\log\log\log L-2\).
These advances leave the fixed-density, long-time formation problem open.

**Spatial and dynamical follow-up:** the
[protected-queue note](2026-11-18-protected-queue-gridlock-delay.md) now proves
in Lean that an original car first moves at a prescribed round despite an
arbitrary exterior. Exact cyclic avoidance probabilities strengthen the
fixed-density lower bound on gridlock time to order `log L`. Its separate
prose completion theorem shows that no observation confined to one bounded
rectangle can universally certify all-time nonjamming: every such local
pattern extends to an eventually jammed state on a sufficiently large square.
Finite-time survival remains compatible with a permanent capture core already
present elsewhere. Neither result controls the eventual iid basin probability.

**Further first-formation estimate — 19 November 2026:** the
[guarded-barrier note](2026-11-19-guarded-barrier-formation.md) uses a
kernel-checked L-shaped snapshot barrier to exclude a first mixed cycle
through order `log L` at each fixed `0<p<1`. The new initial certificate
requires `6T` cars and one hole. Combined with the earlier empty-origin cut,
it also gives a uniform `log L/log log L` horizon over `0<=p<=p0<1`.
The probability of first formation after that cutoff remains the step
needed for fixed-positive-density nonjamming. A supplied family with all
cars moving for order `L` rounds before a mixed staircase forms rejects
the shortcut from a long free prefix to permanent noncapture.

**TRAIN equality follow-up — 24 November 2026:** the equality extension of
§2.2 is now kernel-checked. `BML.Train.half_square_eventually_fullSpeed` proves
eventual full movement on N×N under `2m ≤ N` by the counting-saturation
argument, without the label-uniqueness step: see the
[TRAIN register](../../formal/TRAIN.md#the-boundary-2m--n-counting-saturation).
The kernel-checked lower bound is therefore
\(m_{\mathrm{bad}}(N)\ge\lfloor N/2\rfloor+1\). The upper bound N, the
rectangular gcd adapter and any settling-time bound at equality remain as
described below.

| Status at this snapshot | Consequence for this roadmap |
| --- | --- |
| [PR #9](https://github.com/larsbx/traffic-theory-research/pull/9) and [PR #11](https://github.com/larsbx/traffic-theory-research/pull/11) merged | The complete rectangular TRAIN jam theorem and strict sparse-square eventual-speed-one theorem are already in Lean. |
| [PR #10](https://github.com/larsbx/traffic-theory-research/pull/10) merged | The CLASSIC maximal-free-flow argument has a detailed prose decomposition and independent finite max-plus checks; its full Lean proof remains to do. |
| [PR #13](https://github.com/larsbx/traffic-theory-research/pull/13) merged | CLASSIC numerical species/lane invariants are now in Lean. Probability reductions and shrinking-density bounds have prose proofs and finite checks, with separate formalization gaps. |
| [PR #7](https://github.com/larsbx/traffic-theory-research/pull/7) open, head `536d1fb20816d1e2d422d5a25122953a42c85c6b` | The branch reports completed Lean G1/G2 and the finite-torus coset identity, including bounded orbit times. Its former conflict with main is resolved. These results are pending integration, not untouched proof tasks or merged results. |
| [PR #12](https://github.com/larsbx/traffic-theory-research/pull/12) open, head `db558d58e4cdc34fe94b794a4a99837b4f7e292e` | This is a CLASSIC sparse-flow and blocking-count **blueprint with Python checks**, not a compiled Lean theorem. |

Throughout, **merged Lean** means a universal theorem for the named Lean
model; **PR Lean** means reported proof work on the pinned open branch;
**prose argument** means a mathematical derivation not yet incorporated into
the audited Lean layer; **finite evidence** means only the enumerated domain;
and **research target** means a claim or quantitative question still requiring
an argument. These categories must not be collapsed into one claim that
everything has been formally verified.

## 1. The completed foundation

A full round is an east half-step followed by a north half-step. **CLASSIC**
reads vacancy at the beginning of each half-step. **TRAIN** lets a queue move
together and lets a full homogeneous ring rotate. Consequently unchanged
occupancy can hide positive TRAIN movement. TRAIN jams use actual zero
movement and are required to be nonempty; the empty state is free.

The merged [TRAIN layer](../../formal/TRAIN.md) proves queue/ring semantics,
identity-preserving transport, trace coverage, numerical species and population
conservation, and the exact feasible nonempty-jam populations

\[
W+H\le m\le WH\qquad(W,H\ge2).
\]

Singleton dimensions have no nonempty TRAIN jam. On an \(N\times N\) square,
the actual update kernel also satisfies

\[
2m<N\quad\Longrightarrow\quad
\text{every car moves in every sufficiently late full round}.
\]

This includes the empty state. Public theorems are
`BML.Train.sparse_square_eventually_fullSpeed` and
`BML.Train.sparse_square_moves_equal_population` in
[Train/SpeedOne.lean](../../formal/lean/Train/SpeedOne.lean). The proof passes
through abstract cyclic tags, actual identity transport and release, and the
equivalence between maximal movement counts and every car moving. It is not
just a theorem about a surrogate process. Austin–Benjamini's written rule and
Propositions 1 and 6 are the primary comparison [AB].

These results answer worst-case finite population questions. They do not
determine attraction probabilities at fixed positive density: the sparse
square condition gives \(m/N^2<1/(2N)\), which tends to zero.

## 2. TRAIN: the first population admitting persistent slowdown

For \(N\ge2\), define

\[
m_{\mathrm{bad}}(N)=\min\{m:\text{some }N\times N\text{ state with }m
\text{ cars fails to reach eventual permanent full movement}\}.
\]

The qualification **permanent** matters: a bad orbit can contain individual
rounds in which every car moves. This definition identifies the first bad
population; it does not prove that bad states exist at every larger population.
For \(N=1\) the bad-state set is empty, so the definition is restricted to
\(N\ge2\).

### 2.1 An explicit periodic family with N cars

Place east cars at
\((0,0),(1,0),\ldots,(N-2,0)\), one north car at \((N-1,0)\), and leave
every other site empty. This gives the following **all-size prose argument**
for a periodic orbit with exact period \(N+1\).

Index rounds by their starting times, beginning at zero. In round zero the
north car blocks the whole east queue, and then moves north. At times
\(1\le t\le N\), the east cars occupy row zero except for the hole

\[
h_t=(N+t-2)\bmod N,
\]

and the north car is at
\((N-1,\min\{t,N-1\})\). In rounds \(t=1,\ldots,N\), every east car
moves by queue propagation. The north car moves in every round except
\(t=N-1\): in that round its row-zero destination is occupied after the east
update. In round \(t=N\), the east update puts the hole at \((N-1,0)\),
and the north car enters it, recovering the initial state at time \(N+1\).

The first \(N+1\) states are distinct. The north car's height separates all
but the two states at height \(N-1\); those two have different east-row
holes. Thus the period is exactly \(N+1\). The east cars contribute
\(N(N-1)\) moves and the north car contributes \(N\), giving

\[
\text{period moves}=N^2,\qquad
v=\frac{N^2}{N(N+1)}=\frac N{N+1}<1.
\]

Combining this construction with the merged strict sparse-square theorem gives

\[
\boxed{\left\lceil\frac N2\right\rceil\le m_{\mathrm{bad}}(N)\le N.}
\]

The lower bound follows from merged Lean; the upper bound currently rests on
the prose construction above. The review additionally compared the actual
Lean and Python transition rows for \(N=2,\ldots,8\): **42 rows**, each
orbit having transient zero, period \(N+1\), and exactly \(N^2\) moves.
The reproducible command is in the appendix. This does not replace an all-size
Lean proof or an unrestricted cross-language theorem.

For \(N=2\), the ternary board-code cycle is
`7 -> 55 -> 57 -> 7`, with full-round move totals `1, 1, 2` and velocity
\(2/3\). These three states also lie in the existing exhaustive three-way
Lean/Quint/Python domain. No additional Quint claim is made for all seven
sizes in the appendix.

**Next proof task:** formalize the configuration, the time-indexed hole and
north-car positions, exact recurrence and period, and movement totals. The
substantive question is the optimal universal population guarantee and the
structure of the first bad recurrent orbits, not the existence of this one
family.

### 2.2 The equality case has a concrete proof extension

The merged statement uses \(2m<N\). Equality \(2m=N\) is **not** a known
counterexample. The existing two-car \(4\times4\) boundary fixture becomes
free; it refutes forward persistence of every particular empty pair, not
eventual speed one at equality.

The following counting-saturation argument supports extending the theorem to
\(2m\le N\). It still needs integration into the Lean proof.

Use the corrected diagonal tags from
[Train/Diagonals.lean](../../formal/lean/Train/Diagonals.lean) and
[Train/DiagonalDynamics.lean](../../formal/lean/Train/DiagonalDynamics.lean).
If an adjacent empty pair exists at every time, the existing backward-pair
and permanent-cut argument applies. Otherwise choose a time without one, and
let \(A\) be the occupied corrected classes. The absence of an empty pair gives

\[
\mathbb Z_N=A\cup\operatorname{prev}(A),\qquad
N\le2|A|\le2m\le N.
\]

All inequalities are equalities. There is one car label per occupied class,
and occupied and empty **corrected classes** alternate. This is a statement
about the class support, not an alternating physical board.

For occupied class \(b\), release provides a label in class \(b\) at the
next time because its successor class is empty. The stay-or-predecessor law
says this label came from old \(b\) or old \(\operatorname{next}(b)\).
The latter is empty, so it is the unique old label at \(b\). Every label's
corrected tag stays fixed; the same reasoning repeats forever. The actual
kernel bridge then gives full movement.

This is a proposed formal extension with a specific argument, not an
unexplained conjecture that equality might fail. Incorporating it would
strengthen the **kernel-checked** lower bound to
\(m_{\mathrm{bad}}(N)\ge\lfloor N/2\rfloor+1\). It would not determine
the optimal threshold. Quantitative bounds from the strict permanent-cut
argument also need their own check at equality.

### 2.3 Rectangles require the gcd, not the shorter side

The tempting implication \(2m<\min(W,H)\Rightarrow\) eventual full movement
is false for TRAIN. The merged
[rectangular certificate](../../formal/TRAIN.md#eventual-speed-one-acceptance)
uses \(W=5,H=7,m=2\), initial code `7`: transient 1, period 15, and 29
moves out of 30 opportunities per period. Its velocity is \(29/30\), despite
\(4<5\).

The natural sufficient extension is instead

\[
2m<g,\qquad g=\gcd(W,H),\qquad
Y_t=x_t+y_t-t\pmod g.
\]

Both wrapped coordinate moves advance the class by one because \(g\) divides
both dimensions. The abstract tag argument can therefore be reused if its
stay-or-predecessor, release and transport premises are supplied for the
rectangular kernel. That actual TRAIN adapter is not yet a merged theorem.
The CLASSIC counterpart is proposed in PR #12. It requires its own kernel
proof: a statement that TRAIN is faster does not establish a comparison of
the two systems' eventual outcomes.

## 3. Settling time and blocking counts are different quantities

For a finite orbit that eventually has permanent full movement, let

\[
\begin{aligned}
T(s)&=\min\{T:\text{every round }t\ge T\text{ has full movement}\},\\
B(s)&=\#\{t:\text{at least one car is blocked in round }t\},\\
C(s)&=\sum_{t\ge0}\bigl(m-\operatorname{Moves}(F^t(s))\bigr).
\end{aligned}
\]

Here time counts complete east-then-north rounds; \(B\) counts bad rounds and
\(C\) counts missed car-rounds. Always \(B\le C\). PR #12's advertised
\(m(g-2)\) bound is a bound on **bad rounds**, not directly on elapsed
settling time. A rank proof can also be examined for a stronger cumulative
car-round estimate, but that stronger claim must be stated and proved explicitly.

There is a useful elementary conversion. Put
\(\ell=\operatorname{lcm}(W,H)\). If \(\ell\) consecutive rounds have full
movement, every east car returns after an integer number of width traversals
and every north car after an integer number of height traversals. The state
returns exactly; determinism repeats that free cycle forever. Thus, before
the final bad round, every gap between bad rounds is at most \(\ell\), and
the first bad round has index less than \(\ell\). For \(B>0\), the last
bad index is at most \(\ell B-1\). For \(B=0\), take \(T=0\). Hence

\[
\boxed{T(s)\le\ell B(s)\le\ell C(s).}
\]

This argument works for either rule when full movement has its actual
movement meaning. At this note's original snapshot, combining it with the
proposed strict sparse gcd bound would give \(T\le\ell m(g-2)\), but the
combined theorem was not yet in Lean. The subsequent CLASSIC formalization
now proves this deadline from B7's block budget and B3's finite-window
criterion: `K+1` disjoint windows of `ell` rounds with at most `K` blocked
rounds contain a fully moving window starting by `ell * K`.
A nonempty strict sparse state has \(g\ge3\); the empty state's deadline is
zero. The general two-rule conversion above remains a prose statement outside
the proved CLASSIC scope. Do not attach the same rank bound to the equality
extension without checking its quantitative premises separately.

Finite-state determinism already gives a computable bound: on a fixed
\(W\times H\) board there are at most \(3^{WH}\) occupancy states. In a
regime known to reach permanent full movement, an unrepeated preperiod cannot
exceed the state space. The interesting targets are substantially better
bounds, sharp worst-case examples, and typical or expected times under a
specified initial distribution. Existence of *some* effective finite bound
is not by itself an unresolved research problem.

## 4. CLASSIC: integrate completed arithmetic, then prove rigidity and packing

PR #7 reports universal Lean G1/G2 results for positive rectangles: a
nonempty \(n\)-car jam exists exactly for
\(\min(W,H)\le n\le WH\), and an initial state eventually reaching a jam
exists for the same populations. For each feasible \(0\le n<WH\), it also
constructs an initial state that never reaches a nonempty jam. Consequently
eventual gridlock is forced for all states of a feasible population exactly
at full occupancy. These are **existence and universal quantifier statements**,
not iid attraction probabilities.

The same PR now implements the coset step that the earlier roadmap listed as
untouched. With \(g=\gcd(W,H)\), diagonal step \(D=(+1,-1)\), and
\(\phi(x,y)=x+y\pmod g\), it proves

\[
p\text{ and }q\text{ share a }D\text{-orbit}
\iff\phi(p)=\phi(q),\qquad
\langle(1,-1)\rangle=\ker\phi.
\]

The branch includes signed and bounded natural-time witnesses, exact return
times divisible by \(\operatorname{lcm}(W,H)\), and the effect of an east
translation on class labels. Its `BML/Congruence.lean`, `BML/Cosets.lean`, and
`BML/CosetTimes.lean` should be integrated and checked with the merged lane
and TRAIN modules. They should not be independently reimplemented as if no
proof existed. See the pinned PR head in the snapshot table for this branch's
reported local validation; those reports are not new runs performed by this
documentation change.

The remaining chain is
[B2 cosets](../../formal/blueprint.md#b2-coset-identity) →
[B3 actual-kernel rigidity](../../formal/blueprint.md#b3-lemma-r-free-flow-rigidity) →
[B4 packing and construction](../../formal/blueprint.md#b4-theorem-f-densest-free-flow).
Both directions of Lemma R must connect indefinitely moving traffic with its
static phase-class constraints. Theorem F then needs a class-packing upper
bound and constructions attaining it. Its piecewise maximum is

\[
n_{\mathrm{free}}(W,H)=
\begin{cases}
\max\{H\lfloor W/2\rfloor,\ W\lfloor H/2\rfloor\},&g=1,\\[2mm]
\dfrac{WH}{g}\left\lfloor\dfrac{2g}{3}\right\rfloor,&g\ge2.
\end{cases}
\]

This is not a universal two-thirds density. The merged blueprint supplies
an all-size prose argument. The independent max-plus DP checks its static
optimization on six explicitly listed rectangles, through \(g=6\). The DP takes Lemma R's static constraints as
input; it does not prove dynamic rigidity or the all-size optimization theorem.

PR #13 has already discharged CLASSIC numerical species-count and lane-count
conservation. Distinct remaining obligations include extracting the required
row/column witnesses from mixed winding for the capture theorem, equating
tagged capture movements with the Eulerian `moveCount` sum, and proving the
orbit classifier's general correctness. The separate `Traffic` library's
conservation obligations are not automatically discharged by `BML/Lanes.lean`.

## 5. The probability frontier is formation over long time

Fix CLASSIC, a square of side \(L\), and iid initial probabilities
\(p/2,p/2,1-p\) for east, north and empty. Let

\[
q_L(p)=\Pr(\text{eventual nonempty global gridlock}).
\]

Angel–Holroyd–Martin prove a high-density regime: for some \(p_1<1\), fixed
\(p\ge p_1\) gives eventual fixation with probability tending to one on
growing tori whose aspect ratio tends to a positive finite value. Their
infinite-lattice theorem says each car moves finitely often and each site
eventually stabilizes; it does not give one common finite global stopping
time [AHM]. The 2026 study [HBK] characterizes free-flow states through
\(D=0\), proves their stability, and examines convergence numerically. It
does not provide a fixed-positive-density iid basin or sharp-threshold theorem.

### 5.1 What the merged probability note adds

The [probability note](2026-11-18-probabilistic-gridlock-bounds.md) now gives
prose proofs of the following facts. Write \(J_L\) for eventual jam,
\(M_L\) for eventual formation of a mixed simple direct-blocker cycle, and
\(R_L\) for an initial full east row or full north column. Then

\[
M_L=J_L\cap R_L^c,\qquad
0\le q_L(p)-\Pr(M_L)\le2L\,2^{-L}.
\]

Thus mixed-cycle formation and eventual gridlock have asymptotically equal
probabilities, uniformly in \(p\). This reduction supplies the relevant
event but not its formation probability. A mixed persistent core gives
deterministic capture; creating that core from the evolving correlated
configuration remains the central probabilistic gap.

The same note proves that, for each fixed \(0<\varepsilon<2\),

\[
p_L L\le(2-\varepsilon)\log\log L
\quad\text{eventually}\quad\Longrightarrow\quad q_L(p_L)\to0.
\]

This is a shrinking-density nonjamming result, not a positive-density
free-flow theorem. Lean proves the underlying actual-kernel lane invariants;
the event identity, cycle geometry, strip obstruction, probability laws and
analytic limits remain prose mathematics with separate finite checks.

There is also a structural limit to the empty-strip approach. At fixed
\(p>0\), the probability that even one column contains no north cars is at
most \(L(1-p/2)^L\to0\). Optimizing the strip width alone cannot make this
particular mechanism establish a fixed-positive-density nonjamming interval.

The [diagonal-cuts bound](2026-11-18-diagonal-cuts.md) suppresses direct mixed
cycles through \(T_L=\lfloor c\sqrt{\log L}\rfloor\) for every fixed \(p<1\)
and sufficiently small \(c=c(p)>0\). It follows arrows at the chosen snapshot
and uses unqueried initial cells to stop each path. At this horizon initial
queues also make perfect free flow unlikely. To prove a fixed positive
nonjamming interval, it remains to control cycles that form after \(T_L\).

### 5.2 Questions that remain

One precise threshold formulation is

\[
\begin{aligned}
p_-&=\sup\{a\in[0,1]:\forall p\in(0,a),\ q_L(p)\to0\},\\
p_+&=\inf\{a\in[0,1]:\forall p\in(a,1],\ q_L(p)\to1\}.
\end{aligned}
\]

The high-density result gives
\(0\le p_-\le p_+\le p_1<1\). A positive sharp threshold would require
\(p_->0\) and \(p_-=p_+\). A limit at every density, the value at a
putative critical point, and the width of a finite-size transition window
are additional questions. None is established by the repository or the
primary sources checked for this review.

Other distinct questions must stay separate:

- Does low fixed positive density imply eventual full movement with high
  probability, or merely absence of complete gridlock? Intermediate recurrent
  movement can distinguish these events.
- How do aspect ratio, unequal species proportions, and iid versus
  fixed-population ensembles change the result?
- What controls formation or avoidance of winding capture structures over
  unbounded or size-dependent time? An iid loop count at time zero does not
  apply to the correlated law after evolution.
- What are the basin probabilities within a conserved lane profile? The
  probability note constructs jammed and free representatives for typical
  profiles in a range, but one representative says nothing quantitative about
  its share of the profile's initial states.
- What are the relaxation-time distribution and the appropriate order of
  size and time limits? The finite-time isolation and protected-queue arguments
  prove delay, now logarithmic in side length at every fixed `0<p<1`, including
  noncommutation of limits in the high-density regime; they do not prove
  eternal avoidance of gridlock.
- Is the iid averaged jam probability monotone in density in the relevant
  setting? (Finite sizes W·H ≤ 22: yes, exactly, strictly increasing.
  The fixed-count version fails on 2×11 although q still increases there; see the
  [finite iid monotonicity note](2026-11-18-finite-iid-monotonicity.md). Not on every finite
  torus: q is non-monotone on 2×W for all W ≥ 24, by
  [thin-torus rigidity](2026-11-21-thin-torus-nonmonotonicity.md), and on 2×15, the smallest
  non-monotone 2×W (§4.1 there). Squares remain open. On thin
  tori there is no jammed phase at all: q → 0 at every p < 1, by Theorem P of the same note.) Configurationwise non-monotonicity does not settle that question.
  The note separately gives finite-size non-monotonicity for the mixed-cycle
  event's iid probability; that event differs from the jam event by the ring
  exception.

Any probabilistic formalization must first declare these events, the law and
the order of limits. The deterministic TRAIN theorem, CLASSIC extremal
existence, and high-density probabilistic fixation answer different questions.

## 6. Tiling, Fibonacci order, and trigonometry

### 6.1 What the Traffic layer already establishes

The [Traffic coverage register](../../formal/traffic-layer.md#lean-coverage)
records an exact 21-Wang-tile recoding of CLASSIC frozen configurations,
including unique encoding, and an injective bi-infinite frozen staircase
for **any supplied** bi-infinite east/north direction word. It also proves
finite Fibonacci counts, integer-pair algebra for \(a+b\varphi\), substitution
scaling, and winding conditional on explicit modular closure. See
[Traffic/Wang.lean](../../formal/lean/Traffic/Wang.lean) and
[Traffic/Geometry.lean](../../formal/lean/Traffic/Geometry.lean).

The remaining steps below are chiefly repository formalization obligations
for established Fibonacci mathematics. They should not be advertised as new
open problems in quasicrystal theory.

### 6.2 Supply the word, limits, and real projection

For \(\sigma(E)=EN\), \(\sigma(N)=E\), construct a particular two-sided
Fibonacci hull word instead of assuming one. A concrete route uses the
persistent cut \(E\mid E\) under even substitutions:
\(\sigma^2(E)=ENE\) begins and ends in \(E\), and \(EE\) occurs in
\(\sigma^3(E)=ENEEN\). Nested left suffixes and right prefixes give a
two-sided legal word; its language and recurrence properties need proofs.

Then prove asymptotic letter frequencies and balancedness or an equivalent
bounded transverse-discrepancy statement. Finite Fibonacci count identities
alone do not prove all those infinite-word properties. The expected mean
direction has slope \(1/\varphi\), where
\(\varphi=(1+\sqrt5)/2\), because the letter frequencies have ratio
\(f_N/f_E=1/\varphi\).

The current formal algebraic projection still needs a real embedding,
orthogonal projection onto the line spanned by \((\varphi,1)\), positive projected interval
lengths, and unboundedness in both directions so the intervals cover the
whole line. Identify the resulting one-dimensional tiling and its scale
explicitly before invoking its known spectral properties. The existing
[construction discussion](2026-11-18-bml-tilings-quasicrystals-trigonometry.md#4-fibonacci-staircase-a-frozen-path-whose-projection-is-a-tiling)
gives the intended geometry.

A small preliminary theorem is especially accessible: `staircase_sum` says
the coordinate sum of vertex \(n\) is \(n\). An axis-aligned \(L\times L\) box of
lattice sites, \(L\ge1\), contains only \(2L-1\) possible coordinate sums, hence at most
\(2L-1\) staircase vertices. This yields zero two-dimensional area density
after division by \(L^2\) and passage to the limit. The staircase is a thin
planar configuration whose projection is a one-dimensional tiling; it is
not itself a relatively dense two-dimensional quasicrystal.

### 6.3 Specify the observable before claiming spectral order

Pure-point diffraction of the standard Fibonacci tiling is established
mathematics [BFG, RS]. The repository task is to identify the endpoint set,
weights, normalization, cut-and-project lattice and window, autocorrelation,
and limiting measure, and then formalize or explicitly justify applying that
result. A relation between spatial dynamical spectrum and diffraction also
needs its own hypotheses. Traffic-time dynamics and spatial translations
are different actions.

The original [spectral discussion](2026-11-18-bml-tilings-quasicrystals-trigonometry.md#6-trigonometry-quasicrystals-and-diffraction)
explains the trigonometric connection. The staircase angle
\(\tan\theta=1/\varphi\) and the pentagonal identity
\(\varphi=2\cos(\pi/5)\) express different geometric facts. Neither gives
a universal BML band angle. Finite torus winding and aspect ratio constrain
particular paths; D'Souza and Linesch–D'Souza supply numerical/geometric
traffic evidence [DS, LD], not a theorem that random BML produces a
quasicrystal.

Several boundaries remain essential:

- The 21 Wang tiles allow periodic as well as aperiodic configurations; every
  fully occupied east/north coloring is CLASSIC frozen. The tiles do not force
  quasiperiodicity.
- At full occupancy the unweighted occupation field sees the periodic lattice.
  Species-sensitive or contrast-weighted observables are needed to study
  order in the coloring.
- A finite FFT has finitely many discrete bins by construction. Its peaks
  do not prove an infinite-volume pure-point diffraction statement.
- The frozen-state encoding is for CLASSIC. TRAIN has moving homogeneous
  rings even when the same local occupancy constraints hold; a TRAIN jam
  encoding would need additional ring exclusions or equivalent global data.

The claim that random BML selects a Fibonacci, Penrose or other model-set hull
is unestablished by this repository and these gridlock results. A research
program would first specify an observable, initial ensemble, time/size limit,
candidate hull and invariant measure, then test and prove the relevant
correlations or spectrum. Calling that claim a literature-open conjecture
would require a further targeted literature review.

## 7. Software verification still has its own frontier

The existing Lean, Quint and Python replays are valuable finite evidence with
explicit domains. They do not prove unrestricted equivalence of the source
implementations. Remaining tasks include a general refinement contract for
each update rule, correctness of the pointer-doubling orbit classifier, exact
preperiod/period extraction, and a proof that its velocity classification
agrees with actual movement counters and nonempty-jam semantics.

The `BML` and `Traffic` CLASSIC libraries also need an explicit general
equivalence if results are to transfer automatically between them. Separate
audits, overlapping examples and the same informal rule description do not
constitute that theorem. TRAIN requires its own identity and full-ring
semantics throughout any refinement.

For acceptance, keep universal Lean proofs, Quint evaluation, finite replay,
negative controls, and hosted workflow status separately recorded. A queued
workflow is not a passing receipt, and a successful local run on one head
does not certify a later combined commit. This note changes documentation;
it does not add a new theorem, a general refinement, or a full-suite test run.

## 8. Priorities and concrete completion criteria

The later [certified-gridlock increment](2026-11-18-certified-absorption-bounds.md)
advances the probability and verification priorities below with universal
cutoff-certificate soundness and exact unresolved-mass accounting. Its
[relaxation analysis](2026-11-18-relaxation-obstructions.md) adds a proved
queue obstruction and a conditional expected-defect route. The historical PR
snapshot above is retained; the increment starts after the merges of PRs #12
and #14 and still leaves the positive-density target open.

| Priority | Work | Completion criterion |
| --- | --- | --- |
| 1 | Integrate PR #7's G1/G2 and coset proofs while retaining PR #13 lanes and the completed TRAIN layer. | A combined revision with the required Lean audits and appropriate acceptance receipts; update the formal register to reflect what actually merged. |
| 2 | Complete CLASSIC rigidity and maximal free flow. | Both actual-kernel directions of Lemma R, followed by the piecewise all-size upper bound and attaining constructions for Theorem F. |
| 3 | Strengthen TRAIN's sparse theory. | Audited all-size periodic-family proof, the equality extension, rectangular gcd adapter, and explicit blocking/settling-time statements with their separate hypotheses. |
| 4 | Attack the probabilistic formation problem. | A dynamical formation/avoidance estimate valid over the relevant time scale; a fixed-positive-density result would go beyond the merged shrinking-density window. Formalize existing probability reductions separately. |
| 5 | Complete the Fibonacci construction and projection bridge. | A two-sided hull word, the finite box bound, frequency/discrepancy results and a real projected tiling; only then connect an explicitly defined observable to known diffraction results. |
| 6 | Extend software assurance. | General source refinement and classifier correctness, keeping those theorems distinct from finite cross-language replay. |

The first, second and much of the fifth and sixth items are repository proof
obligations for statements with existing arguments. The optimal TRAIN
population guarantee and quantitative behavior still need mathematical
analysis. A positive sharp probabilistic transition and random selection of
a prescribed spatial-order class require substantially different evidence.

## Appendix: reproduce the finite periodic-family check

After building the existing `train_replay` target and installing the Python
dependencies, run this from the repository root. It uses the existing Python
adapter and the actual compiled Lean exporter; it adds no alternative dynamics.

```sh
python - <<'PY'
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path("formal/quint").resolve()))
from train_check import python_rows

exe = Path("formal/lean/.lake/build/bin/train_replay").resolve()
row_count = 0
for n in range(2, 9):
    initial = sum(3**x for x in range(n - 1)) + 2 * 3**(n - 1)
    codes = []
    current = initial
    for _ in range(n + 1):
        assert current not in codes
        codes.append(current)
        current = python_rows(n, n, [current])[0][5]
    assert current == initial
    expected = python_rows(n, n, codes)
    output = subprocess.check_output(
        [str(exe), str(n), str(n), *map(str, codes)], text=True
    )
    actual = [list(map(int, line.split("\t"))) for line in output.splitlines()]
    assert actual == expected
    moves = sum(row[6] + row[8] for row in actual)
    assert moves == n * n
    row_count += len(actual)
    print(f"N={n}: period={len(actual)}, moves={moves}/{n * (n + 1)}")
assert row_count == 42
print(f"Compared {row_count} complete Lean/Python transition rows")
PY
```

The review ran this finite comparison using the TRAIN sources merged in
PR #11. Those sources, the TRAIN Quint layer and `bml/model.py` are unchanged
in the main snapshot pinned above. The ten-field comparisons include
intermediate/final boards and the exporter's independent movement counts;
they are not merely checks of the displayed mean velocity.

## Sources and related records

- [AB] T. D. Austin and I. Benjamini, *For what number of cars must self
  organization occur in the Biham–Middleton–Levine traffic model from any
  possible starting configuration?*, [arXiv:math/0607759v3](https://arxiv.org/pdf/math/0607759v3).
  Read its movement rule with Propositions 1 and 6 and the questions about
  collisions and the intermediate regime.
- [AHM] O. Angel, A. E. Holroyd and J. B. Martin, *The Jammed Phase of the
  Biham–Middleton–Levine Traffic Model*, Electronic Communications in
  Probability 10 (2005), 167–178,
  [Theorems 1–2](https://arxiv.org/pdf/math/0504001v2).
- [HBK] G. Hertzberg Rabinovich, O. Biham and E. Katzav, *Structure and
  dynamics in the low-density phase of a two-dimensional cellular automaton
  model of traffic flow*, [arXiv:2601.01180v2](https://arxiv.org/html/2601.01180v2)
  (2026). The free-state characterization and numerical convergence study
  must be distinguished from an iid limiting-basin theorem.
- [BFG] M. Baake, N. P. Frank and U. Grimm, *Three variations on a theme by
  Fibonacci*, Stochastics and Dynamics 21(3) (2021), 2140001,
  [Theorem 2.1 and surrounding constructions](https://arxiv.org/pdf/1910.00988v3).
- [RS] C. Richard and N. Strungaru, *A short guide to pure point diffraction
  in cut-and-project sets* (2017),
  [DOI: 10.1088/1751-8121/aa5d44](https://doi.org/10.1088/1751-8121/aa5d44).
- [DS] R. M. D'Souza, *Coexisting phases and lattice dependence of a cellular
  automaton model for traffic flow* (2005),
  [DOI: 10.1103/PhysRevE.71.066112](https://doi.org/10.1103/PhysRevE.71.066112).
- [LD] N. J. Linesch and R. M. D'Souza, *Periodic states, local effects and
  coexistence in the BML traffic jam model* (2008),
  [DOI: 10.1016/j.physa.2008.06.052](https://doi.org/10.1016/j.physa.2008.06.052).
- Repository records: [theorems and quantifiers](../theorems.md),
  [freezing and nucleation](2026-11-18-freezing-gridlock-nucleation.md),
  [probability reductions](2026-11-18-probabilistic-gridlock-bounds.md), and
  [original tiling/trigonometry review](2026-11-18-bml-tilings-quasicrystals-trigonometry.md).

[AB]: https://arxiv.org/pdf/math/0607759v3
[AHM]: https://arxiv.org/pdf/math/0504001v2
[HBK]: https://arxiv.org/html/2601.01180v2
[BFG]: https://arxiv.org/pdf/1910.00988v3
[RS]: https://doi.org/10.1088/1751-8121/aa5d44
[DS]: https://doi.org/10.1103/PhysRevE.71.066112
[LD]: https://doi.org/10.1016/j.physa.2008.06.052
