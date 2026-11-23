# Protected queues delay gridlock in CLASSIC BML

**Research note — 18 November 2026. No novelty claim.** A two-row pattern
forces an original car to make its first move at a prescribed future round,
regardless of every exterior cell. Counting these patterns under the initial
iid law gives an exact finite upper bound on early gridlock. At each fixed
\(0<p<1\), it gives logarithmic lower bounds on the gridlock time with
every coefficient strictly below \(1/\log(2/p)\). The pattern delays
gridlock; it does not rule out eventual gridlock.

**Proof status.** The deterministic shrinking queue, identity tracking, first
movement, and exclusion of jams through that time are proved for the actual
CLASSIC kernel in
[`BML/GuardedQueue.lean`](../../formal/lean/BML/GuardedQueue.lean).
The initial-iid integration, cyclic avoidance polynomial, probability limits,
and bounded-observation completion proposition below have prose proofs.
Section 7 states the implementation scope; the
[formal coverage register](../../formal/README.md) records validation status.

## 1. Model and the protected pattern

Work on a \(W\times H\) torus with \(W,H\ge2\). Coordinates are
\((x,y)\), modulo \(W,H\); east increases \(x\), and north increases
\(y\). A full CLASSIC round applies the synchronous E half-step and then
the synchronous N half-step. Each move requires its destination to be empty
at the beginning of that half-step. Write \(F\) for this full-round map.
The time-\(t\) state \(F^t(s)\) is the state immediately before round
\(t\)'s E-phase; the initial round has index zero.

A jam is a nonempty configuration with no possible movement, and is
absorbing. Define

\[
\tau_J(s)=\inf\{t\ge0:F^t(s)\text{ is a nonempty jam}\},
\]

with \(\inf\varnothing=\infty\). The empty state is not a jam.

Fix \(0\le T\le W-2\). Up to translation, prescribe these cells:

| Part | Prescribed cells | Number |
| --- | --- | ---: |
| Main queue | E at \((x,1)\), \(0\le x\le T\) | \(T+1\) |
| Main hole | Empty at \((T+1,1)\) | 1 |
| Lower guard | E at \((x,0)\), \(1\le x\le T\) | \(T\) |

The guard is empty when \(T=0\). There is no condition on either lower-row
endpoint \((0,0)\) or \((T+1,0)\), or on any other cell. The footprint
fits inside two adjacent rows and \(T+2\) consecutive cyclic columns.
The width restriction and distinct rows ensure that the prescribed sites
are distinct. In particular, the pattern specifies exactly \(2T+1\)
E-cars and one hole.

### Theorem 1: an original car first moves in round \(T\)

For every completion of the exterior, the original E-car at \((0,1)\)
stays there through the beginning of round \(T\), moves east during that
round, and is at \((1,1)\) after the full round. Consequently

\[
\boxed{\tau_J>T.}
\]

**Proof.** We prove the following invariant at the beginning of every round
\(0\le t\le T\):

\[
\begin{array}{ll}
\text{main row:}&E\text{ at }0,\ldots,T-t,
\quad0\text{ at }T+1-t;\\
\text{lower row:}&E\text{ at }1,\ldots,T-t.
\end{array}
\]

An interval with no indices is empty. The invariant holds initially by the
prescription. Suppose it holds at time \(t<T\), and put \(j=T-t\ge1\).
The main car at \(j\) has an empty east destination \(j+1\), so it moves.
Every main car at a smaller index stays: its destination was another E-cell
at the beginning of this synchronous half-step. The newly vacated main cell
\(j\) is therefore empty immediately after the E-phase.

The lower cells \(1,\ldots,j-1\) also stay E, because each has an occupied
E-successor at the start of that phase. The lower car at \(j\) may move
or remain. In either case, the lower cell \(j\) is E or empty after the
E-phase; it cannot become N during an E-update. Hence it cannot supply a
north-moving car to the new main hole during the ensuing N-phase. An N-car
that enters this lower cell during that N-phase cannot immediately move
again: all north eligibility decisions use the pre-N snapshot. No other
site can send a north car to the main hole, since its north predecessor is
unique. Thus the main hole survives, and all stated E-cells survive the
N-phase. This is the invariant at \(t+1\).

The argument also tracks the original rear identity. At every \(t<T\),
its east successor at index one is occupied, so the rear car does not move
in the E-phase. An E-car never moves in the N-phase. It therefore remains
the original car at index zero, rather than merely being replaced by a car
of the same color. At time \(T\), the invariant gives that car at zero and
a hole at one. The car moves east, and remains at one during the N-phase.
The final newly vacated cell needs no guard, because the required movement
has already occurred.

In particular, the time-\(T\) state is not a jam. An earlier jam would be
absorbing and prevent this movement, so no jam occurs at any time at most
\(T\). ∎

This proof includes \(T=0\) and \(T=W-2\), as well as translated
patterns that cross the horizontal boundary. It uses no assumption about
the exterior's later behavior.

## 2. Exact avoidance on one row pair

Initially, different cells independently take values empty, E, N with
probabilities \((1-p,p/2,p/2)\). Let \(u=p/2\), set \(s=T+2\), and
write \(A_x\) for the protected pattern starting at cyclic column \(x\)
on a fixed lower/main row pair. Each event has probability

\[
\boxed{w_T=(1-p)u^{2T+1}.}
\]

Only the initial configuration has a product law. The deterministic theorem
then controls the actual evolution of any state satisfying the pattern.

### Overlap makes horizontal patterns incompatible

If distinct length-\(s\) main windows overlap, the corresponding events
cannot both occur. To see this, translate one start to zero and write the
other as \(d\in\{1,\ldots,W-1\}\). If \(d\le s-1\), the first
window's final hole lies in the second window's E-run. If
\(d\ge W-s+1\), the second window's final hole lies in the first
window's E-run. These are exactly the two ways cyclic windows can overlap.
If neither inequality holds, their column sets are disjoint. The argument
also includes \(s=W\), when every pair of distinct starts is incompatible.

Disjoint main windows give disjoint entire supports, because each guard is
contained in its main window's columns. Their pattern events are therefore
independent. Thus intersections of several \(A_x\)'s have probability
zero if any two windows overlap, and probability \(w_T^k\) if the
\(k\) windows are disjoint.

### Proposition 2: the cyclic avoidance polynomial

Put \(a(W,s,0)=1\). For \(1\le k\le\lfloor W/s\rfloor\), define

\[
a(W,s,k)=\frac Wk
\binom{W-k(s-1)-1}{k-1}.
\]

The exact probability of no protected pattern on this row pair is

\[
\boxed{
Q_{W,s}(w_T)
=\sum_{k=0}^{\lfloor W/s\rfloor}(-w_T)^k a(W,s,k).}
\]

**Proof.** For \(k\ge1\), distinguish one start among \(k\) disjoint
cyclic windows. There are \(W\) choices for that start. In cyclic order,
the distances \(d_1,\ldots,d_k\) between successive starts are at least
\(s\) and sum to \(W\). The nonnegative integers \(d_i-s\) therefore
sum to \(W-ks\). The number of such ordered choices is the number of
weak compositions,

\[
\binom{W-ks+k-1}{k-1}.
\]

Every unordered start set was counted \(k\) times, once for each possible
distinguished start. This gives \(a(W,s,k)\), which is an integer despite
its fractional-looking formula. No larger disjoint collection exists when
\(k>\lfloor W/s\rfloor\). Apply finite inclusion–exclusion, using the
intersection probabilities just proved. ∎

For a full-width window, \(s=W\), the formula reduces to
\(Q_{W,W}(w_T)=1-Ww_T\). The probability interpretation is asserted at
the physical pattern weight \(w_T\); an arbitrary substituted number
need not define a valid pattern law.

### A simpler product upper bound without an independence assumption

For the same row pair,

\[
\boxed{Q_{W,s}(w_T)\le(1-w_T)^W.}
\]

**Proof.** Order the \(W\) pattern events arbitrarily. Before considering
\(A_i\), split the earlier events into those whose windows overlap its
window and those whose windows are disjoint from it. Let \(D\) be joint
avoidance of the latter group, and \(G\) joint avoidance of all earlier
events. Because overlapping events are incompatible with \(A_i\),

\[
\Pr(A_i\cap G)=\Pr(A_i\cap D)=w_T\Pr(D)\ge w_T\Pr(G).
\]

The middle equality uses independence of \(A_i\) from the entire union
of the disjoint windows' supports; it does not require those other events
to be independent of each other. If \(\Pr(G)>0\), this yields
\(\Pr(A_i\mid G)\ge w_T\). If \(\Pr(G)=0\), the final avoidance
probability is already zero. Multiplying the successive conditional
avoidance probabilities proves the claim. ∎

## 3. A finite bound on early gridlock

Choose \(r=\lfloor H/2\rfloor\) disjoint adjacent row pairs, with lower
rows \(0,2,\ldots,2r-2\) and main rows \(1,3,\ldots,2r-1\). Their
initial pattern events involve disjoint rows, hence the row-pair avoidance
events are independent.

### Theorem 3: exact witness-avoidance and exponential bounds

For \(W,H\ge2\), \(0\le T\le W-2\), and \(0\le p\le1\),

\[
\boxed{\begin{aligned}
\Pr_p(\tau_J\le T)
&\le Q_{W,T+2}(w_T)^{\lfloor H/2\rfloor}\\
&\le(1-w_T)^{W\lfloor H/2\rfloor}\\
&\le\exp\{-W\lfloor H/2\rfloor(1-p)(p/2)^{2T+1}\}.
\end{aligned}}
\]

**Proof.** If any chosen row pair has any horizontally translated protected
pattern, Theorem 1 excludes \(\tau_J\le T\). Therefore early gridlock
requires avoidance in every chosen row pair. Multiply their exact avoidance
probabilities, then apply the preceding product bound and
\(1-z\le e^{-z}\). ∎

The polynomial gives the exact probability of avoiding this selected family
of witnesses. It is an upper bound on the early-gridlock probability, not an
exact formula for that probability. Future interactions between different
row pairs do not affect this reasoning: initial independence supplies the
probability calculation, and the witness theorem already permits arbitrary
exterior dynamics.

The formulas use the same number \(\lfloor H/2\rfloor\) of row pairs
at \(T=0\). At \(p=0\) or \(p=1\), the witness weight is zero, so
the displayed bound is the valid but uninformative upper bound one. Directly,
\(p=0\) gives the empty state and \(\tau_J=\infty\), whereas \(p=1\)
gives a nonempty jam at time zero.

### Why all vertical translations cannot be multiplied

Disjoint row pairs are a substantive condition. On a \(3\times3\) torus,
take \(T=1,p=1/2\), so \(w_T=1/128\), and consider all nine cyclic
horizontal/vertical starts. Their exact avoidance probability is

\[
\frac{15301}{16384}>
\left(\frac{127}{128}\right)^9.
\]

Here is a direct calculation. A main row has two E-cars and a hole, with
specified-hole probability \(1/32\). Its lower guard requires one extra
E-cell. Each of the nine individual events has probability \(1/128\).
Distinct starts in the same main row are incompatible. For each pair of
distinct main rows, six of the nine choices of their hole positions are
compatible with the guard on the shared row. There are therefore 18
compatible event pairs, each of probability \(1/4096\).

For three events, one in each main row, their hole positions \(h_j\) must
satisfy \(h_{j-1}\ne h_j-1\pmod3\) for all three rows. There are six
such assignments, each of probability \(1/32768\). No four events can
coexist. Inclusion–exclusion gives

\[
1-\frac9{128}+\frac{18}{4096}-\frac6{32768}
=\frac{15301}{16384}.
\]

The displayed strict comparison follows by exact rational arithmetic. It
shows that the horizontal incompatibility argument cannot be extended to
overlapping vertical pairs: some of their shared E-requirements create
positive dependence.

## 4. A logarithmic gridlock-time lower bound at fixed density

Fix \(0<p<1\), and consider \(L\times L\) tori. Put
\(a=\log(2/p)>0\), with natural logarithms.

### Corollary 4: the leading coefficient

For every fixed \(0<c<1/a\),

\[
\boxed{\Pr_p\!\left(\tau_J\le\lfloor c\log L\rfloor\right)
\longrightarrow0.}
\]

**Proof.** The indicated time lies in \([0,L-2]\) eventually. Since
\(T\le c\log L\),

\[
w_T=(1-p)(p/2)e^{-2aT}
\ge(1-p)(p/2)L^{-2ac}.
\]

Also \(L\lfloor L/2\rfloor\ge L(L-1)/2\). The exponent in
Theorem 3 is therefore at least

\[
\frac{(1-p)(p/2)}2(1-1/L)L^{2-2ac},
\]

which tends to infinity because \(ac<1\). ∎

The conclusion allows \(\tau_J=\infty\). It is a lower bound on the
time of any eventual jam, not a claim that a jam ultimately occurs.

### A centered lower-tail estimate

For any real \(b\) such that

\[
T=\left\lfloor\frac{\log L-b}{a}\right\rfloor
\quad\text{satisfies}\quad0\le T\le L-2,
\]

Theorem 3 gives the explicit bound

\[
\boxed{
\Pr_p(\tau_J\le T)
\le\exp\left\{-\frac{(1-p)(p/2)}2
(1-1/L)e^{2b}\right\}.}
\]

Indeed, \(aT\le\log L-b\) implies
\(w_T\ge(1-p)(p/2)L^{-2}e^{2b}\), and the same bound on the number
of candidate starts applies. Thus any \(b_L\to\infty\) with
\(b_L=o(\log L)\) yields

\[
\Pr_p\!\left(
\tau_J\le\left\lfloor\frac{\log L-b_L}{\log(2/p)}\right\rfloor
\right)\longrightarrow0.
\]

The absence of a \(\log\log L\) packing penalty comes from using all
cyclic horizontal starts with their proved incompatibility structure.
These asymptotic statements fix \(p\) strictly between zero and one.
The finite theorem remains valid for varying densities, but a varying-density
limit requires its own control of the displayed exponent.

## 5. What this delays, and what it leaves open

The [relaxation note](2026-11-18-relaxation-obstructions.md) proves a different
queue obstruction: a car remains blocked long enough to delay permanent full
flow. Here the protected hole guarantees an actual movement at a late time,
which delays complete gridlock. A long initial queue without this protection
need not supply the latter conclusion, because a north car could refill its
hole.

This result also differs from a lower bound on the time of mixed blocking-core
formation. A permanent core can coexist with other cars that are still moving
toward capture. The completion in Section 6 makes this distinction explicit:
it has the protected late-moving tag and an initial mixed core, and eventually
jams.

For each fixed \(L\), \(\Pr_p(\tau_J\le T)\) increases to the eventual
jam probability \(q_L(p)\) as \(T\to\infty\). A bound at
\(T=O(\log L)\) does not control that entire future. It is consistent
with eventual gridlock with probability tending to one in a high-density
regime, as well as with nonjamming. The theorem improves a quantitative time
scale, but does not establish a positive nonjamming interval, a sharp critical
density, or existence of all fixed-density limits. The remaining basin and
limit obligations are stated in the
[probability note](2026-11-18-probabilistic-gridlock-bounds.md).

## 6. Companion proposition: bounded observations admit jammed completions

Let an observed cyclic \(w\times h\) rectangle on an \(L\times L\)
torus have lower-left coordinate \((x_0,y_0)\), with \(w,h\ge1\) and
\(L\ge w+h+1\). Every assignment of empty, E, or N values on this
rectangle has a completion that eventually jams while preserving every
observed cell.

**Proof.** Let \(d_0=x_0-y_0\) and take
\(a=d_0+w\pmod L\). In the observed rectangle, the difference \(x-y\)
has an integer representative in

\[
[d_0-h+1,\ d_0+w-1].
\]

Neither residue \(a\) nor \(a+1\) occurs there. Relative to \(a\), the
displayed representatives differ by integers in \([-(w+h-1),-1]\);
relative to \(a+1\), by integers in \([-(w+h),-2]\). The size hypothesis
keeps both intervals strictly between \(-L\) and zero, so neither contains
a multiple of \(L\).

Preserve the observed values. Outside the rectangle, fill every site with
\(x-y=a\) with E and every site with \(x-y=a+1\) with N. Assign every
remaining unobserved cell arbitrarily. These two disjoint diagonals form a
permanent staircase: an E-car's east successor is an N-car, and that N-car's
north successor is an E-car. Traversing these alternating successors gives a
mixed simple cycle of length \(2L\). The cycle meets every row and column
and none of its cars ever moves.

Each other E-car can make at most \(L-1\) moves before meeting a permanent
obstacle in its row. Each N-car has the analogous bound in its column.
Writing \(n_E,n_N\) for the completed configuration's populations, at most

\[
n_E(L-1)+n_N(L-1)
\]

individual moves remain. Every full round before a nonempty jam has at least
one actual move. Hence the completed system reaches a nonempty jam within
that many rounds. This is the route-cover capture argument, applied to the
explicit staircase. ∎

Consequently, a predicate based solely on the assignment in this prescribed
rectangle, and universally sound for excluding eventual gridlock for every
exterior completion, must reject every pattern. This says nothing about the
conditional probability of different exteriors, and does not address global
conditions combining multiple observation boxes.

For the protected queue, take \(w=T+2,h=2\). When \(L\ge T+5\), the
proposition produces a completion that preserves the whole queue footprint,
has a mixed permanent core already at time zero, and eventually jams. Its
original rear car nevertheless makes its first move in round \(T\), so
\(T<\tau_J<\infty\). This supplies a direct distinction between a late
movement certificate, exclusion of an early core, and exclusion of the jam
basin. The geometric completion statement is a prose result, not a new Lean
theorem in this increment.

## 7. Formal and computational scope

The formal structure `GuardedEastQueue east north T p s` describes a main
run of \(T+1\) E-cars starting at \(p\), its following hole, and a lower
guard run of \(T\) E-cars starting at `north.prev (east.next p)`.
The proved public interfaces include:

| Export | Scope |
| --- | --- |
| `GuardedEastQueue.step`, `.iterate` | One-round shrinking and its iteration for the actual kernel. |
| `.rear_blocked_before`, `.rear_trace` | Earlier blocking and the original rear identity's unchanged position through time \(T\). |
| `.rear_canMove`, `.rear_first_move` | Actual movement in round \(T\), including the trace at \(T+1\) and a distinct destination. |
| `.jam_after`, `.no_jam_through` | Any time of nonempty gridlock is strictly greater than \(T\). |
| `torus_guardedEastQueue_first_move` | The first-move result for the actual torus directions. |
| `torus_guardedEastQueue_jam_after`, `torus_guardedEastQueue_no_jam_through` | The corresponding torus jam-time exclusions. |

The generic shrinking argument requires the east-successor and
north-predecessor maps to commute; the torus wrappers discharge that
geometric premise. The deterministic formalization needs positive torus
dimensions and the actual pattern, rather than separate probability counting
assumptions. The restrictions \(H\ge2\) and \(T+2\le W\) used here
ensure distinct prescribed sites when computing the iid pattern weight.
No probability law or cyclic avoidance theorem is formalized in these Lean
exports.

The Python layer is provided by
[`bml/guarded_queue.py`](../../bml/guarded_queue.py), with tests in
[`tests/test_guarded_queue.py`](../../tests/test_guarded_queue.py) and the
reproduction entry point
[`scripts/check_guarded_queue.py`](../../scripts/check_guarded_queue.py).
Its public interfaces are:

| Interface | Scope |
| --- | --- |
| `GuardedQueueCertificate(width, height, start_x, row, delay)` | The dimensions, translation, and delay of the prescribed reduced pattern. |
| `construct_guarded_queue(..., exterior=None)` | Constructs that pattern while retaining the supplied exterior outside its prescribed cells. |
| `verify_guarded_queue(rows, certificate)` | Checks the exact pattern, independently replays the original identities through round \(T\), and checks both colored production half-steps and their movement counts. |
| `guarded_queue_bounds(width, height, delay, p)` | Computes the exact rational pattern mass, cyclic placement counts, cyclic avoidance probability, early-gridlock upper bound, and simpler product bound. |

The bounds API requires \(W,H\ge2\), \(0\le T\le W-2\), and an exact
rational density in \([0,1]\). It uses exactly \(\lfloor H/2\rfloor\)
disjoint row pairs, including at \(T=0\); it does not silently substitute
all rows in that case. These are bounds on early gridlock, not estimates of
eventual gridlock probability.

The frozen source-bound census passed on all twelve tori with
\(W,H\ge2\) and \(WH\le12\), including every admissible delay and
every exterior assignment to a canonical protected pattern. The translated
cases and the public-verifier calls have distinct scopes:

| Validation scope | Count |
| --- | ---: |
| Canonical exterior cases, across all dimensions and delays | 275,526 |
| All translated cases checked by independent scalar identity replay | 3,263,850 |
| Canonical replay rounds compared with both production half-steps | 299,673 |
| Separate representative calls to the public verifier | 508 |
| Complete initial configurations on the twelve tori | 2,278,206 |
| Finite-time pattern-avoidance and nonempty-gridlock predicates | 6,208,974 |
| Exact iid comparisons at \(p=0,1/10,1/2,4/5,1\) | 130 |

The complete initial-state integration matches the cyclic avoidance
polynomial exactly and checks the actual finite-time gridlock probability
against both upper bounds. The exterior census does not call the public
verifier on every translated case: it uses its own scalar tagged replay,
with production comparison on the canonical cases, and reports the 508
public-verifier calls separately.

Eight rejection controls cover an omitted guard, an initially empty guard,
inconsistent dimensions, a Boolean delay, floating-point density, the TRAIN
rule, a same-species identity swap, and a corrupted production movement
count. Two further exact controls refute incorrect probability assumptions:
the vertical-overlap counterexample in Section 3, and reuse of the initial
iid law after an update. For the latter, on the \(3\times3\) torus with
\(T=1,p=1/2\), one specified pattern has initial mass \(1/128\) but
time-one mass \(7/1024\).

All nine source SHA-256 digests recorded before and after the census agree
and match the frozen files. The receipt records Python 3.12.14, NumPy 2.3.5,
and a runtime of 27.662461 seconds. The 60 focused tests also passed.
From the repository root, reproduce the focused tests and source-bound
receipt with:

```sh
python -m pytest -q tests/test_guarded_queue.py
python scripts/check_guarded_queue.py --report .artifacts/guarded-queue-replay.json
```

The exact finite avoidance calculation supports the specified family of
witnesses. The logarithmic probability theorem and the bounded-observation
completion proposition rely on their proofs above; neither finite
enumeration nor the tagged verifier proves an asymptotic critical-density
theorem.
