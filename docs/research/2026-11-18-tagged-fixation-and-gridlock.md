# Tagged fixation and global gridlock in CLASSIC BML

**Research note — 18 November 2026.** On a finite CLASSIC torus, the existence
of even one eventually stopped car has an exact description:

\[
\boxed{S=J\cup R,}
\]

where \(J\) is eventual nonempty global gridlock and \(R\) is an initially
full eastbound row or northbound column. This note proves that deterministic
identity and derives a finite iid relationship between global gridlock and
the stopping probability of a tagged car sampled from an initially occupied
site. It proves no critical-density theorem and makes no novelty claim.

**Formal scope.** The deterministic identity, its equivalence with finitely
many actual moves, and the original-car-trace bridges are machine-checked in
[`BML/Fixation.lean`](../../formal/lean/BML/Fixation.lean). The public identity
is `BML.hasEventuallyStoppedCar_iff_jam_or_full_lane`, for positive torus
dimensions and the actual CLASSIC kernel. Section 7 records the related
exports. The Palm identities, derivative formula, probability bounds, and
limit comparisons below are prose proofs, not Lean probability theorems.
The [formal coverage register](../../formal/README.md) records the exact
validated scope and audit status.

## 1. Model and the meaning of an eventually stopped tag

Use \(\mathbb Z_W\times\mathbb Z_H\), with \(W,H\ge1\) and area
\(A=WH\). East is \(+x\), north is \(+y\), and each full round consists
of an E half-step followed by an N half-step. Movement eligibility uses the
complete snapshot at the start of each half-step. A car cannot follow another
car into a cell vacated during that same half-step. These are the repository's
[CLASSIC rules](../../bml/model.py); TRAIN is a different update rule.

Give every initial car its own tag. Tags keep their species and move with
their cars. An **eventually stopped tag** makes only finitely many individual
moves. Equivalently, there is a finite time after which it never moves and
stays at one cell forever. This includes tags that never move at all. The
condition concerns the entire future, not a finite observation
window or a small measured velocity.

Write

\[
\begin{aligned}
N(s)&=\text{number of initial cars},\\
Z(s)&=\text{number of eventually stopped original tags},\\
S&=\{Z>0\},\\
J&=\{\text{a nonempty global jam is reached after finitely many rounds}\},\\
R&=\{\text{the initial state has a full E-row or a full N-column}\}.
\end{aligned}
\]

A jam has every car's next cell occupied and is absorbing. The empty
configuration has \(N=Z=0\) and belongs to none of \(S,J,R\). This
nonempty convention prevents a vacuous empty-system exception.

E-count in each row and N-count in each column are conserved. Every E move
removes and inserts one E in the same row, and N moves leave E-counts
unchanged; the column statement is symmetric. Consequently a full E-row or
N-column found later must already have been full of that species initially.

## 2. A stopped tag eventually has a stopped successor

The central issue is whether different moving cars could keep replacing one
another immediately ahead of a stopped tag. The CLASSIC update prevents this
from happening indefinitely.

### Lemma 1: successor stabilization

If a tag stays at a cell forever from some time onward, its next cell is
eventually occupied forever by another eventually stopped tag, or by the
same tag when that direction has length one.

**Proof for an E-tag.** Let the stopped E-tag be at \(u\), with east
successor \(v\). At every sufficiently late full-round boundary, \(v\)
must be occupied; otherwise the tag would move during that round's E phase.

If \(v\) contains an N-tag at one such boundary, that N-tag cannot ever
leave. Suppose its first departure occurs in a later N phase. No other
N-car can replace it during that same phase, because \(v\) was occupied
in the pre-phase snapshot. The E phase has already occurred. Thus \(v\)
would be empty at the next full-round boundary, allowing the supposedly
stopped E-tag to move. This is a contradiction.

If \(v\) instead contains an E-tag, either it never leaves, or consider
its first departure. The original E-tag cannot follow in that same E phase.
For \(v\) to be occupied at the next boundary, an N-tag must enter during
the intervening N phase. That replacement is permanent by the preceding
argument. These exhaust the cases.

**Proof for an N-tag.** Use the snapshot **after the E phase and before the
N phase**, since that is when the stopped N-tag tests its successor \(v\).
At each sufficiently late such snapshot, \(v\) is occupied.

If its occupant is an E-tag, a later E departure would leave \(v\) empty
after that E phase: another E cannot follow into a cell occupied at the
start of the phase. The stopped N-tag would then move immediately in the N
phase. Hence that E-tag is permanent.

If the occupant is an N-tag, it either remains forever or eventually departs
in an N phase. The stopped N-tag cannot follow during that same phase. Before
its next N attempt, an E-tag must fill \(v\); otherwise the attempt succeeds.
That E replacement is permanent by the preceding argument. Singleton
directions cause no difficulty: under CLASSIC, a car whose successor is its
own occupied cell cannot move. ∎

### Corollary 2: a nonempty permanent blocker core

If \(S\) occurs, some future configuration contains a nonempty set of
permanently occupied tagged cells closed under taking the car's successor.

**Proof.** Take all eventually stopped tags. There are finitely many, so
choose a full-round boundary from which none of them moves again.
Their positions are now fixed. Lemma 1 assigns each such position an eventual
permanent successor occupant. That occupant is itself an eventually stopped
tag, so it too has already reached its final position at the chosen boundary.
The set is therefore nonempty and successor-closed at that boundary. ∎

Call such a successor-closed occupied set a **blocking core**. The geometry
needed next does not require extracting a simple cycle from it.

## 3. A core missing a lane forces a full monochromatic lane

### Lemma 3: missing-row and missing-column alternatives

A nonempty blocking core that misses a row contains a full E-row. A nonempty
blocking core that misses a column contains a full N-column.

**Proof.** Suppose row \(y_0\) contains no core cell. For every other row,
let \(d(y)=(y_0-y)\bmod H\) be its forward northward distance to that
missing row. Choose a core cell whose row minimizes \(d\). This minimum is
positive. No core cell in that row can be N: its north successor would belong
to the core at a strictly smaller distance. Thus every core cell in the
minimizing row is E. Starting from the chosen cell, successor closure now
fills that entire row with E-cars.

For a missing column, minimize the eastward cyclic distance to it. An E
successor would reduce the minimum, so every core cell in the minimizing
column is N. Successor closure fills the column. If a dimension is one, a
nonempty core cannot miss its only lane; the corresponding implication is
vacuous. ∎

### Lemma 4: route coverage forces capture

A permanently occupied core meeting every row and every column forces all
cars to stop after finitely many further moves.

**Proof.** An E-car remains in its row and cannot pass that row's permanent
obstacle. It makes at most \(W-1\) further moves. Each N-car similarly makes
at most \(H-1\) moves. Thus at most

\[
n_E(W-1)+n_N(H-1)
\]

individual moves remain. Every full round before a jam has at least one move;
a round with no moves leaves the state unchanged and absorbing. A nonempty
jam is therefore reached within the same number of further full rounds. ∎

### Theorem 5: the fixation event identity

\[
\boxed{S=J\cup R.}
\]

**Proof.** On \(J\), every original tag eventually stops. On \(R\), the
cars in the full monochromatic lane never move, so \(S\) also occurs.

Conversely, suppose \(S\) occurs but \(R\) does not. Corollary 2 gives a
nonempty permanent blocking core at some future time. If that core missed
a row or column, Lemma 3 would give a full E-row or N-column at that time.
Lane-count conservation would reflect it back to an initial full lane,
contradicting \(R^c\). The core consequently meets every row and column.
Lemma 4 gives \(J\). ∎

Outside \(R\), either every car eventually stops, or every car moves
infinitely often. The latter allows intermediate periodic traffic; it does
not mean every car eventually moves in every full round. Inside \(R\),
partial fixation is possible: the \(2\times2\) state `[[E,E],[E,0]]`
has two permanently stopped tags in the full row and one perpetually moving
tag in the other row.

The theorem yields the pointwise inequality needed for probabilities:

\[
\boxed{0\le Z-N\mathbf1_J\le N\mathbf1_R.}
\]

On \(J\), \(Z=N\). On \(J^c\cap R^c\), \(Z=0\). On
\(J^c\cap R\), the elementary bound \(0\le Z\le N\) suffices.

## 4. Sampling an initially occupied site: the Palm probability

Initialize sites independently with probabilities
\((1-p,p/2,p/2)\) for empty, E, and N. For \(p>0\), designate an initial
site \(o\) and define

\[
f(p)=\Pr(\text{the tag initially at }o\text{ eventually stops}
           \mid o\text{ is initially occupied}),\qquad
q(p)=\Pr(J).
\]

This is the **species-averaged Palm probability**: conditional on occupation,
the origin tag is E or N with probability \(1/2\) each. No equality between
the species-specific stopping probabilities is assumed.

Translation symmetry of the initial law and dynamics gives

\[
\mathbb E Z=pAf(p),\qquad \mathbb E N=pA.
\]

Indeed, write \(Z\) as the sum over initial sites of the indicator that
the site has a car and its tag eventually stops; each summand has expectation
\(pf\). Hence \(f=\mathbb E Z/\mathbb E N\). This sampling rule biases
configurations by their number of cars. It differs from first sampling a
nonempty configuration and then uniformly choosing one of its cars, which
would give \(\mathbb E[Z/N\mid N>0]\).

Let

\[
q_{\rm car}(p)=\Pr(J\mid o\text{ initially occupied}),\qquad
\delta(p)=\frac{\mathbb E[Z-N\mathbf1_J]}{pA}.
\]

Translation symmetry and Theorem 5 imply

\[
f=q_{\rm car}+\delta,
\qquad
0\le\delta\le
r_{\rm car}(p):=\Pr(R\mid o\text{ initially occupied})
\le\frac{\Pr(R)}p.
\]

For example,
\(\mathbb E[N\mathbf1_R]=A\Pr(o\text{ occupied},R)=pA r_{\rm car}\).
The correction \(\delta\) is exactly the conditional probability that
the origin tag stops while the whole system does not jam.

### The finite-density derivative identity

For \(0<p<1\),

\[
\boxed{f(p)=q(p)+\frac{1-p}{A}q'(p)+\delta(p).}
\]

**Proof.** A particular initial state with \(N\) cars has probability
\((p/2)^N(1-p)^{A-N}\). The event \(J\) is a fixed subset of the finite
configuration space, so \(q(p)\) is a polynomial obtained from a finite sum.
Differentiating that sum gives

\[
q'(p)=\frac{\mathbb E[(N-pA)\mathbf1_J]}{p(1-p)}.
\]

Thus

\[
q_{\rm car}(p)=\frac{\mathbb E[N\mathbf1_J]}{pA}
=q(p)+\frac{1-p}{A}q'(p).
\]

Combine this with \(f=q_{\rm car}+\delta\). ∎

The derivative has no assumed sign. This calculation uses neither increasingness
of the jam event under adding cars nor monotonicity of its iid probability.
All product-law calculations concern the initial state. No later state is
treated as iid.

## 5. Exact conditional ring probability and the error bound

Put \(u=p/2\). Full E-row events are independent across rows, as are full
N-column events across columns. A full E-row and a full N-column cannot
coexist because they intersect. Therefore

\[
\Pr(R)=2-(1-u^W)^H-(1-u^H)^W.
\]

Conditioning on initial occupation at \(o\) gives the sharper expression

\[
\boxed{
r_{\rm car}(p)=2-
\left(1-\frac{u^{W-1}}2\right)(1-u^W)^{H-1}
-\left(1-\frac{u^{H-1}}2\right)(1-u^H)^{W-1}.}
\]

**Proof.** Given that the origin is E, its row is full E with probability
\(u^{W-1}\). Given that it is N, its row cannot be full E. Other rows
retain their independent full-E probabilities \(u^W\). Averaging the two
equally likely origin species, the conditional probability of no full E-row
is
\((1-u^{W-1}/2)(1-u^W)^{H-1}\). The corresponding no-full-N-column
probability is
\((1-u^{H-1}/2)(1-u^H)^{W-1}\). The E-row and N-column unions remain
disjoint under conditioning, so their probabilities add. ∎

For \(W=H=L\), this simplifies to

\[
r_{\rm car}(p)=
2\left[1-\left(1-\frac{u^{L-1}}2\right)(1-u^L)^{L-1}\right].
\]

### Theorem 6: Palm fixation and global jam probability are close

For \(0<p<1\),

\[
\begin{aligned}
|f(p)-q(p)|
&\le\sqrt{\frac{(1-p)q(p)(1-q(p))}{pA}}+r_{\rm car}(p)\\
&\le\frac12\sqrt{\frac{1-p}{pA}}+\frac{\Pr(R)}p.
\end{aligned}
\]

**Proof.** The derivative identity also says

\[
q_{\rm car}-q
=\frac{\operatorname{Cov}(N,\mathbf1_J)}{pA}.
\]

Under the initial product law, \(N\) is binomial with variance
\(Ap(1-p)\). Cauchy–Schwarz bounds the covariance by
\(\sqrt{Ap(1-p)q(1-q)}\). Divide by \(pA\), use
\(f-q=(q_{\rm car}-q)+\delta\), and bound \(\delta\) by
\(r_{\rm car}\). Finally use \(q(1-q)\le1/4\) and
\(r_{\rm car}\le\Pr(R)/p\). ∎

On square tori, the initial ring union bound gives, for every \(p>0\),

\[
\frac{\Pr(R)}p
\le L(p/2)^{L-1}\le L\,2^{-(L-1)}.
\]

Consequently

\[
\boxed{\begin{aligned}
|f_L(p)-q_L(p)|
&\le\frac12\sqrt{\frac{1-p}{pL^2}}+L(p/2)^{L-1}\\
&\le\frac12\sqrt{\frac{1-p}{pL^2}}+L\,2^{-(L-1)}.
\end{aligned}}
\]

At \(p=1\), every site is occupied initially, so CLASSIC immediately jams
and \(f_L(1)=q_L(1)=1\), with \(\delta(1)=0\). The displayed error
bound remains valid by direct inspection. At \(p=0\), \(q_L(0)=0\), but
the conditional Palm probability is undefined because the origin is never
occupied. No value at zero is silently assigned.

## 6. What the reduction establishes in a large torus limit

For any fixed \(0<p\le1\),

\[
f_L(p)-q_L(p)\longrightarrow0.
\]

More generally, the same conclusion holds for sequences \(p_L>0\) with
\(p_L L^2\to\infty\): the first error term is at most
\(1/(2\sqrt{p_L L^2})\), and the second vanishes independently of density.
Thus if either sequence of probabilities has a limit, the other has the same
limit. Their liminf and limsup also agree even when convergence is unknown.

The comparison is uniform on any intervals \([a_L,1]\) with
\(0<a_L\le1\) and \(a_L L^2\to\infty\), since the same pointwise
estimate gives

\[
\sup_{p\in[a_L,1]}|f_L(p)-q_L(p)|
\le\frac1{2\sqrt{a_L L^2}}+L\,2^{-(L-1)}\longrightarrow0.
\]

Uniform approximation still makes no assertion that either family converges.

The existence-event comparison is simpler:

\[
0\le\Pr(S)-q_L(p)=\Pr(R\setminus J)
\le\Pr(R)\le2L\,2^{-L}.
\]

It holds uniformly in density. Existence of a stopped car, stopping of a
Palm-sampled car, and global gridlock are different finite events or sampling
questions; these estimates specify their asymptotic relationships.

This is a reduction of probability targets, not a proof of a threshold. A
fixed-density estimate for either \(f_L\) or \(q_L\) remains necessary.
The [probabilistic gridlock note](2026-11-18-probabilistic-gridlock-bounds.md)
states the critical-density obligations precisely.
Replacing \(q_L\) by \(f_L\) in its definitions of \(p_-\) and
\(p_+\) gives the same two endpoints, because convergence to zero or one
is equivalent at each fixed positive density. This does not establish
\(p_->0\) or \(p_-=p_+\).

For each finite \(L\), eventual stopping is defined over the entire infinite
future, or certified through exact finite-state recurrence. Only after that
definition do we take \(L\to\infty\). Nothing here identifies these limits
with a process run directly on \(\mathbb Z^2\), interchanges size and time
limits, or replaces eventual fixation by a finite cutoff. The initial-law
Palm conditioning also supplies no stationary law for evolved configurations.

## 7. Formal and finite evidence boundaries

The deterministic formalization uses positive dimensions and the actual
CLASSIC `carTrace`. Its public definitions and bridges are:

| Export | Scope |
| --- | --- |
| `TagEventuallyStopped` | An original car trace is eventually constant. |
| `tagEventuallyStopped_iff_finitely_many_moves` | For an initially present tag, eventual trace constancy is equivalent to a time after which no actual movement round occurs. |
| `HasEventuallyStoppedCar` | Some initially present original tag eventually stops. |
| `EventuallyJammed` | A nonempty jam is reached at some full-round time. |
| `hasPermanentSite_iff_hasEventuallyStoppedCar` | Connects eventually permanent occupied sites to original tags. |
| `future_blockingCore_of_permanent_site` | Produces a nonempty successor-closed future core. |
| `BlockingCore.routeCover_of_no_full_lane` | A nonempty core without a full monochromatic lane supplies all row and column obstacles. |
| `hasEventuallyStoppedCar_iff_jam_or_full_lane` | The deterministic identity \(S=J\cup R\). |
| `eventuallyJammed_every_tag_stops` | Every initially present tag stops after eventual gridlock. |
| `allCarsEventuallyStopped_iff_empty_or_jam` | All original tags stop exactly when the initial state is empty or eventually jams. |

The route-cover argument has no cycle-extraction or externally asserted
winding premise. The probability derivations in Sections 4–6 are separate
from this Lean scope.

The finite Python layer is supplied by
[`bml/fixation.py`](../../bml/fixation.py), with regression and negative
controls in [`tests/test_fixation.py`](../../tests/test_fixation.py). The
reproduction entry point is
[`scripts/check_fixation.py`](../../scripts/check_fixation.py). Its tagged
orbit census determines \(Z\) from zero movement of individual identities
on exact recurrent labeled cycles, rather than defining it from \(J\) or
\(R\). Agreement with unchanged recurrent tag positions is checked too.

A complete recurrence certificate distinguishes an eventually stopped identity
from one temporarily blocked. A return of the colored occupancy pattern does
not mean the original tags are fixed; the labeled period may be longer.
The census also compares its tagged global-jam result with the
production finite-state basin classifier and then checks \(S=J\cup R\)
and the pointwise inequality. These are finite falsification checks of the
universal theorem, not its proof.

The full census uses a source-bound independent tagged replayer. Separate
public supplied-orbit verifier controls validate identity transitions and
compare colored edges with the production kernel; they are not presented as
that slower verifier being called on every census edge. Similarly, an
arithmetic-consistent supplied count table is not automatically authenticated
as a dynamical census. Validation receipts identify the checked source
hashes, domains, controls, and outcomes. No finite check in this section
establishes an asymptotic critical density.

### Completed finite census

The completed seven-domain run checks every initial ternary configuration in
each domain. The table counts configurations, with partial fixation meaning
\(0<Z<N\), equivalently \(S\setminus J\).

| Torus \(W\times H\) | Initial states | \(S\) | \(J\) | \(R\) | Partial fixation |
| --- | ---: | ---: | ---: | ---: | ---: |
| \(2\times2\) | 81 | 36 | 28 | 34 | 8 |
| \(3\times2\) | 729 | 324 | 228 | 270 | 96 |
| \(2\times3\) | 729 | 324 | 228 | 270 | 96 |
| \(4\times2\) | 6,561 | 3,024 | 1,756 | 2,626 | 1,268 |
| \(2\times4\) | 6,561 | 3,024 | 1,756 | 2,626 | 1,268 |
| \(3\times3\) | 19,683 | 7,706 | 5,951 | 4,214 | 1,755 |
| \(4\times3\) | 531,441 | 216,348 | 167,712 | 93,906 | 48,636 |
| **Total** | **565,785** | **230,786** | **177,659** | **103,946** | **53,127** |

The independent replay covers 7,371,243 tagged full-round edges. Every orbit
reaches exact labeled recurrence within the configured budget; there are no
unresolved or cutoff-classified orbits. All pointwise event-identity and
stopped-set agreement checks pass. The receipt records matching before/after
hashes of the checked sources, and the focused regression suite passes all
69 tests.

These raw counts become probabilities by dividing each domain's counts by its
number of states only at \(p=2/3\), when all three cell states are equally
likely. At other densities, the census uses its counts by initial car number
with the exact product-law weights. The run checks the Palm identities and
bounds at \(p=1/7,1/2,2/3,1\) using rational arithmetic.

From the repository root, reproduce the focused tests and the full census
with:

```sh
python -m pytest -q tests/test_fixation.py
python scripts/check_fixation.py --report .artifacts/fixation-replay.json
```

The JSON receipt contains the per-car-count tables, stopped-tag histograms,
exact probability evaluations, verifier controls, source hashes, and resolved
orbit totals used for this evidence. Re-running these commands checks the
local source snapshot; the finite evidence does not extend the probability
claims beyond the proofs above.
