# Maximal frozen cores and the remaining path-mass estimate

**Research note — 19 November 2026.** This note concerns the CLASSIC
east-then-north kernel. Initial sites are independent with probabilities
`1-p,p/2,p/2` for empty, east, and north. All probability weights below
belong to that initial law.

The [guarded-barrier note](2026-11-19-guarded-barrier-formation.md#6-the-remaining-late-formation-probability)
reduces eventual gridlock to a remaining late-formation event. Its sufficient
uniform path bound asks for `o(1/L)` occupied-root probability. Conserved
population gives a weaker sufficient condition: **`o(1)` late-time occupied
path probability at each fixed positive density is enough.** A time supremum
can also be replaced by a late-time lower limit or long-time average.

For a maximal closed core, a stronger identification is available. Its site
set increases with time, and its eventual size is exactly the number of
original cars that stop forever. Dividing by the conserved population gives
an all-time observable whose expected limit differs from the gridlock
probability by at most the initial full-lane probability.

These are reductions and exact finite probability conversions. The estimate
making the limiting mass vanish as `L` grows remains open. The earlier
[late-defect criterion](2026-11-18-relaxation-obstructions.md#5-a-weaker-sufficient-target-late-expected-defect-density)
already uses jam coercivity and long-time averages; the additions here are
the path-specific population weighting, the maximal-core realization of
tagged fixation, and the optimal population-only envelope. No novelty claim
or fixed-positive-density nonjamming theorem is made.

## 1. Direct paths, their mass, and the maximal core

Work on a positive `W` by `H` torus with area `A=WH`. For a snapshot `s`,
let `b_s(x)` be the east successor if `s(x)=E`, and the north successor if
`s(x)=N`. Its value at empty cells can be chosen arbitrarily. Define

\[
 P_d(s)=\{x:s(b_s^j(x))\ne0\text{ for every }0\le j\le d\},
 \qquad C_d(s)=|P_d(s)|,\qquad d\ge0.
\tag{1}
\]

Here **`d` counts edges**: membership tests `d+1` occupied vertices,
including the root. In particular `C_0=N`, where `N` is the number of cars.
Repeated vertices are allowed. These are paths in one snapshot, with that
snapshot's successor function held fixed; they are not car trajectories.

The maximal frozen core is

\[
 K(s)=\bigcap_{d\ge0}P_d(s).
\tag{2}
\]

It contains every root whose direct path never reaches a hole. It can
include trees feeding a directed cycle, as well as the cycle itself.

**Finite characterization.** With `N=N(s)`,

\[
 K(s)=P_N(s)=P_A(s).
\tag{3}
\]

An occupied path with `N+1` vertices repeats an occupied site. Its future
then repeats the same deterministic successor cycle, so it never reaches
a hole. The reverse inclusions follow from (2). For `N=0` all three sets
are empty. The area cutoff uses `A` edges and `A+1` tested vertices;
there is no claim that an arbitrary shorter path already certifies a core.

Equivalently, start with all occupied sites and repeatedly remove a site
whose successor is absent. Each nonstable round removes at least one site,
so this procedure stabilizes in at most `N` removal rounds. The result is
exactly `K(s)`. The executable implementation uses predecessor lists and
a queue, processing each site and successor edge a bounded number of times.

**Maximality and permanence.** The set `K(s)` is occupied and closed under
the appropriate species successor. Conversely every occupied,
successor-closed set is contained in `K(s)`, by induction along a path.
Such a set is a `BlockingCore` in the existing formalization. During the
E phase, each core E-car has an occupied target. During the N phase, every
core N-car still has its occupied core target: core E-cars did not move,
and core N-cars have not yet moved. Thus every core car stays fixed with
the same species through the full round, and through every later round.

Writing `F` for a full CLASSIC round, this proves the sitewise inclusion

\[
 K(s)\subseteq K(F(s))\subseteq K(F^2(s))\subseteq\cdots.
\tag{4}
\]

The inclusion can be strict. The
[delayed staircase](2026-11-19-guarded-barrier-formation.md#a-long-moving-prefix-can-end-in-capture)
has an empty core throughout its all-moving prefix and a nonempty mixed
core at the prescribed capture time. Consequently the initial core mass
provides a lower bound on its eventual mass, not the needed upper bound.

## 2. The limiting core counts exactly the stopped original cars

An eventually permanent site has one fixed nonempty species at every
sufficiently late full-round boundary. Let `Q(s)` be the set of these
sites, and let `Z(s)` count original cars that eventually stop moving.

**Core-limit proposition.** For each finite initial configuration,

\[
 K(F^t(s))\uparrow Q(s),\qquad
 |K(F^t(s))|\longrightarrow Z(s).
\tag{5}
\]

Both set stabilization and count stabilization occur at some finite time
depending on the configuration. This proposition supplies no useful
uniform upper bound on that time.

**Proof.** A member of any `K(F^t(s))` is permanent from that time onward,
so belongs to `Q(s)`. In the other direction, the successor-stabilization
lemmas in the [fixation note](2026-11-18-tagged-fixation-and-gridlock.md#2-a-stopped-tag-eventually-has-a-stopped-successor)
show that an eventually permanent E-site has an eventually permanent east
successor, and an eventually permanent N-site has an eventually permanent
north successor. There are finitely many sites. Choose a common time after
which all sites in `Q(s)` have their eventual species. They form an
occupied closed core at that time, so maximality puts all of them in
`K(F^t(s))` from then onward.

It remains to check that counting permanent sites counts original tags.
CLASSIC cannot replace a departing car by another car of the same species
in the same half-step, because eligibility is read before movement. The
other species' phase cannot replace it with the original species either.
Thus a site with a constant nonempty species at successive full-round
boundaries keeps its tag. The proved car-transport bijection identifies
each eventual permanent occupant with a unique original tag. Conversely,
each eventually stopped original tag occupies one eventual permanent site.
These assignments are inverse. This proves (5). ∎

Use the population-normalized observable

\[
 G_K(s)=
 \begin{cases}|K(s)|/N(s),&N(s)>0,\\0,&N(s)=0.\end{cases}
\tag{6}
\]

Conservation and (4) make this a nondecreasing bounded sequence along every
orbit. Define `J` as eventual **nonempty** global gridlock, `R` as an
initially full E-row or N-column, and `q=Pr_p(J)`. The existing pointwise
fixation identity gives `0 <= Z-N*1_J <= N*1_R`. Dividing on nonempty
boards, using zero on the empty board, and taking expectations gives

\[
 g_\infty:=\lim_{t\to\infty}\mathbb E_p[G_K(F^t(s))]
 =\mathbb E_p\!\left[\frac ZN;\,N>0\right],
 \qquad 0\le g_\infty-q\le\Pr_p(R).
\tag{7}
\]

This sampling means: draw the initial board, then choose one of its cars
uniformly when it is nonempty. It differs from conditioning a specified
initial site to be occupied, which weights boards by their population and
gives the Palm probability in the earlier fixation note.

For square side `L`, the full-lane union bound yields

\[
 0\le g_\infty-q_L(p)\le 2L(p/2)^L.
\tag{8}
\]

The error is uniform in density, since `2L(p/2)^L <= 2L*2^(-L)` for
every `0<=p<=1`. Thus vanishing limiting expected core fraction is
equivalent to vanishing eventual-gridlock probability along **any density
sequence** `p_L`, including densities tending to zero. The pointwise
formula also handles the endpoints: at `p=0`
both quantities vanish; at `p=1` they both equal one.

## 3. Shorter paths give a weaker sufficient probability obligation

One need not explore all the way to the maximal core. For any chosen
`d>=0`, put `G_d=C_d/N` on nonempty boards and `G_d=0` on the empty board.
Let `J_t` be the event that a nonempty jam has been reached by time `t`.
A jam persists and every one of its occupied roots has an infinite
occupied direct path. Population is conserved, so pointwise

\[
 N\mathbf1_{J_t}\le C_d(F^t(s)),
 \qquad \mathbf1_{J_t}\le G_d(F^t(s)).
\tag{9}
\]

Since `Pr(J_t)` increases to `q`,

\[
 \boxed{q\le\liminf_{t\to\infty}\mathbb E_p[G_d(F^t(s))].}
\tag{10}
\]

The same statement holds with the long-time average:

\[
 \boxed{q\le\liminf_{T\to\infty}\frac1T
       \sum_{t=0}^{T-1}\mathbb E_p[G_d(F^t(s))].}
\tag{11}
\]

Indeed average (9), and use the convergence of the averages of `Pr(J_t)`
to `q`. These bounds require no full-lane exception, monotonicity of
`G_d`, time-union bound, or independence of evolved sites. For every
fixed torus, take the time limit first. The path length may depend on
the torus size, but is fixed while that time limit is taken.

### A specified-site version

Under the initial iid law, translation invariance and conservation give

\[
 a_t:=\Pr_p(o\in P_d(F^t(s)))
     =\frac1A\mathbb E_p[C_d(F^t(s))],\qquad
 N\sim\operatorname{Bin}(A,p).
\]

Set `q_t=Pr(J_t)`. From (9) and Cauchy–Schwarz,

\[
 a_t\ge pq_t-
 \sqrt{\frac{p(1-p)}Aq_t(1-q_t)}.
\tag{12}
\]

This uses `Var(N)=Ap(1-p)` and `Var(1_{J_t})=q_t(1-q_t)`;
it imposes no sign on their covariance. If `a` is either
`liminf_t a_t` or `liminf_T T^{-1} sum_{t<T} a_t`, the right-hand side
converges to the corresponding expression in `q`. For `p>0`,

\[
 \boxed{q\le\frac ap+
 \frac1{2\sqrt A}\sqrt{\frac{1-p}{p}}.}
\tag{13}
\]

One may clamp the right side at one or retain (12)'s sharper implicit
dependence on `q`. In particular, on squares and at a fixed positive
density, **`a=o(1)` suffices**. Taking `d=L-1` gives the same `L` occupied
vertices used by the earlier criterion, with the unnecessary factor `L`
removed. A uniform-in-time `o(1)` estimate also suffices, but is stronger
than the late-time or averaged input in (13).

For densities depending on `L`, division by `p` matters. This statement
does not assert uniformity down to zero density. Section 4 gives a finite
formula that retains the exact population law, including its endpoints.

## 4. An optimal conversion using only the population law

Let `m0=min(W,H)`. The proved jam-population threshold excludes `J` when
`N<m0`. Suppose an independently justified late-time path-mass bound
supplies

\[
 \mathbb E_p[N\mathbf1_J]\le z.
\tag{14}
\]

For example, an upper bound `a` on either limiting per-site mass in
Section 3 supplies `z=A*a`, by (9). An observed small value at a finite
cutoff does not supply (14).

Write `pi_m=binom(A,m)*p^m*(1-p)^(A-m)`. Then

\[
\boxed{
 q\le B(z):=\min\left\{
 \sum_{m=m_0}^A\pi_m,\quad
 \min_{m_0\le k\le A}
 \left[\frac zk+
 \sum_{m=m_0}^{k-1}\left(1-\frac mk\right)\pi_m\right]
 \right\}.}
\tag{15}
\]

**Proof.** For any admissible `k`,

\[
 \mathbf1_J\le\frac Nk\mathbf1_J+
       (1-N/k)_+\mathbf1_{\{N\ge m_0\}}.
\]

On `J` this is equality if `N<k` and an upper bound if `N>=k`.
Off `J` the right side is nonnegative. Taking expectations and applying
(14) gives the term indexed by `k`. The remaining term in (15) is the
necessary population tail. ∎

The envelope is sharp for the relaxation that knows only the population
law, the exclusion below `m0`, and (14). To see this, choose abstract
conditional event probabilities `alpha_m` with `0<=alpha_m<=1`,
`alpha_m=0` below `m0`, and `sum m*pi_m*alpha_m<=z`. Maximize
`sum pi_m*alpha_m` by filling eligible population strata from smallest
`m` upward, fractionally at at most one final stratum. If the budget
ends at stratum `k`, the attained value equals the term indexed by `k`
in (15); if all strata fit, it equals the tail. This is sharpness of
that finite linear relaxation, not a claim that BML realizes its
optimizing conditional probabilities.

Prefix sums of `pi_m` and `m*pi_m` evaluate (15) in `O(A)` arithmetic
operations once the binomial probabilities are available. The implementation
uses exact rational arithmetic, rejects floating-point inputs, and handles
`p=0`, `p=1`, zero budgets and saturation. At zero budget `B(0)=0`.

## 5. Exact controls for tempting shortcuts

### Evolved paths do not retain their initial iid probability

On the `3` by `3` torus, take `d=2`, so three occupied vertices are tested.
Exact integration of every initial configuration gives

\[
 a_0=p^3,\qquad
 a_1=\frac32p^3-\frac9{16}p^4+\frac9{32}p^5
          -\frac5{16}p^6+\frac3{32}p^7.
\tag{16}
\]

Consequently

\[
 a_1-a_0=\frac{p^3(1-p)}{32}
              (16-2p+7p^2-3p^3)>0\quad(0<p<1).
\tag{17}
\]

The last factor is positive since `16-2p>=14` and
`7p^2-3p^3>=0` in that interval. At `p=1/5`, the values are
`a_0=1/125` and `a_1=3491/312500`. Thus neither resetting the evolved
law to iid nor assuming that expected path mass decreases is sound.
This polynomial describes this complete finite domain; it is not an
asymptotic estimate for larger tori.

### Recurrent short paths can persist without stopped cars

The ringless `3` by `3` state

\[
 \begin{pmatrix}N&E&E\\0&0&0\\0&0&0\end{pmatrix}
\]

has the four-state colored orbit `14 -> 66 -> 1462 -> 1468 -> 14` in
the repository's ternary encoding. Its labeled orbit has period eight:
the two E identities exchange positions after four rounds. The counts
`C_2` are `1,0,1,0` on the colored cycle.
Every snapshot has empty maximal core, and no original car stops forever.
Nevertheless the cycle-averaged occupied-path fraction is
`(1/4)*(1+0+1+0)/9 = 1/18`. Short-path
mass is therefore a sufficient observable for (10)–(13); its vanishing
is not a necessary condition on an individual nonjam orbit.

### A long path by itself is not a frozen core

For every `L>=3`, put E-cars in row zero except for one N-car at
`x=L-1`. In row one put E-cars everywhere except for a hole at `x=L-2`.
All other rows are empty. The `2L-1` cars form one acyclic direct chain
ending at that hole, and exactly `L` roots have at least `L` occupied
vertices. No full monochromatic lane is present. A mixed cycle would
need at least `2L` cars, while a pure cycle would require a conserved
full lane. Thus this configuration cannot ever jam.

Its longest acyclic path contains all `N=2L-1` cars. Thus testing only
`N` occupied vertices is insufficient in general; the `N+1`-vertex
criterion (3) cannot be shortened for arbitrary configurations.

Uniformly translating this board gives a non-iid initial law with
root-path probability `1/L` at time zero and certain nonjamming. It
illustrates why the old uniform `o(1/L)` condition can be unnecessarily
strong, without making any claim about the iid ensemble.

## 6. Verification boundary and the next estimate

`BML/PathCore.lean` proves maximality, species persistence and monotone
spatial membership for the actual CLASSIC kernel. It proves the exact
`carCount`-edge cutoff, simultaneous eventual equality with the permanent
sites, and the equivalence between an original tag stopping and its trace
entering the core. The coverage register lists the public formal statements.
As of 21 November, `BML/StoppedCore.lean` formalizes the numeric tag/site
bridge and pointwise jam/full-lane count sandwich. `BML/CoreMass.lean`
formalizes the normalized finite initial-Nat-weight comparison with an
explicit positive common denominator, and exact eventual weighted-core
stabilization on each finite support. See the [count/mass formalization
note](2026-11-21-stopped-core-counts.md). The rational interpretation of the
integer inequality, iid full-lane estimate, population envelope, sufficient
path criteria, and asymptotic implications retain their prose scope.

`bml/path_core.py` implements finite path masks, maximal-core pruning,
an independent scalar path walk, and exact rational population envelopes.
`scripts/check_path_core.py` records its finite domain, terminal-cycle
averages, original initial-law weights, independent identity checks,
negative controls and before/after source hashes. A finite prefix is
never reclassified as a complete eventual outcome.

The complete finite census has the following scope. The last column counts
initial states whose eventual orbit is ringless and nonjammed but has positive
mean path mass at `d=L-1`; it does not count distinct recurrent cycles.

| Square side | Initial states | Independently replayed labeled edges | Initial states with later core growth | Ringless nonjam states with recurrent paths |
|---|---:|---:|---:|---:|
| 2 | 81 | 177 | 0 | 28 |
| 3 | 19,683 | 162,141 | 5,121 | 9,387 |

On `3` by `3`, all `52,002` final core-site incidences across initial states
agree with stopped original-tag incidences. The exact population envelope
is checked against the independent optimization that fills the smallest
eligible populations first. Neither the domain counts nor these finite
identities extrapolate to a fixed-density limit.

```sh
python -m pytest -q tests/test_path_core.py
python scripts/check_path_core.py --report .artifacts/path-core-replay.json
cd formal/lean
lake build
lake env lean Audit.lean
```

The remaining analytic target can now be stated in either of two ways.
For each fixed `p` in some interval `(0,p_*)`, prove

\[
 \lim_{L\to\infty}\lim_{t\to\infty}
       \mathbb E_p[G_K(F^t(s))]=0,
\tag{18}
\]

or prove the sufficient, potentially more local estimate

\[
 \lim_{L\to\infty}\liminf_{T\to\infty}\frac1T
       \sum_{t=0}^{T-1}
       \Pr_p(o\in P_{L-1}(F^t(s)))=0.
\tag{19}
\]

The order of limits is part of the obligation. Fixed-time rarity and
the current logarithmic exclusion window do not supply either estimate.
The increasing core records all later arrivals into a permanent blocking
set; bounding that growth under the original iid law is the unresolved
probability step. Equations (7), (10), (13), and (15) specify exactly how
such an estimate would imply eventual nonjamming.
