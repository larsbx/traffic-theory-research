# Guarded barriers and logarithmic mixed-cycle delay

**Research note — 19 November 2026.** The CLASSIC model uses simultaneous
east movement followed by simultaneous north movement, with vacancy tested
at the start of each half-step. Initial cells on the square torus are
independent with probabilities `1-p,p/2,p/2` for empty, east, and north.

The [diagonal-cut estimate](2026-11-18-diagonal-cuts.md) excludes a first
mixed direct-blocker cycle up to order `sqrt(log L)` at every fixed
`0<p<1`. A new initial certificate below has only `6T` prescribed cars and
one hole. It yields a **logarithmic** first-formation delay at each fixed
density, and, combined with the earlier cut, a uniform
`log L / log log L` delay over every interval `0<=p<=p0<1`.

These estimates concern the first mixed cycle, which can precede complete
gridlock. The probability of formation after the new cutoff remains open.
In particular this note proves no fixed-positive-density nonjamming interval.
No novelty claim is made.

## 1. A finite initial-law bound

Let `A_T` be the event that the time-`T` snapshot contains a simple mixed
direct-blocker cycle. Such a cycle is permanent, so this is also the event
that the first such cycle has formed by time `T`. Write

\[
 s_T=4T+1,\qquad
 K_T(L)=\max\left\{0,\left\lfloor\frac{L-3T-1}{4T+1}\right\rfloor\right\},
 \qquad \delta_T(p)=(1-p)(p/2)^{6T}.
\]

For `L>=2`, integer `T>=0`, and `0<=p<=1`,

\[
\boxed{\Pr_p(A_T)\le
 U_{\mathrm{guard}}(L,p,T):=
 \min\left\{1,\frac{Lp}{2}\bigl(1-\delta_T(p)\bigr)^{K_T(L)}\right\}.}
\tag{1}
\]

At `T=0`, the certificate is just one empty successor and (1) becomes
`min(1,L*p^L/2)`. At `p=0` the event is impossible; the zero-population
endpoint is handled directly. At `p=1` the bound is one. A side-one torus
has no simple mixed cycle, so its probability is zero.

## 2. The deterministic barrier

Work first in integer coordinates. Choose nonnegative wall lengths `a,b`,
a time `T`, southwest coordinates `(x0,y0)`, and corner
`(X,Y)=(x0+a,y0+b)`. Prescribe only the following initial sites:

| Sites | Initial value | Number |
|---|---|---:|
| `(x,Y)`, `x0<=x<X` | E | `a` |
| `(X,y)`, `y0<=y<Y+T` | N | `b+T` |
| `(X-1,y)`, `Y<y<=Y+T` | N | `T` |
| `(X,Y+T)` | empty | `1` |

All other cells are arbitrary. When these sites project distinctly to a
torus, the initial product-law weight is
`(1-p)*(p/2)^(a+b+2T)`.

**Barrier lemma.** At full-round boundary `T`, the horizontal E wall and
the lower vertical N wall remain, while their shared northeast corner is
empty:

\[
\begin{aligned}
 F^T(s)(x,Y)&=E &&(x_0\le x<X),\\
 F^T(s)(X,y)&=N &&(y_0\le y<Y),\\
 F^T(s)(X,Y)&=0.
\end{aligned}
\tag{2}
\]

**Proof.** At time `t<T`, the main N prefix extends through
`Y+T-t-1`, its hole is at `(X,Y+T-t)`, and the N guard in column `X-1`
extends from `Y+1` through `Y+T-t`. A north queue loses at most its
leading car in a round, so these prefixes persist as stated.

During the next E phase, the old hole has an N car immediately west of it.
It therefore stays empty. Its N predecessor is unchanged by the E phase
and moves into that hole in the N phase, leaving the new hole one cell
south. All earlier N cars remain blocked during that simultaneous phase.
The guard prefix shortens by at most one. This proves the induction for
the descending hole.

The corner `(X,Y)` contains N before every E phase strictly before time
`T`. It blocks the last E car of the horizontal wall, and every earlier
wall car is blocked by the next one. The N phase preserves E occupancy.
In the final N phase the corner empties, after the E wall has already had
its last opportunity to move. This gives (2). The argument includes
zero-length walls and `T=0`. No assumption is made about the exterior. ∎

**Path consequence.** Any northeast direct-blocker path beginning at
`(x0,y0)` either stops earlier or reaches the empty corner in at most
`a+b` edges. Indeed, upon reaching the top boundary it follows the E wall;
upon reaching the right boundary it follows the N wall. Neither boundary
allows it to leave the rectangle away from the corner. Each edge increases
`x+y` by one, and the corner is empty.

The actual-kernel statements (2), including the arbitrary-exterior
quantification and the rectangular torus adapter, are proved in
[`BML/Barrier.lean`](../../formal/lean/BML/Barrier.lean). The spatial
path argument and probability calculation are prose proofs.

## 3. Adaptive exploration without an evolved iid assumption

Use the exploration from the diagonal-cut note. To determine the time-`T`
color at a lifted vertex `z`, reveal its radius-`T` initial box. Kernel
locality is proved in `BML/Locality.lean`. If the root is `z0` and the
exploration has survived through vertex `z` at path index `j`, every
revealed site has a chosen lift with height `H=x+y` in

\[
 [H(z_0)-2T,\ H(z)+2T],\qquad H(z)=H(z_0)+j.
\]

The direction `d` at `z` is now known. Set `u=z+d`, put the southwest
corner of the barrier at `u`, and take `a=b=2T`. Its initial footprint has
exactly `6T` cars and one hole. Its lifted heights lie in

\[
 [H(z)+2T+1,\ H(z)+5T+1].
\tag{3}
\]

This footprint lies strictly above every already revealed site. If

\[
 j+(4T+1)+3T<L,
\tag{4}
\]

the union of old and candidate lifts has height span less than `L`.
Two lifts projecting to the same torus site have heights differing by a
multiple of `L`, so an old revealed site cannot coincide with a candidate
site. The candidate sites are also distinct from each other: their
horizontal extent is at most `2T` and vertical extent at most `3T`, both
strictly less than `L` whenever a trial is admissible. At `T=0` the
footprint is a single site.

Condition on any surviving exploration transcript. Addresses of queried
sites are functions of previously revealed values, so the transcript
specifies only those values at those addresses. Unqueried initial cells
retain their independent original laws. The barrier may depend on the
known direction `d`, but its fresh sites therefore satisfy the prescription
with conditional probability exactly `delta_T(p)`.

On that event, the path stops by index `j+1+4T=j+s_T`. The exploration
does not need to reveal the candidate barrier separately: the conditional
event supplies a lower bound on stopping in the next `s_T` edges. Continue
the ordinary local exploration if it survives. Conditions (3)–(4) apply
again at `j=0,s_T,...,(K_T(L)-1)s_T`.

Iterated conditioning thus bounds survival from a specified root through
index `K_T(L)*s_T` by

\[
 p(1-\delta_T(p))^{K_T(L)}.
\tag{5}
\]

Here the leading `p` follows from initial translation invariance and
conservation: the marginal occupied-site probability at time `T` is `p`.
No independence between time-`T` sites is asserted. When `K_T(L)=0`, (5)
is just that marginal statement.

As in the earlier diagonal-cut proof, every simple mixed cycle winds
positively in both coordinates and visits the layer `H=0 mod L` at least
twice at distinct vertices. There are `L` roots in this layer. A cycle
contributes at least two surviving roots, so Markov's inequality applied
to their number gives (1).

## 4. Logarithmic delay at a fixed density

Fix `0<p<1` and choose

\[
 0<c<\frac{1}{6\log(2/p)},\qquad T_L=\lfloor c\log L\rfloor.
\]

Then

\[
 \delta_{T_L}(p)=L^{-6c\log(2/p)+o(1)},\qquad
 K_{T_L}(L)=\frac{L}{4c\log L}(1+o(1)).
\]

Their product grows faster than `log L`. Consequently (1) yields

\[
\boxed{\Pr_p(\tau_M\le\lfloor c\log L\rfloor)\longrightarrow0,}
\tag{6}
\]

where `tau_M` is the first mixed-cycle time, with infinity if none forms.
More explicitly, for `epsilon=1-6c*log(2/p)>0`, the upper bound has the
form `L*exp(-C*L^epsilon/log L)` for some `C>0` and all sufficiently
large `L`.

The same proof is uniform over any fixed compact density interval
`0<p_min<=p<=p_max<1`, with `c<1/(6*log(2/p_min))`. The occupied-barrier
weight is not monotone in density over `(0,1)`, so substituting `p_max`
does not establish uniformity down to zero.

## 5. Uniform delay, including densities tending to zero

Let `U_empty` be the earlier diagonal-cut bound, with

\[
 w_T(p)=(1-p)^{a_T}(1-p/2)^{b_T},\quad
 a_T=\frac{(T+1)(5T+2)}2,\quad b_T=T(T+1),
\]

and `K_empty=max(0,floor((L-2T-1)/(3T+1)))`. Both certificates give
valid bounds, so their minimum is also an upper bound. No independence
between the two certificate events is needed.

Fix `0<=p0<1` and `0<c<1/6`. For sufficiently large `L`, put

\[
 T_L=\left\lfloor\frac{c\log L}{\log\log L}\right\rfloor.
\]

Then

\[
\boxed{\sup_{0\le p\le p_0}\Pr_p(\tau_M\le T_L)\longrightarrow0.}
\tag{7}
\]

**Proof.** Eventually `T=T_L>=2`. If `p<=1/T`, the elementary bounds
`-log(1-p)<=2p` and `-log(1-p/2)<=p` give

\[
 -\log w_T(p)\le 2pa_T+pb_T
 \le 6T+8+2/T\le 6T+9.
\]

Thus `K_empty*w_T(p)>=K_empty*exp(-6T-9)=L^(1-o(1))`, uniformly in
this density range. If `1/T<=p<=p0`, the new certificate gives

\[
 \delta_T(p)\ge(1-p_0)(2T)^{-6T}=L^{-6c+o(1)}.
\]

Hence `K_T(L)*delta_T(p)>=L^(1-6c+o(1))` uniformly in the second
range. Both products dominate `log L`. Applying `1-x<=exp(-x)` and
the common prefactor at most `L/2` proves (7). The case `p=0` is immediate. ∎

This bound permits arbitrary density sequences below `p0`; it does not
assume monotonicity of the eventual-gridlock event or its probability.

## 6. The remaining late-formation probability

Let `q_L(p)` be eventual nonempty global-gridlock probability, and let `R`
be an initially full E-row or N-column. The existing event identity gives,
for every finite cutoff `T`,

\[
 0\le q_L(p)-\Pr_p(T<\tau_M<\infty)
 \le 2L(p/2)^L+\Pr_p(A_T).
\tag{8}
\]

Substitute either (6) or (7). At the corresponding cutoff, the right side
tends to zero in its stated density range. Thus the next probability
obligation remains an upper bound on **formation after the cutoff**.
To prove a positive nonjamming interval one needs that late probability to
vanish for every fixed `p` in some interval `(0,p_*)` with `p_*>0`.

The estimate in this note also holds in the high-density regime where
Angel–Holroyd–Martin prove eventual torus fixation. There the late term
instead tends to one. Extending a delay alone therefore cannot establish
the low-density conclusion. A suitable further estimate must control
repeated encounters and correlated future dynamics, or prove entry into
a forward-invariant noncapture set with high initial-law probability.
See [AHM, Theorem 2](https://personal.math.ubc.ca/~holroyd/papers/bml.pdf)
and the [existing safe-set reduction](2026-11-18-fixed-density-formation.md#4-what-a-block-argument-still-has-to-prove).

### A sufficient estimate that would control all future times

For a fixed root `z`, let `P_t(z,L-1)` mean that its direct blocker path
in the time-`t` snapshot has occupied vertices at indices `0,...,L-1`.
Define

\[
 h_L(p)=\sup_{t\ge0}\Pr_p(P_t(z,L-1)).
\]

Translation invariance makes this independent of the chosen root. The
same two-root count gives `Pr_p(A_t)<=L*h_L(p)/2` for every `t`.
Since `A_t` is increasing in time, continuity from below gives

\[
\boxed{q_L(p)\le 2L(p/2)^L+\frac L2 h_L(p).}
\tag{9}
\]

No union over times is needed: an already formed mixed cycle persists.
Thus a concrete sufficient next estimate is

\[
 h_L(p)=o(1/L)
\tag{10}
\]

for every fixed `p` in some positive interval. For example, an estimate
`h_L(p)<=C(p)*exp(-a(p)*L)` with positive constants independent of `L`
and time would suffice. Equations (9)–(10) are a conditional criterion;
this note does not establish (10). The current barrier weight decreases
with the horizon and its fresh-site trial count eventually becomes zero,
so taking the supremum of the present finite-time bounds does not supply
the missing uniform estimate.

The subsequent [path-mass reduction](2026-11-19-maximal-core-and-path-mass.md#3-shorter-paths-give-a-weaker-sufficient-probability-obligation)
weakens this sufficient input: conserved population allows an `o(1)`
late-time or long-time-averaged root probability at each fixed positive
density. It also identifies a monotone maximal-core fraction whose limiting
expectation agrees with eventual gridlock up to the full-lane exception.
The required decay estimate remains unproved.

### A long moving prefix can end in capture

There is a useful explicit control. For `L>=4` and
`0<=T<=floor((L-2)/2)`, put exactly `2L` cars at

\[
 E_i=(i-T,i),\qquad N_i=(i+1,i-T)\pmod L,
 \qquad i\in\mathbb Z_L,
\]

leaving all other sites empty. At a checkpoint with `r` rounds remaining,
their positions are `E_i=(i-r,i)`, `N_i=(i+1,i-r)`. For `1<=r<=T`, a
source overlap would require `2r=-1 mod L`, an east target collision
`2r=0 mod L`, and a north target collision after the east phase
`2r=1 mod L`. All are excluded by `2<=2r<=L-2`. Same-species targets
are free because their cars lie in distinct rows or columns. Thus all
cars move for `T` complete rounds.

At time `T`, the cars form the mixed staircase `E_i=(i,i)`,
`N_i=(i+1,i)`: each E points to the corresponding N, and each N points
to the next E. Every car is now permanently blocked. The first mixed
cycle appears exactly at `T`, since an earlier permanent cycle would
contradict the preceding all-moving rounds.

This family shows that an all-moving prefix of order `L`, or the absence
of a tag that never moved initially, does not certify nonjamming. It is
not an iid counterexample to a positive nonjamming interval: its density
is `2/L`, and the fully prescribed board has small initial probability.

## 7. Verification and scope

`BML/Barrier.lean` proves `GuardedNorthHole.step`, `.iterate`,
`.empty_at_deadline`, `eastWall_preserved`, `draining_l_barrier`, and
`torus_draining_l_barrier` for the actual kernel. The module allows zero
lengths and leaves the exterior unrestricted. These declarations are
required by the transitive axiom audit.

`bml/barriers.py` supplies exact rational certificate weights and finite
formation bounds, explicit initial footprints, and a phase-aware verifier.
The independent acceptance script compares both production half-steps with
a scalar oracle, checks small arbitrary-exterior domains, seam placements,
fresh-site separation, initial-law weights, and the delayed-capture family.
Successful runs are recorded in a source-bound receipt; the script's
declared domain is finite.

```sh
python -m pytest -q tests/test_barriers.py
python scripts/check_barriers.py --report .artifacts/barriers-replay.json
cd formal/lean
lake build
lake env lean Audit.lean
```

The spatial path trap, conditional probability calculation, asymptotic
limits, and delayed-capture family have the prose proofs above. They are
not an end-to-end Lean probability theorem. The Lean deterministic proof
and the independent finite checks have their separate roles.
