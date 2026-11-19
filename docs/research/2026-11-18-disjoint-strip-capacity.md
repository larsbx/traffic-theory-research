# Disjoint-strip capacity and finite gridlock bounds

**Date:** 2026-11-18. **Rule:** CLASSIC, synchronous east then north.
**Scope:** a deterministic conserved-profile obstruction, an exact initial-iid
probability bound, and separately scoped executable checks. The geometric and
probability arguments below are prose proofs. They do not establish a fixed
positive critical density or eventual perfect free flow.

The [probability note](2026-11-18-probabilistic-gridlock-bounds.md) excludes
gridlock when one north-empty strip is wider than every east-row count. Here
several disjoint strips can collectively exceed the available east-car
capacity, even when each strip individually fails that earlier test.

## 1. A conserved capacity obstruction

Work on a positive \(W\times H\) torus. Let \(r_y\) be the number of east cars
in row \(y\), and \(c_x\) the number of north cars in column \(x\). Both
profiles are conserved under the actual CLASSIC kernel, as proved in
[`BML/Lanes.lean`](../../formal/lean/BML/Lanes.lean).

Fix \(1\le k\le W\). Select \(B\) pairwise disjoint cyclic blocks, each
consisting of \(k\) consecutive columns, such that every selected column has
\(c_x=0\). Define the east-row capacity

\[
C_k=\sum_{y=0}^{H-1}\left\lfloor\frac{r_y}{k}\right\rfloor.
\]

### Proposition 1: disjoint-strip obstruction

If

\[
\boxed{B>C_k\quad\text{and}\quad c_x<H\text{ for every column }x,}
\]

then no configuration with this conserved profile can be a nonempty jam.
In particular, the initial configuration cannot eventually gridlock.

**Proof.** Suppose a jam were to occur. Every occupied vertex has its successor
in its own direction occupied. Following successors and removing the initial
tail gives a simple directed blocker cycle.

A pure north cycle fills a north column, contradicting \(c_x<H\). A pure
east cycle fills an east row, which contributes \(\lfloor W/k\rfloor\) to
\(C_k\). Pairwise disjointness gives \(B\le\lfloor W/k\rfloor\), also a
contradiction.

A mixed cycle winds horizontally: its positive number of east steps is a
multiple of \(W\). If \(k=W\), a selected strip would make every column
north-empty, leaving no north vertex for a mixed cycle. Otherwise, for each
selected strip choose a traversal entering its first column from the preceding
column. Inside the strip, no north vertex exists, so the cycle takes east steps
until it has crossed all \(k\) columns in a single row. This uses \(k\)
distinct east vertices in that row. The selected crossings for different
strips use disjoint vertices because their column sets are disjoint.

If \(b_y\) chosen crossings use row \(y\), then \(k b_y\le r_y\), hence
\(b_y\le\lfloor r_y/k\rfloor\). Summing gives
\(B=\sum_y b_y\le C_k\), a contradiction. The argument applies to every
future state because all the lane counts are conserved. ∎

No independence or random placement is needed for this proposition. It also
covers singleton dimensions. Full monochromatic lanes must still be treated
as above: a north-free strip alone does not rule out a full north column
elsewhere.

### A strict improvement over every single-strip test

On an \(8\times8\) torus take

\[
r=(2,1,1,1,1,1,1,1),\qquad c=(0,0,2,2,0,0,2,2).
\]

The two blocks \(\{0,1\}\) and \(\{4,5\}\) are north-empty. For \(k=2\),
\(B=2\) and \(C_k=1\), so Proposition 1 certifies nonjamming. A concrete
realization places an east car in column zero of every row, one extra east car
at \((1,0)\), and north cars at

\[
(2,0),(2,1),(3,2),(3,3),(6,4),(6,5),(7,6),(7,7).
\]

Coordinates are \((x,y)\), with north increasing \(y\). The longest cyclic
north-empty run has length two, exactly the largest east-row count. Thus no
single strip is strictly wider than every row count. The transposed,
species-swapped test also fails because every original row contains an east
car. The example has nine east and eight north cars; its obstruction is more
informative than merely having fewer than eight cars of one species.

## 2. An exact finite iid upper bound

Initially each site is independently empty, east, or north with probabilities
\((1-p,p/2,p/2)\). Let \(q_{W,H}(p)\) be the probability of eventual
nonempty gridlock. Fix a partition into
\(m=\lfloor W/k\rfloor\) disjoint \(k\)-column blocks, leaving any
remainder unused. Let \(B\) count the north-empty blocks of this partition.

Writing \(u=p/2\), the exact marginal laws are

\[
B\sim\operatorname{Bin}\bigl(m,(1-u)^{Hk}\bigr),
\qquad
C_k\overset{d}=\sum_{y=1}^{H}\left\lfloor\frac{X_y}{k}\right\rfloor,
\quad X_y\stackrel{\mathrm{iid}}{\sim}\operatorname{Bin}(W,u).
\]

The block indicators are independent because they involve disjoint initial
sites. The east-row counts are independent for the same reason. **The random
variables \(B\) and \(C_k\) are generally dependent.** Their separate
marginal laws suffice for the following union bound.

### Proposition 2: capacity-tail bound

For any integer \(1\le a\le m\),

\[
\boxed{
q_{W,H}(p)\le
\min\left\{1,
\Pr(C_k\ge a)+\Pr(B<a)+1-(1-u^H)^W
\right\}.}
\]

**Proof.** Outside the first two bad events, \(C_k<a\le B\), so
\(B>C_k\). The last term is exactly the probability of some full north
column: the \(W\) full-column events are independent, each with probability
\(u^H\). Proposition 1 rules out gridlock outside the union of these three
events. No independence between the three events is used. ∎

The parameter \(a\) is a threshold for the number of strips, distinct from
the torus height \(H\). Minimizing over all allowed \((k,a)\) yields another
valid upper bound. This is a deterministic optimization of exact bounds for
the specified \((W,H,p)\).

For \(a=1\), the capacity term is

\[
\Pr(C_k\ge1)
=1-\left[1-\Pr\!\left(\operatorname{Bin}(W,u)\ge k\right)\right]^H.
\]

This already sharpens the earlier row union bound
\(H\Pr(\operatorname{Bin}(W,u)\ge k)\). The exact full-north-column term
also sharpens \(Wu^H\). Allowing \(a>1\) gives a further improvement that
uses the capacity obstruction itself.

### Exact polynomial calculation

For rational \(u=A/D\), form the integer polynomial

\[
P(z)=\sum_{n=0}^{W}\binom Wn A^n(D-A)^{W-n}z^{\lfloor n/k\rfloor}.
\]

The coefficient of \(z^j\) in \(P(z)^H\), divided by \(D^{WH}\), is
\(\Pr(C_k=j)\). All needed thresholds satisfy \(a\le m\), so terms of
degree at least \(m\) can be discarded after every multiplication without
changing any required lower tail. The implementation uses integer convolution
and converts only the resulting probabilities to exact fractions.

The binomial lower tail for \(B\) is also evaluated exactly. There is no
sampling, floating-point tail approximation, or independence assumption about
an evolved state.

### Reproducible finite improvements

Every allowed \(k\) and \(a\) was checked for each row below. Displayed
decimals are rounded; the comparisons and saved report use exact fractions.

| Square side and density | Earlier strip bound, best \(k\) | Capacity bound restricted to \(a=1\) | Full capacity bound |
| --- | --- | --- | --- |
| \(L=8,\ p=1/40\) | 0.03439493958, \(k=2\) | 0.03391409216, \(k=2\) | **0.005543863957**, \((k,a)=(1,5)\) |
| \(L=12,\ p=1/18\) | 0.2118171878, \(k=3\) | 0.2108233715, \(k=3\) | **0.1926061171**, \((k,a)=(2,2)\) |

In the first case the exact capacity bound is below \(1/100\), whereas every
\(a=1\) bound is above \(1/40\). In the second it is below \(1/5\), whereas
every \(a=1\) bound is above \(1/5\). These strict rational comparisons show
that the gain is not solely the replacement of a row union bound by its exact
independent-row probability. These are upper bounds, not computed values of
the eventual gridlock probabilities on the two larger squares.

## 3. Limits and relation to the critical-density problem

This certificate still requires at least one north-empty column. At every
fixed \(0<p<1\) on growing squares,

\[
\Pr(\text{some north-empty column})\le L(1-p/2)^L\longrightarrow0.
\]

For every allowed \(k,a\), the term \(\Pr(B<a)\) is at least
\(1-L(1-p/2)^L\). Consequently even the optimized capacity upper bound
tends to one at fixed positive density. This method supplies no fixed-density
nonjamming interval.

The [lane-profile obstruction note](2026-11-18-lane-profile-obstruction.md)
proves a broader limitation: with high probability, the conserved profile
admits a ringless jammed representative. Every sound universal certificate
depending only on that profile must then reject it. That statement concerns
certificate acceptance, not the probability that a random representative
eventually jams.

Theorem 6a of the [probability note](2026-11-18-probabilistic-gridlock-bounds.md)
separately sharpens the shrinking-density window to

\[
p_L L\le2\log\log L-4\log\log\log L-2
\quad\Longrightarrow\quad q_L(p_L)\to0,
\]

when the inequality holds eventually. That refinement follows from the earlier
single-strip estimate. No improved asymptotic order is attributed to the
capacity calculation here.

## 4. Executable evidence and proof boundary

[`bml/capacity.py`](../../bml/capacity.py) provides a verifier for supplied
disjoint-strip certificates and exact rational capacity bounds. It rejects
overlapping strips, stale lane counts, equality \(B=C_k\), unexcluded full
north columns, and use with TRAIN. The geometric theorem is the prose argument
in Proposition 1; this Python verifier is not a universal Lean refinement.

[`scripts/check_capacity.py`](../../scripts/check_capacity.py) checks every
state on \(2\times2,3\times2,2\times3,4\times2,2\times4,3\times3,4\times3\).
For every width and cyclic partition offset, it compares the vectorized
certificate predicate with the complete production basin classifier. It also
integrates each of the three marginal events directly from the enumerated
initial configurations at five exact densities, independently checking the
convolution and binomial formulas. Separate public-verifier controls check the
strict \(8\times8\) example and corrupted certificates.

The completed census contains 565,785 states and 8,821,224 partition-predicate
checks. All 525 exact marginal evaluations agree with direct initial-state
weights. The union of capacity certificates covers 696 additional states
beyond the union of all cyclic north-empty single-strip certificates in the
same orientation: 48 on \(4\times2\) and 648 on \(4\times3\). This census
comparison does not include the species-swapped orientation; the separate
\(8\times8\) control checks both orientations. All 696 additional states
lie outside the gridlock basin.
The 49 focused unit tests additionally cover singleton dimensions, both
density endpoints, malformed inputs, and the strict finite improvements.

Run from the repository root:

```sh
python -m pytest -q tests/test_capacity.py
python scripts/check_capacity.py --report .artifacts/capacity-replay.json
```

The report records source hashes, all finite domains, exact fractions,
individual marginal checks, and the optimized numerical examples. The
finite census supports the implementation; the prose proofs establish the
all-size geometric and probabilistic statements. No Lean capacity theorem,
TRAIN transfer, or positive critical-density theorem is claimed.
