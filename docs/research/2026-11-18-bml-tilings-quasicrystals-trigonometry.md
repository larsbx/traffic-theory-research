# BML gridlock, tilings, quasicrystals, and trigonometry

Date: 2026-11-18

Status: research note recording published results and explicit derivations from
the discussion that motivated this repository. The arguments below are exposition,
with no novelty claim. A selected subset now has a
[Traffic Lean and Quint formalization](../../formal/traffic-layer.md); its coverage matrix
distinguishes kernel-checked statements, bounded executable evidence, and the
remaining mathematical obligations. Neither this note nor that layer establishes
that random traffic generates quasicrystals.

## 1. Relationship and evidence map

Biham–Middleton–Levine (BML) traffic connects to tiling theory through finite
local matching rules, to quasiperiodic order through specially chosen symbolic
sequences and projections, and to trigonometry through directions, geometric
widths, and Fourier diffraction.

The most concrete bridge in this note is a deliberately constructed Fibonacci
staircase: put cars at its vertices, each facing the next vertex. The resulting
configuration is frozen. Projecting the staircase onto its mean direction gives
a one-dimensional Fibonacci tiling.

Gridlock describes whether cars move. Quasiperiodicity describes spatial order.
The blocking condition permits periodic, quasiperiodic, and disordered patterns.

| Claim | Status and scope |
| --- | --- |
| Sufficiently dense iid BML traffic on the infinite square lattice eventually stops locally and each car moves finitely often. | Published theorem of Angel, Holroyd, and Martin [2]. |
| Analogous high-density freezing occurs with probability tending to one on growing tori of a fixed limiting positive aspect ratio. | Published theorem [2]. |
| Completely frozen configurations admit an exact 21-Wang-tile recoding. | Direct derivation in Section 3; fixed tile orientations. |
| A bi-infinite Fibonacci staircase is frozen and projects to a Fibonacci tiling. | Direct construction and proof in Section 4. |
| Fibonacci rectangle sizes and trigonometric jam geometry occur in BML studies. | Published numerical and geometric analysis [3], [4]. |
| The standard Fibonacci tiling has pure point diffraction and dynamical spectrum. | Published result for that tiling system [7]; regular model-set framework [6], [8]. |
| Random BML dynamics selects a Fibonacci, Penrose, or other quasicrystal hull. | Not established here or by the cited gridlock theorem. |

There is also a historical link. Dov Levine coauthored both the original BML
traffic paper [1] and the foundational Levine–Steinhardt quasicrystal paper [5].
Shared authorship does not itself give an implication between their theorems.

## 2. Model and rigorous high-density result

### 2.1 Update rule

At each site of the square lattice there is an eastbound car, a northbound car,
or a vacancy. Write the alphabet as

$$
\mathcal A=\{0,E,N\}.
$$

On alternating half-steps, all cars of one species simultaneously attempt to move
one lattice unit in their direction. A move succeeds only if the destination is
empty at the start of that half-step. In particular, a car cannot move into a site
merely because its occupant will move during the same half-step. The model was
introduced by Biham, Middleton, and Levine in 1992 [1].

Here, "completely frozen" means that neither species makes any move in either
half-step. A full traffic cycle consists of both species' half-steps. This avoids
confusing a quiet half-step with permanent gridlock.

### 2.2 Published theorem

Angel, Holroyd, and Martin initialize sites of $\mathbb Z^2$ independently with

$$
\Pr(E)=\Pr(N)=p/2,\qquad \Pr(0)=1-p.
$$

Their Theorem 1 states that there exists $p_0<1$ such that, for every $p\ge p_0$,
almost surely every car makes finitely many moves and every site's state is
eventually constant. This is local eventual stabilization; it does not assert
one finite stopping time shared by the entire infinite lattice [2].

Their Theorem 2 gives eventual complete freezing with probability tending to one
on $m\times n$ tori as both dimensions grow and $m/n$ tends to a finite positive
limit, at sufficiently high fixed density [2].

The proof builds blocking paths, including local replacement-blocking patterns,
and compares connectivity of large blocks with supercritical oriented
percolation. The authors do not calculate a sharp critical density. The theorem
does not establish the complete phase diagram, a universal deterministic density
threshold, or quasiperiodic spatial order [2].

## 3. Exact tiling description of completely frozen configurations

The results in this section are direct derivations from the update rule.

### 3.1 Two forbidden neighboring pairs

Let $c:\mathbb Z^2\to\mathcal A$, with $e_1=(1,0)$ and $e_2=(0,1)$.
Then $c$ is completely frozen if and only if

$$
c(x)=E\Longrightarrow c(x+e_1)\ne0,
\qquad
c(x)=N\Longrightarrow c(x+e_2)\ne0
\quad\text{for every }x.
$$

**Proof.** If a full cycle makes no moves, the configuration is unchanged at
both half-steps. Every car's destination must therefore be occupied when its
species is active, establishing both implications in the original configuration.
Conversely, if both implications hold, there are no eligible moves in either
half-step. The configuration stays unchanged, so the implications continue to
hold at every subsequent time.

Equivalently, forbid the horizontal pair with $E$ immediately west of $0$, and
the vertical pair with $N$ immediately south of $0$. Thus the frozen
configurations form a two-dimensional subshift of finite type: a shift-invariant
set specified by finitely many local forbidden patterns.

### 3.2 Twenty-one oriented Wang tiles

For each $(a,b,c)\in\mathcal A^3$, define a square tile with edge colors

$$
(\text{west},\text{south},\text{east},\text{north})=(a,a,b,c).
$$

Keep the tile exactly when

$$
a=E\Longrightarrow b\ne0,
\qquad
a=N\Longrightarrow c\ne0.
$$

The tiles have fixed orientations: rotation and reflection are not allowed.
There are nine choices with $a=0$, six with $a=E$, and six with $a=N$, for
a total of

$$
9+6+6=21.
$$

**Encoding.** Given a frozen configuration, put the tile

$$
\bigl(c(x),c(x+e_1),c(x+e_2)\bigr)
$$

at each site $x$. The frozen-state conditions make it an allowed tile, and all
shared edges match.

**Decoding.** In a valid tiling, let $a(x)$ be the common west/south color.
Horizontal and vertical edge matches force

$$
b(x)=a(x+e_1),\qquad c(x)=a(x+e_2).
$$

Tile admissibility therefore gives exactly the two frozen-state implications.
Encoding and decoding are inverse, local, and commute with integer translations.
This is a bijective local recoding, preserving periods, on $\mathbb Z^2$ and on
rectangular tori with wraparound edge matching.

This result concerns static configurations. Full BML histories have two spatial
dimensions plus a time coordinate. Their finite local update constraints live
in three dimensions; a whole history should not be identified with the
two-dimensional static Wang system above.

### 3.3 Blocking rules do not enforce aperiodicity

Fill every site with a car and choose its orientation arbitrarily. There are no
vacancies, so every such configuration is frozen. On an $m\times n$ torus this
already supplies $2^{mn}$ frozen colorings. When $mn$ is even, imposing equal
species counts still leaves $\binom{mn}{mn/2}$ examples.

Periodic assignments, Fibonacci-based assignments, and independently random
assignments all satisfy the same blocking rule. The tiling formulation is exact,
but its allowed tiles do not force quasiperiodicity.

## 4. Fibonacci staircase: a frozen path whose projection is a tiling

This section constructs a specially prepared configuration. It does not describe
a typical outcome of iid traffic initialization.

### 4.1 Symbolic construction

Use the Fibonacci substitution

$$
\sigma(E)=EN,\qquad \sigma(N)=E.
$$

Its successive iterates of $E$ begin

$$
E,\quad EN,\quad ENE,\quad ENEEN,\quad ENEENENE,\ldots
$$

Choose a bi-infinite word $u\in\{E,N\}^{\mathbb Z}$ in the Fibonacci substitution
hull: every finite subword of $u$ occurs in an iterated substitution word.
Using a bi-infinite hull element avoids treating a one-sided word as though it
automatically covered a whole line.

Set $r_0=(0,0)$ and, for every $n\in\mathbb Z$, define

$$
r_{n+1}-r_n=
\begin{cases}
e_1,&u_n=E,\\
e_2,&u_n=N.
\end{cases}
$$

The vertices are distinct because $r_{n,1}+r_{n,2}=n$.

Put a car of orientation $u_n$ at $r_n$ and leave all other sites empty.
Every destination is the occupied next vertex $r_{n+1}$. No car is eligible
in either half-step, so the configuration is completely frozen.

The blocking argument works for any bi-infinite east/north word. Fibonacci
order is an additional choice of spatial organization.

### 4.2 Frequencies and mean direction

The substitution matrix, with columns counting letters in substitution images,
is

$$
M=
\begin{pmatrix}
1&1\\
1&0
\end{pmatrix}.
$$

Write

$$
\varphi=\frac{1+\sqrt5}{2}.
$$

The eigenvalues are $\varphi$ and $-1/\varphi$. The normalized positive
eigenvector gives the standard Fibonacci frequencies

$$
f_E=\frac1\varphi,\qquad f_N=\frac1{\varphi^2}.
$$

The Fibonacci substitution and its frequency and spectral data are treated in
[7]. For our staircase these frequencies imply

$$
\frac{r_n}{n}\longrightarrow
\left(\frac1\varphi,\frac1{\varphi^2}\right),
$$

so the mean direction is $(\varphi,1)$. If $\theta$ is its angle to the horizontal,

$$
\tan\theta=\frac1\varphi.
$$

These are asymptotic frequency and direction statements. Bounded transverse
deviation requires the additional balanced/Sturmian property of the Fibonacci
word; it does not follow from frequencies alone. Likewise, irrational mean slope
alone does not establish quasiperiodic order.

### 4.3 Orthogonal projection

Let

$$
v=\frac{(\varphi,1)}{\sqrt{\varphi^2+1}},
\qquad x_n=r_n\cdot v.
$$

The projected east and north steps have lengths

$$
\ell_E=\frac{\varphi}{\sqrt{\varphi^2+1}}=\cos\theta,
\qquad
\ell_N=\frac1{\sqrt{\varphi^2+1}}=\sin\theta.
$$

Both are positive, and

$$
\frac{\ell_E}{\ell_N}=\cot\theta=\varphi.
$$

Consequently the intervals $[x_n,x_{n+1}]$ cover the whole line, meeting only at
endpoints, with long and short lengths in Fibonacci order. After multiplying
lengths by $\sqrt{\varphi^2+1}$, they are the standard lengths $\varphi$ and $1$.
This is exactly a one-dimensional Fibonacci tiling.

Its geometric inflation is consistent because

$$
\varphi\ell_E=\ell_E+\ell_N,\qquad
\varphi\ell_N=\ell_E.
$$

Thus the same constructed object has a frozen-traffic description, a symbolic
Fibonacci description, and a projected tiling description.

The standard cut-and-project presentation selects lattice points in a suitable
strip of slope $1/\varphi$ and projects them onto the strip direction.
Richard and Strungaru give this construction explicitly in their Figure 2 [6].

### 4.4 Scope and finite-boundary caution

Any $L\times L$ lattice box contains at most $2L-1$ staircase vertices, since
the coordinate sum takes at most that many values and each value selects at
most one vertex. Hence the car set has uniformly zero two-dimensional density.
It is not a relatively dense two-dimensional point set.

The projected object is a one-dimensional quasiperiodic tiling. The original
isolated staircase is not a two-dimensional quasicrystal, and it is outside the
iid high-density assumptions of Section 2.

A finite truncated staircase with an empty site ahead of its last car is not
frozen: its last car can move. A finite demonstration must specify boundary
conditions or additional blocking. It cannot certify the infinite construction
by silently treating a truncated end as blocked.

## 5. Torus winding, commensurability, and traffic geometry

### 5.1 Exact winding constraint for frozen configurations

On an $L_x\times L_y$ torus, draw an edge from every car to its occupied
destination in a frozen configuration. Every vertex of this finite directed
graph has one outgoing edge, so each component feeds into a directed cycle.

Lift a cycle to $\mathbb Z^2$. If it contains $H$ east steps and $V$ north steps,
closure on the torus implies

$$
H=aL_x,\qquad V=bL_y
$$

for nonnegative integers $a,b$, not both zero. These are winding counts.
If $a>0$, the angle of the total lifted displacement satisfies

$$
\tan\theta=\frac{V}{H}=\frac{bL_y}{aL_x}.
$$

The case $a=0$ is vertical, and $b=0$ is horizontal. A staircase need not be
straight: this formula describes its net direction. It is a rational direction
for every finite integer torus.

On the infinite plane, an east/north path cannot make a directed cycle, since
its coordinate sum strictly increases at every step. Frozen forward-dependency
paths must instead continue indefinitely.

### 5.2 Published Fibonacci rectangles and trigonometric estimates

D'Souza studied BML on rectangles with consecutive Fibonacci side lengths,
including $89\times55$ and $377\times233$. The numerical study found ordered
intermediate states with flowing bands and moving jam fronts, including exactly
repeating microscopic configurations [3].

Every finite aspect ratio is rational:

$$
\frac{L_x}{L_y}=\frac{F_{n+1}}{F_n}\longrightarrow\varphi.
$$

The equality with $\varphi$ is a limiting statement, not an exact identity for
a finite rectangle. Such grids can probe an irrational limiting geometry, but
finite temporal or spatial periodicity alone does not establish a quasicrystal.

D'Souza also used band/interface slopes, including $1/2$, $1$, and $2$, with
trigonometric width and length calculations to estimate trapped-car counts
$J$ and velocities of the form

$$
v_{\mathrm{traffic}}\approx1-\frac{J}{N_{\mathrm{cars}}}.
$$

Velocity here is normalized to one for free flow per car's update opportunity
(one opportunity per full traffic cycle), not per individual species half-step.

These calculations depend on the observed jam geometry and associated
approximations [3]. They are separate from the rigorous percolation theorem.
Linesch and D'Souza subsequently found periodic intermediate states on square
grids too; Fibonacci dimensions are not necessary for those states [4].

## 6. Trigonometry, quasicrystals, and diffraction

### 6.1 Pentagonal geometry

The elementary identities

$$
\varphi=2\cos(\pi/5)
=\frac{\sin(2\pi/5)}{\sin(\pi/5)}
$$

connect the golden ratio with pentagonal angles. The sine ratio follows from
the double-angle identity. The same number enters Fibonacci inflation and
Penrose-related geometry; the original Levine–Steinhardt paper discusses the
Penrose/Fibonacci connection [5].

The staircase angle satisfying $\tan\theta=1/\varphi$ is not $36^\circ$.
These are distinct geometric uses of the same algebraic number. Neither formula
supplies a universal BML density or traffic angle.

### 6.2 Fourier phases and the infinite-volume limit

For a finite portion of a weighted point set, use the Fourier convention

$$
A_R(k)=\sum_{x\in\Lambda\cap B_R}w_xe^{-2\pi i k\cdot x},
\qquad
I_R(k)=\frac{|A_R(k)|^2}{\operatorname{vol}(B_R)}.
$$

The exponential is a sine/cosine phase. Reinforcement and cancellation of these
phases give diffraction peaks. The normalization here is for an
infinite-volume limit; experimental overall intensity prefactors are separate.

With $\omega=\sum_{x\in\Lambda}w_x\delta_x$, one defines the autocorrelation,
when it exists, by volume-averaged convolution of finite restrictions, and then
takes its Fourier transform $\widehat\gamma$. Pure point diffraction means

$$
\widehat\gamma=\sum_{k\in\mathcal M}I(k)\delta_k.
$$

This is a statement about a measure in the infinite-volume limit, not a claim
that finite intensity functions converge pointwise to ordinary functions
representing delta peaks. Regular model sets have pure point diffraction under
the hypotheses of that framework [6], [8].

### 6.3 Explicit Fibonacci intensities

For the standard Fibonacci endpoint set with long tiles of length $\varphi$,
short tiles of length $1$, and unit weight at every endpoint, the Fourier module
is

$$
\mathcal M=\frac1{\sqrt5}\mathbb Z[\varphi].
$$

In the Fourier convention above, its Bragg intensities are

$$
I(k)=
\frac{\varphi^2}{5}
\operatorname{sinc}^2(\pi\varphi k^\star),
\qquad k\in\mathcal M,
$$

and there are no Bragg peaks outside this module. Individual intensities inside
the module may vanish. Here $\operatorname{sinc}(z)=\sin(z)/z$ with value $1$
at zero [7].

The star map is algebraic conjugation of the entire element:

$$
\varphi'=1-\varphi,\qquad
k=\frac{m+n\varphi}{\sqrt5}
\quad\Longrightarrow\quad
k^\star=-\frac{m+n\varphi'}{\sqrt5}.
$$

The denominator is conjugated too. The formula assumes the rescaled lengths
$\varphi,1$; using the unrescaled staircase projection changes the wave-number
and density scales.

The algebraic module determines available frequencies, while the trigonometric
factor determines their intensities. This published spectral result applies to
the projected Fibonacci tiling in Section 4 after the stated rescaling. It is
not a diffraction theorem for arbitrary BML jams.

### 6.4 What a BML Fourier picture would and would not show

BML already lives on the periodic square lattice. At full occupancy, a
measurement that ignores orientations sees the same lattice for every
east/north coloring. It cannot distinguish random species assignments from
ordered ones.

To study emergent order, specify the observable: occupancy with its mean
removed, separate species fields, or a species contrast such as opposite
weights for east and north cars. The choice can change which spectral
components are visible.

A finite discrete Fourier transform always has discrete frequency bins.
Bright bins or regular stripes do not prove infinite-volume pure point
diffraction. Increasing windows, controlled correlations, and a limiting
pattern or measure must be specified.

An irrational frequency ratio alone is also insufficient. Fibonacci order
includes restrictions on allowed finite words and their recurrence, beyond
its letter frequencies.

## 7. Traffic time evolution versus spatial tiling dynamics

Let $F$ denote a complete traffic cycle. A completely frozen configuration
satisfies $F(C)=C$. This is a property of time evolution.

For a tiling, let $T_t$ denote spatial translation. Spatial eigenfunctions obey
relations such as

$$
f(T_t\mathcal T)=e^{2\pi i k\cdot t}f(\mathcal T).
$$

Pure point dynamical spectrum concerns whether such eigenfunctions span the
relevant $L^2$ space for a specified invariant measure. Being fixed by $F$ does
not establish that spatial spectral property.

There is a separate finite-state observation: a finite BML system, with the
update phase included in its state, eventually repeats a state. Its eventual
cycle can be stationary or can contain recurring motion. This elementary
temporal recurrence does not determine spatial quasiperiodicity.

For substitution/Pisot questions, the Fibonacci matrix supplies an expanding
eigenvalue $\varphi$ and a contracting conjugate $-1/\varphi$. Those enter because
the construction chose the Fibonacci substitution. The generic blocking rule
provides no Pisot expansion, recognizability, coincidence condition, or pure
point spatial spectrum.

## 8. Research and proof obligations

The following table tracks the original proposal against the initial
[Traffic formalization layer](../../formal/traffic-layer.md). Its acceptance gate records the
source revision and hashes; formal status is limited to the stated theorem
domains and finite checking bounds.

| Obligation | Concrete target | Current boundary |
| --- | --- | --- |
| Static blocking | Formalize the two forbidden-pair characterization. | Lean proves equivalence with the actual simultaneous updates, including complete-cycle fixed points and persistence. |
| Wang recoding | Formalize the 21 types and inverse local encoding/decoding. | Lean proves exact enumeration and inverse recoding on a general grid; concrete cyclic grids instantiate it. |
| Fibonacci path | Formalize a bi-infinite hull word, occupied successors, and projection. | Lean constructs a frozen staircase for any supplied bi-infinite direction word and proves finite Fibonacci count/algebraic identities. A Fibonacci hull element, real projection, frequency and density limits remain open. |
| Finite demonstration | Choose boundary conditions that do not silently block a truncated endpoint. | Quint specifies finite tori and tests truncated-path and update-order controls; Lean–Quint agreement is checked on six small grid sizes. |
| Traffic geometry | Reproduce selected Fibonacci-rectangle and square-grid cases. | Large-grid experiments remain open; the Traffic layer proves winding under modular closure, while BML also supplies arithmetic components of the separate extremal results. |
| Spatial order | Specify an observable and a family or hull of limiting traffic patterns. | Recurrence/substitution/model-set identification and controlled correlation limits remain open. |
| Spectral conclusion | Establish the appropriate spatial spectrum for that specified system. | A separate spectral proof or verified bridge to an applicable published theorem remains open. |

For the constructed Fibonacci staircase, ordinary arguments establish blocking
and projection, and published Fibonacci theory supplies the spectral result.
For general traffic, success on the blocking obligation alone leaves the
structural and spectral obligations open.

No claim is made here that random BML dynamics selects a Fibonacci or Penrose
hull, that Fibonacci aspect ratios force quasiperiodicity, or that a bounded
simulation proves an infinite-volume theorem.

## References

The references are primary papers or technical treatments by researchers in the
subject. Links identify the exact source of published claims; Sections 3–5.1
contain direct derivations rather than results attributed to the traffic papers.

1. Ofer Biham, A. Alan Middleton, and Dov Levine,
   **Self-organization and a dynamical transition in traffic-flow models**,
   Physical Review A 46 (1992), R6124–R6127.
   [DOI](https://doi.org/10.1103/PhysRevA.46.R6124);
   [arXiv:cond-mat/9206001](https://arxiv.org/abs/cond-mat/9206001).
   Source for the original traffic model.

2. Omer Angel, Alexander E. Holroyd, and James B. Martin,
   **The Jammed Phase of the Biham–Middleton–Levine Traffic Model**,
   Electronic Communications in Probability 10 (2005), 167–178.
   [arXiv:math/0504001v2](https://arxiv.org/abs/math/0504001v2);
   [PDF](https://arxiv.org/pdf/math/0504001).
   Theorems 1–2 and the blocking-path/percolation proof.

3. Raissa M. D'Souza,
   **Coexisting phases and lattice dependence of a cellular automaton model
   for traffic flow**, Physical Review E 71 (2005), 066112.
   [DOI](https://doi.org/10.1103/PhysRevE.71.066112);
   [published PDF](https://www.eng.yale.edu/softmatter/jclub/DSouza.PRE.2005.pdf);
   [earlier preprint](https://arxiv.org/abs/cond-mat/0402351).
   The preprint title is *Geometric structure of coexisting phases found in the
   Biham–Middleton–Levine traffic model*. See the published paper's Section III.B
   for Fibonacci rectangles and Section IV, especially IV.C and Figure 11, for
   geometry and trigonometric velocity estimates.

4. Nicholas J. Linesch and Raissa M. D'Souza,
   **Periodic States, Local Effects and Coexistence in the BML Traffic Jam Model**,
   Physica A 387 (2008), 6170–6176.
   [DOI](https://doi.org/10.1016/j.physa.2008.06.052);
   [arXiv:0709.3604v3](https://arxiv.org/abs/0709.3604v3).
   Periodic and disordered intermediate states, including square grids.

5. Dov Levine and Paul Joseph Steinhardt,
   **Quasicrystals: A New Class of Ordered Structures**,
   Physical Review Letters 53 (1984), 2477–2480.
   [DOI](https://doi.org/10.1103/PhysRevLett.53.2477);
   [PDF](https://journals.aps.org/prl/pdf/10.1103/PhysRevLett.53.2477).
   Historical Penrose/Fibonacci connection and quasicrystal diffraction.

6. Christoph Richard and Nicolae Strungaru,
   **A short guide to pure point diffraction in cut-and-project sets**,
   Journal of Physics A: Mathematical and Theoretical 50(15) (2017), 154003.
   [DOI](https://doi.org/10.1088/1751-8121/aa5d44);
   [arXiv:1606.08831v2](https://arxiv.org/abs/1606.08831v2);
   [PDF](https://arxiv.org/pdf/1606.08831).
   Figure 2 gives the Fibonacci strip projection; the paper proves the
   diffraction formula for regular cut-and-project sets.

7. Michael Baake, Natalie Priebe Frank, and Uwe Grimm,
   **Three variations on a theme by Fibonacci**,
   Stochastics and Dynamics 21(3) (2021), 2140001; published online in 2020.
   [DOI](https://doi.org/10.1142/S0219493721400013);
   [arXiv:1910.00988v3](https://arxiv.org/abs/1910.00988v3);
   [PDF](https://arxiv.org/pdf/1910.00988).
   Sections 1–2, especially Theorem 2.1, give the Fibonacci frequencies,
   Fourier module, intensity formula, and pure point spectrum.

8. Michael Baake and Uwe Grimm,
   **Inflation versus projection sets in aperiodic systems: The role of the
   window in averaging and diffraction**,
   Acta Crystallographica Section A 76(5) (2020), 559–570.
   [DOI](https://doi.org/10.1107/S2053273320007421);
   [published full text](https://journals.iucr.org/a/issues/2020/05/00/ae5086/);
   [arXiv:2004.03256v2](https://arxiv.org/abs/2004.03256v2);
   [PDF](https://arxiv.org/pdf/2004.03256).
   Technical treatment of averaging, windows, Fibonacci diffraction, and
   distinctions among spectral types.

[1]: https://arxiv.org/abs/cond-mat/9206001
[2]: https://arxiv.org/abs/math/0504001v2
[3]: https://doi.org/10.1103/PhysRevE.71.066112
[4]: https://arxiv.org/abs/0709.3604v3
[5]: https://doi.org/10.1103/PhysRevLett.53.2477
[6]: https://arxiv.org/abs/1606.08831v2
[7]: https://arxiv.org/abs/1910.00988v3
[8]: https://arxiv.org/abs/2004.03256v2
