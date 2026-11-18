# Freezing, nucleation, and the BML gridlock question

**Research note — 18 November 2026.** The useful connection with freezing is
the separation between a possible final state, formation of a persistent seed,
and capture of the surrounding system. For BML, these become distinct
deterministic and probabilistic questions. This note gives a finite capture
argument and identifies the probability estimate it leaves open.

Use the repository's synchronous **east-then-north** rule on
\(\mathbb Z_W\times\mathbb Z_H\), with positive dimensions. Eligibility is
computed before each half-step. Let \(F\) be a full step and let
\(n_E,n_N\) be the conserved species counts. A jam is a **nonempty** fixed
configuration; the empty configuration is free flow by convention. The
[theorem document](../theorems.md) fixes these definitions and their boundaries.

## 1. What the water analogy contributes

Water's equilibrium melting boundary and its observed freezing onset answer
different questions. Creating an ice nucleus requires overcoming an interface
cost. A supercooled sample can consequently remain liquid until nucleation
occurs. For homogeneous nucleation at constant temperature, a common model is

\[
\Pr(\text{nucleation by }t)=1-\exp[-J(T)Vt],
\]

where \(J(T)\) is a rate per unit volume. Shardt et al. experimentally vary
droplet volume and cooling rate and describe this Poisson model [1]. Their
results show why observed onset depends on exposure time and sample size;
one quoted onset temperature is not a universal kinetic cutoff.

BML suggests an analogous set of questions: which structures persist, how they
form, and whether they stop the rest of the traffic. Its randomness comes from
the chosen initial ensemble; subsequent evolution is deterministic. No BML
Gibbs free energy, thermal nucleation rate, or equilibrium coexistence condition
has been established here. Applying the displayed exponential law to traffic
would require a separate derivation or an explicitly tested approximation.

Published BML studies already motivate this comparison. D'Souza finds moving
bands and jammed wavefronts, with geometry depending on the torus dimensions
[2]. Linesch and D'Souza report that selected local perturbations can nucleate
a global jam, and that different outcomes coexist at the same density and
aspect ratio [3]. These observations support studying structures and their
basins; they do not identify a universal freezing density.

## 2. Four questions that must remain separate

| Question | Mathematical object | What an answer establishes |
| --- | --- | --- |
| Existence | A frozen state with specified counts | An allowed configuration exists. |
| Basin | Initial states whose orbits reach that state or class | Those initial states eventually jam. |
| Capture | A persistent structure forcing other cars to stop | A sufficient dynamical certificate. |
| Limiting probability | Basin measure under a specified ensemble as dimensions grow | A statistical phase claim, if the limit is proved. |

The repository's minimum-jam construction ranges over **all species
allocations** at total count \(n\). It gives a jam whenever
\(\min(W,H)\le n\le WH\). On an \(L\times L\) torus its existence
threshold therefore has density \(1/L\). This does not say that a typical
random configuration at that density jams.

Likewise, the construction of a nonjamming state at every sub-full count can
use a single species. It does not prove existence for every prescribed pair
\((n_E,n_N)\), or for balanced counts. These quantifiers matter when comparing
constructions with experiments that fix both species.

Two useful ensembles are the product law

\[
\mu_p(E)=\mu_p(N)=p/2,\qquad \mu_p(0)=1-p,
\]

independently at each site, and the uniform law on configurations with exact
counts \((n_E,n_N)\). They need separate labels in every result. Conditioning
the first law on counts produces the second, but unconditioned probabilities
also average over fluctuating counts.

For square tori define

\[
\tau_J(s)=\inf\{t\ge0:F^t(s)\text{ is a nonempty fixed state}\},
\qquad P_J(L,p)=\mu_p(\tau_J<\infty).
\]

The [existing open target](../theorems.md#0-the-open-problem-stated-precisely)
concerns limits of \(P_J\). Neither a positive universal critical density nor
its numerical value is proved here. Exceptional nonjamming configurations can
exist at each size even when their probability tends to zero.

## 3. A permanent core need not capture every car

A **direct blocking core** is a nonempty set \(C\) of occupied cells such that
each car in \(C\) points directly to another cell of \(C\). During the east
half-step every eastbound core car has an occupied destination, so it stays.
The northbound core cars then have occupied destinations too. Induction proves
that all these cars remain at their original cells forever, regardless of
motion outside \(C\).

This is stronger than observing a region of stopped cars in one snapshot.
A moving jam front may release cars at its head while admitting others at its
tail [2]. Such an active intermediate pattern does not by itself provide a
permanently immobile set of car identities.

Conversely, permanent immobility alone need not imply global gridlock. A full
row of eastbound cars is a permanent core. Put some eastbound cars and at least
one vacancy in another row. That row always has a car immediately behind a
vacancy and therefore always has motion. The combined system has stationary
cars and continuing traffic. A core can persist without spanning the routes
needed to capture the rest.

This example also explains why adding a car cannot automatically be treated as
increasing the eventual-jam event. The repository records stronger
[nonmonotonicity witnesses](../theorems.md#4-non-monotonicity) in which adding a
car keeps an original car moving forever. A monotone coupling argument needs
additional structure; particle count alone does not supply it.

## 4. Winding turns a local certificate into global capture

Consider a simple direct blocker cycle. Lift its steps to \(\mathbb Z^2\).
If it contains \(a\) east steps and \(b\) north steps, closure gives

\[
a=uW,\qquad b=vH,\qquad u,v\ge0,\qquad u+v>0.
\]

The cycle cannot be a contractible directed loop: every lifted step increases
the coordinate sum. Its obstruction depends on torus winding. In particular,
a fixed-size direct loop cannot remain confined to a bounded patch as both
torus dimensions grow.

If both orientations occur, then \(u,v>0\). The lifted east steps traverse
every column residue and the north steps traverse every row residue. Thus the
cycle is a permanent core meeting every row and every column. A pure east
cycle instead occupies a full row, and a pure north cycle a full column.
The mixed cycle has at least \(W+H\) cars. This simplest exact capture
certificate therefore already spans the torus; it is not a bounded local
nucleus whose size stays fixed in a large-system limit.

**Published precedent.** Angel, Holroyd, and Martin explicitly state in the
proof of Theorem 2 that a cyclic blocking path with both horizontal and
vertical steps suffices for all cars to move only finitely often [4,
numbered arXiv p. 12]. Their blocking paths include additional local dependency
patterns beyond direct occupied-successor edges. The direct-cycle criterion
here is a transparent specialization, not a claim of discovering mixed-cycle
capture.

### A direct finite bound

Suppose that, at a full-step boundary \(t_0\), a direct blocking core meets
every row and every column. Then every car eventually stops, and both the
number of subsequent individual moves and the number of full steps needed
to reach a fixed state are bounded by

\[
\boxed{M=n_E(W-1)+n_N(H-1).}
\]

**Proof.** Core cars never move, by the half-step induction above. Each other
eastbound car stays in its original row. Choose a core cell in that row.
The car cannot pass through this permanently occupied cell, so it makes at
most \(W-1\) further east moves. The corresponding bound for a northbound
car is \(H-1\). Summing proves the bound \(M\) on all future individual
moves; core cars contribute zero and only make this estimate looser.

Every nonfixed full step makes at least one individual move, by G0 in the
theorem document. A step with no moves leaves a fixed state, so it cannot be
an idle interval before movement resumes. More than \(M\) nonfixed steps
would therefore require more than \(M\) moves. Consequently
\(F^{t_0+M}(s)\) is fixed. Nonemptiness persists, so this is gridlock. ∎

The proof allows arbitrary species counts and dimensions equal to one.
Coverage of every row and column is a convenient sufficient hypothesis;
only rows containing eastbound cars and columns containing northbound cars
actually need permanent obstacles. No necessity or optimality is claimed.
A mixed direct cycle supplies the stronger hypothesis immediately.

This is a prose derivation. Consult the [formal coverage register](../../formal/README.md)
for the actual executable and machine-checked scope of
[`bml/capture.py`](../../bml/capture.py) and
[`BML/Capture.lean`](../../formal/lean/BML/Capture.lean). A link to an
implementation does not establish that every statement in this section has
been formalized or that a hosted acceptance run succeeded.

## 5. Why the missing probability is about formation

Let \(C_0\) mean that a simple direct blocker loop exists initially on an
\(L\times L\) torus under \(\mu_p\). Such a loop contains
\(L\le\ell\le L^2\) distinct cells. There are at most
\(L^2 2^\ell\) rooted direction words of length \(\ell\); each valid
simple loop requires its specified orientations with probability
\((p/2)^\ell\). Hence, for \(0\le p<1\),

\[
\Pr(C_0)\le L^2\sum_{\ell=L}^{L^2}p^\ell
\le\frac{L^2p^L}{1-p}\longrightarrow0.
\]

This bound holds even at fixed densities sufficiently close to one, where
AHM's finite-torus theorem establishes eventual fixation with probability
tending to one [4, Theorem 2]. Therefore absence of an initial direct loop
cannot establish a low-density flowing phase. The repository already records
a [finite witness](../theorems.md#8-why-an-initial-loop-bound-does-not-prove-a-low-density-phase)
that forms a jam despite having no such initial loop.

There is no contradiction with AHM's high-density proof: it uses the richer
blocking-path structure mentioned above. Its theorem applies as both
dimensions grow with their ratio tending to a positive finite limit; it does
not identify a critical density near the values suggested by simulations.

At positive times, \(F^t(s)\) is correlated. Multiplying probabilities as
though its cells were freshly iid, or extending the time-zero bound through
an unproved union over unlimited time, is invalid. A mixed-cycle formation
event provides a sufficient route into the jam basin. Estimating that event
would give a lower bound on jamming, not an exact characterization unless
the missing converse were separately proved.

## 6. Proposed reproducible probability study

The following pilot is a proposal, not a completed experiment or a promised
critical-density estimate.

Use dimensions \((16,16),(32,32),(32,16),(33,32)\), densities
\(0.20,0.30,0.35,0.40,0.50\), and 32 independent initial configurations
per setting. Keep iid runs separate from exact-count runs, where
\(n=\lfloor pWH\rfloor\), \(n_E=\lfloor n/2\rfloor\), and
\(n_N=n-n_E\). Pin the generator algorithm, seeds, complete initial states,
update convention, and code revision. The nearby square and coprime rectangle
help distinguish arithmetic effects from a change in macroscopic aspect ratio.

Resume the same trajectories to budgets \(10^3,10^4,10^5\) full steps.
Record first permanent-core detection, row/column coverage, mixed-cycle
winding, first capture certificate, and first fixed state. For a detected
capture certificate, verify the remaining-move bound using labeled replay.
Report the fractions that are certified JAM, certified FREE, certified
intermediate cycles, or still unresolved, with sampling uncertainty.

A repeated full-step configuration certifies a deterministic occupancy cycle.
Claims that a particular original car moves forever require an identity-aware
cycle or another identity argument. A small measured velocity over the last
window certifies neither recurrence nor eventual gridlock. D'Souza and Linesch
and D'Souza explicitly distinguish observed long-lived behavior from verified
periodic states [2,3].

For interventions, preserve the declared ensemble constraints. A proposed
seed insertion should be paired with a matched rearrangement retaining total
and species counts. If row counts of eastbound cars or column counts of
northbound cars change, record that too: these are conserved by the dynamics.
Selection of successful-looking seeds must not be confused with an unbiased
estimate of their natural formation probability.

Finally, report the measured quantity as
\(P_J(L,p;T)=\Pr(\tau_J\le T)\), with \(T\) visible. The eventual
quantity takes \(T\to\infty\) at fixed size before any large-size limit.
No interchange of these limits is justified by a finite pilot. The next
mathematical obligation is a controlled estimate for formation of structures
that force capture, or for avoidance of every relevant capture mechanism.

## References

1. Nadia Shardt et al., **Homogeneous freezing of water droplets for different
   volumes and cooling rates**, Physical Chemistry Chemical Physics 24 (2022),
   28213–28221. [DOI](https://doi.org/10.1039/D2CP03896J);
   [publisher text](https://pubs.rsc.org/en/content/articlehtml/2022/cp/d2cp03896j).
   Primary experimental source for the volume/time dependence and Poisson
   nucleation model. It is not a model of BML.

2. Raissa M. D'Souza, **Coexisting phases and lattice dependence of a cellular
   automaton model for traffic flow**, Physical Review E 71 (2005), 066112.
   [DOI](https://doi.org/10.1103/PhysRevE.71.066112);
   [published PDF](https://web.cs.ucdavis.edu/~raissa/Pubs/bml-pre.pdf).
   Sections III–IV treat simulation limits, intermediate patterns, geometry,
   and moving jam fronts.

3. Nicholas J. Linesch and Raissa M. D'Souza, **Periodic States, Local Effects
   and Coexistence in the BML Traffic Jam Model**, Physica A 387 (2008),
   6170–6176. [DOI](https://doi.org/10.1016/j.physa.2008.06.052);
   [arXiv:0709.3604v3](https://arxiv.org/abs/0709.3604v3).
   Primary source for local perturbations, coexistence, and the distinction
   between periodic states and potentially long-lived transients.

4. Omer Angel, Alexander E. Holroyd, and James B. Martin, **The Jammed Phase
   of the Biham–Middleton–Levine Traffic Model**, Electronic Communications in
   Probability 10 (2005), 167–178.
   [DOI](https://doi.org/10.1214/ECP.v10-1148);
   [arXiv:math/0504001v2](https://arxiv.org/abs/math/0504001v2);
   [PDF](https://arxiv.org/pdf/math/0504001).
   Theorems 1–2 give high-density fixation; the proof of Theorem 2 begins on
   numbered arXiv p. 12 with the mixed cyclic blocking-path capture criterion.
   Page numbers here refer to the 15-page arXiv manuscript, not journal pages.
