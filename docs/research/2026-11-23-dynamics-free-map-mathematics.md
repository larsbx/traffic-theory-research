# Dynamics-free mathematics on real street maps

**Research note — 23 November 2026.** Most results in this repository are statements about
configurations and graphs, not about orbits of one update rule. This note restates them for
lane graphs built from OpenStreetMap (`app/`) under two assumptions that BML satisfies but do
not determine it. It then adds four results from outside the repository that can be computed
from the map alone. Code: [`app/src/structure.js`](../../app/src/structure.js), served as
`GET /api/analyze` ([`app/src/api.js`](../../app/src/api.js)); tests:
[`app/test/structure.test.js`](../../app/test/structure.test.js).

## 0. Setting

A **lane graph** G = (V, A) has cells V (7.5 m, one car length) and unit-step arcs A
(`app/src/raster.js`). A state places at most one car per cell. Each car k carries a committed
next cell q_k ∈ out(p_k) ∪ {EXIT}. Every model considered here satisfies:

- **(E) Exclusion.** A cell holds at most one car, and a car advances at most one cell per
  half-step.
- **(C) Commitment.** A car re-chooses q_k only after it moves. A car's move into q_k requires
  q_k to be vacant before the half-step (CLASSIC), or vacated in the same half-step by a car
  that moves too (TRAIN).

Signals, the box rule, dawdling and breakdowns only **remove** moves. Every statement below that
says "never moves" or "at most" therefore holds under all of them. BML is one rule satisfying
(E)+(C), and so are car-following models with a reaction-time grid, block-signalled rail and
automated guided vehicles.

The **jam graph** J ⊆ G has an arc b → c iff some car at b can commit to c. That covers some
legal arrival a → b (turn rules: `sim.turnOptions`) and also a freshly spawned car, which may
take any out-lane. J depends on the routing law, but it does not depend on signals or on the
box rule, which act on timing.

## 1. Results that transfer from the torus

| repository result | its dynamics-free content | on a map | code |
|---|---|---|---|
| Lemma G0 | frozen ⟺ the wait-for map β is total | **P1** | `analysis.certificate` |
| Theorem G1 | β has a cycle, and a cycle is a closed lattice loop | **P2**: cores have ≥ girth(J) cars | `jamGraph`, `girthOf` |
| Wang-tile encoding | frozen states are locally checkable labellings | "can these junctions be jammed?" is a finite constraint problem | — |
| Torus winding | a blocker loop is a closed walk on the torus | **R1**: loops have even length ≥ 4 | `girthOf` |
| Capture bound (Lean) | every round some car moves, and none moves past the core | **R2** for fixed routes | — |
| Non-monotonicity | the stuck set is not monotone in the state | removing cars or capacity need not help | — |
| Fibonacci staircase | blocking along irrational slopes follows mechanical words | **P4**: streets are Sturmian | `cuttingWord`, `freeSpeed` |

**P1 (certificate; the form of G0 on maps).** Let β(k) be the car occupying q_k. Under the box
rule, when k waits to enter a junction, β(k) is the first car on k's committed path through
the box. Every car on a β-cycle, and every car whose β-path reaches one, never moves again.
Under TRAIN the exception is a cycle of direct arcs that all lie on one axis, which rotates.

*Proof.* Let t be the first half-step at which some car k of the cycle moves. Under CLASSIC, k
needs its blocker's cell vacant before t. But the blocker has not moved yet, by the choice of t.
Under TRAIN, k moves only together with its direct blocker, in the same phase. So the whole
cycle moves at t, along one axis, through direct arcs. That is the excluded case. Commitment
keeps every q_k fixed until then. The claim for the trees feeding the cycle follows by induction
along β-paths. ∎ (Also in [`app/README.md`](../../app/README.md#jam-certificates); property-tested
in `app/test/sim.test.js`.)

**P2 (minimum jam; the form of G1 on maps).** Every β-cycle of direct arcs is a simple directed
cycle of J. Hence every permanent core of direct arcs has at least girth(J) cars. Conversely, let
C be any simple cycle of J. For every n with |C| ≤ n ≤ |{v : v reaches C in J}|, some
configuration of n cars is frozen.

*Proof.* (⇒) Consecutive cars on a direct β-cycle sit in distinct cells b → c with c = q_k, so
b → c is an arc of J. (⇐) Put one car on each cell of C, committed to its successor on C, with
arrivals chosen to make each hop legal; J guarantees such an arrival exists. Then fill a
spanning in-forest of the cells reaching C, from the cycle outwards. Each new car is committed to
its parent, which is occupied and frozen. ∎

Measured (`app/test/structure.test.js`): every core observed in simulation on the six presets
lies on J and has ≥ girth(J) cars. A single car's *turn* graph is the wrong object here. The
2×2 box of a two-way crossing is a 4-cycle of J made of four cars, each driving **straight**
from a different direction, and no one car could drive around it. The girth of the turn graph
there was 20, while the observed cores had 4 cars.

*Scope.* Under the box rule a β-arc can be indirect: k waits for a car further along its box
path. Such cycles are certified by P1, but they need not be cycles of J, so P2's bound covers
direct cores only.

**R1 (parity).** Every arc of G changes x + y by ±1, so G is bipartite and every cycle has even
length. The girths observed are 4, 18, 52, 58, 62, 106 and 140, all even. A jam loop of length 4
is exactly a 2×2 box. Anything longer must go around at least one non-road cell, which is a
building, at 7.5 m.

**R2 (capture for fixed routes).** Suppose every car's route is fixed in advance, as for AGVs
or trains. Let d_k be the number of hops car k makes before reaching a frozen car. While any
car outside the frozen set can move, at least one does. So every car is frozen within Σ_k d_k
rounds. On the torus with straight routes this is the shape of the Lean bound
n_E(W−1) + n_N(H−1). With random routing, d_k is a random variable and the bound becomes a
statement about its tail.

## 2. Four results from outside the repository

**P3 (throughput bound; max-flow/min-cut).**
1. *Lemma.* Under CLASSIC, a cell that no car can spawn into is entered at most once per two
   half-steps. Every cell is entered at most once per half-step.

   *Proof.* Let entries happen at t < t′. The first car must leave strictly after t. The second
   needs the cell vacant before t′, so the first car left at or before t′ − 1. Hence t′ ≥ t + 2.
   The second bound is exclusion. ∎
2. *Bound.* Give each cell a capacity in cars per full step: 1 for CLASSIC cells without spawns,
   2 otherwise. The long-run exit rate Φ is then at most the maximum flow from entries to exits
   (`throughputBound`). Every exiting car crossed every entry–exit cut after it spawned. Each
   such crossing is an entry into a cut cell, and the lemma caps those entries. ∎ Cars present
   at time 0 add a one-time transient.
3. *Measured.* Both the lemma and the bound are checked against simulation on six maps under
   both rules.

The same cut, weighted by a per-lane capacity curve instead of by the lemma, is the starting
point of the cell transmission model (Daganzo 1994). It also underlies the analytical
macroscopic fundamental diagram (Daganzo & Geroliminis 2008), which needs block lengths and
signal timings but no vehicle dynamics.

**P4 (Sturmian streets).** A straight street at bearing θ rasterises to the cutting sequence of
its line, as `raster.traverse` produces it. That is a Sturmian word in the axes {H, V} (Morse &
Hedlund 1940). Let α = min(|tan θ|, |cot θ|). The minority letter has frequency α/(1+α) ≤ ½ and
never repeats. So the switch rate is σ = 2α/(1+α).

Under pure two-phase alternation (green = 1), a free car spends one half-step on a hop whose
axis differs from the previous one, and two otherwise. Its free speed is therefore

  v(θ) = 2 / (2 − σ) = 1 + α cells per full step = 1 / max(|cos θ|, |sin θ|) in straight-line cell lengths.

Diagonal streets are therefore faster than axis-aligned ones under BML lights, up to √2 at
45°. The rasteriser's staircases thus inherit the dynamics of the repository's blocking
staircases. *Measured:* the word's switch rate and speed agree to 2·10⁻³ at ten bearings, and a
single simulated car at slope ½ matches v = 3/2.

**H1 (risk index; graph zeta function). A heuristic, not a theorem.** Treat occupancy as i.i.d.
with density ρ. Let q(b → c) be the mean-field routing probability on J, averaged over arrivals.
A simple cycle C then closes instantaneously with probability w(C) = ∏_{b→c ∈ C} ρ·q(b→c), and

  R(ρ) = Σ_{C simple, |C| ≤ ℓ_max} w(C)  ≤  Σ_{ℓ≥1} tr((ρQ)^ℓ)/ℓ = −log det(I − ρQ) = log ζ_J(ρ),

where ζ_J is the weighted Bowen–Lanford zeta function of the directed graph J. The series
converges while ρ·λ_max(Q) < 1, and exits make Q substochastic. As ρ → 0,
R(ρ) ≈ N_g (ρ q̄)^g, where N_g counts the shortest cycles. So the girth sets the exponent: ρ⁴ at
a 2×2 box against ρ⁵² on the Eixample grid. Queues correlate occupancy upward, so R ranks maps
and hotspots rather than predicting rates. `cycleCensus` enumerates cycles within a work budget
and reports whether it finished.

| map | girth(G) | J, city code: girth · cycles ≤ g+8 · R(0.3) | J, BML lights: girth · cycles · R(0.3) | Φ ≤ (CLASSIC / TRAIN) | jams seen in simulation |
|---|---|---|---|---|---|
| Midtown | 58 | 140 · 0 · 0 | 58 · 1 · 1·10⁻³² | 13 / 26 | none |
| Eixample | 52 | 106 · 4 · 2·10⁻⁵⁷ | 52 · 65 · 8·10⁻³⁰ | 16 / 32 | none |
| Grachten | ∞ | ∞ · 0 · 0 | ∞ · 0 · 0 | 12 / 24 | none |
| Étoile | 18 | 62 · 3 · 5·10⁻³⁴ | 18 · 4 · 1·10⁻¹¹ | 20 / 40 | once laws are repealed |
| Bank | 4 | 4 · 2 · 7·10⁻⁴ | 4 · 2 · 2·10⁻³ | 26 / 42 | once laws are repealed |
| Shibuya | 4 | 4 · 1 · 5·10⁻⁴ | 4 · 1 · 1·10⁻³ | 25 / 48 | at ρ ≈ 0.45 even under the city code |

The ordering by R matches the simulations in `app/README.md`. Under the city code J still has
Bank's and Shibuya's 4-cycles. The box rule and signals keep Bank clear in time, which J cannot
see. Shibuya still locks at ρ ≈ 0.45 even so.

**Deadlock detection on real fleets.** P1 needs only positions and committed next links. Given
those from connected vehicles, AGVs or a block-signalled railway, a cycle of the wait-for graph
is an exact deadlock certificate under (C). This is the circular-wait condition of Coffman,
Elphick and Shoshani (1971). Human drivers re-route, which violates (C), so for them a cycle is
a warning, not a proof.

## 3. Open and not computed here

- **Designing out short loops.** The fewest turn bans that raise girth(J) to a target g\* is a
  restricted feedback-arc-set problem, NP-hard in general (Karp 1972). An ILP over the census's
  short cycles would solve city-sized instances. Not implemented.
- **What needs dynamics or data.** Whether a jam forms, its nucleation rate, typical capture
  times and any density threshold are statements about a measure on orbits. P1–P4 and H1 bound
  them or rank maps for them. They do not decide them, and the sharp-threshold question stays
  open even on the BML torus ([`theorems.md`](../theorems.md)).

## References

- R. Bowen, O. E. Lanford, Zeta functions of restrictions of the shift transformation, *Proc.
  Sympos. Pure Math.* 14 (1970).
- E. G. Coffman, M. Elphick, A. Shoshani, System deadlocks, *ACM Computing Surveys* 3 (1971).
- C. F. Daganzo, The cell transmission model, *Transp. Res. B* 28 (1994).
- C. F. Daganzo, N. Geroliminis, An analytical approximation for the macroscopic fundamental
  diagram of urban traffic, *Transp. Res. B* 42 (2008).
- J. Edmonds, R. M. Karp, Theoretical improvements in algorithmic efficiency for network flow
  problems, *J. ACM* 19 (1972).
- R. M. Karp, Reducibility among combinatorial problems (1972).
- M. Morse, G. A. Hedlund, Symbolic dynamics II. Sturmian trajectories, *Amer. J. Math.* 62 (1940).
