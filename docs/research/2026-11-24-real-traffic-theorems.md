# Theorems for real traffic flow

**Research note — 24 November 2026.** The lane-graph results
([previous note](2026-11-23-dynamics-free-map-mathematics.md), [paper](../paper/paper.pdf)) rest
on a lattice: 7.5 m cells, unit speed, and drivers who never revise a committed move. Real
traffic has continuous space and time, has signal plans, and has drivers who re-route when
blocked. This note derives five results whose assumptions are physical and measurable. It
proves them and states what data would test each one. Where a result has a lattice instance, it
is checked in the simulator.

In the layers of the paper (§2), these are L2 statements: about real traffic, under the stated
assumptions. Their lattice instances (L1) are proved and tested here. None has yet been tested
against observed traffic.

Code: [`app/src/realflow.js`](../../app/src/realflow.js). Tests:
[`app/test/realflow.test.js`](../../app/test/realflow.test.js). Experiment:
[`app/scripts/reroute.mjs`](../../app/scripts/reroute.mjs) →
[`data/2026-11-24-reroute.json`](data/2026-11-24-reroute.json).

## 0. Assumptions, all physically measurable

| | assumption | physical value / source |
|---|---|---|
| **(X) exclusion** | A vehicle cannot advance while the front-to-front headway to its leader is at most the jam spacing s_jam. It enters a space only once that space is free. | s_jam ≈ 6.5–7.5 m, so k_jam = 1/s_jam ≈ 130–150 veh/km/lane |
| **(O) options** | At each moment a vehicle has a finite set of legal next moves (lane and turn choices) from its current position. It may switch among them at will, except where it is physically committed, as inside a junction box. Each move needs certain space to be free. | the lane geometry and turn restrictions of the network |
| **(S) signals** | Stop line e has an effective green fraction λ_e and a saturation flow s_e, the maximum discharge rate during green. | signal plans; s_e ≈ 1,800–1,900 veh/h/lane [HCM] |
| **(V) speed limit** | No vehicle exceeds v_f. | posted or measured free-flow speed |

(X) is the physical form of the CLASSIC rule. The TRAIN rule, where a whole queue starts in the
same instant, is not physical, so it is not used here.

## R1. Gridlock needs a loop's worth of jammed vehicles

**Theorem R1.** Let C be a closed loop of lane, of length L(C), along which vehicles are committed,
each to the path ahead of the next one. If every vehicle on C is permanently stopped, then C holds
at least L(C)/s_jam = k_jam·L(C) vehicles.

*Proof.* Going round the loop, the front-to-front headways of the n vehicles add up to L(C),
because the committed paths join into the closed loop. A stopped vehicle has headway ≤ s_jam by
(X). So L(C) ≤ n·s_jam. ∎

So the minimum size of a gridlock is the jam density times the length of the shortest committed
loop. This continuous form does not depend on any discretisation. The lattice Theorem 3(a),
"at least girth(J) cars", is the case s_jam = cell length.

| loop | length | at least |
|---|---|---|
| a 2×2 crossing box (four 15 m sides) | ≈ 60 m | 8 vehicles |
| round a Manhattan block (80 m × 274 m) | ≈ 708 m | 95 vehicles |
| Midtown preset, shortest loop of J, city code | 140 cells × 7.5 m = 1,050 m | 140 vehicles |

*Data to test it:* stopped-queue lengths in gridlock events, from drone or CCTV trajectories
such as pNEUMA [BG], against loop lengths from OpenStreetMap.

## R2. Structural traps and safe cells under re-routing

Under (O), each vehicle k has options o, each needing a set of space need(o) to be free: its
next cell and, if it is committed through a junction box, the rest of its path through the box.
A **trap** is a set S of on-street vehicles such that every option of every k ∈ S
needs some space occupied by a vehicle of S. A genuinely empty menu satisfies
this condition vacuously. An exit has an empty list of required cells and
defeats the condition. The simulator supplies an explicit fallback exit if
planning finds an empty turn list. The map certificate uses declared exits.

**Theorem R2.**
- **(a) Soundness.** Use (X) as CLASSIC pre-step vacancy. Assume a vehicle that
  has not moved retains its position and that its first hop or exit must use
  an option from its original menu. No vehicle of a trap ever records a hop or exit.
- **(b) Greatest trap.** A union of traps is a trap, so there is a greatest one, S\*. It is found
  by repeatedly deleting vehicles that have an option whose needed space is free, at an exit or
  held by a deleted vehicle.
- **(c) Commitment.** If every vehicle has exactly one option, its committed move, then S\*
  contains the frozen set certified by the wait-for-cycle theorem (paper, Theorem 2). Without the
  box rule the two are equal. With it, S\* also sees blocking anywhere along a box path.
- **(d) Re-routing shrinks traps.** Adding options to vehicles can only shrink S\*.
- **(e) Safe cells.** With the box rule off, take the least fixed point of the
  operator that admits a road cell when each supported arrival has an exit or
  a single-cell move into the set. Every member of a proposed trap must be
  able to re-route from its actual arrival using that menu. Such a trap
  contains no safe cell and is empty on a fully ranked map.

*Proof.*
- (a) At the first half-step containing a hop or exit by a member of S, its
  option requires a cell still occupied at the start of the step by a member
  of S. This contradicts CLASSIC vacancy. A temporary breakdown can delay a
  move without changing the menu. Permanent breakdowns can remove options,
  and towing changes the stationary-position premise.
- (b) If S₁ and S₂ are traps, every option of a vehicle in S_i needs space held by S_i ⊆ S₁ ∪ S₂,
  so the union is a trap. A deleted vehicle has an escaping option, so it cannot belong to a trap
  built from the vehicles that remain. Every changing pass deletes a vehicle,
  so at most the starting population many passes can change the set. The
  result is closed and contains all traps. Adding back any excluded vehicle
  that passed the final keep test would yield a larger trap, proving the
  fixed-point claim on the original population.
- (c) With one option each, k ∈ S\* iff its blocker is in S\*. Following blockers inside a finite
  set reaches a wait-for cycle, so S\* consists of the wait-for cycles and their basins. Under the
  box rule an option needs the whole box path, which also catches blocking beyond the first
  occupant.
- (d) Each deletion test only gains escape routes.
- (e) Grow from the empty set. Each changing pass ranks a new road cell.
  Each ranked cell has an exit or lower rank witness for every arrival. Each
  unranked cell has an arrival with no exit and all its destinations unranked.
  These conditions give a fixed point, and rank induction places it inside
  every set closed under the rule. Apply rank induction again to trap members.
  An exit cannot have a blocker. For a lower-ranked destination the occupant,
  if any, lies outside the trap by induction. Both cases violate closure. ∎

With a single required cell per option, this is the OR-request model of
deadlock [Holt]. The wait-for-cycle certificate is the single-request case.
Even freely re-routing vehicles can form a trap if all their options require
cells occupied by its members.

The [Lean proof and acceptance commands](../../formal/lean/README.md#lane-graph-traps-and-safe-cells-r2)
cover termination and maximality of deletion, permanence under the trace
contract, and leastness and trap exclusion from checked ranks. The preset
certificate records arrival directions, turns, declared exits and ranks.
Both the checker against the rasterized maps and the Lean checker accept
8,443 of 8,443 road cells in the six maps under each of the two no-box laws.

**Simulated evidence from the original experiment.** The script matched the
two policies on six presets, four law regimes, three densities and five seeds.
This gives 360 matched cases and 720 executions.

| | committed drivers | re-routing drivers |
|---|---|---|
| no box rule ("block the box", BML lights): safe-cell share | — | **100 % on all six maps** |
| endpoint trap share, no box rule, 180 executions per policy | up to 0.95 (Shibuya), 1.00 (Étoile) | **0 in every run** |
| trapped share with the box rule ("free turns", ρ = 0.4) | Étoile 1.00, Bank 0.38, Shibuya 0.70 | Étoile 0.10, Bank 0.12, Shibuya 0.18 |
| flow J at ρ = 0.3, Étoile, BML lights | 0.000 | 0.207 |
| flow J at ρ = 0.3, Bank, "block the box" | 0.026 | 0.149 |

The proof excludes self-supported blocking sets under the stated menus. Long
waits from signals, contention, route choice and temporary breakdowns remain
possible. Waiting-time guarantees would need a progress assumption and
discharge evidence.

*Data to test it:* use vehicle trajectories during gridlock events [BG] to
check supported arrivals, legal alternatives, actual commitments, exit
availability and the space needed for each move. Use observed timing and
throughput to evaluate finite congestion.

## R3. A loop cannot lock faster than its inflow can fill it

**Theorem R3.** Let a loop C of length L(C) hold n₀ vehicles at time 0, and let the total
capacity of the links entering C be Q, so the inflow is at most Q, and by (S) at most Σ λ_e s_e
over its entries. Then C cannot be in gridlock before
t\* = (L(C)/s_jam − n₀) / Q.

*Proof.* By R1, gridlock on C needs at least L(C)/s_jam vehicles on C. Vehicles are conserved
and the outflow is non-negative, so N_C(t) ≤ n₀ + Q·t. ∎

Example: round a Manhattan block (708 m) holding 29 vehicles (41 veh/km), with two signalised
entries of 1,800 veh/h each at λ = ½ (Q = 0.5 veh/s). It cannot lock in less than ≈ 130 s,
which gives a window for clearing an incident. `closureTimeBound` computes the bound.

*Data to test it:* incident logs with queue growth from loop detectors [UTD19].

## R4. Throughput is bounded by the cheapest cut through the stop lines

**Theorem R4.** The long-run rate Φ of completed trips from entries to exits satisfies
Φ ≤ F\* = min over entry–exit cuts of Σ_{e∈cut} λ_e·s_e.

*Proof.* Over a long time, a stop line discharges at most s_e during its green fraction λ_e,
which is the definition of saturation flow with effective green including lost time.
Unsignalised links get λ_e = 1 with their capacity as s_e. Every completed trip crosses every
cut. Taking the cheapest cut gives the bound, and max-flow min-cut computes it. ∎

The lattice Theorem 5 is the case s_e = one car per full step at a cell (CLASSIC). *Data:*
city signal plans and saturation flows [HCM], against network-wide trip completion counts.

## R5. Little's law gives a rigorous envelope for the macroscopic fundamental diagram

**Theorem R5.** On any finite window [0, T], let λ_T be the rate of trips both started and
completed in the window, ℓ̄_T their mean length, N̄_T the mean accumulation and v̄_T the mean
speed. Then
λ_T·ℓ̄_T ≤ v̄_T·N̄_T ≤ v_f·N̄_T.
In the long run, by Little's law, the first inequality becomes an equality, so
Φ ≤ min(N̄·v_f/ℓ̄, F\*) and the mean travel time satisfies T̄ = N̄/Φ ≥ max(ℓ̄/v_f, N̄/F\*).

*Proof.* The distance covered in the window by all vehicles is ∫ Σ v dt = v̄_T·N̄_T·T. It
includes the full length of every trip completed inside the window, which gives the first
inequality. The second is (V). In the long run, the boundary terms divided by T vanish and the
sample-path Little's law N̄ = Φ·T̄ [Stidham] gives the rest, with R4 supplying F\*. ∎

This is a triangular upper envelope for the macroscopic fundamental diagram [GD] that needs
only v_f, mean trip length and cut capacity. *Lattice check:* the exact finite-window
inequality holds with no tolerance on three presets (`realflow.test.js`). *Data:* accumulation
and trip lengths from GPS traces or loop detectors [UTD19].

## What is proved, tested and open

| result | proved | tested in the simulator | tested on real data |
|---|---|---|---|
| R1 jam-spacing bound | yes | lattice case (paper, Theorem 3(a)) | no |
| R2 traps, safe cells | yes | soundness, equality with the certificate, safe-cell claim, 360-run experiment | no |
| R3 closure time | yes | closed form only | no |
| R4 signal cut bound | yes | lattice case (paper, Theorem 5) | no |
| R5 Little / MFD envelope | yes | exact finite-window inequality | no |

What is open:
- the real-data tests listed under each result;
- a version of R2 that allows *partial* re-routing, where drivers revise with some probability;
- whether S\* = ∅ bounds how long transient jams last, which needs dynamics, not structure.

## References

- [BG] E. Barmpounakis, N. Geroliminis. On the new era of urban traffic monitoring with massive
  drone data: the pNEUMA large-scale field experiment. *Transp. Res. C* 111 (2020) 50–71.
- [GD] N. Geroliminis, C. F. Daganzo. Existence of urban-scale macroscopic fundamental diagrams:
  some experimental findings. *Transp. Res. B* 42 (2008) 759–770.
- [HCM] Transportation Research Board. *Highway Capacity Manual*, 7th ed. (2022).
- [Holt] R. C. Holt. Some deadlock properties of computer systems. *ACM Comput. Surv.* 4 (1972)
  179–196.
- [Stidham] S. Stidham. A last word on L = λW. *Oper. Res.* 22 (1974) 417–421.
- [UTD19] A. Loder, L. Ambühl, M. Menendez, K. W. Axhausen. Understanding traffic capacity of
  urban networks. *Sci. Rep.* 9 (2019) 16283.
