# Traffic nets: one formal object for every model here

**Research note — 24 November 2026.** BML, the [roundabout grid](2026-11-24-roundabout-bml.md)
and the [mixed grid with or without links](2026-11-24-mixed-roundabout-grid.md) were three
kernels with three copies of the same gridlock argument. This note defines one object in Lean
of which they are parameter choices, proves the gridlock argument once, and ties the Python
kernel to the Lean definition by replay.

**Status.** Everything in §§1–4 is checked by Lean with no `sorry` and only the standard axioms
(`NetAudit.lean`). §5 is a finite replay. §6 lists what is still prose.

Lean: [`BML/Net.lean`](../../formal/lean/BML/Net.lean),
[`BML/NetInstances.lean`](../../formal/lean/BML/NetInstances.lean),
[`BML/NetGridlock.lean`](../../formal/lean/BML/NetGridlock.lean),
[`NetExport.lean`](../../formal/lean/NetExport.lean). Replay:
[`scripts/check_net.py`](../../scripts/check_net.py).

## 1. The object

A **net** over a type of cells and a type of car classes has

| field | meaning | models |
|---|---|---|
| `next k p` | where a class-k car in cell p goes next; `none` is an exit | routes, turns, open boundaries |
| `prev k c` | the inverse of `next k`, with proof | routes of one class never merge |
| `order c` | the classes in the order they win a contested entry to c | yield and priority rules |
| `gate t k c` | whether class k may enter c during tick t | signals, phases, offsets |

A state assigns to each cell at most one class. One tick (`step`) moves every car whose next
cell is vacant at the start of the tick, whose gate is open, and which is first in the merge
order among the cars contending for that cell. The definition is executable.

## 2. What is proved for every net

Call a state **stuck** if every car's next cell exists and is occupied. Call a net **complete**
if every route into a cell is listed in that cell's merge order, and **fair with period P** if
every gate opens at least once in every window of P ticks.

| Lean name | statement |
|---|---|
| `stuck_step` | a stuck state is unchanged by every tick, whatever the gates show |
| `stuck_iff` | for a complete, fair net: stuck ⟺ no tick of one period changes the state |
| `stuck_iff_run_constant` | the same along the run from tick 0: stuck ⟺ the state never changes |
| `stuck_blocker_cycle` | in a stuck state, following blockers from any car returns to an earlier cell within as many steps as there are occupied cells |

`stuck_iff` is Lemma G0, RB-0 and MX-0 at once. `stuck_blocker_cycle` is the first half of
every least-gridlock theorem: a gridlock has at least as many cars as the shortest directed
cycle of its blocker graph.

## 3. Instances

**BML** (`bml`). Both species go straight, the gate admits east cars on even ticks and north
cars on odd ticks. `bml_even` and `bml_odd` prove that an even tick of the net is exactly
`BML.halfStep` east and an odd tick exactly `BML.halfStep` north, for arbitrary reversible
neighbour maps; `bml_round` gives the full BML step. So every existing BML theorem is a
theorem about this instance.

**Mixed grid** (`mixed`). Cells are the junction, the two roundabout quadrants and the two
links of each intersection. A layout chooses the roundabout set and whether links exist. The
net is complete and fair with period 2, so `mixed_stuck_iff` is Lemma MX-0, now kernel-checked
for every roundabout set, with and without links, on any reversible grid. The roundabout grid
is the layout with every intersection a roundabout.

## 4. The least gridlock of the mixed torus (Theorem MX-G)

On the `w × h` torus, for every roundabout set and with or without links. The car count of a
state is the number of occupied cells.

| Lean name | statement |
|---|---|
| `junctions_frozen` | the junction cells of a stuck state form a frozen BML board |
| `stuck_carCount_cases` | a stuck state with a car has a full east street, or a full north street, or a simple blocker cycle through at least w + h junctions with the links behind them |
| `stuck_carCount_ge_street` | so its car count is at least the number of cells of some row street or some column street |
| `rowStreet_length`, `colStreet_length` | a row street has w + (w if links) + r_y cells and a column street h + (h if links) + c_x |
| `row_gridlock`, `col_gridlock` | filling one street is a stuck state with exactly that many cars |

Together: the least gridlock is exactly min((1+ℓ)·W + min_y r_y, (1+ℓ)·H + min_x c_x), which is
the formula of MX-G for both variants. The proof projects a stuck state onto its junctions and
reuses the existing BML winding theorem (`jam_has_simple_blocker_cycle`), with one new lemma that
ties the winding numbers to the species met on the cycle.

With `mixed_stuck_iff`, "stuck" here is the dynamical notion: the state is unchanged by two
consecutive ticks.

## 5. Replay against the Python kernel

`net_export` runs the generic `step` on the mixed instance and prints each tick;
`scripts/check_net.py` recomputes it with `bml.mixed.step`. The two agree on 26,650 ticks:
every valid state of the boards with at most two intersections, for every roundabout set, with
and without links, on both tick parities, and pseudo-random runs of eight ticks on seven
boards up to 5×4. This is finite evidence that the Python kernel implements the Lean
definition, not a refinement proof.

## 6. What is not yet formal

| result | status |
|---|---|
| a gridlock at every count between the least and all cells (rest of MX-G) | prose, with finite checks |
| extremes over placements and the random-placement law (MX-E, MX-P) | prose; they are arithmetic consequences of the formula in §4 |
| conservation of cars per class | not stated for nets |
| free-flow layer (RB-R, RB-F, MX-F) | prose; the planned form is a conflict graph on (cell, phase) slots |
| capacity census, jamming sweep | finite data and simulation |

Limits of the object itself: routes of one class may not merge, a car advances at most one cell
per tick, and re-routing is not expressible. Each needs a change to the definition, not a new
instance.
