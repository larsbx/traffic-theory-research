# Traffic nets: one formal object for every model here

**Research note — 24 November 2026.** BML, the [roundabout grid](2026-11-24-roundabout-bml.md)
and the [mixed grid with or without links](2026-11-24-mixed-roundabout-grid.md) were three
kernels with three copies of the same gridlock argument. This note defines one object in Lean
of which they are parameter choices, proves the gridlock argument once, and ties the Python
kernel to the Lean definition by replay.

**Status.** Everything in §§1–8 is checked by Lean with no `sorry` and only the standard axioms
(`NetAudit.lean`, 638 declarations). §9 is a finite replay. §10 lists what is still prose.

Lean: [`BML/Net.lean`](../../formal/lean/BML/Net.lean),
[`BML/NetInstances.lean`](../../formal/lean/BML/NetInstances.lean),
[`BML/NetGridlock.lean`](../../formal/lean/BML/NetGridlock.lean),
[`BML/NetFree.lean`](../../formal/lean/BML/NetFree.lean),
[`BML/NetCount.lean`](../../formal/lean/BML/NetCount.lean),
[`BML/NetMixed.lean`](../../formal/lean/BML/NetMixed.lean),
[`BML/NetPlacement.lean`](../../formal/lean/BML/NetPlacement.lean),
[`BML/NetRoundabout.lean`](../../formal/lean/BML/NetRoundabout.lean),
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
| `stuck_extendable` | a stuck state with a car and an empty cell has an empty cell whose next cell, for some species, is occupied; queuing a car there keeps it stuck (`stuck_place`) |
| `stuck_carCount_le_cells`, `gridCells_length` | a gridlock has at most as many cars as the grid has cells, which is (1 + 2ℓ)·w·h + 2·\|R\| |
| `gridlock_count_iff` | **MX-G**: an n-car gridlock exists iff some straight street has at most n cells and the grid has at least n |

Together: the gridlock populations are exactly the interval from
min((1+ℓ)·W + min_y r_y, (1+ℓ)·H + min_x c_x) to (1+2ℓ)·W·H + 2·|R|, which is MX-G for both
variants. The proof projects a stuck state onto its junctions and
reuses the existing BML winding theorem (`jam_has_simple_blocker_cycle`), with one new lemma that
ties the winding numbers to the species met on the cycle.

With `mixed_stuck_iff`, "stuck" here is the dynamical notion: the state is unchanged by two
consecutive ticks.

## 5. Free flow, for every net

A state is **free** if no car is ever delayed by another car: in every tick, every car whose
gate is open moves. A car may still wait for a closed gate. The **solo timetable** of a car is
the path it would follow alone on the net, which depends only on its route and its gates.

| Lean name | statement |
|---|---|
| `step_undelayed` | a tick in which nobody is delayed moves every car by its own solo advance |
| `free_run_iff` | in a free state, the car in a cell at tick t is the one whose solo timetable puts it there |
| `Free.sub` | **heredity**: removing cars from a free state leaves it free |
| `Free.run_sub` | and the run of the smaller state is the corresponding part of the larger run |
| `free_iff_pairs` | **pairwise**: a state is free iff each of its two-car sub-states is free |

So the free states of any net are exactly the sets of cars that are pairwise compatible, where
two cars are compatible if the state holding just those two is free. Capacity is the largest
such set. This is what the static criterion RB-R says for the roundabout grid, and it is what
makes the capacity searches in `bml/roundabout.py` and `bml/mixed.py` complete: they grow free
states one car at a time, which reaches every free state by `Free.sub`.

These theorems need no assumption on the net: no fairness, no completeness, no finiteness.

## 6. Freeness is decided in finite time, and cars are conserved

| Lean name | statement |
|---|---|
| `free_of_recurrence` | if the gates have period P, the run is undelayed up to tick T0 + P·m, and the state there equals the state at T0, then the state is free |
| `mixed_periodic` | the mixed grid's gates have period 2 |
| `count_step`, `count_run` | on a net whose routes never end where a car can arrive (`RouteClosed`), a state with no car at an exit keeps its number of cars of each class for ever |
| `mixed_routeClosed`, `mixed_count_run` | the mixed grid is such a net, so its valid states conserve each species |

`free_of_recurrence` is what the Python `is_free` checks now test: both kernels simulate to a
horizon and additionally require that the state recurs with a gate-aligned period. So every
"free" verdict in the capacity censuses is an instance of this theorem (given the kernel
replay of §9), and every "not free" verdict exhibits a delayed tick.

## 7. Where the roundabouts are (Corollary MX-E)

With k roundabouts, w' = (1+ℓ)·w and h' = (1+ℓ)·h:

| Lean name | statement |
|---|---|
| `exists_light_row`, `exists_light_col` | some row has at most ⌊k/h⌋ roundabouts and some column at most ⌊k/w⌋ |
| `best_bound` | so every placement has a gridlock with at most min(w' + ⌊k/h⌋, h' + ⌊k/w⌋) cars |
| `best_attained` | the balanced placement (`balanced`) has k roundabouts and every gridlock has at least that many cars |
| `row_heavy`, `col_heavy` | every row has at least k − w(h−1) roundabouts and every column at least k − h(w−1) |
| `worst_bound` | so every gridlock has at least min(w' + (k − w(h−1)), h' + (k − h(w−1))) cars |
| `worst_attained` | filling the other rows (or columns) first gives a gridlock with exactly that many |

The balanced placement gives row y ⌊k/h⌋ roundabouts, one more for the first k mod h rows,
laid on consecutive columns of a cyclic order that continues from the previous row; every
column then holds at least ⌊k/w⌋.

## 8. Capacity of the roundabout torus (Corollary RB-C)

All intersections are roundabouts and there are no links.

| Lean name | statement |
|---|---|
| `undelayed_carCount_le` | a valid state in which nobody is delayed for even one tick has at most w·h cars |
| `free_carCount_le` | so every valid free state has at most w·h cars |
| `capacity_attained` | east cars on every east quadrant are a valid free state with w·h cars |

The upper bound needs only one tick: a junction cell occupied now is empty next tick, and every
car in a quadrant now is in a junction next tick, so the junctions occupied now and next are
disjoint and together hold every car.

## 9. Replay against the Python kernel

`net_export` runs the generic `step` on the mixed instance and prints each tick;
`scripts/check_net.py` recomputes it with `bml.mixed.step`. The two agree on 26,650 ticks:
every valid state of the boards with at most two intersections, for every roundabout set, with
and without links, on both tick parities, and pseudo-random runs of eight ticks on seven
boards up to 5×4. This is finite evidence that the Python kernel implements the Lean
definition, not a refinement proof.

## 10. What is not yet formal

| result | status |
|---|---|
| which pairs of cars are compatible on the roundabout grid (RB-R), the species frontier with both species (RB-F) and the pulsing corollary (RB-P) | prose, with exhaustive finite checks; §5 reduces RB-R to a statement about pairs |
| the junction time budget on mixed grids (MX-F) | prose |
| the law of the least gridlock under random placement (MX-P) | prose |
| that the Python horizons are long enough for every free state to recur | not needed for soundness: a free verdict is certified by §6, so a horizon too short could only misreport a free state as not free, and the census tests would detect that |
| capacity census for mixed grids, jamming sweep | finite data and simulation |

Limits of the object itself: routes of one class may not merge, a car advances at most one cell
per tick, and re-routing is not expressible. Each needs a change to the definition, not a new
instance.
