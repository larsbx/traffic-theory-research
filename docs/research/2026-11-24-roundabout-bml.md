# Roundabout BML: free-flow capacity and the species frontier

**Research note — 24 November 2026.** BML controls every intersection by a two-phase signal:
the E half-step, then the N half-step. This note replaces every intersection by a roundabout,
with no signal and a yield rule, and derives the exact free-flow theory of the resulting
model.

**Result (Theorem RB-F).** On the W×H torus, with g = gcd(W,H) and m = WH/g, a configuration
with n_E east cars and n_N north cars in which every car moves at every step forever exists
if and only if

> ⌈n_E/m⌉ + ⌈n_N/m⌉ ≤ g.

So the free-flow capacity is exactly WH, one car per roundabout, for every W and H. Both
species can flow freely together iff g ≥ 2, and the two species then share the g diagonal
classes in whole units of m cars. BML's capacity, by Theorem F of [theorems.md](../theorems.md),
is (WH/g)·⌊2g/3⌋ for g ≥ 2, and mixing needs g ≥ 3.

Everything here is a direct derivation with a complete prose proof, and it carries no claim of
novelty. Of this note, Lean checks RB-0 and the least gridlock of RB-G (as the all-roundabout
case of the [traffic net](2026-11-24-traffic-nets.md)), and that freeness is hereditary and
pairwise on any net; RB-R, RB-F and their corollaries are not formalized. The finite checks in §6 decide freeness
and gridlock from the dynamics, not from the formulas they test.

Code: [`bml/roundabout.py`](../../bml/roundabout.py). Tests:
[`tests/test_roundabout.py`](../../tests/test_roundabout.py). Replay:
[`scripts/check_roundabout.py`](../../scripts/check_roundabout.py).

## 0. The model

**Cells.** A roundabout is a counter-clockwise ring of four quadrant cells. A car enters the
quadrant just downstream of its arm and leaves from the quadrant just upstream of its exit, so
a straight-through car crosses two quadrants. East cars cross SW then SE; north cars cross SE
then NE. The NW quadrant is never used and is dropped. Intersection (x,y) ∈ ℤ_W × ℤ_H
therefore has three cells:

| cell | quadrant | holds |
|---|---|---|
| a(x,y) | SW | · or E (private) |
| c(x,y) | SE | · or E or N (shared) |
| b(x,y) | NE | · or N (private) |

Links between roundabouts have length zero: a car leaving one roundabout enters the next.

**Routes.**

- E: a(x,y) → c(x,y) → a(x+1,y) → … , a ring of 2W cells along row y;
- N: c(x,y) → b(x,y) → c(x,y+1) → … , a ring of 2H cells along column x.

One block is two cells. There are 3WH cells in all.

**Step.** There are no phases. In one step every car whose next cell is empty at the start of
the step moves into it, all at once (the CLASSIC vacancy rule: nobody enters a cell vacated in
the same step). The only cell with two entrances is c(x,y), entered from a(x,y) by an E car
already circulating and from b(x,y−1) by an N car entering the roundabout. If both want it,
exactly one moves. **Yield on entry** lets the E car go. The mirror rule lets the N car go.

**Scope.** All four results below hold for both yield rules, and the proofs use only that a
contested merge moves exactly one car. The reflection x ↔ y exchanges species and the two
yield rules (`transpose`). Cars never turn, as in BML, so the fourth quadrant is unused and a
ring can never close on itself.

**Turning traffic is a different model, and its four-car lock is an artifact.** With turns all
four quadrants are used. Four cars can then enter an empty ring in the same step, one per arm,
and if each has a further quadrant to cross, every next cell is occupied and the ring is fixed.
This does not describe a real roundabout. It comes from two features of the minimal model:

- the ring has as many cells as arms, so every cell is an entry cell and also the cell that the
  next entrant checks. If no two entry cells are adjacent, an entrant needs its entry cell t
  and the cell t−1 behind it empty. Afterwards t−1 is empty, or it was filled from t−2, which
  is then empty and could not be entered in that step. So entries never fill the ring;
- a full ring cannot rotate under the CLASSIC vacancy rule. Real circulating cars move
  together, as under the TRAIN rule, until one reaches its exit.

A real roundabout locks when a queue from downstream blocks an exit, which involves the
surrounding network and more than four cars. Nothing in this note covers turning traffic.

## 1. Lemma RB-0 (gridlock = fixed point)

**Claim.** For both yield rules, these are equivalent: (1) the step fixes s; (2) no car moves;
(3) every car's next cell on its route is occupied.

*Proof.* (3)⇒(2)⇒(1) is immediate. (1)⇒(2): a car that moves leaves a cell that was occupied
at the start of the step, which nobody can enter during it, so the cell changes. (2)⇒(3): if
a car's next cell is empty, either it moves, or it loses a contested merge and the other car
moves. ∎

A **gridlock** is a fixed point with at least one car.

## 2. Theorem RB-G (gridlock needs two cars per block of a winding loop)

**Claim.** A gridlock with exactly n cars exists ⟺ 2·min(W,H) ≤ n ≤ 3WH.

*Proof.* *Lower bound.* In a gridlock map each car to the car in its next cell, which exists
by RB-0. The cars form a finite set, so iterating from any car reaches a cycle of distinct
occupied cells. The cycle alternates shared and private cells. From c(x,y) it reaches
c(x+1,y) through a(x+1,y) if c(x,y) holds an E car, and c(x,y+1) through b(x,y) if it holds an
N car. Let it make α steps of the first kind and β of the second, so that it has 2(α+β) cars
and α+β ≥ 1. It closes on the torus, so W | α and H | β. Hence α ≥ W or β ≥ H.

*Construction.* Let W ≤ H; the other case is the mirror image. Fill row 0 with E cars: all
a(x,0) and c(x,0), which is 2W cars, each blocked by the next. Then add cars in this order,
each blocked by a cell filled earlier:

1. for each column x and y = H−1, …, 1: an N car in b(x,y), blocked by c(x,y+1), then an N car
   in c(x,y), blocked by b(x,y);
2. an N car in each b(x,0), blocked by c(x,1);
3. an E car in each a(x,y) with y ≥ 1, blocked by c(x,y).

The order lists all 3WH cells, and every prefix of length ≥ 2W is a gridlock. ∎

## 3. Lemma RB-R (free flow is a static condition)

A configuration is **free** if every car moves at every step, forever.

**Coordinates.** Give an E car in row y the ring position p ∈ ℤ_{2W}, with a(x,y) ↦ 2x and
c(x,y) ↦ 2x+1. Give an N car in column x the ring position r ∈ ℤ_{2H}, with c(x,y) ↦ 2y and
b(x,y) ↦ 2y+1. Define the **phase classes**

> κ_E = p + 2y mod 2g,  κ_N = r + 2x mod 2g.

They are well defined because 2g divides 2W and 2H.

**Claim.** For both yield rules, a configuration is free ⟺

- (i) no car has a car of its own species in its next cell, and
- (ii) for every E car and every N car, κ_N − κ_E ∉ {0, −1, −2} mod 2g.

*Proof.* The three excluded differences are the three local conflicts at a shared cell c(x,y):

| κ_N − κ_E | E car at | N car at | who is stopped |
|---|---|---|---|
| 0 | a(x,y), class 2x+2y | c(x,y), class 2x+2y | E: its next cell is occupied |
| −1 | a(x,y), class 2x+2y | b(x,y−1), class 2x+2y−1 | the loser of the merge |
| −2 | c(x,y), class 2x+2y+1 | b(x,y−1), class 2x+2y−1 | N: its next cell is occupied |

(⇐) Assume (i) and (ii). Every car moves in the next step: a car's next cell does not hold its
own species by (i), does not hold the other species by rows 0 and −2 of the table, and is not
contested by row −1. After the step every p and r has grown by 1, so (i) holds again, and both
classes have grown by 1, so (ii) holds again. Induction gives freeness.

(⇒) Assume s is free, so at time t the positions are p+t and r+t. (i) holds at time 0. Suppose
an E car in row y and an N car in column x have κ_N − κ_E ≡ −δ with δ ∈ {0,1,2}. Their only
common cell is c(x,y). Take the row of the table for −δ: it asks for a time t with
p + t ≡ p* (mod 2W) and r + t ≡ r* (mod 2H), where (p*, r*) are the listed ring positions.
Such t exists iff p* − p ≡ r* − r (mod 2g), which is the stated class difference. At that time
a car is stopped, a contradiction. ∎

**Consequences.** Freeness is hereditary: removing cars from a free configuration leaves it
free. A free configuration returns to itself after 2·lcm(W,H) steps, so checking that many
steps decides freeness (`is_free`).

## 4. Theorem RB-F (capacity and species frontier)

**Claim.** A free configuration with n_E east and n_N north cars exists ⟺
⌈n_E/m⌉ + ⌈n_N/m⌉ ≤ g, where m = WH/g. This holds for both yield rules.

For S ⊆ ℤ_{2g} let ι(S) be the largest size of a subset of S containing no two elements that
differ by 1. Then ι(ℤ_{2g}) = g, and ι is monotone and translation invariant.

**Lemma A (counting a species).** In a free configuration let A ⊆ ℤ_{2g} be the set of classes
of its E cars. Then n_E ≤ m·ι(A). The same holds for N cars and their class set B.

*Proof.* Fix a row y. Its E cars sit at ring positions with residues in A − 2y mod 2g, no two
of them adjacent in ℤ_{2W}, by (i). If A = ℤ_{2g}, the row has at most W = (W/g)·ι(A) cars.
Otherwise pick u ∉ A − 2y. The W/g positions with residue u hold no E car and cut the ring into
W/g arcs, each mapped bijectively onto ℤ_{2g} ∖ {u}. Two residues in ℤ_{2g} ∖ {u} that differ
by 1 come from adjacent positions of the arc. So the cars of one arc have pairwise
non-adjacent residues in A − 2y, and there are at most ι(A − 2y) = ι(A) of them. Summing over
arcs and over the H rows gives n_E ≤ H·(W/g)·ι(A). ∎

**Lemma B (the species exclude each other).** If A and B are both nonempty, then g ≥ 2 and
ι(A) + ι(B) ≤ g.

*Proof.* By (ii), B is disjoint from A + {0, −1, −2}. For g = 1 that set is all of ℤ_2, so
g ≥ 2. Take I ⊆ A and J ⊆ B of sizes ι(A) and ι(B) without elements differing by 1. Consider
the two-element sets {k−1, k} for k ∈ I and {k′, k′+1} for k′ ∈ J. Two sets of the first kind
meet only if their k differ by at most 1, likewise for the second kind, and {k−1, k} meets
{k′, k′+1} only if k′ ∈ {k−2, k−1, k}. None of these happens. So the ι(A) + ι(B) sets are
pairwise disjoint in ℤ_{2g}, and 2(ι(A) + ι(B)) ≤ 2g. ∎

*Proof of RB-F.* (⇒) Put i = ι(A) and j = ι(B), with ι(∅) = 0. Lemma A gives ⌈n_E/m⌉ ≤ i and
⌈n_N/m⌉ ≤ j. If both species are present, i + j ≤ g by Lemma B. If one is absent, the other
has ι ≤ g.

(⇐) Put i = ⌈n_E/m⌉ and j = ⌈n_N/m⌉, so i + j ≤ g. Place an E car in a(x,y) whenever
(x+y) mod g ∈ [0, i), and an N car in b(x,y) whenever (x+y+1−i) mod g ∈ [0, j). Each diagonal
class has m intersections, so this places m·i and m·j cars. All cars sit in private cells, so
(i) holds. The E classes are the even residues 0, 2, …, 2i−2. If i ≥ 1 the N classes are the
odd residues 2i−1, …, 2i+2j−3, so every difference κ_N − κ_E lies in [1, 2g−3] and avoids
0, −1, −2 mod 2g. If i = 0 there is nothing to check. By RB-R the configuration is free, and
by heredity so is any sub-configuration with exactly n_E and n_N cars. ∎

**Corollary RB-C (capacity).** The largest free population is WH for every W and H. It is
reached with both species present iff g ≥ 2. For g = 1 no free configuration has both species.
The maximal species pairs are (m·i, m·(g−i)) for i = 0, …, g.

**Corollary RB-P (capacity states pulse).** Let s be free with WH cars. Then every shared cell
is occupied at exactly every second step. If both species are present, all shared cells are
occupied at the same steps: at alternate steps every roundabout holds a car in its shared
quadrant and all 2WH private cells are empty.

*Proof.* A cell occupied at times t and t+1 holds the same car at both times, by the vacancy
rule. In a free configuration every car moves, so no cell is occupied at two consecutive
times. Over one period P = 2·lcm(W,H) a shared cell is thus occupied at most P/2 times, while
each car spends exactly P/2 steps in shared cells. With WH cars and WH shared cells, each
shared cell is occupied exactly P/2 times, hence at alternate steps. An E car is in c(x,y) and
c(x+1,y) two steps apart, so the parity is constant along a row holding an E car, and likewise
along a column holding an N car. Every shared cell is visited, so each one lies in such a row
or such a column. If both species are present, this forces every row to hold an E car or
every column to hold an N car. In the first case one column with an N car meets every row,
and symmetrically in the second, so the parity is global. ∎

The same count proves n ≤ WH directly, without the classes. In single-species capacity states
each street keeps its own parity, so the second statement needs both species.

## 5. Signals against roundabouts

Take one tick to be a BML half-step or a roundabout step. A free car then covers one block in
two ticks in both models. In both, a cell vacated during a tick cannot be entered during that
tick. A roundabout car can leave a cell one tick after entering it, so a cell releases at most
one car per two ticks. A BML car must hold its cell through the other species' phase, so it
stays two ticks and a cell releases at most one car per three ticks.

| | BML, CLASSIC | roundabout BML |
|---|---|---|
| cells per intersection | 1 | 3 |
| control | E phase, N phase | none; yield at the merge |
| gridlock with n cars exists | min(W,H) ≤ n ≤ WH (G1) | 2·min(W,H) ≤ n ≤ 3WH (RB-G) |
| free-flow capacity, cars per intersection | ⌊2g/3⌋/g for g ≥ 2 (F) | 1 (RB-C) |
| both species free together | g ≥ 3 | g ≥ 2 |
| ceiling on crossings per intersection per tick | 1/3 | 1/2 |
| ceiling reached in free flow | iff 3 divides g | for every W and H |
| free-flow capacity, cars per cell | ≤ 2/3 | 1/3 |

So the roundabout city carries 3/2 times the best free BML flow per intersection, and it does
so on every torus, where BML needs 3 | g. The price is storage: it has three times the cells
and fills a third of them.

## 6. Evidence and scope

`free_levels` enumerates every free configuration of a board from the dynamics: it grows
free configurations one car at a time, which is complete by heredity, and decides freeness by
simulating one period. `scripts/check_roundabout.py` compares the result with RB-R, RB-F, RB-C
and RB-P for both yield rules:

| W×H | g | free configurations | at capacity | of those mixed | maximal (n_E, n_N) |
|---|---|---|---|---|---|
| 2×2 | 2 | 133 | 12 | 4 | (0,4) (2,2) (4,0) |
| 3×2 | 1 | 666 | 12 | 0 | (0,6) (6,0) |
| 4×2 | 2 | 5,509 | 24 | 4 | (0,8) (4,4) (8,0) |
| 3×3 | 3 | 22,061 | 28 | 12 | (0,9) (3,6) (6,3) (9,0) |
| 5×2 | 1 | 31,935 | 36 | 0 | (0,10) (10,0) |
| 4×3 | 1 | 208,798 | 24 | 0 | (0,12) (12,0) |
| 6×2 | 2 | 237,208 | 72 | 4 | (0,12) (6,6) (12,0) |

The tests also run all 12^{WH} configurations of every board with WH ≤ 5: the static criterion
agrees with simulated freeness, the realised species pairs are exactly those of RB-F, and the
gridlock populations are exactly the interval of RB-G. The construction of RB-F is replayed
on every board up to 6×6 and that of RB-G up to 8×8.

These are finite checks of the universal proofs above, and they prove nothing beyond their
domains. The largest searched g is 3.

**Not addressed.** Whether a random configuration below capacity reaches free flow, and at
what density the roundabout city gridlocks, are open here exactly as for BML. Links of
positive length, longer rings and turning traffic change the model. No Lean formalization exists yet.

**Related work.** [Fouladvand–Sadjadi–Shaebani][FSS] simulate a single yield-at-entry
roundabout as a stochastic cellular automaton and compare its delay with signal control.
[Gershenson–Rosenblueth][GR] discuss roundabouts as a substitute for traffic lights in a
cellular-automaton city. A search found no exact capacity result for a BML lattice of
roundabouts; that is not a novelty claim.

[FSS]: https://arxiv.org/abs/cond-mat/0309560
[GR]: https://arxiv.org/abs/0907.1925
