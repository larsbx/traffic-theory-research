# Blueprint: proof status and open formal obligations

This hand-off document records the completed B0–B7 proofs and the remaining
obligations of [the coverage register](README.md), with proofs decomposed into
lemmas small enough to formalise one at a time.

- Each lemma lists the existing results it rests on, so a prover can work
  bottom-up. Lean signatures target the `BML` kernel in this package (`Kernel`,
  `Torus`, `Transport`, `Counting`, `Enumeration`). `carCount` is the actual
  occupied-position count, proved equal to the executable species-count sum.
- G1's exact-count construction is complete in `AllCounts.lean` and
  `Gridlock.lean`. B0 is complete in `Ring.lean`; B1 uses `Lanes.lean`,
  `NonGridlock.lean`, and the prefix-rank counting theorem in `Enumeration.lean`.
  `GridlockThresholds.lean` proves the forced-gridlock boundary among feasible
  populations. B2 is complete in `Congruence.lean`, `Cosets.lean`, and
  `CosetTimes.lean`. B3 is complete in `Rigid.lean`, `Encounters.lean`,
  `FreeFlowConditions.lean`, `FreeFlowNecessity.lean`, and `FreeFlow.lean`.
  B4 is complete in `PhaseCounts.lean`, `FreePacking.lean`, `FreePureBound.lean`,
  `FreePattern.lean`, `FreeConstruction.lean`, `FreeDeletion.lean`, and
  `FreeMaximum.lean`, with finite-sum helpers in `FiniteSums.lean`.
  B5 and B6 are complete in the separate TRAIN library linked below.
  B7 is complete in `SparseDynamics.lean` and `SparseSpeed.lean`.

Conventions: `E = eastDirection w h hw` and `N = northDirection w h hh`.
`f = torusStep w h hw hh = step E N`, and `f^t = iterate f t`.

| Id | Obligation | Status of the mathematics | Depends on |
|---|---|---|---|
| B0 | Ring arithmetic helpers | kernel-checked in `Ring.lean`, including bounded reachability | `Torus` |
| B1 | G2: no forced gridlock below full occupancy | kernel-checked exact-count construction and all-time non-jamming; forced boundary proved for n≤WH | B0, `Kernel`, `Enumeration`, `Lanes` |
| B2 | Coset identity ⟨(1,−1)⟩ = ker φ | kernel-checked signed action, arbitrary-point fibers, east-translated coset, bounded/positive witnesses, and exact lcm period | B0, `Congruence`, actual cyclic coordinates |
| B3 | Lemma R: static ⟺ perpetual free flow | kernel-checked for the actual phases, with strict/inclusive lcm windows, bounded failure witnesses, and lcm return | B0, B2, Kernel |
| B4 | Theorem F: densest free flow | kernel-checked exact capacity, all-count constructions, static/perpetual/eventual existence spectra, and square corollaries | B2, B3, Counting |
| B5 | Theorem T: TRAIN jam populations W+H…WH | kernel-checked in full; see [TRAIN coverage](TRAIN.md) | `BML.Train` kernel and counting |
| B6 | TRAIN eventual speed one on sparse N×N squares | kernel-checked in full; see [TRAIN coverage](TRAIN.md) | `Train/Diagonals`, `Train/FreeFlow`, actual diagonal transport/release |
| B7 | CLASSIC eventual speed one for 2m<gcd(W,H) | kernel-checked full movement from round lcm(W,H)·m(g−2) onward and at most m(g−2) blocked rounds per prefix | B2 geometry, B3 finite free window, CLASSIC transport and car count |

---

## B0. Ring arithmetic helpers: completed

[`BML/Ring.lean`](lean/BML/Ring.lean) proves these statements for the actual
cyclic coordinates used by the CLASSIC kernel:

```lean
theorem cyclicNext_val (n : Nat) (hn : 0 < n) (i : Fin n) :
    (cyclicNext n hn i).val = (i.val + 1) % n

theorem iterate_cyclicNext_val (n : Nat) (hn : 0 < n) (k : Nat) (i : Fin n) :
    (iterate (cyclicNext n hn) k i).val = (i.val + k) % n

theorem cyclicNext_reaches_lt (n : Nat) (hn : 0 < n) (i j : Fin n) :
    ∃ k, k < n ∧ iterate (cyclicNext n hn) k i = j
```

*Proof.*

- First lemma: case `i.val + 1 < n` (then `Nat.mod_eq_of_lt`), else
  `i.val + 1 = n` (then `Nat.mod_self`).
- Second lemma: induction on `k`, using `Nat.mod_add_mod`.

**Reachability.** The compiled proof takes `k = j.val - i.val` when `i.val ≤ j.val`,
and `k = n + j.val - i.val` otherwise. The modular formula, `Fin.ext`, and the
coordinate bounds prove that k<n and the target is j. `cyclicNext_reaches`
forgets the bound; `iterate_cyclicNext_period` proves return after n steps,
including singleton rings.

---

## B1. G2: completed for every 0 ≤ n < WH

[`BML/NonGridlock.lean`](lean/BML/NonGridlock.lean) proves the following theorem
for every positive rectangle. E, N, and f abbreviate the actual directions and
step function as above.

```lean
theorem exists_never_jam_with_count (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (n : Nat) (hn : n < w * h) :
    ∃ s : Config (Position w h), carCount w h s = n ∧
      ∀ t, ¬ Jam E N (iterate f t s)
```

For `n = 0`, use the empty state with `empty_not_jam` and `empty_fixed`. Below, assume
`n ≥ 1`, so `w * h ≥ 2`.

**Case w ≥ 2 (east cars only).** Fill in column-major order:
`s (x, y) = .east ↔ x.val * h + y.val < n`.

**Lemma B1.1 (a mixed row exists).** Let y₀ = 0 if n ≤ (w−1)·h, else y₀ = h−1. Row y₀ holds
an east car at x = 0 and an empty cell at x = w−1.

- If n ≤ (w−1)·h: the car is at index 0 < n, and the hole is at index (w−1)·h ≥ n.
- Otherwise the car is at index h−1 < h ≤ (w−1)·h < n, and the hole is at index w·h−1 ≥ n.

`eastColumnPrefix_mixed_row` establishes the product bounds and closes the
index inequalities with `omega`.

**Count.** `k ↦ (k / h, k % h)` is a bijection from `{k < n}` onto the east cells, so
`carCount = n`. `eastColumnPrefix_carCount` applies `carCount_of_rank` from
`Enumeration.lean` with this column-major rank bijection and its inverse.

**Invariant.** `I y₀ s := (∀ p, s p ≠ .north) ∧ (∃ x, s (x, y₀) = .east) ∧ (∃ x, s (x, y₀) = .empty)`.

**Lemma B1.2 (the north phase is the identity without north cars).**
`(∀ p, s p ≠ .north) → halfStep N .north s = s`. Proof: `halfStep_eq_of_blocked`, since
`Blocked` holds vacuously.

**Lemma B1.3 (the east phase creates no north car).** This is `other_species_unchanged`
with `c = .north`.

**Lemma B1.4 (a row's car persists).** If `s (x, y₀) = .east`, then some x′ has
`halfStep E .east s (x′, y₀) = .east`.

- If the car moves: `moving_destination_filled`, with x′ = `cyclicNext x`. The east
  neighbour keeps y.
- If it does not move: unfold `halfStep` at `(x, y₀)`; the car stays.

**Lemma B1.5 (a row's hole persists).** If `s (x, y₀) = .empty`, then some x′ has
`halfStep E .east s (x′, y₀) = .empty`.

- If `s (E.prev (x, y₀)) = .east`, that car can move, since its east cell is `(x, y₀)`,
  which is empty. By `moving_source_emptied` its source `E.prev (x, y₀)`, still in row y₀,
  becomes empty.
- Otherwise nothing enters `(x, y₀)`; unfold `halfStep` there.

Under CLASSIC semantics a vacated source cannot be refilled in the same phase: its west
neighbour saw it occupied. That is exactly why `moving_source_emptied` holds.

**Lemma B1.6 (a mixed ring has a mover).** If row y₀ has an east car at x₀ and an empty cell
at x₁, then some p in row y₀ has `CanMove E .east s p`.

- Let `cᵢ = (iterate (cyclicNext w hw) i x₀, y₀)`.
- Prove by induction on i: `s cᵢ = .empty → ∃ p, CanMove E .east s p`.
  - i = 0 is impossible, because c₀ is the car.
  - At i+1: if `s cᵢ = .empty`, use the induction hypothesis. Otherwise `s cᵢ ≠ .empty`,
    and since there are no north cars, `s cᵢ = .east`. Its east cell is `cᵢ₊₁`, which is
    empty, so `cᵢ` can move.
- Apply this at the i with `cᵢ = (x₁, y₀)`, which exists by B0 reachability. No `Nat.find`
  is needed.

**Assembly.**

1. `I y₀ s → I y₀ (f s)`: combine B1.2–B1.5. The north phase acts on a state with no
   north cars (B1.3), so it is the identity (B1.2).
2. `I y₀ s → ¬ Frozen E N s`: B1.6 gives a mover, which contradicts `Blocked E .east s`.
3. Hence `∀ t, ¬ Jam E N (f^t s)`, by induction on t and `Jam → Frozen`.

**Case w = 1 (then h ≥ 2).** Mirror the argument: north cars only, and columns in place of
rows. The east phase is the identity (B1.2 with species swapped), and B1.4–B1.6 run along
`N`. Alternatively, fill `s (x, y) = .north ↔ y.val < n` and work in column x = 0, which
holds n ≥ 1 cars and h − n ≥ 1 holes.

**Compiled declarations.** `Lanes.lean` defines `EastMixedRow` and
`NorthMixedColumn`. `halfStep_eq_of_absent_species` proves B1.2;
`EastMixedRow.halfStep` combines B1.3–B1.5; `EastMixedRow.has_mover` proves
B1.6 from B0 reachability. The `.step`, `.iterate`, and `.never_jam` theorems
assemble the invariant, with dual declarations for a north-only column.
`nonGridlockWith` selects the appropriate prefix, `nonGridlockWith_carCount`
proves its count, and `nonGridlockWith_never_jam` proves the all-time conclusion.

The empty configuration is frozen but is not `Jam`, which requires a car.
This is why the theorem says **never jammed**, rather than never frozen.
The 1×1 torus has just the sub-full case n=0; its n=1 configurations are already
CLASSIC jams. Positive constructions retain an eligible mover but need not
have every car moving, so neither speed one nor eventual free flow is claimed.

**Forced-gridlock corollary.** `GridlockThresholds.lean` proves
`carCount_eq_area_iff`, `full_carCount_is_jam`, and
`forced_eventual_jam_iff`: for positive w,h and `n ≤ w*h`, every n-car
configuration eventually reaches a nonempty jam if and only if `n = w*h`.
Full occupancy jams at time zero; G2 supplies a counterexample at every
smaller count. The feasibility assumption excludes the vacuous universal
statement at n>w*h.

---

## B2. Coset identity: completed

Let g = gcd w h. In ℤ_w × ℤ_h, the subgroup ⟨(1, −1)⟩ is the kernel of
(x, y) ↦ x + y mod g. Stated on representatives, for `a < w` and `b < h`:

```lean
theorem coset_iff (w h a b : Nat) (hw : 0 < w) (hh : 0 < h) (ha : a < w) (hb : b < h) :
    (a + b) % Nat.gcd w h = 0 ↔
      ∃ t : Int, t % (w : Int) = (a : Int) ∧ ((b : Int) + t) % (h : Int) = 0
```

This is the compiled `BML.coset_iff` in
[`Congruence.lean`](lean/BML/Congruence.lean). `coset_dvd_iff` first proves the
signed divisibility criterion, and `coset_int_iff` expresses it with integer
remainders for arbitrary signed coordinate differences. No coprimality or
supplied Bézout coefficients are assumed.

Read it as: (a, b) = (t mod w, −t mod h) for some t ∈ ℤ.

The bound `ha : a < w` is necessary: `t % w` is always below w. Without it, w = h = 2, a = 2,
b = 0 makes the left side true and the right side false. `hb` is not needed for the
equivalence, but it keeps (a, b) a representative pair as B3 uses it.

**Lemma B2.1 (Bézout).** `∃ x y : Int, x * m + y * n = Nat.gcd m n`.

`nat_gcd_bezout` uses `Nat.gcd.induction` with the predicate
P m n := ∃ x y, x*m + y*n = gcd m n.

- Base `P 0 n`: take x = 0, y = 1, since gcd 0 n = n.
- Step: assume 0 < m and `P (n % m) m`, so x′·(n % m) + y′·m = gcd (n % m) m = gcd m n.
- Substitute n % m = n − m·(n / m); the compiled proof casts `Nat.mod_add_div` into Int.
- This gives (y′ − x′·(n/m))·m + x′·n = gcd m n.

**(→)** Write a + b = g·k. Take x, y from B2.1 for (w, h); then x·k·w + y·k·h = a + b.
Put t := a − x·k·w.

- Then t ≡ a (mod w), so `t % w = a % w = a`, using `a < w` and `Int.emod_emod_of_dvd`
  or `Int.add_mul_emod_self`.
- And b + t = y·k·h, which is ≡ 0 (mod h).

**(←)** g divides both w and h. Reducing `t % w = a` mod g gives t ≡ a (mod g), and reducing
`(b + t) % h = 0` gives b + t ≡ 0 (mod g). So a + b ≡ 0 (mod g). Use `Int.emod_emod_of_dvd`
twice, then cast back to `Nat`.

**Corollary B2.2.** The coset (1, 0) + ⟨(1, −1)⟩ is {(a, b) : (a + b) % g = 1 % g}.
The compiled `phaseClass_east` gives the actual east neighbor's class as
`(phaseClass p + 1) % gcd w h`. `east_diagonalShift_exists_iff` identifies its
signed orbit with precisely that next class, covering g=1 and singleton axes.

**Corollary B2.3 (non-negative time).** If t ∈ ℤ witnesses `coset_iff`, so does
t + k·lcm(w, h) for any integer k. `diagonalShift_emod_lcm` proves that reduction
modulo lcm preserves the actual signed action. Writing L = lcm(w,h), the
compiled `diagonalStep_reaches_lt_iff` and `diagonalStep_reaches_pos_iff` give
equivalent witnesses in `[0,L)` and `[1,L]`, respectively.
`east_diagonalStep_reaches_lt_iff` and `east_diagonalStep_reaches_pos_iff`
give the same two windows for the translated class-one relation.

**Bridge to actual coordinates.** [`Cosets.lean`](lean/BML/Cosets.lean) defines
`diagonalStep p = (cyclicNext w hw p.1, cyclicPrev h hh p.2)` and the signed
action `diagonalShift`. Its action laws and `iterate_diagonalStep` connect the
integer congruences to actual iteration, rather than to a separately assumed
coordinate-motion model. For arbitrary p,q,

```lean
theorem diagonalShift_exists_iff (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (p q : Position w h) :
    (∃ t : Int, diagonalShift w h hw hh t p = q) ↔
      phaseClass w h p = phaseClass w h q
```

`diagonal_kernel_iff` specializes this to the origin and zero class.
[`CosetTimes.lean`](lean/BML/CosetTimes.lean) proves return after L steps and
the stronger `iterate_diagonalStep_eq_self_iff`: a natural time returns to its
start exactly when L divides it. Thus the least positive return time is L.
These are statements about positions, with no configuration or free-flow
assumption. They supply the class-zero and class-one encounter geometry and
time windows used by the compiled traffic-dynamics proof in B3.

**Finite implementation gate.** `CosetExport.lean` emits the actual diagonal
successor, phase class, and east translate at every coordinate. The checker
`scripts/check_cosets.py` reconstructs each complete cycle, compares an
independent modular oracle, and checks both ordered-pair relations. Its default
domain W,H≤12 contains 144 rectangles, 6,084 positions, 283,526 orbit visits,
and 422,500 ordered pairs per relation, with 12 required rejection controls.
These totals describe finite coordinate checks; successful acceptance is
recorded in a source-bound receipt. B3 has its own traffic proof and finite
acceptance gate; the packing proof and constructions are completed separately in B4.

---

## B3. Lemma R: free-flow rigidity

**Status: completed for the actual CLASSIC kernel.**

Let g = gcd(w,h), L = lcm(w,h), and φ(p) = `phaseClass w h p`.
[`FreeFlowConditions.lean`](lean/BML/FreeFlowConditions.lean) states the
phase exclusions directly on canonical residues, including g=1:

```lean
def StaticFree (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) : Prop :=
  (∀ p, s p = .east → s ((eastDirection w h hw).next p) ≠ .east) ∧
  (∀ p, s p = .north → s ((northDirection w h hh).next p) ≠ .north) ∧
  (∀ e q, s e = .east → s q = .north →
    phaseClass w h q ≠ phaseClass w h e ∧
    phaseClass w h q ≠ (phaseClass w h e + 1) % Nat.gcd w h)
```

[`Rigid.lean`](lean/BML/Rigid.lean) uses the actual intermediate board for
north eligibility. This definition and its rigid-motion lemmas are generic
over invertible directions:

```lean
def AllMove (east north : Direction α) (s : Config α) : Prop :=
  (∀ p, s p = .east → CanMove east .east s p) ∧
  (∀ p, halfStep east .east s p = .north →
    CanMove north .north (halfStep east .east s) p)
```

Using the E, N, and f conventions above, the compiled public theorems in
[`FreeFlow.lean`](lean/BML/FreeFlow.lean) have these statements:

```lean
theorem lemmaR (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) :
    StaticFree w h hw hh s ↔ ∀ t, AllMove E N (iterate f t s)

theorem lemmaR_finite_lt (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) :
    (∀ t, AllMove E N (iterate f t s)) ↔
      (∀ t, t < Nat.lcm w h → AllMove E N (iterate f t s))

theorem lemmaR_finite (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) :
    (∀ t, AllMove E N (iterate f t s)) ↔
      (∀ t, t ≤ Nat.lcm w h → AllMove E N (iterate f t s))
```

**B3.1: rigid half-step and orbit.** `halfStep_rigid` proves that if every
sp-car can move, then
`halfStep d sp s p = sp.cell ↔ s (d.prev p) = sp.cell`.
The forward implication splits the outgoing and incoming cases of the
actual half-step; the reverse implication uses `moving_destination_filled`.
`other_species_unchanged` handles the inactive species. This gives
`allMove_step_east_iff` and `allMove_step_north_iff` for the full round.

Induction proves `allMove_iterate_east_iff` and
`allMove_iterate_north_iff`: if all rounds u<t moved fully, occupancy at p
at time t is precisely initial occupancy at `iterate E.prev t p` or
`iterate N.prev t p`. The corresponding `allMove_iterate_east_at` and
`allMove_iterate_north_at` state the same equivalences at forward-translated
positions. No assumption of future movement is used.

**B3.2: sufficiency and invariance.** `staticFree_allMove` first establishes
east eligibility. A same-species east blocker violates adjacency; a north
blocker lies in the forbidden next phase class. After the east phase,
north cars remain at their initial cells. A north blocker violates adjacency;
an east blocker at a north target has a rigid predecessor in the forbidden
equal phase class. Thus north eligibility is checked on the actual
intermediate configuration.

`staticFree_step` then preserves all three static conditions. The one-round
rigid equivalences pull same-species adjacency back to s. Both species'
phase classes increase by one modulo g, whose cyclic successor is injective,
so the two phase exclusions persist. Ordinary induction gives
`staticFree_iterate` and `staticFree_perpetual_allMove`.

**B3.3: necessity from the first L rounds.**
[`FreeFlowNecessity.lean`](lean/BML/FreeFlowNecessity.lean) proves
`staticFree_of_allMove_before_lcm` from `∀ t<L, AllMove E N (f^t s)`.

- A same-species adjacency contradicts movement at t=0. For north cars,
  `other_species_unchanged` carries the adjacency through the east phase.
- A forbidden next-class east/north pair has an encounter at some t<L,
  by `next_phase_encounter_lt_iff` in
  [`Encounters.lean`](lean/BML/Encounters.lean). The rigid prefix places the
  north car in the east car's target at time t, contradicting east movement.
- An equal-class pair has a meeting time 1≤t≤L, by
  `same_phase_encounter_pos_iff`. Every round u<t is in the assumed window,
  so rigid prefix motion would put an east and a north car in the same cell
  at full time t. A configuration assigns one cell value, giving a
  contradiction. No movement at time L is needed.

This proves the reverse direction of R and the sharper half-open window
`lemmaR_finite_lt`. The inclusive `lemmaR_finite` follows immediately.
`lemmaR_window` relates the static predicate directly to the strict window;
`not_staticFree_iff_blocked_before_lcm` gives an equivalent blocked-round
witness at some t<L whenever a static condition fails.

**B3.4: return and eventual entry.** `iterate_east_lcm` and
`iterate_north_lcm` return each coordinate to its start. The rigid orbit
therefore gives `freeFlow_returns_lcm`, namely `f^L s = s` for static-free s,
and `freeFlow_periodic` gives `f^(t+L) s = f^t s` at every time. This is a
period of the configuration, not necessarily its least positive period.

`eventually_allMove_iff_reaches_staticFree` proves that eventual permanent
full movement is equivalent to reaching a static-free configuration. It
does not assert that every orbit reaches one or bound the entry time.
All B3 statements cover empty boards and every positive rectangle, including
singleton dimensions. They use the CLASSIC phases; no TRAIN speed-one
transfer or packing theorem follows without its separate argument.

**Finite implementation gate.** `FreeFlowExport.lean` evaluates the actual
`StaticFree` and `AllMove` propositions and exports both phase traces over
the first L rounds. `scripts/check_freeflow.py` declares the exhaustive
WH≤9 domain: 93,387 initial states on 23 ordered positive rectangles and
622,362 full transitions. It compares the phase states and movement counts
with NumPy, and compares perpetual movement from time zero with independent
scalar orbit following. Rigid prefixes, lcm closure of static-free states,
complete coverage, and corrupted-output rejection controls are checked
separately. These finite checks supplement the general proof; source-bound
receipts identify the successful runs.

---

## B4. Theorem F: densest free flow

Let g=gcd(w,h), M=w·h/g, and V(g)=⌊2g/3⌋. `BML/FreeMaximum.lean`
defines the exact capacity:

```lean
def freeMax (w h : Nat) : Nat :=
  if Nat.gcd w h = 1 then max (h * (w / 2)) (w * (h / 2))
  else (w * h / Nat.gcd w h) * ((2 * Nat.gcd w h) / 3)
```

For every positive rectangle, the compiled declarations are:

| Declaration | Statement |
|---|---|
| `staticFree_carCount_le_freeMax` | Every actual StaticFree configuration has at most freeMax cars. |
| `maxFreeConfig_staticFree`, `maxFreeConfig_carCount_eq_freeMax` | An executable maximum board is free and has exactly the capacity. |
| `freeWith_staticFree`, `freeWith_carCount_of_le` | The executable constructor is free and has exactly n cars whenever n≤freeMax. |
| `exists_staticFree_with_count_iff` | A static-free board of count n exists iff n≤freeMax. |
| `exists_perpetual_allMove_with_count_iff` | The same interval characterizes perpetual full movement from time zero. |
| `exists_eventual_allMove_with_count_iff` | The same interval characterizes existence allowing an initial transient. |
| `above_freeMax_never_staticFree` | Above capacity, no iterate can satisfy StaticFree. |
| `freeMax_square`, `freeMax_square_attains_two_thirds_iff` | Square capacity is L⌊2L/3⌋; density two thirds is attained iff 3∣L. |

### Upper bound

`PhaseCounts.lean` first proves that every phase fiber has exactly M cells.
East shift bijects consecutive fibers, cyclic reachability makes their sizes
equal, and the partition of all WH positions determines the common size.
Let aᵢ and bᵢ be the actual east and north populations of class i, and cᵢ=aᵢ+bᵢ.
The same-species adjacency rules and the actual shifts give

```text
cᵢ ≤ M,   aᵢ + aᵢ₊₁ ≤ M,   bᵢ + bᵢ₊₁ ≤ M.
```

For example, translate the east cars in class i into class i+1. Their targets
are distinct and disjoint from its existing east cars. The two cross-species
rules give aᵢ=0 or bᵢ=0, and aᵢ=0 or bᵢ₊₁=0.

`FreePacking.lean` proves the abstract weighted bound when g≥2:

1. **Triple cap.** These five relations imply cᵢ+cᵢ₊₁+cᵢ₊₂≤2M.
   If aᵢ>0, the first two north counts vanish, so use the east-pair cap and
   the third total cap. If aᵢ=aᵢ₊₁=0, use the north-pair cap and the third
   total cap. Otherwise aᵢ=0<aᵢ₊₁, the latter two north counts vanish,
   and the east-pair cap on those classes plus bᵢ≤M suffices.
2. **An empty class.** Rotate it to the last position. For g=3q+r,
   group the first 3q entries into triples. The remainder contributes zero
   when r=0 or 1, and at most M when r=2. Thus the total is at most M⌊2g/3⌋.
3. **No empty class.** Any positive east count forces a positive east count
   in the next class, so cyclic propagation forces one species throughout.
   Summing the adjacent-pair caps yields 2n≤gM. Since g≤2⌊2g/3⌋ for g≥2,
   the same bound follows.

For g=1, the sole phase class forbids mixed species. `FreePureBound.lean`
uses adjacent-pair double counting in each actual row or column to obtain
max(h⌊w/2⌋,w⌊h/2⌋). A singleton lane has capacity zero because its site
is its own successor. `FreeMaximum.lean` combines the two branches with the
proved partition of the actual `carCount`.

### Constructions and exact population spectrum

`FreePattern.lean` builds a cyclic word from `N E ·` triples and `E ·` pairs:

| g | Pattern |
|---|---|
| 3q | q triples |
| 3q+2 | q triples and one pair |
| 3q+1≥4 | q−1 triples and two pairs |

A finite bijection proves the exact occupied-class count ⌊2g/3⌋. Every E class
is followed by an empty class, and every N class by an E class, including the
cyclic seam. `FreeConstruction.lean` fills these classes and uses the proved
fiber size for the exact count. For g=1 it chooses the larger alternating
pure-species construction, omitting an unpaired final coordinate on odd lanes.

`FreeDeletion.lean` proves that arbitrary species-preserving deletion keeps all
static conditions. Its executable `thinConfig` retains the first n occupied
positions, with exact count min(n, original count). This completes every
population from zero through the maximum.

Lemma R supplies the dynamic from-time-zero statement. For eventual free flow,
necessity uses actual car-count conservation at entry into StaticFree, while
sufficiency takes a constructed board with transient zero. None of these
existence results says every board below capacity eventually flows freely.

### Finite implementation evidence

`scripts/check_free_max.py` evaluates the actual Lean constructor at every
attainable count on all 144 rectangles with sides 1…12: 3,334 configurations
and 146,348 full transitions through complete lcm windows. It independently
checks the formula, exact counts, static constraints, both phase states and
move counts, closure, domain completeness, and rejection controls. These finite
checks accompany the universal proof. The independent max-plus DP in
`bml.freeflow_dp` continues to agree on 3×3, 4×4, 3×6, 5×5, 6×6 and 8×4.

---

## B5. Theorem T: completed TRAIN formalization

This obligation is now discharged by the executable `BML.Train` library.
[`Train/Kernel.lean`](lean/Train/Kernel.lean) defines actual snapshot queue movement
and full-ring rotation. It proves that its bounded scan equals a propagated
movement mask together with full rings, and that stopped cars have opposite
blockers. An unchanged occupancy pattern is not sufficient for TRAIN gridlock.

[`Train/Threshold.lean`](lean/Train/Threshold.lean) proves
`BML.Train.noMoves_population_iff`: for all positive w,h and natural n, a nonempty
configuration with zero movers in both successive TRAIN phases and population n
exists if and only if w+h≤n≤w*h. `jam_rows_columns` and `jam_population_lower`
formalize the east-per-column/north-per-row proof outlined here. Disjoint witness
lists supply the numerical lower bound. Singleton dimensions have no such jam.

The proof supplies every population in the interval. The executable
`stuckConfig w h k` uses a core with word E^(w−1) N^(h−1) E N and a prefix of
interior north cars, counted by an explicit duplicate-free listing.
`stuckConfig_jam` proves actual TRAIN blockage and `stuckConfig_population`
proves population w+h+k. Python's `train_stuck_with` uses the same closed form.

Numeric species and population conservation, movement-based jam equivalence,
and persistence are also proved. `TrainAudit.lean` audits the compiled library
and exporter. The actual Lean, Quint, and Python evaluators are compared on
explicit finite domains by `scripts/check_train.py`; this finite replay is
separate from the universal Lean theorem. See [TRAIN.md](TRAIN.md) for the
complete statements, construction, commands, and evidence boundaries.

---

## B6. Completed TRAIN speed-one proof on sparse squares

This obligation is discharged by the compiled `Train/SpeedOne.lean` theorem,
including the pure cyclic proof, actual diagonal-dynamics bridge, and numerical
full-speed characterization.

The result is [Austin–Benjamini Proposition 1, v3](https://arxiv.org/pdf/math/0607759v3)
for the actual TRAIN rule: for N>0 and any N×N configuration s,

\[
2\operatorname{population}(s)<N
\;\Longrightarrow\;
\exists T\;\forall t\ge T:\;
\operatorname{totalMoveCount}(\operatorname{torusStep}^{t}(s))
=\operatorname{population}(s).
\]

The public theorems are `sparse_square_eventually_fullSpeed` and
`sparse_square_moves_equal_population`, both in `BML.Train`. The empty board
is included. The condition is strict and requires no species balance.

The existing compiled pieces are:

- `Train/FreeFlow.lean`: movement counts are bounded by population, and equality
  means every car moves in its own phase. Conservation rewrites eventual full
  movement as equality with the initial population.
- `Train/Diagonals.lean`: `sparse_eventual_stable` accepts a finite list of labels
  and corrected cyclic traces. Each trace stays or moves one predecessor step;
  an occupied class followed by an empty one must retain some occupant.
  Under `2 * labels.length < N`, it proves a common time after which every
  trace stays fixed. The empty list is permitted.

`Train/DiagonalDynamics.lean` discharges those hypotheses for the actual kernel.
Initial labels are `occupiedPositions s`. A full-cycle transport follows each
car and covers every current car. The corrected tag is `x+y−t mod N`; it is
stable for a moving car and decreases for a blocked one. Release follows by
considering whether the occupied diagonal contains an east car before the
east phase. The numeric wrapper then converts stable traces into full movement.

The cyclic proof uses adjacent empty pairs. Sparse occupancy guarantees a pair
at each time; one-step transport and release imply that every pair at t+1 was
already empty at t. A finite descending-family argument yields a permanent
pair. Cutting the cycle at a permanent vacancy makes each blocked event
decrease a natural-number rank. Attained minima and a finite maximum of
individual eventual times give simultaneous eventual stability. No eventual
periodicity or bounded test result is assumed.

This proves the result for squares only and supplies no effective stabilization-time bound.
The CLASSIC rectangular proof is in B7 below. TRAIN finite acceptance covers all
1,305 sparse square states through N=5 and checks full actual movement on
every terminal-cycle edge. Eight targeted orbit certificates add 53 transition
rows; ten new Quint tests and six controls check the clock, counts, recurrence,
enumeration, and square scope. See [TRAIN.md](TRAIN.md) for exact domains,
commands, and source-bound acceptance status.

---

## B7. CLASSIC low-density speed one

**Status: kernel-checked for every positive rectangle.**

For `g = gcd(W,H)` and `m = carCount`, the strict hypothesis is `2m < g`.
The proofs use the CLASSIC transport and counting kernel. Austin–Benjamini’s
corrected-diagonal argument for the TRAIN rule motivates the construction.
The correction subtracts the number of completed rounds from the diagonal
class modulo `g`.

| Part | Lean declarations | Argument |
| --- | --- | --- |
| B7.0 | `phaseIndex_east`, `phaseIndex_north`, `correctedClass_roundTransport` | Either coordinate step advances the phase by one modulo `g`. A moving tag keeps its corrected class. A blocked tag takes one cyclic predecessor step. |
| B7.1 | `corrected_release` | An east car can enter a vacant next class. When the occupied class has only north cars, their north targets have no east predecessor that can fill them during the first phase. |
| B7.2 | `corrected_survival` | Every car survives via `roundTransport_preserves_car`. Its corrected class stays or moves to its predecessor. |
| B7.3 | `corrected_emptyPair_backwards`, `corrected_emptyPair_before` | Survival excludes a predecessor-time occupant of the second class. Release then excludes one in the first class. Induction gives the same pair throughout a finite prefix. |
| B7.4 | `corrected_emptyPair_of_sparse` | Without an empty pair, the occupied list and its cyclic predecessors would cover all `g` classes with at most `2m` entries. Conservation applies the argument at each time. |
| B7.5 | `low_density_tag_block_bound` | Cut at the first class of an empty pair at time `T`. An original car's rotated class stays between 1 and `g−1` through `T`. Its distance drops by one for each blocked round, so its block count is at most `g−2`. |

[BML/SparseDynamics.lean](lean/BML/SparseDynamics.lean) proves the class and
empty-pair lemmas. [BML/SparseSpeed.lean](lean/BML/SparseSpeed.lean) sums the
per-tag bounds using the initial species counts. Trace surjectivity gives a
blocked original tag whenever `AllMove` fails. The theorem
`low_density_block_bound` bounds the number of such rounds in each prefix
`[0,T)` by `m(g−2)`. The prefix count is nondecreasing and attains a maximum.
Any later blockage would increase it, proving `low_density_speed_one`.

**Elapsed-time deadline.** Put `ell = lcm(W,H)` and `K = m(g−2)`.
`low_density_speed_one_deadline` proves that every round `t ≥ ell * K`
has `AllMove`, and `low_density_staticFree_deadline` gives `StaticFree` at
the deadline. The proof combines the blockage budget with B3's
`lemmaR_finite_lt`: among `K+1` disjoint windows of `ell` rounds, at least
one has no blocked round. Its start is at most `ell * K`, and its full
movement forces permanent free flow from that start.

The bound `K` counts blocked rounds; `ell * K` bounds elapsed time to
permanent free flow. The theorem includes the empty board, with deadline
zero, and singleton dimensions. A nonempty state satisfying the strict
hypothesis has `g ≥ 3`. No sharpness or equality-case extension is claimed.
The deterministic condition gives a shrinking density range as the torus
grows. The fixed-positive-density probability problem remains open.

The [finite replay](../scripts/check_sparse_speed.py) independently checks
every sparse board on 14 ordered shapes through its first board recurrence,
with larger sparse queues and strict-density and phase-semantics controls.

---

## Not in this blueprint

The fixed-positive-density probabilistic switch (loop formation under μ_p) has
no proof to blueprint yet. The
[probability note](../docs/research/2026-11-18-probabilistic-gridlock-bounds.md)
separately proves the mixed-cycle reduction, a shrinking-density no-gridlock
window, and finite-time bounds in prose; see `docs/theorems.md` §§8–8c. Those
results do not establish a positive critical density.
