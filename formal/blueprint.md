# Blueprint: open formal obligations

This is a hand-off document. It states the open obligations of
[the coverage register](README.md) precisely, with proofs decomposed into
lemmas small enough to formalise one at a time.

- Each lemma lists the existing results it rests on, so a prover can work
  bottom-up. Lean signatures target the `BML` kernel on `main` (`Kernel`,
  `Torus`, `Transport`); `carCount` refers to PR #7's `Counting.lean`.
- Signatures are **specifications, not compiled code**. Adjust names freely,
  but keep the statements.
- Nothing here is a Lean theorem until it passes `lake build` and the axiom audit.

Conventions: `E = eastDirection w h hw` and `N = northDirection w h hh`.
`f = torusStep w h hw hh = step E N`, and `f^t = iterate f t`.

| Id | Obligation | Status of the mathematics | Depends on |
|---|---|---|---|
| B0 | Ring arithmetic helpers | elementary | — |
| B1 | G2: no forced gridlock below full occupancy | complete proof below | B0, Kernel |
| B2 | Coset identity ⟨(1,−1)⟩ = ker φ | complete proof below (Bézout) | — |
| B3 | Lemma R: static ⟺ perpetual free flow | complete proof below | B0, B2, Kernel |
| B4 | Theorem F: densest free flow | proof outline; the packing step needs care | B3 |
| B5 | Theorem T: train rule, least stuck count W+H | complete proof below; needs a TRAIN kernel | new kernel |

---

## B0. Ring arithmetic helpers

```lean
theorem cyclicNext_val (n : Nat) (hn : 0 < n) (i : Fin n) :
    (cyclicNext n hn i).val = (i.val + 1) % n

theorem iterate_cyclicNext_val (n : Nat) (hn : 0 < n) (i : Fin n) (k : Nat) :
    (iterate (cyclicNext n hn) k i).val = (i.val + k) % n
```

*Proof.*
- First lemma: case `i.val + 1 < n` (then `Nat.mod_eq_of_lt`), else
  `i.val + 1 = n` (then `Nat.mod_self`).
- Second lemma: induction on `k`, using `Nat.mod_add_mod`.

**Corollary (reachability).** For `i j : Fin n`, take `k = (j.val + n - i.val) % n`.
Then `iterate (cyclicNext n hn) k i = j`; check with `Fin.ext` and `omega` on the values.

---

## B1. G2: some configuration with n cars never gridlocks, for 0 ≤ n < WH

```lean
theorem exists_never_frozen (w h : Nat) (hw : 0 < w) (hh : 0 < h)
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

Both cases are pure `omega` once the indices are written out.

**Count.** `k ↦ (k / h, k % h)` is a bijection from `{k < n}` onto the east cells, so
`carCount = n`. Prove it with PR #7's list counting, or by an explicit
`List.range n` permutation argument.

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

---

## B2. Coset identity

Let g = gcd w h. In ℤ_w × ℤ_h, the subgroup ⟨(1, −1)⟩ is the kernel of
(x, y) ↦ x + y mod g. Stated on representatives, for `a < w` and `b < h`:

```lean
theorem coset_iff (w h a b : Nat) (hw : 0 < w) (hh : 0 < h) (ha : a < w) (hb : b < h) :
    (a + b) % Nat.gcd w h = 0 ↔
      ∃ t : Int, t % w = a ∧ (b + t) % h = 0
```

Read it as: (a, b) = (t mod w, −t mod h) for some t ∈ ℤ.

The bound `ha : a < w` is necessary: `t % w` is always below w. Without it, w = h = 2, a = 2,
b = 0 makes the left side true and the right side false. `hb` is not needed for the
equivalence, but it keeps (a, b) a representative pair as B3 uses it.

**Lemma B2.1 (Bézout).** `∃ x y : Int, x * m + y * n = Nat.gcd m n`.

Use `Nat.gcd.induction` with the predicate P m n := ∃ x y, x*m + y*n = gcd m n.
- Base `P 0 n`: take x = 0, y = 1, since gcd 0 n = n.
- Step: assume 0 < m and `P (n % m) m`, so x′·(n % m) + y′·m = gcd (n % m) m = gcd m n.
- Substitute n % m = n − m·(n / m), i.e. `Int.emod_def`.
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
Apply `coset_iff` to (a − 1 mod w, b).

**Corollary B2.3 (non-negative time).** If t ∈ ℤ witnesses `coset_iff`, so does
t + L·lcm(w, h) for any L. So a witness can be taken in any window of length lcm(w, h),
for example [1, lcm(w, h)].

---

## B3. Lemma R: free-flow rigidity

Let φ(p) = (p.1 + p.2) mod g.

```lean
def StaticFree (s : Config (Position w h)) : Prop :=
  (∀ p, s p = .east → s (E.next p) ≠ .east) ∧
  (∀ p, s p = .north → s (N.next p) ≠ .north) ∧
  (∀ e q, s e = .east → s q = .north →
     (φ q + g - φ e) % g ≠ 0 ∧ (φ q + g - φ e) % g ≠ 1 % g)

/-- Every car moves in its own phase. -/
def AllMove (s : Config (Position w h)) : Prop :=
  (∀ p, s p = .east → CanMove E .east s p) ∧
  (∀ p, halfStep E .east s p = .north → CanMove N .north (halfStep E .east s) p)

theorem lemmaR (s : Config (Position w h)) :
    StaticFree s ↔ ∀ t, AllMove (iterate f t s)

theorem lemmaR_finite (s : Config (Position w h)) :
    (∀ t, AllMove (iterate f t s)) ↔ (∀ t ≤ Nat.lcm w h, AllMove (iterate f t s))
```

**Lemma B3.1 (rigid half-step).** If every sp-car can move (`∀ p, s p = sp.cell → CanMove d sp s p`),
then `halfStep d sp s p = sp.cell ↔ s (d.prev p) = sp.cell`, and the other species is unchanged.
- (→) Unfold `halfStep` at p. If `s p = sp.cell`, the car at p moves, so the result is `.empty`;
  this branch never yields `sp.cell`. Otherwise the result is `sp.cell` exactly in the
  incoming branch, which has `s (d.prev p) = sp.cell`.
- (←) The car at `d.prev p` moves into `d.next (d.prev p) = p`: use
  `moving_destination_filled` and `d.next_prev`.
- Other species: `other_species_unchanged`.

**Lemma B3.2 (rigid orbit).** If `∀ u < t, AllMove (f^u s)`, then
- `f^t s p = .east ↔ s (iterate E.prev t p) = .east`, and
- `f^t s p = .north ↔ s (iterate N.prev t p) = .north`.

Proof: induction on t, using B3.1 for each phase. The north phase sees east cars already
shifted, which B3.1 for the east phase supplies.

**(⇒) StaticFree → AllMove at every t.** Use strong induction on t. By the induction hypothesis
and B3.2, the time-t configuration is the shift of s. Translate each blocking possibility back
to time 0:
1. An east car's target holds an east car: the cars are at e + (t, 0) and e + (t+1, 0), so s
   has east cars at e and e + (1, 0). This contradicts the first conjunct.
2. An east car's target holds a north car q + (0, t) = e + (t+1, 0): then (q − e) = (t+1, −t) lies in
   (1, 0) + ⟨(1, −1)⟩, so φ q − φ e ≡ 1 (B2.2). Contradiction.
3. A north car's target holds a north car: as in 1, with the second conjunct.
4. A north car's target holds an east car that has just moved, q + (0, t+1) = e + (t+1, 0):
   then (q − e) ∈ ⟨(1, −1)⟩, so φ q − φ e ≡ 0 (B2, ←). Contradiction.

Each case needs only the easy direction (←) of B2 and B2.2.

**(⇐) AllMove at every t → StaticFree.**
- Conjuncts 1 and 2 fail at t = 0. For 2, the east phase leaves north cars in place, by
  `other_species_unchanged`.
- Conjunct 3: suppose φ q − φ e ≡ 1. By B2.2 (→) and B2.3, take t ∈ [0, lcm) with
  q + (0, t) = e + (t+1, 0). At time t, by B3.2, the east car e + (t, 0) has its target occupied
  by the north car q + (0, t), so `AllMove` fails at t.
- If φ q − φ e ≡ 0, take t ∈ [1, lcm] with q + (0, t) = e + (t, 0). At time t − 1, the north car
  q + (0, t−1) targets q + (0, t) = e + (t, 0). The east car has just entered that cell in the
  east phase (B3.1), so `AllMove` fails at t − 1.

**`lemmaR_finite`.** The (⇐) proof only uses times t ≤ lcm(w, h).

---

## B4. Theorem F: densest free flow (outline)

With g = gcd(w, h) and V(g) = ⌊2g/3⌋ (already proved: `freeClasses_eq_two_thirds`):
- for g = 1: n_free = max(h⌊w/2⌋, w⌊h/2⌋);
- for g ≥ 2: n_free = (w·h/g) · V(g).

**Construction (≥).** Label the classes ℤ_g with k blocks `N E ·`, then blocks `E ·`, with
k = ⌊g/3⌋ − ((⌊g/3⌋ − g) mod 2). Show `StaticFree` with decidable class arithmetic, then apply
B3. The count is (w·h/g) × (number of non-blank labels), because each class has w·h/g cells.
- Cells per class: the map p ↦ φ p is (w·h/g)-to-one. Show it via the bijection
  (x, y) ↦ (x, x + y mod h), or count rows: each row meets each class in w/g cells.

**Upper bound (≤).** This is the delicate step. Let A = φ(E cars) and B = φ(N cars). B3 gives
B ∩ (A ∪ (A+1)) = ∅.
1. Per row, the cells of a maximal A-run of length r form w/g horizontal segments of length r.
   Conjunct 1 of `StaticFree` caps each segment at ⌈r/2⌉. Columns and B-runs are symmetric.
2. Combinatorics on the cyclic word over {A, B, ·}: Σ over blocks Bˢ Aʳ · of
   ⌈s/2⌉ + ⌈r/2⌉ ≤ V(g). Both prose proofs are in `docs/theorems.md` §5.

Suggested route: prove the word inequality as a standalone `Nat` lemma over `List (Fin 3)`,
by strong induction on the block decomposition. Then prove the per-segment cap. Finally sum
over rows and columns with PR #7's counting.

---

## B5. Theorem T: train rule (needs a TRAIN kernel)

The Lean kernel is CLASSIC only. TRAIN moves a maximal line of same-species cars when the cell
ahead of its head is empty, or when the line is a full ring.

```lean
/-- The sp-car at p belongs to a line that moves under TRAIN. -/
def TrainMoves (d : Direction α) (sp : Species) (s : Config α) (p : α) (L : Nat) : Prop :=
  s p = sp.cell ∧
  ((∃ k < L, (∀ i ≤ k, s (iterate d.next i p) = sp.cell) ∧
              s (iterate d.next (k+1) p) = .empty) ∨
   (∀ i < L, s (iterate d.next i p) = sp.cell))
```

Here L is the ring length: w for east, h for north. The disjunction reads "the queue ends in a
hole" or "the queue is the whole ring". The TRAIN `halfStep` moves exactly the `TrainMoves`
cars. Its Quint/Python correspondence should be replayed against `bml.model.TRAIN`.

```lean
theorem train_stuck_lower_bound (s) (hstuck : TrainStuck s) (hne : Nonempty s) :
    w + h ≤ carCount w h s
```

**Proof.**
1. Every column has an east car. A column with north cars but no east car contains a north
   line that ends in a hole or fills the column, and that line moves. An empty column x has
   column x−1 also without east cars, because an east car there would move into x. By
   induction westwards there would be no east cars at all, and then no cars at all.
2. Symmetrically, every row has a north car.
3. Choose one east car per column, an injection `Fin w →` east cells, and one north car per row,
   `Fin h →` north cells. The images are disjoint because the species differ, so
   w + h ≤ carCount.

**Construction.** Use the staircase from `bml.extremal.train_stuck_with`: path cell i steps east
iff i·w mod (w+h) < w. Check stuckness locally (each line ends at a car of the other species,
and no line is a full ring), then extend greedily. For a first formal version, prove only
attainment at n = w + h.

---

## Not in this blueprint

The probabilistic switch (loop formation under μ_p) has no proof to blueprint yet;
see `docs/theorems.md` §8.
