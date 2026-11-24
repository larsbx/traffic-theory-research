import BML.FiniteCycle

/-!
# Traffic nets

One object for every exclusion model in this repository. A net has cells, car
classes with a route (a partial successor per class, `none` meaning exit),
periodic or arbitrary entry gates (signals), and a merge order at every cell
(yield rules). One tick moves every car whose next cell is vacant at the start
of the tick, whose gate is open, and which wins the merge. BML, the roundabout
grid, mixed grids and link cells are parameter choices (`BML.NetInstances`).

The theorems here are proved once for every net:

* `stuck_step`, `stuck_iff`: no car ever moves iff every car's next cell is
  occupied, given that every gate opens within a bounded number of ticks and
  every route is admitted by the merge order;
* `stuck_blocker_cycle`: a stuck state with a car contains a closed blocker
  walk no longer than the number of occupied cells.
-/
namespace BML.Net

structure Net (Cell Class : Type) where
  /-- The route: where a car of this class goes next. `none` is an exit. -/
  next : Class → Cell → Option Cell
  /-- Routes of one class never merge, so entry has at most one source per class. -/
  prev : Class → Cell → Option Cell
  prev_iff : ∀ k p c, prev k c = some p ↔ next k p = some c
  /-- Merge rule: the first listed class with a car waiting and an open gate enters. -/
  order : Cell → List Class
  /-- Signal: may a car of this class enter this cell during this tick? -/
  gate : Nat → Class → Cell → Bool

abbrev Config (Cell Class : Type) := Cell → Option Class

variable {Cell Class : Type} [DecidableEq Class]

/-- A car of class `k` sits directly behind `c` on its route. -/
def wants (net : Net Cell Class) (s : Config Cell Class) (k : Class) (c : Cell) : Bool :=
  match net.prev k c with
  | some p => decide (s p = some k)
  | none => false

/-- The class that enters `c` in tick `t`. Vacancy is read before the tick. -/
def winner (net : Net Cell Class) (t : Nat) (s : Config Cell Class) (c : Cell) : Option Class :=
  if (s c).isSome then none
  else (net.order c).find? fun k => net.gate t k c && wants net s k c

def leaves (net : Net Cell Class) (t : Nat) (s : Config Cell Class) (p : Cell) : Bool :=
  match s p with
  | none => false
  | some k =>
    match net.next k p with
    | none => true
    | some c => decide (winner net t s c = some k)

/-- One synchronous tick. -/
def step (net : Net Cell Class) (t : Nat) (s : Config Cell Class) : Config Cell Class := fun c =>
  match winner net t s c with
  | some k => some k
  | none => if leaves net t s c then none else s c

def run (net : Net Cell Class) (s : Config Cell Class) : Nat → Config Cell Class
  | 0 => s
  | t + 1 => step net t (run net s t)

/-- Every car's next cell exists and is occupied. -/
def Stuck (net : Net Cell Class) (s : Config Cell Class) : Prop :=
  ∀ p k, s p = some k → ∃ c, net.next k p = some c ∧ (s c).isSome = true

/-- Every route into a cell is admitted by that cell's merge order. -/
def Complete (net : Net Cell Class) : Prop :=
  ∀ k p c, net.next k p = some c → k ∈ net.order c

/-- Every gate opens at least once in every window of `period` ticks. -/
def Fair (net : Net Cell Class) (period : Nat) : Prop :=
  ∀ t k c, ∃ d, d < period ∧ net.gate (t + d) k c = true

variable {net : Net Cell Class} {s : Config Cell Class}

theorem winner_vacant {t : Nat} {c : Cell} {k : Class} (h : winner net t s c = some k) :
    s c = none := by
  unfold winner at h
  cases hc : s c with
  | none => rfl
  | some j => simp [hc] at h

theorem winner_none_of_stuck (hs : Stuck net s) (t : Nat) (c : Cell) : winner net t s c = none := by
  unfold winner
  split
  · rfl
  · rename_i hc
    apply List.find?_eq_none.mpr
    intro k _
    have hw : wants net s k c = false := by
      unfold wants
      cases hp : net.prev k c with
      | none => rfl
      | some p =>
        by_cases hk : s p = some k
        · obtain ⟨c', hn, ho⟩ := hs p k hk
          have hc' : c' = c := by
            have := (net.prev_iff k p c).mp hp
            rw [hn] at this
            exact Option.some.inj this
          rw [hc'] at ho
          exact absurd ho hc
        · simp [hk]
    simp [hw]

/-- A stuck state is unchanged by every tick, whatever the signals show. -/
theorem stuck_step (hs : Stuck net s) (t : Nat) : step net t s = s := by
  funext c
  unfold step
  rw [winner_none_of_stuck hs t c]
  have hl : leaves net t s c = false := by
    unfold leaves
    cases hc : s c with
    | none => rfl
    | some k =>
      obtain ⟨c', hn, _⟩ := hs c k hc
      simp [hn, winner_none_of_stuck hs t c']
  simp [hl]

theorem stuck_run (hs : Stuck net s) (t : Nat) : run net s t = s := by
  induction t with
  | zero => rfl
  | succ t ih => simp [run, ih, stuck_step hs t]

/-- If some car has a vacant next cell or an exit, a tick within one gate
period changes the state. -/
theorem moves_of_not_stuck (hc : Complete net) {period : Nat} (hpos : 0 < period)
    (hf : Fair net period) (hs : ¬ Stuck net s) (t : Nat) :
    ∃ d, d < period ∧ step net (t + d) s ≠ s := by
  classical
  have hcar : ∃ p k, s p = some k ∧
      (net.next k p = none ∨ ∃ c, net.next k p = some c ∧ s c = none) := by
    apply Classical.byContradiction
    intro hno
    apply hs
    intro p k hk
    cases hn : net.next k p with
    | none => exact absurd ⟨p, k, hk, Or.inl hn⟩ hno
    | some c =>
      cases hoc : s c with
      | none => exact absurd ⟨p, k, hk, Or.inr ⟨c, hn, hoc⟩⟩ hno
      | some j => exact ⟨c, rfl, by simp [hoc]⟩
  obtain ⟨p, k, hk, hexit | ⟨c, hn, hvac⟩⟩ := hcar
  · refine ⟨0, hpos, fun heq => ?_⟩
    have hp := congrFun heq p
    have hw : winner net t s p = none := by simp [winner, hk]
    simp [step, hw, leaves, hk, hexit] at hp
  · obtain ⟨d, hd, hg⟩ := hf t k c
    refine ⟨d, hd, fun heq => ?_⟩
    have hcell := congrFun heq c
    have hsome : (winner net (t + d) s c).isSome = true := by
      have hwant : wants net s k c = true := by
        have hp := (net.prev_iff k p c).mpr hn
        simp [wants, hp, hk]
      unfold winner
      simp only [hvac, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      exact List.find?_isSome.mpr ⟨k, hc k p c hn, by simp [hg, hwant]⟩
    cases hw : winner net (t + d) s c with
    | none => simp [hw] at hsome
    | some j => simp [step, hw, hvac] at hcell

/-- **Gridlock, for every net.** With fair gates and a complete merge order,
a state is stuck iff no tick of one gate period changes it. -/
theorem stuck_iff (hc : Complete net) {period : Nat} (hpos : 0 < period)
    (hf : Fair net period) (t : Nat) :
    Stuck net s ↔ ∀ d, d < period → step net (t + d) s = s := by
  constructor
  · intro hs d _
    exact stuck_step hs (t + d)
  · intro h
    apply Classical.byContradiction
    intro hs
    obtain ⟨d, hd, hne⟩ := moves_of_not_stuck hc hpos hf hs t
    exact hne (h d hd)

/-- The same along the actual run from tick 0: stuck iff the state never changes. -/
theorem stuck_iff_run_constant (hc : Complete net) {period : Nat} (hpos : 0 < period)
    (hf : Fair net period) : Stuck net s ↔ ∀ t, run net s t = s := by
  constructor
  · exact stuck_run
  · intro h
    refine (stuck_iff hc hpos hf 0).mpr fun d _ => ?_
    have h1 := h (d + 1)
    rw [run, h d] at h1
    simpa using h1

/-- The cell in front of the car at `p`; `p` itself if there is none. -/
def ahead (net : Net Cell Class) (s : Config Cell Class) (p : Cell) : Cell :=
  match s p with
  | some k => (net.next k p).getD p
  | none => p

omit [DecidableEq Class] in
theorem ahead_occupied (hs : Stuck net s) {p : Cell} (hp : (s p).isSome = true) :
    (s (ahead net s p)).isSome = true := by
  cases hk : s p with
  | none => simp [hk] at hp
  | some k =>
    obtain ⟨c, hn, ho⟩ := hs p k hk
    simpa [ahead, hk, hn] using ho

omit [DecidableEq Class] in
/-- In a stuck state the car at `p` is blocked by the car at `ahead p`. -/
theorem ahead_blocks (hs : Stuck net s) {p : Cell} {k : Class} (hk : s p = some k) :
    net.next k p = some (ahead net s p) := by
  obtain ⟨c, hn, _⟩ := hs p k hk
  simp [ahead, hk, hn]

omit [DecidableEq Class] in
/-- **Blocker cycle, for every net.** In a stuck state, following blockers from
any car returns to an earlier cell within as many steps as there are occupied
cells. So a gridlock has at least as many cars as its shortest blocker cycle. -/
theorem stuck_blocker_cycle (hs : Stuck net s) (occupied : List Cell)
    (hocc : ∀ p, p ∈ occupied ↔ (s p).isSome = true) {p : Cell} (hp : (s p).isSome = true) :
    ∃ i j, i < j ∧ j ≤ occupied.length ∧
      iterate (ahead net s) i p = iterate (ahead net s) j p :=
  closed_orbit_repeats (ahead net s) occupied
    (fun q hq => (hocc _).mpr (ahead_occupied hs ((hocc q).mp hq))) p ((hocc p).mpr hp)

end BML.Net
