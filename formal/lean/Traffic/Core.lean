import Std

/-!
# BML transition semantics and frozen configurations

All movement decisions in a half-step inspect the old configuration.  A grid
provides mutually inverse forward/backward neighbors for each traffic phase.
No commutation assumption is needed for the freezing results, so they also
apply to finite cyclic grids.
-/

namespace Traffic

inductive Cell where
  | empty
  | east
  | north
  deriving DecidableEq, Repr, Inhabited

inductive Phase where
  | east
  | north
  deriving DecidableEq, Repr, Inhabited

def Phase.car : Phase → Cell
  | .east => .east
  | .north => .north

@[simp] theorem Phase.car_ne_empty (p : Phase) : p.car ≠ Cell.empty := by
  cases p <;> decide

@[simp] theorem Phase.car_inj {p q : Phase} : p.car = q.car ↔ p = q := by
  cases p <;> cases q <;> simp [Phase.car]

def allCells : List Cell := [.empty, .east, .north]

def allPhases : List Phase := [.east, .north]

@[simp] theorem mem_allCells (a : Cell) : a ∈ allCells := by
  cases a <;> decide

@[simp] theorem mem_allPhases (p : Phase) : p ∈ allPhases := by
  cases p <;> decide

universe u v

structure Grid (V : Type u) where
  next : Phase → V → V
  prev : Phase → V → V
  next_prev : ∀ p x, next p (prev p x) = x
  prev_next : ∀ p x, prev p (next p x) = x

abbrev Config (V : Type u) := V → Cell

/-- A car is eligible exactly when its destination is vacant in the old state. -/
def Moves (g : Grid V) (c : Config V) (p : Phase) (x : V) : Prop :=
  c x = p.car ∧ c (g.next p x) = .empty

instance (g : Grid V) (c : Config V) (p : Phase) (x : V) :
    Decidable (Moves g c p x) :=
  inferInstanceAs (Decidable (c x = p.car ∧ c (g.next p x) = .empty))

/-- Simultaneous update: both the departing and arriving checks use `c`. -/
def halfStep (g : Grid V) (p : Phase) (c : Config V) : Config V :=
  fun x =>
    if Moves g c p x then .empty
    else if Moves g c p (g.prev p x) then p.car
    else c x

/-- One full cycle, with east followed by north. -/
def fullStep (g : Grid V) (c : Config V) : Config V :=
  halfStep g .north (halfStep g .east c)

/-- Semantic freezing: each actual species update fixes the configuration. -/
def Frozen (g : Grid V) (c : Config V) : Prop :=
  ∀ p, halfStep g p c = c

/-- Every car's forward destination is occupied. -/
def TargetsBlocked (g : Grid V) (c : Config V) : Prop :=
  ∀ p x, c x = p.car → c (g.next p x) ≠ .empty

theorem moves_not_incoming (g : Grid V) (c : Config V) (p : Phase) (x : V)
    (h : Moves g c p x) : ¬ Moves g c p (g.prev p x) := by
  intro hin
  have hempty : c x = .empty := by
    simpa only [g.next_prev] using hin.2
  exact p.car_ne_empty (h.1.symm.trans hempty)

theorem mover_leaves (g : Grid V) (c : Config V) (p : Phase) (x : V)
    (h : Moves g c p x) : halfStep g p c x = .empty := by
  simp [halfStep, h]

theorem mover_arrives (g : Grid V) (c : Config V) (p : Phase) (x : V)
    (h : Moves g c p x) : halfStep g p c (g.next p x) = p.car := by
  have hout : ¬ Moves g c p (g.next p x) := by
    intro hout
    exact p.car_ne_empty (hout.1.symm.trans h.2)
  simp [halfStep, hout, g.prev_next, h]

theorem halfStep_eq_iff_no_moves (g : Grid V) (p : Phase) (c : Config V) :
    halfStep g p c = c ↔ ∀ x, ¬ Moves g c p x := by
  constructor
  · intro hfix x hmove
    have hx := congrFun hfix x
    rw [mover_leaves g c p x hmove] at hx
    exact p.car_ne_empty (hmove.1.symm.trans hx.symm)
  · intro hnone
    funext x
    simp [halfStep, hnone x, hnone (g.prev p x)]

theorem frozen_iff_no_moves (g : Grid V) (c : Config V) :
    Frozen g c ↔ ∀ p x, ¬ Moves g c p x := by
  constructor
  · intro h p
    exact (halfStep_eq_iff_no_moves g p c).mp (h p)
  · intro h p
    exact (halfStep_eq_iff_no_moves g p c).mpr (h p)

theorem frozen_iff_targets (g : Grid V) (c : Config V) :
    Frozen g c ↔ TargetsBlocked g c := by
  rw [frozen_iff_no_moves]
  constructor
  · intro h p x hcar hempty
    exact h p x ⟨hcar, hempty⟩
  · intro h p x hmove
    exact h p x hmove.1 hmove.2

theorem frozen_iff_east_north (g : Grid V) (c : Config V) :
    Frozen g c ↔
      (∀ x, c x = .east → c (g.next .east x) ≠ .empty) ∧
      (∀ x, c x = .north → c (g.next .north x) ≠ .empty) := by
  rw [frozen_iff_targets]
  constructor
  · intro h
    exact ⟨h .east, h .north⟩
  · rintro ⟨he, hn⟩ p
    cases p
    · exact he
    · exact hn

theorem frozen_halfStep (g : Grid V) (c : Config V) (h : Frozen g c)
    (p : Phase) : Frozen g (halfStep g p c) := by
  rw [h p]
  exact h

theorem frozen_fullStep (g : Grid V) (c : Config V) (h : Frozen g c) :
    fullStep g c = c := by
  simp only [fullStep, h .east, h .north]

/-- A species cannot be created or destroyed by the other species' update. -/
theorem halfStep_eq_other_iff (g : Grid V) (p : Phase) (c : Config V)
    (x : V) (a : Cell) (hzero : a ≠ .empty) (hphase : a ≠ p.car) :
    halfStep g p c x = a ↔ c x = a := by
  constructor
  · intro h
    unfold halfStep at h
    split at h
    · exact False.elim (hzero h.symm)
    · split at h
      · exact False.elim (hphase h.symm)
      · exact h
  · intro h
    have hout : ¬ Moves g c p x := by
      intro hm
      exact hphase (h.symm.trans hm.1)
    have hin : ¬ Moves g c p (g.prev p x) := by
      intro hm
      have hempty : c x = .empty := by
        simpa only [g.next_prev] using hm.2
      exact hzero (h.symm.trans hempty)
    simp [halfStep, hout, hin, h]

/-- Fixed points of a complete cycle cannot conceal motion between half-steps. -/
theorem fullStep_fixed_iff_frozen (g : Grid V) (c : Config V) :
    fullStep g c = c ↔ Frozen g c := by
  constructor
  · intro hfix
    have hnoeast : ∀ x, ¬ Moves g c .east x := by
      intro x hm
      have hfinal : halfStep g .north (halfStep g .east c) x = Cell.east := by
        change fullStep g c x = Cell.east
        rw [hfix]
        exact hm.1
      have hafter : halfStep g .east c x = Cell.east :=
        (halfStep_eq_other_iff g .north (halfStep g .east c) x .east
          (by decide) (by decide)).mp hfinal
      rw [mover_leaves g c .east x hm] at hafter
      cases hafter
    have he := (halfStep_eq_iff_no_moves g .east c).mpr hnoeast
    have hn : halfStep g .north c = c := by
      simpa only [fullStep, he] using hfix
    intro p
    cases p
    · exact he
    · exact hn
  · exact frozen_fullStep g c

def evolve (g : Grid V) (c : Config V) : Nat → Config V
  | 0 => c
  | n + 1 => fullStep g (evolve g c n)

theorem frozen_evolve (g : Grid V) (c : Config V) (h : Frozen g c)
    (n : Nat) : evolve g c n = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [evolve, ih, frozen_fullStep g c h]

theorem full_occupancy_frozen (g : Grid V) (c : Config V)
    (h : ∀ x, c x ≠ .empty) : Frozen g c := by
  apply (frozen_iff_targets g c).mpr
  intro p x _
  exact h (g.next p x)

/-- The occupied-successor criterion, stated without choosing a global path. -/
theorem frozen_of_successor (g : Grid V) (c : Config V)
    (h : ∀ x, c x ≠ .empty →
      ∃ p, c x = p.car ∧ c (g.next p x) ≠ .empty) : Frozen g c := by
  apply (frozen_iff_targets g c).mpr
  intro p x hp
  have hnonempty : c x ≠ .empty := by
    rw [hp]
    exact p.car_ne_empty
  obtain ⟨q, hq, htarget⟩ := h x hnonempty
  have hpq : p = q := Phase.car_inj.mp (hp.symm.trans hq)
  simpa only [hpq] using htarget

/-- Cars on a bi-infinite occupied successor path are frozen under the update. -/
theorem frozen_of_occupied_path (g : Grid V) (c : Config V)
    (r : Int → V) (u : Int → Phase)
    (hcar : ∀ n, c (r n) = (u n).car)
    (hcover : ∀ x, c x ≠ .empty → ∃ n, r n = x)
    (hnext : ∀ n, r (n + 1) = g.next (u n) (r n)) : Frozen g c := by
  apply frozen_of_successor g c
  intro x hx
  obtain ⟨n, rfl⟩ := hcover x hx
  refine ⟨u n, hcar n, ?_⟩
  rw [← hnext n, hcar (n + 1)]
  exact (u (n + 1)).car_ne_empty

/-- Forward-neighbor-preserving maps transport frozen configurations. -/
theorem frozen_pullback (gV : Grid V) (gW : Grid W) (f : W → V)
    (hf : ∀ p x, f (gW.next p x) = gV.next p (f x))
    (c : Config V) (h : Frozen gV c) : Frozen gW (fun x => c (f x)) := by
  apply (frozen_iff_targets gW _).mpr
  intro p x hcar
  change c (f (gW.next p x)) ≠ .empty
  rw [hf]
  exact (frozen_iff_targets gV c).mp h p (f x) hcar

abbrev Position := Int × Int

abbrev Configuration := Config Position

def squareGrid : Grid Position where
  next p x := match p with
    | .east => (x.1 + 1, x.2)
    | .north => (x.1, x.2 + 1)
  prev p x := match p with
    | .east => (x.1 - 1, x.2)
    | .north => (x.1, x.2 - 1)
  next_prev := by
    intro p x
    cases p <;> apply Prod.ext <;> simp
  prev_next := by
    intro p x
    cases p <;> apply Prod.ext <;> simp

end Traffic
