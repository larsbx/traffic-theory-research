import Std

/-!
An executable BML kernel with synchronous east then north phases.
The general proofs use reversible neighbor maps; `Torus.lean` instantiates
these with positive finite cyclic coordinates. Empty fixed states are not jams.
-/
namespace BML

inductive Cell where
  | empty | east | north
  deriving DecidableEq, BEq, Repr

inductive Species where
  | east | north
  deriving DecidableEq, BEq, Repr

def Species.cell : Species → Cell
  | .east => .east
  | .north => .north

@[simp] theorem Species.cell_ne_empty (sp : Species) : sp.cell ≠ .empty := by
  cases sp <;> decide

structure Direction (α : Type) where
  next : α → α
  prev : α → α
  next_prev : ∀ p, next (prev p) = p
  prev_next : ∀ p, prev (next p) = p

abbrev Config (α : Type) := α → Cell

def CanMove (d : Direction α) (sp : Species) (s : Config α) (p : α) : Prop :=
  s p = sp.cell ∧ s (d.next p) = .empty

instance (d : Direction α) (sp : Species) (s : Config α) (p : α) :
    Decidable (CanMove d sp s p) := inferInstanceAs (Decidable (_ ∧ _))

/-- Source and destination decisions use only the pre-phase configuration. -/
def halfStep (d : Direction α) (sp : Species) (s : Config α) : Config α := fun p =>
  if s p = sp.cell then
    if s (d.next p) = .empty then .empty else sp.cell
  else if s p = .empty ∧ s (d.prev p) = sp.cell then sp.cell
  else s p

/-- The local blocking condition, including the vacuous empty configuration. -/
def Blocked (d : Direction α) (sp : Species) (s : Config α) : Prop :=
  ∀ p, s p = sp.cell → s (d.next p) ≠ .empty

theorem moving_source_emptied (d : Direction α) (sp : Species)
    (s : Config α) (p : α) (h : CanMove d sp s p) :
    halfStep d sp s p = .empty := by
  simp [halfStep, h.1, h.2]

theorem moving_destination_filled (d : Direction α) (sp : Species)
    (s : Config α) (p : α) (h : CanMove d sp s p) :
    halfStep d sp s (d.next p) = sp.cell := by
  simp [halfStep, h.1, h.2, d.prev_next, Ne.symm sp.cell_ne_empty]

theorem other_species_unchanged (d : Direction α) (sp : Species)
    (s : Config α) (p : α) (c : Cell) (hne : c ≠ .empty) (hsp : c ≠ sp.cell) :
    halfStep d sp s p = c ↔ s p = c := by
  unfold halfStep
  split <;> rename_i h
  · split <;> simp_all [Ne.symm hne, Ne.symm hsp]
  · split <;> simp_all [Ne.symm hne, Ne.symm hsp]

theorem halfStep_eq_of_blocked (d : Direction α) (sp : Species)
    (s : Config α) (h : Blocked d sp s) : halfStep d sp s = s := by
  funext p
  unfold halfStep
  split
  · rename_i hp
    simp [h p hp, hp]
  · rename_i hp
    have hIncoming : ¬ (s p = .empty ∧ s (d.prev p) = sp.cell) := by
      intro hi
      have hb := h (d.prev p) hi.2
      rw [d.next_prev] at hb
      exact hb hi.1
    simp [hIncoming]

theorem blocked_of_halfStep_eq (d : Direction α) (sp : Species)
    (s : Config α) (h : halfStep d sp s = s) : Blocked d sp s := by
  intro p hp he
  have hm := moving_source_emptied d sp s p ⟨hp, he⟩
  rw [h, hp] at hm
  exact sp.cell_ne_empty hm

theorem halfStep_eq_iff_blocked (d : Direction α) (sp : Species) (s : Config α) :
    halfStep d sp s = s ↔ Blocked d sp s :=
  ⟨blocked_of_halfStep_eq d sp s, halfStep_eq_of_blocked d sp s⟩

def step (east north : Direction α) (s : Config α) : Config α :=
  halfStep north .north (halfStep east .east s)

def Frozen (east north : Direction α) (s : Config α) : Prop :=
  Blocked east .east s ∧ Blocked north .north s

def Nonempty (s : Config α) : Prop := ∃ p, s p ≠ .empty

def Jam (east north : Direction α) (s : Config α) : Prop :=
  Nonempty s ∧ Frozen east north s

/-- The converse is essential: north updates cannot restore a moved east car. -/
theorem step_eq_iff_frozen (east north : Direction α) (s : Config α) :
    step east north s = s ↔ Frozen east north s := by
  constructor
  · intro h
    have he : Blocked east .east s := by
      intro p hp hd
      have hempty := moving_source_emptied east .east s p ⟨hp, hd⟩
      have hsame : step east north s p = .east := by rw [h]; exact hp
      have hn := (other_species_unchanged north .north
        (halfStep east .east s) p .east (by decide) (by decide)).mp hsame
      rw [hempty] at hn
      cases hn
    have heq := halfStep_eq_of_blocked east .east s he
    have hn : halfStep north .north s = s := by
      simpa [step, heq] using h
    exact ⟨he, blocked_of_halfStep_eq north .north s hn⟩
  · intro h
    simp [step, halfStep_eq_of_blocked east .east s h.1,
      halfStep_eq_of_blocked north .north s h.2]

theorem jam_iff_nonempty_fixed (east north : Direction α) (s : Config α) :
    Jam east north s ↔ Nonempty s ∧ step east north s = s := by
  rw [step_eq_iff_frozen]
  rfl

def iterate (f : α → α) : Nat → α → α
  | 0, a => a
  | n+1, a => f (iterate f n a)

theorem iterate_eq_of_fixed (f : α → α) (a : α) (h : f a = a) (t : Nat) :
    iterate f t a = a := by
  induction t with
  | zero => rfl
  | succ t ih => simp [iterate, ih, h]

theorem frozen_persists (east north : Direction α) (s : Config α)
    (h : Frozen east north s) (t : Nat) : iterate (step east north) t s = s :=
  iterate_eq_of_fixed _ _ ((step_eq_iff_frozen east north s).mpr h) t

theorem fully_occupied_frozen (east north : Direction α) (s : Config α)
    (h : ∀ p, s p ≠ .empty) : Frozen east north s := by
  exact ⟨fun p _ => h (east.next p), fun p _ => h (north.next p)⟩

theorem empty_fixed (east north : Direction α) :
    step east north (fun _ => .empty) = (fun _ => .empty) := by
  apply (step_eq_iff_frozen east north _).mpr
  constructor <;> intro p hp <;> cases hp

theorem empty_not_jam (east north : Direction α) :
    ¬ Jam east north (fun _ => .empty) := by
  intro ⟨⟨p, hp⟩, _⟩
  exact hp rfl

theorem iterate_add (f : α → α) (a : α) (m n : Nat) :
    iterate f (m+n) a = iterate f n (iterate f m a) := by
  induction n with
  | zero => simp [iterate]
  | succ n ih => simp [iterate, ih]

theorem reached_frozen_persists (east north : Direction α) (s : Config α)
    (t : Nat) (h : Frozen east north (iterate (step east north) t s)) (u : Nat) :
    iterate (step east north) (t+u) s = iterate (step east north) t s := by
  rw [iterate_add]
  exact frozen_persists east north _ h u

/-- Zero movement means both synchronous phases have no eligible source. -/
def NoMoves (east north : Direction α) (s : Config α) : Prop :=
  (∀ p, ¬ CanMove east .east s p) ∧
  (∀ p, ¬ CanMove north .north (halfStep east .east s) p)

theorem blocked_iff_no_movers (d : Direction α) (sp : Species) (s : Config α) :
    Blocked d sp s ↔ ∀ p, ¬ CanMove d sp s p := by
  constructor
  · intro h p hm
    exact h p hm.1 hm.2
  · intro h p hp he
    exact h p ⟨hp, he⟩

theorem noMoves_iff_frozen (east north : Direction α) (s : Config α) :
    NoMoves east north s ↔ Frozen east north s := by
  constructor
  · intro ⟨he, hn⟩
    have he' := (blocked_iff_no_movers east .east s).mpr he
    have heq := halfStep_eq_of_blocked east .east s he'
    rw [heq] at hn
    exact ⟨he', (blocked_iff_no_movers north .north s).mpr hn⟩
  · intro ⟨he, hn⟩
    have heq := halfStep_eq_of_blocked east .east s he
    constructor
    · exact (blocked_iff_no_movers east .east s).mp he
    · rw [heq]
      exact (blocked_iff_no_movers north .north s).mp hn

theorem step_eq_iff_noMoves (east north : Direction α) (s : Config α) :
    step east north s = s ↔ NoMoves east north s := by
  rw [step_eq_iff_frozen, noMoves_iff_frozen]

end BML
