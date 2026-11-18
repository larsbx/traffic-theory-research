import BML.Torus
import BML.Transport

namespace BML.Witness

abbrev Pos := Position 4 2
abbrev e := eastDirection 4 2 (by decide)
abbrev n := northDirection 4 2 (by decide)
abbrev f := torusStep 4 2 (by decide) (by decide)

def before : Config Pos := decode 4 2 3858
def jammed : Config Pos := decode 4 2 2048
def after : Config Pos := decode 4 2 3860
def alternate : Config Pos := decode 4 2 4340

theorem before_reaches_jammed : iterate f 3 before = jammed := by
  funext p
  exact (by decide : ∀ x : Fin 4, ∀ y : Fin 2, iterate f 3 before (x,y) = jammed (x,y)) p.1 p.2

theorem jammed_fixed : f jammed = jammed := by
  funext p
  exact (by decide : ∀ x : Fin 4, ∀ y : Fin 2, f jammed (x,y) = jammed (x,y)) p.1 p.2

theorem jammed_nonempty : Nonempty jammed := by
  exact ⟨(⟨0, by decide⟩, ⟨0, by decide⟩), by decide⟩

theorem jammed_is_jam : Jam e n jammed :=
  (jam_iff_nonempty_fixed e n jammed).mpr ⟨jammed_nonempty, jammed_fixed⟩

theorem before_eventually_jams : ∃ t, Jam e n (iterate f t before) := by
  exact ⟨3, by rw [before_reaches_jammed]; exact jammed_is_jam⟩

/-- The new state differs only by adding a north car in the initially empty cell (0,0). -/
theorem adds_one_north :
    before (⟨0, by decide⟩, ⟨0, by decide⟩) = .empty ∧
    after (⟨0, by decide⟩, ⟨0, by decide⟩) = .north ∧
    ∀ p : Pos, p ≠ (⟨0, by decide⟩, ⟨0, by decide⟩) → after p = before p := by
  refine ⟨by decide, by decide, ?_⟩
  intro p hp
  exact (by decide : ∀ x : Fin 4, ∀ y : Fin 2,
    (x,y) ≠ (⟨0, by decide⟩, ⟨0, by decide⟩) → after (x,y) = before (x,y)) p.1 p.2 hp

theorem after_to_alternate : f after = alternate := by
  funext p
  exact (by decide : ∀ x : Fin 4, ∀ y : Fin 2, f after (x,y) = alternate (x,y)) p.1 p.2

theorem alternate_to_after : f alternate = after := by
  funext p
  exact (by decide : ∀ x : Fin 4, ∀ y : Fin 2, f alternate (x,y) = after (x,y)) p.1 p.2

theorem after_ne_alternate : after ≠ alternate := by
  intro h
  have hp := congrFun h (⟨1, by decide⟩, ⟨0, by decide⟩)
  change Cell.north = Cell.empty at hp
  cases hp

theorem orbit_in_pair (t : Nat) : iterate f t after = after ∨ iterate f t after = alternate := by
  induction t with
  | zero => exact Or.inl rfl
  | succ t ih =>
    rcases ih with ih | ih
    · exact Or.inr (by simp [iterate, ih, after_to_alternate])
    · exact Or.inl (by simp [iterate, ih, alternate_to_after])

theorem after_never_fixed (t : Nat) : f (iterate f t after) ≠ iterate f t after := by
  rcases orbit_in_pair t with ht | ht
  · rw [ht, after_to_alternate]
    exact Ne.symm after_ne_alternate
  · rw [ht, alternate_to_after]
    exact after_ne_alternate

theorem after_never_jams (t : Nat) : ¬ Jam e n (iterate f t after) := by
  intro h
  exact after_never_fixed t ((jam_iff_nonempty_fixed e n _).mp h).2

/-- The added north car is blocked at (0,0) at every full-step boundary and never moves. -/
theorem added_car_stays_blocked (t : Nat) :
    iterate f t after (⟨0, by decide⟩, ⟨0, by decide⟩) = .north ∧
    ¬ CanMove n .north (halfStep e .east (iterate f t after))
      (⟨0, by decide⟩, ⟨0, by decide⟩) := by
  rcases orbit_in_pair t with ht | ht <;> rw [ht] <;> decide

/-- Each periodic state has one movable original north car in column 1. -/
theorem original_column_moves (t : Nat) :
    ∃ y : Fin 2, CanMove n .north (halfStep e .east (iterate f t after))
      (⟨1, by decide⟩, y) := by
  rcases orbit_in_pair t with ht | ht
  · rw [ht]; exact ⟨⟨0, by decide⟩, by decide⟩
  · rw [ht]; exact ⟨⟨1, by decide⟩, by decide⟩

def originalStart : Pos := (⟨1, by decide⟩, ⟨0, by decide⟩)
def originalOther : Pos := (⟨1, by decide⟩, ⟨1, by decide⟩)

theorem traced_car_is_original : before originalStart = .north ∧ after originalStart = .north := by
  decide

theorem original_transport_after :
    transport n .north (halfStep e .east after) originalStart = originalOther := by
  decide

theorem original_transport_alternate :
    transport n .north (halfStep e .east alternate) originalOther = originalStart := by
  decide

/-- Follow this particular original car, rather than only an unlabeled occupied site. -/
def originalTrace : Nat → Pos
  | 0 => originalStart
  | t+1 => transport n .north (halfStep e .east (iterate f t after)) (originalTrace t)

theorem original_trace_in_pair (t : Nat) :
    (iterate f t after = after ∧ originalTrace t = originalStart) ∨
    (iterate f t after = alternate ∧ originalTrace t = originalOther) := by
  induction t with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ t ih =>
    rcases ih with ⟨hs, hp⟩ | ⟨hs, hp⟩
    · exact Or.inr ⟨by simp [iterate, hs, after_to_alternate],
        by simp [originalTrace, hs, hp, original_transport_after]⟩
    · exact Or.inl ⟨by simp [iterate, hs, alternate_to_after],
        by simp [originalTrace, hs, hp, original_transport_alternate]⟩

theorem original_traced_car_moves_forever (t : Nat) :
    CanMove n .north (halfStep e .east (iterate f t after)) (originalTrace t) := by
  rcases original_trace_in_pair t with ⟨hs, hp⟩ | ⟨hs, hp⟩ <;> rw [hs, hp] <;> decide

end BML.Witness
