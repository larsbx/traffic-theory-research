import BML.Kernel

/-!
Rigid motion during a prefix of CLASSIC updates in which every car moves.
The north phase is evaluated after the east phase, exactly as in `step`.
These statements use reversible directions on an arbitrary set of positions.
-/
namespace BML

/-- Every east car moves, then every north car moves in the resulting board. -/
def AllMove (east north : Direction α) (s : Config α) : Prop :=
  (∀ p, s p = .east → CanMove east .east s p) ∧
  (∀ p, halfStep east .east s p = .north →
    CanMove north .north (halfStep east .east s) p)

/-- If every car of the active species moves, its occupancy is a rigid shift. -/
theorem halfStep_rigid (d : Direction α) (sp : Species) (s : Config α)
    (hm : ∀ p, s p = sp.cell → CanMove d sp s p) (p : α) :
    halfStep d sp s p = sp.cell ↔ s (d.prev p) = sp.cell := by
  constructor
  · intro hc
    by_cases hp : s p = sp.cell
    · have hz := moving_source_emptied d sp s p (hm p hp)
      rw [hc] at hz
      exact False.elim (sp.cell_ne_empty hz)
    · have hin : s p = .empty ∧ s (d.prev p) = sp.cell := by
        by_cases hn : s p = .empty ∧ s (d.prev p) = sp.cell
        · exact hn
        · have hs : halfStep d sp s p = s p := by simp [halfStep, hp, hn]
          rw [hs] at hc
          exact False.elim (hp hc)
      exact hin.2
  · intro hp
    have hv := moving_destination_filled d sp s (d.prev p) (hm (d.prev p) hp)
    simpa only [d.next_prev] using hv

/-- A complete moving round translates east occupancy by the east direction. -/
theorem allMove_step_east_iff (east north : Direction α) (s : Config α)
    (hm : AllMove east north s) (p : α) :
    step east north s p = .east ↔ s (east.prev p) = .east := by
  exact (other_species_unchanged north .north (halfStep east .east s) p
    .east (by decide) (by decide)).trans (halfStep_rigid east .east s hm.1 p)

/-- A complete moving round translates north occupancy by the north direction. -/
theorem allMove_step_north_iff (east north : Direction α) (s : Config α)
    (hm : AllMove east north s) (p : α) :
    step east north s p = .north ↔ s (north.prev p) = .north := by
  exact (halfStep_rigid north .north (halfStep east .east s) hm.2 p).trans
    (other_species_unchanged east .east s (north.prev p) .north (by decide) (by decide))

/-- Iterating a function commutes with one additional application of it. -/
theorem iterate_apply_comm (f : α → α) (t : Nat) (p : α) :
    iterate f t (f p) = f (iterate f t p) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [iterate, ih]

/-- Matching forward and backward direction iterates cancel. -/
theorem direction_iterate_prev_next (d : Direction α) (t : Nat) (p : α) :
    iterate d.prev t (iterate d.next t p) = p := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change d.prev (iterate d.prev t (d.next (iterate d.next t p))) = p
      rw [← iterate_apply_comm d.prev t, d.prev_next, ih]

/-- Matching backward and forward direction iterates cancel. -/
theorem direction_iterate_next_prev (d : Direction α) (t : Nat) (p : α) :
    iterate d.next t (iterate d.prev t p) = p := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change d.next (iterate d.next t (d.prev (iterate d.prev t p))) = p
      rw [← iterate_apply_comm d.next t, d.next_prev, ih]

/-- East occupancy after a moving prefix is the inverse translate of its
initial occupancy. Only the rounds strictly before t are assumed to move. -/
theorem allMove_iterate_east_iff (east north : Direction α) (s : Config α)
    (t : Nat) (hm : ∀ u < t, AllMove east north (iterate (step east north) u s))
    (p : α) :
    iterate (step east north) t s p = .east ↔
      s (iterate east.prev t p) = .east := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
      change step east north (iterate (step east north) t s) p = .east ↔ _
      rw [allMove_step_east_iff east north _ (hm t (by omega))]
      have he := ih (fun u hu => hm u (by omega)) (east.prev p)
      simpa only [iterate, iterate_apply_comm] using he

/-- North occupancy after a moving prefix is the inverse translate of its
initial occupancy, with east-then-north timing inherited from `AllMove`. -/
theorem allMove_iterate_north_iff (east north : Direction α) (s : Config α)
    (t : Nat) (hm : ∀ u < t, AllMove east north (iterate (step east north) u s))
    (p : α) :
    iterate (step east north) t s p = .north ↔
      s (iterate north.prev t p) = .north := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
      change step east north (iterate (step east north) t s) p = .north ↔ _
      rw [allMove_step_north_iff east north _ (hm t (by omega))]
      have hn := ih (fun u hu => hm u (by omega)) (north.prev p)
      simpa only [iterate, iterate_apply_comm] using hn

/-- At its forward-translated location, east occupancy is exactly its initial
occupancy after any prefix of fully moving rounds. -/
theorem allMove_iterate_east_at (east north : Direction α) (s : Config α)
    (t : Nat) (hm : ∀ u < t, AllMove east north (iterate (step east north) u s))
    (p : α) :
    iterate (step east north) t s (iterate east.next t p) = .east ↔ s p = .east := by
  rw [allMove_iterate_east_iff east north s t hm, direction_iterate_prev_next]

/-- At its forward-translated location, north occupancy is exactly its initial
occupancy after any prefix of fully moving rounds. -/
theorem allMove_iterate_north_at (east north : Direction α) (s : Config α)
    (t : Nat) (hm : ∀ u < t, AllMove east north (iterate (step east north) u s))
    (p : α) :
    iterate (step east north) t s (iterate north.next t p) = .north ↔ s p = .north := by
  rw [allMove_iterate_north_iff east north s t hm, direction_iterate_prev_next]

end BML
