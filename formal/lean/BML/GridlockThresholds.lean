import BML.NonGridlock

/-!
Exact full-density threshold for forced CLASSIC gridlock. The universal claim
is restricted to feasible populations; above the torus area there are no
configurations, so an unrestricted universal statement would hold vacuously.
-/
namespace BML

/-- Occupied-list count equals the torus area exactly when every cell is occupied. -/
theorem carCount_eq_area_iff (w h : Nat) (s : Config (Position w h)) :
    carCount w h s = w * h ↔ ∀ p, s p ≠ .empty := by
  unfold carCount occupiedCells
  rw [← positions_length w h, List.length_filter_eq_length_iff]
  constructor
  · intro hall p
    exact of_decide_eq_true (hall p (mem_positions w h p))
  · intro hall p _
    exact decide_eq_true (hall p)

/-- On a positive torus, full occupancy gives a nonempty frozen configuration. -/
theorem full_carCount_is_jam (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (hcount : carCount w h s = w * h) :
    Jam (eastDirection w h hw) (northDirection w h hh) s := by
  have hfull := (carCount_eq_area_iff w h s).mp hcount
  exact ⟨⟨(⟨0, hw⟩, ⟨0, hh⟩), hfull _⟩,
    fully_occupied_frozen _ _ s hfull⟩

/-- Among feasible populations on a positive torus, every initial configuration
reaches a nonempty jam exactly at full occupancy. The area bound prevents the
universal quantifier from becoming vacuous at an impossible population. -/
theorem forced_eventual_jam_iff (w h n : Nat) (hw : 0 < w) (hh : 0 < h)
    (hn : n ≤ w * h) :
    (∀ s : Config (Position w h), carCount w h s = n →
      ∃ t, Jam (eastDirection w h hw) (northDirection w h hh)
        (iterate (torusStep w h hw hh) t s)) ↔ n = w * h := by
  constructor
  · intro hforced
    by_cases hfull : n = w * h
    · exact hfull
    · have hproper : n < w * h := by omega
      obtain ⟨s, hcount, hnever⟩ := exists_never_jam_with_count w h hw hh n hproper
      obtain ⟨t, hjam⟩ := hforced s hcount
      exact False.elim (hnever t hjam)
  · intro hfull s hcount
    refine ⟨0, ?_⟩
    exact full_carCount_is_jam w h hw hh s (hcount.trans hfull)

end BML
