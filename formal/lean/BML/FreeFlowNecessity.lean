import BML.FreeFlowConditions
import BML.Rigid
import BML.Encounters

/-!
Necessity of the static CLASSIC free-flow conditions from a bounded moving
prefix.  Equal phase classes force two rigidly moving species to occupy one
site within a common period.  The next phase class forces an occupied east
target before the end of that period.
-/
namespace BML

/-- Moving throughout the first lcm complete rounds already forces every
static adjacency and phase-separation condition. -/
theorem staticFree_of_allMove_before_lcm (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h))
    (hm : ∀ t, t < Nat.lcm w h →
      AllMove (eastDirection w h hw) (northDirection w h hh)
        (iterate (torusStep w h hw hh) t s)) :
    StaticFree w h hw hh s := by
  let east := eastDirection w h hw
  let north := northDirection w h hh
  have hzero : AllMove east north s := hm 0 (Nat.lcm_pos hw hh)
  refine ⟨?_, ?_, ?_⟩
  · intro p hp hnext
    have hz := (hzero.1 p hp).2
    rw [hnext] at hz
    cases hz
  · intro p hp hnext
    have hp' := (other_species_unchanged east .east s p .north
      (by decide) (by decide)).mpr hp
    have hnext' := (other_species_unchanged east .east s (north.next p) .north
      (by decide) (by decide)).mpr hnext
    have hz := (hzero.2 p hp').2
    rw [hnext'] at hz
    cases hz
  · intro e q he hq
    constructor
    · intro hphase
      obtain ⟨t, _, ht, hmeet⟩ :=
        (same_phase_encounter_pos_iff w h hw hh e q).mpr hphase.symm
      have hprefix : ∀ u < t, AllMove east north (iterate (step east north) u s) := by
        intro u hu
        exact hm u (Nat.lt_of_lt_of_le hu ht)
      have he' := (allMove_iterate_east_at east north s t hprefix e).mpr he
      have hq' := (allMove_iterate_north_at east north s t hprefix q).mpr hq
      rw [hmeet, hq'] at he'
      cases he'
    · intro hphase
      obtain ⟨t, ht, hmeet⟩ :=
        (next_phase_encounter_lt_iff w h hw hh e q).mpr hphase
      have hprefix : ∀ u < t, AllMove east north (iterate (step east north) u s) := by
        intro u hu
        exact hm u (Nat.lt_trans hu ht)
      have he' := (allMove_iterate_east_at east north s t hprefix e).mpr he
      have hq' := (allMove_iterate_north_at east north s t hprefix q).mpr hq
      have hz := ((hm t ht).1 (iterate east.next t e) he').2
      rw [hmeet] at hz
      change iterate (step east north) t s (iterate north.next t q) = .empty at hz
      rw [hq'] at hz
      cases hz

end BML
