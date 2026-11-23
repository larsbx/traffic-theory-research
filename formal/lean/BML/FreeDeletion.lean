import BML.FreeFlowConditions
import BML.Counting

/-!
Deleting cars preserves the static free-flow conditions. The executable
prefix construction realizes every population below any free configuration.
-/
namespace BML

/-- Every retained car has the same species and position in the original board. -/
def CarSubconfig {α : Type} (small large : Config α) : Prop :=
  ∀ p, small p ≠ .empty → small p = large p

theorem CarSubconfig.species {α : Type} {small large : Config α}
    (hs : CarSubconfig small large) (sp : Species) (p : α)
    (hp : small p = sp.cell) : large p = sp.cell := by
  have hn : small p ≠ .empty := by rw [hp]; exact sp.cell_ne_empty
  rw [← hs p hn]
  exact hp

/-- Free-flow constraints are hereditary under arbitrary species-preserving deletion. -/
theorem staticFree_of_subconfig (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (small large : Config (Position w h)) (hsub : CarSubconfig small large)
    (hfree : StaticFree w h hw hh large) : StaticFree w h hw hh small := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp hnext
    exact hfree.1 p (hsub.species .east p hp)
      (hsub.species .east _ hnext)
  · intro p hp hnext
    exact hfree.2.1 p (hsub.species .north p hp)
      (hsub.species .north _ hnext)
  · intro e q he hn
    exact hfree.2.2 e q (hsub.species .east e he) (hsub.species .north q hn)

/-- Retain the first n occupied positions in the actual row-major enumeration. -/
def thinConfig (w h : Nat) (s : Config (Position w h)) (n : Nat) :
    Config (Position w h) :=
  fun p => if p ∈ (occupiedCells w h s).take n then s p else .empty

theorem thinConfig_subconfig (w h : Nat) (s : Config (Position w h)) (n : Nat) :
    CarSubconfig (thinConfig w h s n) s := by
  intro p hp
  unfold thinConfig at *
  split at hp
  · rename_i hmem
    simp [hmem]
  · exact False.elim (hp rfl)

theorem thinConfig_occupied_iff (w h : Nat) (s : Config (Position w h))
    (n : Nat) (p : Position w h) :
    thinConfig w h s n p ≠ .empty ↔ p ∈ (occupiedCells w h s).take n := by
  by_cases hp : p ∈ (occupiedCells w h s).take n
  · have hs : s p ≠ .empty := (mem_occupiedCells w h s p).mp (List.mem_of_mem_take hp)
    simp [thinConfig, hp, hs]
  · simp [thinConfig, hp]

/-- The prefix construction has exactly min(n, original population) cars. -/
theorem thinConfig_carCount (w h : Nat) (s : Config (Position w h)) (n : Nat) :
    carCount w h (thinConfig w h s n) = min n (carCount w h s) := by
  have hp : (occupiedCells w h (thinConfig w h s n)).Perm
      ((occupiedCells w h s).take n) := by
    apply (List.perm_ext_iff_of_nodup (occupiedCells_nodup w h _)
      ((occupiedCells_nodup w h s).take)).mpr
    intro p
    rw [mem_occupiedCells, thinConfig_occupied_iff]
  simpa only [carCount, List.length_take] using hp.length_eq

theorem thinConfig_staticFree (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (hs : StaticFree w h hw hh s) (n : Nat) :
    StaticFree w h hw hh (thinConfig w h s n) :=
  staticFree_of_subconfig w h hw hh _ s (thinConfig_subconfig w h s n) hs

theorem exists_staticFree_with_smaller_count (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (hs : StaticFree w h hw hh s)
    (n : Nat) (hn : n ≤ carCount w h s) :
    ∃ t : Config (Position w h), StaticFree w h hw hh t ∧ carCount w h t = n := by
  refine ⟨thinConfig w h s n, thinConfig_staticFree w h hw hh s hs n, ?_⟩
  rw [thinConfig_carCount, Nat.min_eq_left hn]

end BML
