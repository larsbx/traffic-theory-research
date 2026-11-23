import BML.FreeFlowConditions
import BML.Counting
import BML.FiniteSums

/-!
Same-species adjacency bounds in each lane. On a coprime rectangle the sole
phase class excludes mixed species, giving the sharp pure-direction bound.
-/
namespace BML

private theorem list_sum_flatMap_nat (xs : List α) (f : α → List Nat) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem speciesCount_eq_row_sums (w h : Nat) (sp : Species)
    (s : Config (Position w h)) :
    speciesCount w h sp s =
      sumFin h (fun y => sumFin w (fun x => if s (x,y) = sp.cell then 1 else 0)) := by
  simp [speciesCount, positions, sumFin, List.map_flatMap, list_sum_flatMap_nat,
    List.map_map, Function.comp_def]

theorem speciesCount_eq_column_sums (w h : Nat) (sp : Species)
    (s : Config (Position w h)) :
    speciesCount w h sp s =
      sumFin w (fun x => sumFin h (fun y => if s (x,y) = sp.cell then 1 else 0)) := by
  rw [speciesCount_eq_row_sums, sumFin_swap]

theorem staticFree_eastCount_le (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (hs : StaticFree w h hw hh s) :
    speciesCount w h .east s ≤ h * (w / 2) := by
  rw [speciesCount_eq_row_sums, ← sumFin_const h (w / 2)]
  apply sumFin_le
  intro y
  apply sumFin_le_half_of_adjacent w hw
  intro x
  have hadj := hs.1 (x,y)
  change s (x,y) = .east → s (cyclicNext w hw x,y) ≠ .east at hadj
  by_cases hx : s (x,y) = .east
  · simp [Species.cell, hx, hadj hx]
  · by_cases hn : s (cyclicNext w hw x,y) = .east <;> simp [Species.cell, hx, hn]

theorem staticFree_northCount_le (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (hs : StaticFree w h hw hh s) :
    speciesCount w h .north s ≤ w * (h / 2) := by
  rw [speciesCount_eq_column_sums, ← sumFin_const w (h / 2)]
  apply sumFin_le
  intro x
  apply sumFin_le_half_of_adjacent h hh
  intro y
  have hadj := hs.2.1 (x,y)
  change s (x,y) = .north → s (x,cyclicNext h hh y) ≠ .north at hadj
  by_cases hy : s (x,y) = .north
  · simp [Species.cell, hy, hadj hy]
  · by_cases hn : s (x,cyclicNext h hh y) = .north <;> simp [Species.cell, hy, hn]

/-- A free board on a coprime torus contains at most one species. -/
theorem staticFree_coprime_pure (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (hg : Nat.gcd w h = 1)
    (hs : StaticFree w h hw hh s) :
    (∀ p, s p ≠ .east) ∨ (∀ p, s p ≠ .north) := by
  classical
  by_cases he : ∃ e, s e = .east
  · right
    obtain ⟨e, he⟩ := he
    intro q hq
    have hsep := (hs.2.2 e q he hq).1
    have he0 := phaseClass_lt w h hw e
    have hq0 := phaseClass_lt w h hw q
    rw [hg] at he0 hq0
    exact hsep (by omega)
  · left
    intro p hp
    exact he ⟨p,hp⟩

theorem speciesCount_eq_zero_of_absent (w h : Nat) (sp : Species)
    (s : Config (Position w h)) (hs : ∀ p, s p ≠ sp.cell) :
    speciesCount w h sp s = 0 := by
  simp [speciesCount, hs, List.map_const', List.sum_replicate_nat]

theorem staticFree_coprime_carCount_le (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (hg : Nat.gcd w h = 1)
    (hs : StaticFree w h hw hh s) :
    carCount w h s ≤ max (h * (w / 2)) (w * (h / 2)) := by
  rw [carCount_eq_speciesCount]
  rcases staticFree_coprime_pure w h hw hh s hg hs with he | hn
  · rw [speciesCount_eq_zero_of_absent w h .east s he, Nat.zero_add]
    exact Nat.le_trans (staticFree_northCount_le w h hw hh s hs) (Nat.le_max_right _ _)
  · rw [speciesCount_eq_zero_of_absent w h .north s hn, Nat.add_zero]
    exact Nat.le_trans (staticFree_eastCount_le w h hw hh s hs) (Nat.le_max_left _ _)

end BML
