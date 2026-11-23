import BML.SmallUnjamming

/-! The geometric CLASSIC un-jamming classification, including both small-side exclusions. -/
namespace BML.Gated

open Packed

variable {w h : Nat}

private theorem layout_22 : (torusLayout 2 2).Valid (by decide : 0 < 2) (by decide : 0 < 2) :=
  ⟨by decide, by decide, by decide, by decide⟩

private theorem layout_23 : (torusLayout 2 3).Valid (by decide : 0 < 2) (by decide : 0 < 3) :=
  ⟨by decide, by decide, by decide, by decide⟩

private theorem layout_32 : (torusLayout 3 2).Valid (by decide : 0 < 3) (by decide : 0 < 2) :=
  ⟨by decide, by decide, by decide, by decide⟩

private theorem layout_33 : (torusLayout 3 3).Valid (by decide : 0 < 3) (by decide : 0 < 3) :=
  ⟨by decide, by decide, by decide, by decide⟩

-- Each finite check assigns every cell except the origin one of the three
-- CLASSIC cell values. The origin is the normalized site of the added car.
set_option maxHeartbeats 0 in
private theorem checked_22 :
    unjammingExclusionCheck (by decide : 0 < 2) (by decide : 0 < 2) (torusLayout 2 2) = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
private theorem checked_23 :
    unjammingExclusionCheck (by decide : 0 < 2) (by decide : 0 < 3) (torusLayout 2 3) = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
private theorem checked_32 :
    unjammingExclusionCheck (by decide : 0 < 3) (by decide : 0 < 2) (torusLayout 3 2) = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
private theorem checked_33 :
    unjammingExclusionCheck (by decide : 0 < 3) (by decide : 0 < 3) (torusLayout 3 3) = true :=
  by decide +kernel

/-- Exhaustive exclusion of genuine single-car un-jamming on 2×2, 2×3,
3×2 and 3×3 tori. -/
theorem no_genuine_unjamming_small (hw : 0 < w) (hh : 0 < h)
    (hwsmall : w = 2 ∨ w = 3) (hhsmall : h = 2 ∨ h = 3)
    (x y : Config (Position w h)) : ¬ GenuineUnjamming hw hh x y := by
  rcases hwsmall with rfl | rfl <;> rcases hhsmall with rfl | rfl
  · exact no_genuine_unjamming_of_check layout_22 checked_22 x y
  · exact no_genuine_unjamming_of_check layout_23 checked_23 x y
  · exact no_genuine_unjamming_of_check layout_32 checked_32 x y
  · exact no_genuine_unjamming_of_check layout_33 checked_33 x y

theorem no_genuine_unjamming_singleton (hw : 0 < w) (hh : 0 < h)
    (hthin : w = 1 ∨ h = 1) (x y : Config (Position w h)) :
    ¬ GenuineUnjamming hw hh x y := by
  rintro ⟨⟨p, _, hp, _, hs⟩, hx, hy, _⟩
  obtain ⟨t, ht⟩ := singleton_side_preserves_eventual_jam hw hh hthin p hp hs hx
  exact hy t ht

/-- Theorem U for the CLASSIC kernel and the original-car definition of
genuine un-jamming. -/
theorem genuine_unjamming_iff (hw : 0 < w) (hh : 0 < h) :
    (∃ x y, GenuineUnjamming hw hh x y) ↔ 2 ≤ min w h ∧ 4 ≤ max w h := by
  constructor
  · rintro ⟨x, y, hxy⟩
    have hthin : ¬ (w = 1 ∨ h = 1) :=
      fun h => no_genuine_unjamming_singleton hw hh h x y hxy
    have hw2 : 2 ≤ w := by omega
    have hh2 : 2 ≤ h := by omega
    refine ⟨by omega, ?_⟩
    by_cases hmax : 4 ≤ max w h
    · exact hmax
    · exact False.elim (no_genuine_unjamming_small hw hh (by omega) (by omega) x y hxy)
  · rintro ⟨hmin, hmax⟩
    exact exists_genuine_unjamming (by omega) (by omega) hmax


/-- Adding a car in a spare row prevents gridlock whenever both sides are
at least two. The original full row stays permanently blocked. -/
theorem exists_ordinary_unjamming (hw : 2 ≤ w) (hh : 2 ≤ h) :
    ∃ x y : Config (Position w h),
      (∃ p sp, x p = .empty ∧ y p = Species.cell sp ∧ ∀ q, q ≠ p → y q = x q) ∧
      EventuallyJammed (eastDirection w h (by omega)) (northDirection w h (by omega)) x ∧
      ∀ t, ¬ Jam (eastDirection w h (by omega)) (northDirection w h (by omega))
        (iterate (torusStep w h (by omega) (by omega)) t y) := by
  let c₀ : Fin w := ⟨0, by omega⟩
  let c₁ : Fin w := ⟨1, by omega⟩
  let r₀ : Fin h := ⟨0, by omega⟩
  let r₁ : Fin h := ⟨1, by omega⟩
  let p : Position w h := (c₀,r₁)
  let x : Config (Position w h) := fun q => if q.2 = r₀ then .east else .empty
  let y : Config (Position w h) := fun q => if q = p then .east else x q
  have hrow : r₁ ≠ r₀ := by
    intro h
    have he : 1 = 0 := congrArg Fin.val h
    omega
  have hcol : c₁ ≠ c₀ := by
    intro h
    have he : 1 = 0 := congrArg Fin.val h
    omega
  refine ⟨x, y, ⟨p, .east, by simp [x, p, hrow], by simp [y, Species.cell], ?_⟩, ?_, ?_⟩
  · intro q hq
    simp [y, hq]
  · refine ⟨0, ?_⟩
    change Jam (eastDirection w h (by omega)) (northDirection w h (by omega)) x
    refine ⟨⟨(c₀,r₀), by simp [x]⟩, ?_, ?_⟩
    · intro q hq
      change x q = .east at hq
      have hqrow : q.2 = r₀ := by
        by_cases hr : q.2 = r₀
        · exact hr
        · simp [x, hr] at hq
      change x (cyclicNext w (by omega) q.1, q.2) ≠ .empty
      simp [x, hqrow]
    · intro q hq
      change (if q.2 = r₀ then Cell.east else Cell.empty) = Cell.north at hq
      split at hq <;> cases hq
  · have hmix : EastMixedRow w h y r₁ := by
      refine ⟨?_, ⟨c₀, by simp [y, p]⟩, ⟨c₁, by simp [y, p, x, hrow, hcol]⟩⟩
      intro q
      simp only [y, x]
      split <;> first | decide | (split <;> decide)
    exact hmix.never_jam w h (by omega) (by omega) y

end BML.Gated
