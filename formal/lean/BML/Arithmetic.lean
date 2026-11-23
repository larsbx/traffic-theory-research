import BML.Kernel

/-!
Arithmetic components used by the complete G1 proof in Gridlock.lean and
the complete free-flow capacity proof in FreeMaximum.lean.
-/
namespace BML

/-- A nonzero nonnegative winding around a positive torus costs at least min(W,H). -/
theorem winding_length_lower_bound (w h a b : Nat)
    (ha : w ∣ a) (hb : h ∣ b) (hne : 0 < a + b) : min w h ≤ a + b := by
  by_cases haz : a = 0
  · have hbp : 0 < b := by omega
    have hhb := Nat.le_of_dvd hbp hb
    have hmin := Nat.min_le_right w h
    omega
  · have hap : 0 < a := by omega
    have hwa := Nat.le_of_dvd hap ha
    have hmin := Nat.min_le_left w h
    omega

/-- The equivalent nested-floor expression for the free-flow class capacity. -/
def freeClasses (g : Nat) : Nat := (g + g / 3) / 2

theorem freeClasses_eq_two_thirds (g : Nat) : freeClasses g = (2 * g) / 3 := by
  unfold freeClasses
  omega

theorem freeClasses_le_two_thirds (g : Nat) : 3 * freeClasses g ≤ 2 * g := by
  rw [freeClasses_eq_two_thirds]
  omega

theorem freeClasses_attains_two_thirds_iff (g : Nat) :
    3 * freeClasses g = 2 * g ↔ 3 ∣ g := by
  rw [freeClasses_eq_two_thirds, Nat.dvd_iff_mod_eq_zero]
  omega

end BML
