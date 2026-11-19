import BML.Torus

/-!
Arithmetic and reachability of the positive cyclic coordinate used by the
CLASSIC finite-torus kernel. These statements describe the existing cyclicNext
function directly and do not depend on TRAIN movement semantics.
-/
namespace BML

/-- The piecewise cyclic successor is addition by one modulo the coordinate size. -/
theorem cyclicNext_val (n : Nat) (hn : 0 < n) (i : Fin n) :
    (cyclicNext n hn i).val = (i.val + 1) % n := by
  by_cases hl : i.val + 1 < n
  · simp [cyclicNext, hl, Nat.mod_eq_of_lt hl]
  · have he : i.val + 1 = n := by have hi := i.isLt; omega
    simp [cyclicNext, he]

/-- Iterated successor adds the number of steps modulo the coordinate size. -/
theorem iterate_cyclicNext_val (n : Nat) (hn : 0 < n) (k : Nat) (i : Fin n) :
    (iterate (cyclicNext n hn) k i).val = (i.val + k) % n := by
  induction k with
  | zero => simp [iterate, Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    simp only [iterate, cyclicNext_val, ih, Nat.mod_add_mod]
    rw [Nat.add_assoc]

/-- A full traversal returns to its starting coordinate, including singleton rings. -/
theorem iterate_cyclicNext_period (n : Nat) (hn : 0 < n) (i : Fin n) :
    iterate (cyclicNext n hn) n i = i := by
  apply Fin.ext
  rw [iterate_cyclicNext_val, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

/-- Every coordinate is reached from every other coordinate in fewer than n steps. -/
theorem cyclicNext_reaches_lt (n : Nat) (hn : 0 < n) (i j : Fin n) :
    ∃ k, k < n ∧ iterate (cyclicNext n hn) k i = j := by
  have hi := i.isLt
  have hj := j.isLt
  by_cases hij : i.val ≤ j.val
  · refine ⟨j.val - i.val, by omega, ?_⟩
    apply Fin.ext
    rw [iterate_cyclicNext_val]
    have he : i.val + (j.val - i.val) = j.val := by omega
    rw [he, Nat.mod_eq_of_lt hj]
  · refine ⟨n + j.val - i.val, by omega, ?_⟩
    apply Fin.ext
    rw [iterate_cyclicNext_val]
    have he : i.val + (n + j.val - i.val) = n + j.val := by omega
    rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt hj]

/-- Unbounded form convenient for propagating local properties around a ring. -/
theorem cyclicNext_reaches (n : Nat) (hn : 0 < n) (i j : Fin n) :
    ∃ k, iterate (cyclicNext n hn) k i = j := by
  obtain ⟨k, _, hk⟩ := cyclicNext_reaches_lt n hn i j
  exact ⟨k, hk⟩

end BML
