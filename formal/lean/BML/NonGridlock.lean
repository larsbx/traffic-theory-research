import BML.Enumeration
import BML.Lanes

/-!
CLASSIC G2: every population strictly below the torus area admits a
configuration that never jams. A column-major east-only prefix has a mixed
row when the width is at least two. Width-one tori use a north-only prefix.
The zero population is handled separately: the empty fixed point is not Jam.
-/
namespace BML

/-- Fill a column-major prefix with east cars. -/
def eastColumnPrefix (w h n : Nat) : Config (Position w h) :=
  fun p => if p.1.val * h + p.2.val < n then .east else .empty

/-- Fill a row-major prefix with north cars. -/
def northRowPrefix (w h n : Nat) : Config (Position w h) :=
  fun p => if p.1.val + w * p.2.val < n then .north else .empty

/-- An explicit never-jamming configuration at every sub-full population.
The definition is total; the theorems assume positive dimensions and n < w*h. -/
def nonGridlockWith (w h n : Nat) : Config (Position w h) :=
  if 2 ≤ w then eastColumnPrefix w h n else northRowPrefix w h n

theorem eastColumnPrefix_carCount (w h n : Nat) (hh : 0 < h) (hn : n ≤ w * h) :
    carCount w h (eastColumnPrefix w h n) = n := by
  apply carCount_of_rank w h (h*w) (eastColumnPrefix w h n)
    (fun p => rowMajorRank h w (p.2, p.1))
    (fun i => let p := rowMajorPosition h w hh i; (p.2, p.1))
    (by intro p; simp)
    (by intro i; exact rowMajorRank_position h w hh i) n
    (by simpa only [Nat.mul_comm] using hn)
  intro p
  simp [eastColumnPrefix, Nat.mul_comm, Nat.add_comm]

theorem northRowPrefix_carCount (w h n : Nat) (hw : 0 < w) (hn : n ≤ w * h) :
    carCount w h (northRowPrefix w h n) = n := by
  apply carCount_of_rank w h (w*h) (northRowPrefix w h n)
    (rowMajorRank w h) (rowMajorPosition w h hw)
    (rowMajorPosition_rank w h hw) (rowMajorRank_position w h hw) n hn
  intro p
  simp [northRowPrefix]

/-- In a nonempty proper column-major prefix, either the first or last row
contains both an east car and a hole. -/
theorem eastColumnPrefix_mixed_row (w h n : Nat) (hw : 2 ≤ w) (hh : 0 < h)
    (hpos : 0 < n) (hn : n < w * h) :
    ∃ y, EastMixedRow w h (eastColumnPrefix w h n) y := by
  have hwp : 0 < w := by omega
  have hlast : (w - 1) * h + h = w * h := by
    calc
      (w - 1) * h + h = (w - 1 + 1) * h := by simp [Nat.add_mul]
      _ = w * h := by rw [Nat.sub_add_cancel hwp]
  have hfirst : h ≤ (w - 1) * h := by
    simpa using Nat.mul_le_mul_right h (show 1 ≤ w - 1 by omega)
  have honly : ∀ p, eastColumnPrefix w h n p ≠ .north := by
    intro p
    unfold eastColumnPrefix
    split <;> decide
  by_cases hcut : n ≤ (w - 1) * h
  · refine ⟨⟨0, hh⟩, honly, ?_, ?_⟩
    · exact ⟨⟨0, hwp⟩, by simp [eastColumnPrefix, hpos]⟩
    · exact ⟨⟨w - 1, by omega⟩, by simp [eastColumnPrefix, Nat.not_lt.mpr hcut]⟩
  · refine ⟨⟨h - 1, by omega⟩, honly, ?_, ?_⟩
    · have hc : h - 1 < n := by omega
      exact ⟨⟨0, hwp⟩, by simp [eastColumnPrefix, hc]⟩
    · have he : ¬ ((w - 1) * h + (h - 1) < n) := by omega
      exact ⟨⟨w - 1, by omega⟩, by simp [eastColumnPrefix, he]⟩

/-- A nonempty proper prefix in a width-one torus leaves its sole column mixed. -/
theorem northRowPrefix_one_mixed_column (h n : Nat) (hh : 0 < h)
    (hpos : 0 < n) (hn : n < h) :
    NorthMixedColumn 1 h (northRowPrefix 1 h n) ⟨0, by decide⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    unfold northRowPrefix
    split <;> decide
  · exact ⟨⟨0, hh⟩, by simp [northRowPrefix, hpos]⟩
  · have he : ¬ (h - 1 < n) := by omega
    exact ⟨⟨h - 1, by omega⟩, by simp [northRowPrefix, he]⟩

@[simp] theorem nonGridlockWith_zero (w h : Nat) :
    nonGridlockWith w h 0 = (fun _ => .empty) := by
  unfold nonGridlockWith
  split <;> funext p <;> simp [eastColumnPrefix, northRowPrefix]

/-- The executable G2 constructor contains exactly the requested number of cars. -/
theorem nonGridlockWith_carCount (w h n : Nat) (hw : 0 < w) (hh : 0 < h)
    (hn : n < w * h) : carCount w h (nonGridlockWith w h n) = n := by
  unfold nonGridlockWith
  split
  · exact eastColumnPrefix_carCount w h n hh (Nat.le_of_lt hn)
  · exact northRowPrefix_carCount w h n hw (Nat.le_of_lt hn)

/-- No finite-time iterate of the executable G2 construction is jammed. -/
theorem nonGridlockWith_never_jam (w h n : Nat) (hw : 0 < w) (hh : 0 < h)
    (hn : n < w * h) (t : Nat) :
    ¬ Jam (eastDirection w h hw) (northDirection w h hh)
      (iterate (torusStep w h hw hh) t (nonGridlockWith w h n)) := by
  by_cases hz : n = 0
  · subst n
    rw [nonGridlockWith_zero]
    rw [iterate_eq_of_fixed (torusStep w h hw hh) (fun _ => .empty)
      (empty_fixed (eastDirection w h hw) (northDirection w h hh)) t]
    exact empty_not_jam _ _
  · have hpos : 0 < n := by omega
    by_cases hw2 : 2 ≤ w
    · rw [nonGridlockWith, ite_eq_left hw2]
      obtain ⟨y, hmix⟩ := eastColumnPrefix_mixed_row w h n hw2 hh hpos hn
      exact EastMixedRow.never_jam w h hw hh _ y hmix t
    · have hw1 : w = 1 := by omega
      subst w
      rw [nonGridlockWith, ite_eq_right (by omega : ¬ 2 ≤ 1)]
      have hmix := northRowPrefix_one_mixed_column h n hh hpos (by simpa using hn)
      exact NorthMixedColumn.never_jam 1 h hw hh _ _ hmix t

/-- CLASSIC G2, with exact population and an unbounded-time conclusion. -/
theorem exists_never_jam_with_count (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (n : Nat) (hn : n < w * h) :
    ∃ s, carCount w h s = n ∧ ∀ t,
      ¬ Jam (eastDirection w h hw) (northDirection w h hh)
        (iterate (torusStep w h hw hh) t s) := by
  exact ⟨nonGridlockWith w h n, nonGridlockWith_carCount w h n hw hh hn,
    nonGridlockWith_never_jam w h n hw hh hn⟩

end BML
