import BML.Cosets

/-!
Natural-time forms of the diagonal coset identity.  Signed orbit witnesses are
reduced modulo the common period, and the resulting times are related to the
actual cyclic diagonal step by the existing iteration theorem.
-/
namespace BML

/-- Reducing signed time modulo the least common multiple preserves the action. -/
theorem diagonalShift_emod_lcm (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (t : Int) (p : Position w h) :
    diagonalShift w h hw hh (t % (Nat.lcm w h : Int)) p =
      diagonalShift w h hw hh t p := by
  have hwm : (w : Int) ∣ (Nat.lcm w h : Int) :=
    Int.ofNat_dvd.mpr (Nat.dvd_lcm_left w h)
  have hhm : (h : Int) ∣ (Nat.lcm w h : Int) :=
    Int.ofNat_dvd.mpr (Nat.dvd_lcm_right w h)
  have ht := (diagonalShift_eq_iff w h hw hh t p
    (diagonalShift w h hw hh t p)).mp rfl
  apply (diagonalShift_eq_iff w h hw hh (t % (Nat.lcm w h : Int)) p
    (diagonalShift w h hw hh t p)).mpr
  constructor
  · rw [Int.emod_emod_of_dvd t hwm]
    exact ht.1
  · have he := (Int.emod_add_cancel_left
      (i := ((diagonalShift w h hw hh t p).2.val : Int) - p.2.val)).mpr
      (Int.emod_emod_of_dvd t hhm)
    exact he.trans ht.2

/-- A signed diagonal shift returns to its starting point precisely when both
coordinate sizes divide the time.  This does not depend on the starting point. -/
theorem diagonalShift_eq_self_iff (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (t : Int) (p : Position w h) :
    diagonalShift w h hw hh t p = p ↔
      (w : Int) ∣ t ∧ (h : Int) ∣ t := by
  rw [diagonalShift_eq_iff]
  simp only [Int.sub_self, Int.zero_emod, Int.zero_add, ← Int.dvd_iff_emod_eq_zero]

/-- The exact return times of the actual diagonal step are the multiples of lcm. -/
theorem iterate_diagonalStep_eq_self_iff (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (t : Nat) (p : Position w h) :
    iterate (diagonalStep w h hw hh) t p = p ↔ Nat.lcm w h ∣ t := by
  rw [iterate_diagonalStep, diagonalShift_eq_self_iff]
  simp only [Int.ofNat_dvd, Nat.lcm_dvd_iff]

/-- One least-common-multiple period returns every point to itself. -/
theorem iterate_diagonalStep_lcm (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (p : Position w h) :
    iterate (diagonalStep w h hw hh) (Nat.lcm w h) p = p := by
  exact (iterate_diagonalStep_eq_self_iff w h hw hh (Nat.lcm w h) p).mpr
    (Nat.dvd_refl (Nat.lcm w h))

/-- The coset identity has a natural witness in the half-open period window. -/
theorem diagonalStep_reaches_lt_iff (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (p q : Position w h) :
    (∃ t : Nat, t < Nat.lcm w h ∧ iterate (diagonalStep w h hw hh) t p = q) ↔
      phaseClass w h p = phaseClass w h q := by
  constructor
  · rintro ⟨t, _, ht⟩
    apply (diagonalShift_exists_iff w h hw hh p q).mp
    exact ⟨(t : Int), (iterate_diagonalStep w h hw hh t p).symm.trans ht⟩
  · intro he
    obtain ⟨t, ht⟩ := (diagonalShift_exists_iff w h hw hh p q).mpr he
    have hpos : (0 : Int) < (Nat.lcm w h : Int) := by
      exact_mod_cast Nat.lcm_pos hw hh
    have hnonneg := Int.emod_nonneg t (by omega : (Nat.lcm w h : Int) ≠ 0)
    have hlt := Int.emod_lt_of_pos t hpos
    have hcast : (((t % (Nat.lcm w h : Int)).toNat : Nat) : Int) =
        t % (Nat.lcm w h : Int) := by omega
    refine ⟨(t % (Nat.lcm w h : Int)).toNat, by omega, ?_⟩
    rw [iterate_diagonalStep, hcast]
    exact (diagonalShift_emod_lcm w h hw hh t p).trans ht

/-- Unbounded natural reachability gives the same phase-class equivalence. -/
theorem diagonalStep_reaches_iff (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (p q : Position w h) :
    (∃ t : Nat, iterate (diagonalStep w h hw hh) t p = q) ↔
      phaseClass w h p = phaseClass w h q := by
  constructor
  · rintro ⟨t, ht⟩
    apply (diagonalShift_exists_iff w h hw hh p q).mp
    exact ⟨(t : Int), (iterate_diagonalStep w h hw hh t p).symm.trans ht⟩
  · intro he
    obtain ⟨t, _, ht⟩ := (diagonalStep_reaches_lt_iff w h hw hh p q).mpr he
    exact ⟨t, ht⟩

/-- The time-zero witness can be replaced by one complete period, giving a
strictly positive witness in the closed period window. -/
theorem diagonalStep_reaches_pos_iff (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (p q : Position w h) :
    (∃ t : Nat, 0 < t ∧ t ≤ Nat.lcm w h ∧
      iterate (diagonalStep w h hw hh) t p = q) ↔
      phaseClass w h p = phaseClass w h q := by
  constructor
  · rintro ⟨t, _, _, ht⟩
    exact (diagonalStep_reaches_iff w h hw hh p q).mp ⟨t, ht⟩
  · intro he
    obtain ⟨t, htlt, ht⟩ := (diagonalStep_reaches_lt_iff w h hw hh p q).mpr he
    by_cases hz : t = 0
    · subst t
      have hpq : p = q := ht
      exact ⟨Nat.lcm w h, Nat.lcm_pos hw hh, Nat.le_refl _,
        (iterate_diagonalStep_lcm w h hw hh p).trans hpq⟩
    · exact ⟨t, by omega, Nat.le_of_lt htlt, ht⟩

/-- The phase-one translated coset has a natural witness before the end of a
period, starting at the actual east successor of the source point. -/
theorem east_diagonalStep_reaches_lt_iff (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (p q : Position w h) :
    (∃ t : Nat, t < Nat.lcm w h ∧
      iterate (diagonalStep w h hw hh) t ((eastDirection w h hw).next p) = q) ↔
      phaseClass w h q = (phaseClass w h p + 1) % Nat.gcd w h := by
  rw [diagonalStep_reaches_lt_iff, phaseClass_east]
  exact eq_comm

/-- The translated coset also has a strictly positive witness within one
period, including when the target is the east successor itself. -/
theorem east_diagonalStep_reaches_pos_iff (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (p q : Position w h) :
    (∃ t : Nat, 0 < t ∧ t ≤ Nat.lcm w h ∧
      iterate (diagonalStep w h hw hh) t ((eastDirection w h hw).next p) = q) ↔
      phaseClass w h q = (phaseClass w h p + 1) % Nat.gcd w h := by
  rw [diagonalStep_reaches_pos_iff, phaseClass_east]
  exact eq_comm

end BML
