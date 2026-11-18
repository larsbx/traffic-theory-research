import Std

/-!
Integer congruences for the CLASSIC finite-torus coset argument.  The arithmetic
is proved directly in Lean's core library: no external number-theory library or
assumed Bézout interface is used.
-/
namespace BML

/-- Bézout coefficients for natural moduli, interpreted over the integers. -/
theorem nat_gcd_bezout (w h : Nat) :
    ∃ u v : Int, (Nat.gcd w h : Int) = (w : Int) * u + (h : Int) * v := by
  induction w, h using Nat.gcd.induction with
  | H0 h =>
      exact ⟨0, 1, by simp⟩
  | H1 w h hw ih =>
      obtain ⟨u, v, huv⟩ := ih
      have hdiv : (h % w : Int) + (w : Int) * (h / w : Int) = (h : Int) := by
        exact_mod_cast Nat.mod_add_div h w
      refine ⟨v - (h / w : Int) * u, u, ?_⟩
      rw [Nat.gcd_rec]
      grind

/-- A common-residue problem is solvable exactly when the gcd divides the sum. -/
theorem coset_dvd_iff (w h : Nat) (a b : Int) :
    (Nat.gcd w h : Int) ∣ (a + b) ↔
      ∃ t : Int, (w : Int) ∣ (t - a) ∧ (h : Int) ∣ (b + t) := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨u, v, huv⟩ := nat_gcd_bezout w h
    refine ⟨a - (w : Int) * (u * k), ?_, ?_⟩
    · refine ⟨-(u * k), ?_⟩
      grind
    · refine ⟨v * k, ?_⟩
      grind
  · rintro ⟨t, hta, hbt⟩
    have hgw : (Nat.gcd w h : Int) ∣ (w : Int) :=
      Int.ofNat_dvd.mpr (Nat.gcd_dvd_left w h)
    have hgh : (Nat.gcd w h : Int) ∣ (h : Int) :=
      Int.ofNat_dvd.mpr (Nat.gcd_dvd_right w h)
    have hd := Int.dvd_sub (Int.dvd_trans hgh hbt) (Int.dvd_trans hgw hta)
    have he : (b + t) - (t - a) = a + b := by omega
    simpa only [he] using hd

/-- The signed congruence form needed for arbitrary differences of torus points. -/
theorem coset_int_iff (w h : Nat) (_hw : 0 < w) (_hh : 0 < h) (a b : Int) :
    (a + b) % (Nat.gcd w h : Int) = 0 ↔
      ∃ t : Int, t % (w : Int) = a % (w : Int) ∧ (b + t) % (h : Int) = 0 := by
  rw [← Int.dvd_iff_emod_eq_zero, coset_dvd_iff]
  simp only [Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]

/-- The representative-pair statement from the blueprint.  The bound on a
allows its residue to be written as a itself; the bound on b records that both
coordinates are torus representatives. -/
theorem coset_iff (w h a b : Nat) (hw : 0 < w) (hh : 0 < h)
    (ha : a < w) (_hb : b < h) :
    (a + b) % Nat.gcd w h = 0 ↔
      ∃ t : Int, t % (w : Int) = (a : Int) ∧ ((b : Int) + t) % (h : Int) = 0 := by
  simpa only [← Int.natCast_add, ← Int.natCast_emod, Nat.mod_eq_of_lt ha,
    Int.natCast_eq_zero] using coset_int_iff w h hw hh (a : Int) (b : Int)

end BML
