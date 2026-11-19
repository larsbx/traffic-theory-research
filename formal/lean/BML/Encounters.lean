import BML.CosetTimes

/-!
Coordinate encounter identities for the rigid-motion bridge.  These statements
use the existing east and north cyclic maps and do not assume traffic motion.
-/
namespace BML

/-- Forward east iteration is the existing signed cyclic action at natural time. -/
theorem iterate_east_eq (w h : Nat) (hw : 0 < w) (t : Nat)
    (p : Position w h) :
    iterate (eastDirection w h hw).next t p =
      (cyclicShift w hw (t : Int) p.1, p.2) := by
  induction t with
  | zero => simp [iterate]
  | succ t ih =>
      rw [iterate, ih]
      change (cyclicNext w hw (cyclicShift w hw (t : Int) p.1), p.2) = _
      rw [← cyclicShift_one, cyclicShift_add]
      congr 2
      omega

/-- Forward north iteration is the existing signed cyclic action at natural time. -/
theorem iterate_north_eq (w h : Nat) (hh : 0 < h) (t : Nat)
    (p : Position w h) :
    iterate (northDirection w h hh).next t p =
      (p.1, cyclicShift h hh (t : Int) p.2) := by
  induction t with
  | zero => simp [iterate]
  | succ t ih =>
      rw [iterate, ih]
      change (p.1, cyclicNext h hh (cyclicShift h hh (t : Int) p.2)) = _
      rw [← cyclicShift_one, cyclicShift_add]
      congr 2
      omega

/-- Equality after a backward shift is equivalent to forward equality in the
opposite order. -/
theorem cyclicShift_neg_eq_forward_iff (n : Nat) (hn : 0 < n) (t : Int)
    (i j : Fin n) : cyclicShift n hn (-t) i = j ↔ i = cyclicShift n hn t j := by
  constructor
  · intro he
    have hh := congrArg (cyclicShift n hn t) he
    simpa only [cyclicShift_add, show t + -t = 0 by omega, cyclicShift_zero] using hh
  · intro he
    rw [he, cyclicShift_add, show -t + t = 0 by omega, cyclicShift_zero]

/-- A diagonal displacement is exactly equality of the forward east and north
positions at the same natural time. -/
theorem diagonal_encounter_iff (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (t : Nat) (e q : Position w h) :
    iterate (diagonalStep w h hw hh) t e = q ↔
      iterate (eastDirection w h hw).next t e =
        iterate (northDirection w h hh).next t q := by
  rw [iterate_diagonalStep, iterate_east_eq, iterate_north_eq]
  change (cyclicShift w hw (t : Int) e.1, cyclicShift h hh (-(t : Int)) e.2) = q ↔ _
  rw [Prod.ext_iff, Prod.ext_iff, cyclicShift_neg_eq_forward_iff]

/-- Moving the initial east point once corresponds to the east target at
time t, including t=0. -/
theorem east_diagonal_encounter_iff (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (t : Nat) (e q : Position w h) :
    iterate (diagonalStep w h hw hh) t ((eastDirection w h hw).next e) = q ↔
      (eastDirection w h hw).next (iterate (eastDirection w h hw).next t e) =
        iterate (northDirection w h hh).next t q := by
  rw [diagonal_encounter_iff]
  have he : iterate (eastDirection w h hw).next t ((eastDirection w h hw).next e) =
      (eastDirection w h hw).next (iterate (eastDirection w h hw).next t e) := by
    rw [iterate_east_eq, iterate_east_eq]
    change (cyclicShift w hw (t : Int) (cyclicNext w hw e.1), e.2) =
      (cyclicNext w hw (cyclicShift w hw (t : Int) e.1), e.2)
    rw [← cyclicShift_one, ← cyclicShift_one, cyclicShift_add, cyclicShift_add,
      Int.add_comm (t : Int) 1]
  rw [he]

/-- Equal phase classes give a strictly positive meeting time within one
least-common-multiple period. -/
theorem same_phase_encounter_pos_iff (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (e q : Position w h) :
    (∃ t : Nat, 0 < t ∧ t ≤ Nat.lcm w h ∧
      iterate (eastDirection w h hw).next t e =
        iterate (northDirection w h hh).next t q) ↔
      phaseClass w h e = phaseClass w h q := by
  simp only [← diagonal_encounter_iff]
  exact diagonalStep_reaches_pos_iff w h hw hh e q

/-- The next phase class gives an east-target encounter before the end of the
period, with the time-zero case retained. -/
theorem next_phase_encounter_lt_iff (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (e q : Position w h) :
    (∃ t : Nat, t < Nat.lcm w h ∧
      (eastDirection w h hw).next (iterate (eastDirection w h hw).next t e) =
        iterate (northDirection w h hh).next t q) ↔
      phaseClass w h q = (phaseClass w h e + 1) % Nat.gcd w h := by
  simp only [← east_diagonal_encounter_iff]
  exact east_diagonalStep_reaches_lt_iff w h hw hh e q

/-- One cyclic north step increments the same phase class as an east step. -/
theorem phaseClass_north (w h : Nat) (hh : 0 < h) (p : Position w h) :
    phaseClass w h ((northDirection w h hh).next p) =
      (phaseClass w h p + 1) % Nat.gcd w h := by
  have hm := Nat.mod_mod_of_dvd (p.2.val + 1) (Nat.gcd_dvd_right w h)
  have ha := congrArg (fun k => (p.1.val + k) % Nat.gcd w h) hm
  simp only [Nat.add_mod_mod] at ha
  change (p.1.val + (cyclicNext h hh p.2).val) % Nat.gcd w h = _
  rw [cyclicNext_val]
  change (p.1.val + (p.2.val + 1) % h) % Nat.gcd w h =
    ((p.1.val + p.2.val) % Nat.gcd w h + 1) % Nat.gcd w h
  rw [ha, Nat.mod_add_mod]
  simp only [Nat.add_assoc]

/-- The diagonal phase, with its natural finite index type. -/
def phaseIndex (w h : Nat) (hw : 0 < w) (p : Position w h) : Fin (Nat.gcd w h) :=
  ⟨phaseClass w h p, phaseClass_lt w h hw p⟩

@[simp] theorem phaseIndex_val (w h : Nat) (hw : 0 < w) (p : Position w h) :
    (phaseIndex w h hw p).val = phaseClass w h p := rfl

theorem phaseIndex_east (w h : Nat) (hw : 0 < w) (p : Position w h) :
    phaseIndex w h hw ((eastDirection w h hw).next p) =
      cyclicNext (Nat.gcd w h) (Nat.gcd_pos_of_pos_left h hw) (phaseIndex w h hw p) := by
  apply Fin.ext
  simp only [phaseIndex_val, cyclicNext_val, phaseClass_east]

theorem phaseIndex_north (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (p : Position w h) :
    phaseIndex w h hw ((northDirection w h hh).next p) =
      cyclicNext (Nat.gcd w h) (Nat.gcd_pos_of_pos_left h hw) (phaseIndex w h hw p) := by
  apply Fin.ext
  simp only [phaseIndex_val, cyclicNext_val, phaseClass_north]

/-- An east predecessor of a north successor is one inverse diagonal step,
so it preserves the phase class. -/
theorem phaseClass_eastPrev_northNext (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (p : Position w h) :
    phaseClass w h ((eastDirection w h hw).prev ((northDirection w h hh).next p)) =
      phaseClass w h p := by
  have he := phaseClass_diagonalShift w h hw hh (-1) p
  simpa only [diagonalShift, cyclicShift_neg_one, Int.neg_neg, cyclicShift_one,
    eastDirection, northDirection] using he

/-- Shifting a cyclic coordinate by a multiple of its size is the identity. -/
theorem cyclicShift_eq_self_of_dvd (n : Nat) (hn : 0 < n) (t : Int)
    (ht : (n : Int) ∣ t) (i : Fin n) : cyclicShift n hn t i = i := by
  apply (cyclicShift_eq_iff_mod n hn t i i).mpr
  simp only [Int.sub_self, Int.zero_emod]
  exact Int.emod_eq_zero_of_dvd ht

/-- The common period returns every east coordinate to its start. -/
theorem iterate_east_lcm (w h : Nat) (hw : 0 < w) (p : Position w h) :
    iterate (eastDirection w h hw).next (Nat.lcm w h) p = p := by
  rw [iterate_east_eq,
    cyclicShift_eq_self_of_dvd w hw (Nat.lcm w h : Int)
      (Int.ofNat_dvd.mpr (Nat.dvd_lcm_left w h))]

/-- The common period returns every north coordinate to its start. -/
theorem iterate_north_lcm (w h : Nat) (hh : 0 < h) (p : Position w h) :
    iterate (northDirection w h hh).next (Nat.lcm w h) p = p := by
  rw [iterate_north_eq,
    cyclicShift_eq_self_of_dvd h hh (Nat.lcm w h : Int)
      (Int.ofNat_dvd.mpr (Nat.dvd_lcm_right w h))]

end BML
