import BML.Capture
import BML.Counting
import BML.Encounters

/-!
B7.0–B7.4 for CLASSIC. Corrected classes subtract the number of complete
east-then-north rounds from the actual diagonal phase modulo gcd(w,h).
-/
namespace BML

section

variable {w h : Nat} (hw : 0 < w) (hh : 0 < h)

local notation "g" => Nat.gcd w h
local notation "hg" => Nat.gcd_pos_of_pos_left h hw
local notation "E" => eastDirection w h hw
local notation "N" => northDirection w h hh

def correctedClass (t : Nat) (p : Position w h) : Fin g :=
  cyclicShift g hg (-(t : Int)) (phaseIndex w h hw p)

private theorem correctedClass_next (t : Nat) (p q : Position w h)
    (hnext : phaseIndex w h hw q = cyclicNext g hg (phaseIndex w h hw p)) :
    correctedClass hw (t + 1) q = correctedClass hw t p := by
  rw [correctedClass, hnext, ← cyclicShift_one, cyclicShift_add, correctedClass]
  congr 1
  omega

theorem correctedClass_stay (t : Nat) (p : Position w h) :
    correctedClass hw (t + 1) p = cyclicPrev g hg (correctedClass hw t p) := by
  simp only [← cyclicShift_neg_one, correctedClass, cyclicShift_add]
  congr 1
  omega

/-- A successful CLASSIC move preserves the corrected class. A blocked car
takes exactly one cyclic predecessor step in the corrected frame. -/
theorem correctedClass_roundTransport (u : Config (Position w h)) (sp : Species)
    (t : Nat) (p : Position w h) :
    correctedClass hw (t + 1) (roundTransport E N sp u p) =
      if RoundCanMove E N sp u p then correctedClass hw t p
      else cyclicPrev g hg (correctedClass hw t p) := by
  cases sp with
  | east =>
    by_cases hm : CanMove E .east u p
    · simpa only [roundTransport, RoundCanMove, transport, hm, ↓reduceIte] using
        correctedClass_next hw t p ((E).next p) (phaseIndex_east w h hw p)
    · simpa only [roundTransport, RoundCanMove, transport, hm, ↓reduceIte] using
        correctedClass_stay hw t p
  | north =>
    by_cases hm : CanMove N .north (halfStep E .east u) p
    · simpa only [roundTransport, RoundCanMove, transport, hm, ↓reduceIte] using
        correctedClass_next hw t p ((N).next p) (phaseIndex_north w h hw hh p)
    · simpa only [roundTransport, RoundCanMove, transport, hm, ↓reduceIte] using
        correctedClass_stay hw t p

def CorrectedOccupied (u : Config (Position w h)) (t : Nat) (i : Fin g) : Prop :=
  ∃ p, u p ≠ .empty ∧ correctedClass hw t p = i

def CorrectedEmptyPair (u : Config (Position w h)) (t : Nat) (i : Fin g) : Prop :=
  ¬ CorrectedOccupied hw u t i ∧ ¬ CorrectedOccupied hw u t (cyclicNext g hg i)

private theorem target_class (t : Nat) (p q : Position w h)
    (hnext : phaseIndex w h hw q = cyclicNext g hg (phaseIndex w h hw p)) :
    correctedClass hw t q = cyclicNext g hg (correctedClass hw t p) := by
  have he := correctedClass_next hw t p q hnext
  rw [correctedClass_stay] at he
  simpa only [cyclicNext_prev] using congrArg (cyclicNext g hg) he

private theorem same_class_eastPrev_northNext (t : Nat) (p : Position w h) :
    correctedClass hw t ((E).prev ((N).next p)) = correctedClass hw t p := by
  unfold correctedClass
  congr 1
  apply Fin.ext
  exact phaseClass_eastPrev_northNext w h hw hh p

private theorem corrected_occupied_of_move (u : Config (Position w h)) (sp : Species)
    (t : Nat) (p : Position w h) (hp : u p = sp.cell) (hm : RoundCanMove E N sp u p) :
    CorrectedOccupied hw (torusStep w h hw hh u) (t + 1) (correctedClass hw t p) := by
  refine ⟨roundTransport E N sp u p, ?_, ?_⟩
  · rw [torusStep, roundTransport_preserves_car E N sp u p hp]
    exact sp.cell_ne_empty
  · simp only [correctedClass_roundTransport hw hh, hm, ↓reduceIte]

/-- B7.1. With the next corrected class vacant, an east car can move. If
there is no east car in the current class, the north target has no east
predecessor that could fill it during the first phase. -/
theorem corrected_release (u : Config (Position w h)) (t : Nat) (i : Fin g)
    (hocc : CorrectedOccupied hw u t i)
    (hempty : ¬ CorrectedOccupied hw u t (cyclicNext g hg i)) :
    CorrectedOccupied hw (torusStep w h hw hh u) (t + 1) i := by
  classical
  by_cases he : ∃ p, u p = .east ∧ correctedClass hw t p = i
  · obtain ⟨p, hp, hi⟩ := he
    have htarget := target_class hw t p ((E).next p) (phaseIndex_east w h hw p)
    rw [hi] at htarget
    have hm : CanMove E .east u p :=
      ⟨hp, Classical.byContradiction fun h => hempty ⟨(E).next p, h, htarget⟩⟩
    rw [← hi]
    exact corrected_occupied_of_move hw hh u .east t p hp hm
  · obtain ⟨p, hp, hi⟩ := hocc
    have hn : u p = .north := by
      cases hc : u p with
      | empty => exact (hp hc).elim
      | east => exact (he ⟨p, hc, hi⟩).elim
      | north => rfl
    have htarget := target_class hw t p ((N).next p) (phaseIndex_north w h hw hh p)
    rw [hi] at htarget
    have hq : u ((N).next p) = .empty :=
      Classical.byContradiction fun h => hempty ⟨(N).next p, h, htarget⟩
    have hsource : u ((E).prev ((N).next p)) ≠ .east := fun h =>
      he ⟨_, h, (same_class_eastPrev_northNext hw hh t p).trans hi⟩
    have hm : CanMove N .north (halfStep E .east u) p :=
      ⟨(other_species_unchanged E .east u p .north (by decide) (by decide)).mpr hn,
        by simp [halfStep, Species.cell, hq, hsource]⟩
    rw [← hi]
    exact corrected_occupied_of_move hw hh u .north t p hn hm

/-- B7.2. Every occupied corrected class sends a car to itself or to its
cyclic predecessor in the next complete round. -/
theorem corrected_survival (u : Config (Position w h)) (t : Nat) (i : Fin g)
    (hocc : CorrectedOccupied hw u t i) :
    CorrectedOccupied hw (torusStep w h hw hh u) (t + 1) i ∨
      CorrectedOccupied hw (torusStep w h hw hh u) (t + 1) (cyclicPrev g hg i) := by
  obtain ⟨p, hp, hi⟩ := hocc
  have hspecies : ∃ sp : Species, u p = sp.cell := by
    cases hc : u p with
    | empty => exact (hp hc).elim
    | east => exact ⟨.east, rfl⟩
    | north => exact ⟨.north, rfl⟩
  obtain ⟨sp, hsp⟩ := hspecies
  let q := roundTransport E N sp u p
  have hq : torusStep w h hw hh u q ≠ .empty := by
    rw [torusStep, roundTransport_preserves_car E N sp u p hsp]
    exact sp.cell_ne_empty
  have hrow : correctedClass hw (t + 1) q = _ :=
    correctedClass_roundTransport hw hh u sp t p
  rw [hi] at hrow
  split at hrow
  · exact Or.inl ⟨q, hq, hrow⟩
  · exact Or.inr ⟨q, hq, hrow⟩

/-- Even if an empty adjacent pair disappears, its first class stays empty
for one more full round: a car can only enter it from that pair. -/
theorem corrected_emptyPair_first_after (u : Config (Position w h)) (t : Nat) (i : Fin g)
    (hp : CorrectedEmptyPair hw u t i) :
    ¬ CorrectedOccupied hw (torusStep w h hw hh u) (t + 1) i := by
  rintro ⟨q, hq, hclass⟩
  have hspecies : ∃ sp : Species, torusStep w h hw hh u q = sp.cell := by
    cases hc : torusStep w h hw hh u q with
    | empty => exact (hq hc).elim
    | east => exact ⟨.east, rfl⟩
    | north => exact ⟨.north, rfl⟩
  obtain ⟨sp, hsp⟩ := hspecies
  obtain ⟨p, hcar, htransport⟩ := roundTransport_surjective_on_cars E N sp u q hsp
  have hrow := correctedClass_roundTransport hw hh u sp t p
  rw [htransport, hclass] at hrow
  have hoccupied : u p ≠ .empty := fun h => sp.cell_ne_empty (hcar.symm.trans h)
  by_cases hm : RoundCanMove E N sp u p
  · rw [ite_eq_left hm] at hrow
    exact hp.1 ⟨p, hoccupied, hrow.symm⟩
  · rw [ite_eq_right hm] at hrow
    have hnext := congrArg (cyclicNext g hg) hrow
    rw [cyclicNext_prev] at hnext
    exact hp.2 ⟨p, hoccupied, hnext.symm⟩

/-- B7.3. An empty adjacent pair at the end of a CLASSIC round was empty
at its start in the corrected frame. -/
theorem corrected_emptyPair_backwards (u : Config (Position w h)) (t : Nat) (i : Fin g)
    (hp : CorrectedEmptyPair hw (torusStep w h hw hh u) (t + 1) i) :
    CorrectedEmptyPair hw u t i := by
  have hnext : ¬ CorrectedOccupied hw u t (cyclicNext g hg i) := by
    intro ho
    rcases corrected_survival hw hh u t _ ho with hs | hs
    · exact hp.2 hs
    · exact hp.1 (by simpa only [cyclicPrev_next] using hs)
  exact ⟨fun ho => hp.1 (corrected_release hw hh u t i ho hnext), hnext⟩

theorem corrected_emptyPair_before (s : Config (Position w h)) {t T : Nat}
    (hle : t ≤ T) (i : Fin g)
    (hp : CorrectedEmptyPair hw (iterate (torusStep w h hw hh) T s) T i) :
    CorrectedEmptyPair hw (iterate (torusStep w h hw hh) t s) t i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction k with
  | zero => exact hp
  | succ k ih => exact ih (corrected_emptyPair_backwards hw hh _ (t + k) i hp)

/-- B7.4. If no adjacent pair were empty, the car classes and their
predecessors would cover all g classes using at most 2m entries. -/
theorem corrected_emptyPair_of_sparse (u : Config (Position w h)) (t : Nat)
    (hm : 2 * carCount w h u < g) : ∃ i, CorrectedEmptyPair hw u t i := by
  classical
  let xs := (occupiedCells w h u).map (correctedClass hw t)
  have hmem (i : Fin g) : i ∈ xs ↔ CorrectedOccupied hw u t i := by
    simp only [xs, List.mem_map, mem_occupiedCells, CorrectedOccupied]
  apply Classical.byContradiction
  intro hpair
  have hcover : List.finRange g ⊆ xs ++ xs.map (cyclicPrev g hg) := by
    intro i _
    by_cases hi : i ∈ xs
    · exact List.mem_append_left _ hi
    · have hj : cyclicNext g hg i ∈ xs := by
        apply Classical.byContradiction
        intro hj
        exact hpair ⟨i, mt (hmem i).mpr hi, mt (hmem _).mpr hj⟩
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_, hj, cyclicPrev_next g hg i⟩)
  have hlength := (List.nodup_finRange g).length_le_of_subset hcover
  simp only [xs, List.length_finRange, List.length_append, List.length_map] at hlength
  change g ≤ carCount w h u + carCount w h u at hlength
  omega

end

end BML
