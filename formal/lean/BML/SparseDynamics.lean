import BML.Capture
import BML.Counting
import BML.Encounters
import BML.Rigid

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

private theorem perm_of_nodup_cover {α : Type} (xs ys : List α)
    (hn : xs.Nodup) (hcover : xs ⊆ ys) (hlen : ys.length ≤ xs.length) :
    xs.Perm ys := by
  classical
  induction xs generalizing ys with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst ys
    exact List.Perm.refl []
  | cons a xs ih =>
    have hn' := List.nodup_cons.mp hn
    have ha : a ∈ ys := hcover (List.mem_cons_self ..)
    have hcover' : xs ⊆ ys.erase a := by
      intro b hb
      have hba : b ≠ a := fun he => hn'.1 (he ▸ hb)
      exact (List.mem_erase_of_ne hba).mpr (hcover (List.mem_cons_of_mem a hb))
    have hlen' : (ys.erase a).length ≤ xs.length := by
      rw [List.length_erase]
      simp only [ha, ↓reduceIte]
      simp only [List.length_cons] at hlen
      omega
    exact ((ih (ys.erase a) hn'.2 hcover' hlen').cons a).trans
      (List.perm_cons_erase ha).symm

private theorem eq_of_nodup_map {α β : Type} (f : α → β) (xs : List α)
    (hn : (xs.map f).Nodup) (p q : α) (hp : p ∈ xs) (hq : q ∈ xs)
    (he : f p = f q) : p = q := by
  induction xs with
  | nil => simp at hp
  | cons a xs ih =>
    have hn' := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hp with rfl | hpTail
    · rcases List.mem_cons.mp hq with rfl | hqTail
      · rfl
      · exact (hn'.1 (List.mem_map.mpr ⟨q, hqTail, he.symm⟩)).elim
    · rcases List.mem_cons.mp hq with rfl | hqTail
      · exact (hn'.1 (List.mem_map.mpr ⟨p, hpTail, he⟩)).elim
      · exact ih hn'.2 hpTail hqTail

/-- The equality regime has alternating occupied and empty corrected
classes, with exactly one actual car in each occupied class. -/
def CorrectedAlternating (u : Config (Position w h)) (t : Nat) : Prop :=
  (∀ i, CorrectedOccupied hw u t i ↔
    ¬ CorrectedOccupied hw u t (cyclicNext g hg i)) ∧
  (∀ p q, u p ≠ .empty → u q ≠ .empty →
    correctedClass hw t p = correctedClass hw t q → p = q)

/-- B7.6 saturation. With at most g/2 cars and no empty adjacent pair,
the car classes and their predecessors cover g classes using at most g
entries. They therefore have no repetitions: occupied classes alternate,
and two actual cars cannot share an occupied corrected class. -/
theorem corrected_alternating_of_no_emptyPair (u : Config (Position w h)) (t : Nat)
    (hm : 2 * carCount w h u ≤ g)
    (hnone : ∀ i, ¬ CorrectedEmptyPair hw u t i) :
    CorrectedAlternating hw u t := by
  classical
  let xs := (occupiedCells w h u).map (correctedClass hw t)
  have hmem (i : Fin g) : i ∈ xs ↔ CorrectedOccupied hw u t i := by
    simp only [xs, List.mem_map, mem_occupiedCells, CorrectedOccupied]
  have hcover : List.finRange g ⊆ xs ++ xs.map (cyclicPrev g hg) := by
    intro i _
    by_cases hi : i ∈ xs
    · exact List.mem_append_left _ hi
    · have hj : cyclicNext g hg i ∈ xs := by
        apply Classical.byContradiction
        intro hj
        exact hnone i ⟨mt (hmem i).mpr hi, mt (hmem _).mpr hj⟩
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_, hj, cyclicPrev_next g hg i⟩)
  have hlen : (xs ++ xs.map (cyclicPrev g hg)).length ≤ (List.finRange g).length := by
    simp only [xs, List.length_append, List.length_map, List.length_finRange]
    change carCount w h u + carCount w h u ≤ g
    omega
  have hnodup := (List.nodup_finRange g).perm
    (perm_of_nodup_cover _ _ (List.nodup_finRange g) hcover hlen)
  obtain ⟨hxs, _, hdisjoint⟩ := List.nodup_append.mp hnodup
  constructor
  · intro i
    constructor
    · intro hi hj
      exact hdisjoint i ((hmem i).mpr hi) i
        (List.mem_map.mpr ⟨_, (hmem _).mpr hj, cyclicPrev_next g hg i⟩) rfl
    · intro hj
      exact Classical.byContradiction (fun hi => hnone i ⟨hi, hj⟩)
  · intro p q hp hq he
    exact eq_of_nodup_map (correctedClass hw t) (occupiedCells w h u) hxs p q
      ((mem_occupiedCells w h u p).mpr hp) ((mem_occupiedCells w h u q).mpr hq) he

/-- In an alternating singleton-class configuration every actual car
moves in the following CLASSIC round. The north target is checked after
the east phase; a potential east entrant would share the north car's
corrected class, contradicting singleton occupancy. -/
theorem corrected_alternating_allMove (u : Config (Position w h)) (t : Nat)
    (ha : CorrectedAlternating hw u t) : AllMove E N u := by
  classical
  constructor
  · intro p hp
    have hempty := (ha.1 (correctedClass hw t p)).mp ⟨p, by simp [hp], rfl⟩
    refine ⟨hp, Classical.byContradiction (fun htarget => hempty ?_)⟩
    exact ⟨(E).next p, htarget, target_class hw t p ((E).next p) (phaseIndex_east w h hw p)⟩
  · intro p hp
    have hn : u p = .north :=
      (other_species_unchanged E .east u p .north (by decide) (by decide)).mp hp
    have hempty := (ha.1 (correctedClass hw t p)).mp ⟨p, by simp [hn], rfl⟩
    have hq : u ((N).next p) = .empty := by
      apply Classical.byContradiction
      intro htarget
      exact hempty ⟨(N).next p, htarget,
        target_class hw t p ((N).next p) (phaseIndex_north w h hw hh p)⟩
    have hsource : u ((E).prev ((N).next p)) ≠ .east := by
      intro he
      have heq := ha.2 ((E).prev ((N).next p)) p (by simp [he]) (by simp [hn])
        (same_class_eastPrev_northNext hw hh t p)
      rw [heq, hn] at he
      cases he
    exact ⟨hp, by simp [halfStep, Species.cell, hq, hsource]⟩

/-- Inclusive sparse configurations without an empty corrected pair move
every car in the next complete CLASSIC round. -/
theorem corrected_allMove_of_no_emptyPair (u : Config (Position w h)) (t : Nat)
    (hm : 2 * carCount w h u ≤ g)
    (hnone : ∀ i, ¬ CorrectedEmptyPair hw u t i) : AllMove E N u :=
  corrected_alternating_allMove hw hh u t
    (corrected_alternating_of_no_emptyPair hw u t hm hnone)

/-- Once all corrected adjacent pairs contain a car, no empty pair can
appear in a later CLASSIC round. This is the contrapositive of B7.3. -/
theorem corrected_no_emptyPair_step (u : Config (Position w h)) (t : Nat)
    (hnone : ∀ i, ¬ CorrectedEmptyPair hw u t i) :
    ∀ i, ¬ CorrectedEmptyPair hw (torusStep w h hw hh u) (t + 1) i :=
  fun i hpair => hnone i (corrected_emptyPair_backwards hw hh u t i hpair)

/-- The alternating singleton-class regime is preserved by the actual
east-then-north CLASSIC update, under the inclusive population bound. -/
theorem corrected_alternating_step (u : Config (Position w h)) (t : Nat)
    (hm : 2 * carCount w h u ≤ g) (ha : CorrectedAlternating hw u t) :
    CorrectedAlternating hw (torusStep w h hw hh u) (t + 1) := by
  apply corrected_alternating_of_no_emptyPair hw _ (t + 1)
  · simpa only [torusStep_carCount] using hm
  · apply corrected_no_emptyPair_step hw hh u t
    intro i hp
    exact hp.1 ((ha.1 i).mpr hp.2)

/-- At any time after an inclusive sparse state has no empty corrected
pair, every car moves in every subsequent CLASSIC round. -/
theorem corrected_no_emptyPair_perpetual_allMove (u : Config (Position w h)) (t : Nat)
    (hm : 2 * carCount w h u ≤ g)
    (hnone : ∀ i, ¬ CorrectedEmptyPair hw u t i) (n : Nat) :
    AllMove E N (iterate (torusStep w h hw hh) n u) := by
  have ha : CorrectedAlternating hw (iterate (torusStep w h hw hh) n u) (t + n) := by
    induction n with
    | zero => exact corrected_alternating_of_no_emptyPair hw u t hm hnone
    | succ n ih =>
      have hsize : 2 * carCount w h (iterate (torusStep w h hw hh) n u) ≤ g := by
        simpa only [iterate_torusStep_carCount] using hm
      exact corrected_alternating_step hw hh _ (t + n) hsize ih
  exact corrected_alternating_allMove hw hh _ (t + n) ha

end

end BML
