import BML.SparseSpeed

/-!
The inclusive CLASSIC sparse threshold. At equality, absence of an adjacent
empty corrected-class pair saturates the class cover and forces static free
flow. The empty-pair rank argument otherwise retains the strict-case budgets.
-/
namespace BML

private theorem perm_of_nodup_cover_length {α : Type} (xs ys : List α)
    (hn : xs.Nodup) (hsub : xs ⊆ ys) (hlen : ys.length ≤ xs.length) : xs.Perm ys := by
  classical
  induction xs generalizing ys with
  | nil =>
    have he : ys = [] := by simpa using hlen
    subst ys
    exact List.Perm.refl []
  | cons a xs ih =>
    have hd := List.nodup_cons.mp hn
    have ha : a ∈ ys := hsub (List.mem_cons_self ..)
    have htail : xs ⊆ ys.erase a := by
      intro x hx
      have hne : x ≠ a := fun h => hd.1 (h ▸ hx)
      exact (List.mem_erase_of_ne hne).mpr (hsub (List.mem_cons_of_mem a hx))
    have herase : (ys.erase a).length = ys.length - 1 := by
      rw [List.length_erase]
      simp [ha]
    have hsmall : (ys.erase a).length ≤ xs.length := by
      have hpos := List.length_pos_of_mem ha
      simp only [List.length_cons] at hlen
      omega
    exact ((ih (ys.erase a) hd.2 htail hsmall).cons a).trans (List.perm_cons_erase ha).symm

private theorem eq_of_nodup_map {α β : Type} (f : α → β) (xs : List α)
    (hn : (xs.map f).Nodup) (p q : α) (hp : p ∈ xs) (hq : q ∈ xs)
    (heq : f p = f q) : p = q := by
  induction xs generalizing p q with
  | nil => simp at hp
  | cons a xs ih =>
    have hd := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hp with rfl | hpTail
    · rcases List.mem_cons.mp hq with rfl | hqTail
      · rfl
      · exact (hd.1 (List.mem_map.mpr ⟨q, hqTail, heq.symm⟩)).elim
    · rcases List.mem_cons.mp hq with rfl | hqTail
      · exact (hd.1 (List.mem_map.mpr ⟨p, hpTail, heq⟩)).elim
      · exact ih hd.2 p q hpTail hqTail heq

section

variable {w h : Nat} (hw : 0 < w) (hh : 0 < h)

local notation "g" => Nat.gcd w h
local notation "hg" => Nat.gcd_pos_of_pos_left h hw
local notation "E" => eastDirection w h hw
local notation "N" => northDirection w h hh
local notation "orbit" => iterate (torusStep w h hw hh)

private theorem correctedClass_of_phase_next (t : Nat) (p q : Position w h)
    (heq : phaseIndex w h hw q = cyclicNext g hg (phaseIndex w h hw p)) :
    correctedClass hw t q = cyclicNext g hg (correctedClass hw t p) := by
  unfold correctedClass
  rw [heq, ← cyclicShift_one, cyclicShift_add, ← cyclicShift_one, cyclicShift_add]
  congr 1
  omega

/-- At the inclusive sparse threshold, absence of an adjacent empty pair
forces one car per occupied corrected class and no adjacent occupied classes.
These are sufficient for all static CLASSIC free-flow conditions. -/
theorem staticFree_of_no_corrected_emptyPair (s : Config (Position w h)) (t : Nat)
    (hm : 2 * carCount w h s ≤ g)
    (hpair : ¬ ∃ i, CorrectedEmptyPair hw s t i) : StaticFree w h hw hh s := by
  classical
  let xs := (occupiedCells w h s).map (correctedClass hw t)
  have hmem (i : Fin g) : i ∈ xs ↔ CorrectedOccupied hw s t i := by
    simp only [xs, List.mem_map, mem_occupiedCells, CorrectedOccupied]
  have hcover : List.finRange g ⊆ xs ++ xs.map (cyclicPrev g hg) := by
    intro i _
    by_cases hi : i ∈ xs
    · exact List.mem_append_left _ hi
    · have hj : cyclicNext g hg i ∈ xs := by
        apply Classical.byContradiction
        intro hj
        exact hpair ⟨i, mt (hmem i).mpr hi, mt (hmem _).mpr hj⟩
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_, hj, cyclicPrev_next g hg i⟩)
  have hlen : (xs ++ xs.map (cyclicPrev g hg)).length ≤ (List.finRange g).length := by
    simp only [xs, List.length_append, List.length_map, List.length_finRange]
    change carCount w h s + carCount w h s ≤ g
    omega
  have hperm := perm_of_nodup_cover_length _ _ (List.nodup_finRange g) hcover hlen
  have hnd := List.nodup_append.mp (hperm.nodup (List.nodup_finRange g))
  have hunique (p q : Position w h) (hp : s p ≠ .empty) (hq : s q ≠ .empty)
      (heq : correctedClass hw t p = correctedClass hw t q) : p = q :=
    eq_of_nodup_map (correctedClass hw t) (occupiedCells w h s) hnd.1 p q
      ((mem_occupiedCells w h s p).mpr hp) ((mem_occupiedCells w h s q).mpr hq) heq
  have hnext (i : Fin g) (hi : CorrectedOccupied hw s t i) :
      ¬ CorrectedOccupied hw s t (cyclicNext g hg i) := by
    intro hj
    have hprev : i ∈ xs.map (cyclicPrev g hg) :=
      List.mem_map.mpr ⟨_, (hmem _).mpr hj, cyclicPrev_next g hg i⟩
    exact hnd.2.2 i ((hmem i).mpr hi) i hprev rfl
  have hneq (p q : Position w h) (hp : s p ≠ .empty) (hq : s q ≠ .empty)
      (heq : phaseIndex w h hw q = cyclicNext g hg (phaseIndex w h hw p)) : False := by
    have hclass := correctedClass_of_phase_next hw t p q heq
    exact hnext _ ⟨p, hp, rfl⟩ ⟨q, hq, hclass⟩
  refine ⟨?_, ?_, ?_⟩
  · intro p hp hq
    exact hneq p ((E).next p) (by simp [hp]) (by simp [hq]) (phaseIndex_east w h hw p)
  · intro p hp hq
    exact hneq p ((N).next p) (by simp [hp]) (by simp [hq]) (phaseIndex_north w h hw hh p)
  · intro e q he hn
    constructor
    · intro hsame
      have hp : phaseIndex w h hw e = phaseIndex w h hw q := Fin.ext hsame.symm
      have hclass : correctedClass hw t e = correctedClass hw t q :=
        congrArg (cyclicShift g hg (-(t : Int))) hp
      have heq := hunique e q (by simp [he]) (by simp [hn]) hclass
      subst q
      simp [he] at hn
    · intro hsucc
      apply hneq e q (by simp [he]) (by simp [hn])
      apply Fin.ext
      simpa only [phaseIndex_val, cyclicNext_val] using hsucc

/-- A blocked round under 2m≤g still has an adjacent empty pair before it;
otherwise saturation would make the current state static-free. -/
theorem corrected_emptyPair_of_blocked_le (s : Config (Position w h)) (t : Nat)
    (hm : 2 * carCount w h s ≤ g) (hb : ¬ AllMove E N s) :
    ∃ i, CorrectedEmptyPair hw s t i := by
  classical
  apply Classical.byContradiction
  intro hnone
  exact hb (staticFree_allMove w h hw hh s
    (staticFree_of_no_corrected_emptyPair hw hh s t hm hnone))

/-- Equality preserves the original per-tag bound. If the final round
moves fully it adds no block; otherwise its pre-round empty pair supplies
an avoided cut through that round. -/
theorem low_density_tag_block_bound_le (s : Config (Position w h))
    (hm : 2 * carCount w h s ≤ g) (sp : Species) (p : Position w h)
    (hp : s p = sp.cell) (T : Nat) : blockedTagCount hw hh s sp p T ≤ g - 2 := by
  induction T with
  | zero => simp [blockedTagCount]
  | succ T ih =>
    by_cases hall : AllMove E N (orbit T s)
    · have hmove := (allMove_iff_traceCanMove hw hh s T).mp hall sp p hp
      rw [blockedTagCount_succ]
      simpa only [hmove, not_true_eq_false, ↓reduceIte, Nat.add_zero] using ih
    · have hsize : 2 * carCount w h (orbit T s) ≤ g := by
        simpa only [iterate_torusStep_carCount] using hm
      obtain ⟨cut, hcut⟩ := corrected_emptyPair_of_blocked_le hw hh (orbit T s) T hsize hall
      exact tag_block_bound_of_emptyPair_before hw hh s sp p hp T cut hcut

/-- The original blocked-round budget extends to the inclusive threshold. -/
theorem low_density_block_bound_le (s : Config (Position w h))
    (hm : 2 * carCount w h s ≤ g) (T : Nat) :
    blockedRoundCount hw hh s T ≤ carCount w h s * (g - 2) :=
  blockedRoundCount_le_of_tag_bound hw hh s T (g - 2)
    (fun sp p hp => low_density_tag_block_bound_le hw hh s hm sp p hp T)

/-- The same elapsed-time deadline is valid with the inclusive population
hypothesis 2m≤gcd(w,h). -/
theorem low_density_staticFree_deadline_le (s : Config (Position w h))
    (hm : 2 * carCount w h s ≤ g) :
    StaticFree w h hw hh (orbit (sparseSpeedDeadline w h s) s) :=
  staticFree_of_blockedRoundCount_bound hw hh s (carCount w h s * (g - 2))
    (low_density_block_bound_le hw hh s hm)

/-- Every round at or after the sparse deadline moves fully, including
at the equality case 2m=gcd(w,h). -/
theorem low_density_speed_one_deadline_le (s : Config (Position w h))
    (hm : 2 * carCount w h s ≤ g) (t : Nat) (ht : sparseSpeedDeadline w h s ≤ t) :
    AllMove E N (orbit t s) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [iterate_add]
  exact staticFree_perpetual_allMove w h hw hh _
    (low_density_staticFree_deadline_le hw hh s hm) d

/-- Inclusive sparse eventual full movement for the actual CLASSIC kernel. -/
theorem low_density_speed_one_le (s : Config (Position w h))
    (hm : 2 * carCount w h s ≤ g) : ∃ T, ∀ t ≥ T, AllMove E N (orbit t s) :=
  ⟨sparseSpeedDeadline w h s, low_density_speed_one_deadline_le hw hh s hm⟩

/-- On an n×n square, equality 2m=n has the same n*m*(n-2) deadline. -/
theorem low_density_square_speed_one_deadline_le (n : Nat) (hn : 0 < n)
    (s : Config (Position n n)) (hm : 2 * carCount n n s ≤ n)
    (t : Nat) (ht : n * (carCount n n s * (n - 2)) ≤ t) :
    AllMove (eastDirection n n hn) (northDirection n n hn)
      (iterate (torusStep n n hn hn) t s) := by
  apply low_density_speed_one_deadline_le hn hn s (by simpa only [Nat.gcd_self] using hm) t
  simpa only [sparseSpeedDeadline, Nat.lcm_self, Nat.gcd_self] using ht

end

end BML
