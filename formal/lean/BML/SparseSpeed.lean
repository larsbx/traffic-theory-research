import BML.SparseDynamics
import BML.FreeFlow
import BML.FiniteCycle
import BML.FiniteSums

/-!
B7.5 and assembly for CLASSIC. A pair vacant at the end of a finite
prefix supplies a cut every original car avoids throughout that prefix.
-/
namespace BML

section

variable {w h : Nat} (hw : 0 < w) (hh : 0 < h)

local notation "g" => Nat.gcd w h
local notation "hg" => Nat.gcd_pos_of_pos_left h hw
local notation "E" => eastDirection w h hw
local notation "N" => northDirection w h hh
local notation "orbit" => iterate (torusStep w h hw hh)

/-- The actual CLASSIC move test on an original car's position at time t. -/
def TraceCanMove (s : Config (Position w h)) (sp : Species) (p : Position w h)
    (t : Nat) : Prop :=
  RoundCanMove E N sp (orbit t s) (carTrace E N sp s t p)

instance (s : Config (Position w h)) (sp : Species) (p : Position w h) (t : Nat) :
    Decidable (TraceCanMove hw hh s sp p t) := by
  unfold TraceCanMove
  infer_instance

def blockedTagCount (s : Config (Position w h)) (sp : Species) (p : Position w h)
    (T : Nat) : Nat :=
  ((List.range T).filter fun t => decide (¬ TraceCanMove hw hh s sp p t)).length

/-- The number of complete rounds in [0,T) in which at least one car is blocked. -/
def blockedRoundCount (s : Config (Position w h)) (T : Nat) : Nat :=
  ((List.range T).filter fun t => decide (¬ AllMove E N (orbit t s))).length

private theorem filter_range_succ_length (P : Nat → Prop) [DecidablePred P] (t : Nat) :
    ((List.range (t + 1)).filter fun i => decide (P i)).length =
      ((List.range t).filter fun i => decide (P i)).length + (if P t then 1 else 0) := by
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases hp : P t <;> simp [hp]

private theorem blockedTagCount_succ (s : Config (Position w h)) (sp : Species)
    (p : Position w h) (t : Nat) :
    blockedTagCount hw hh s sp p (t + 1) = blockedTagCount hw hh s sp p t +
      (if ¬ TraceCanMove hw hh s sp p t then 1 else 0) :=
  filter_range_succ_length _ t

private theorem blockedRoundCount_succ (s : Config (Position w h)) (t : Nat) :
    blockedRoundCount hw hh s (t + 1) = blockedRoundCount hw hh s t +
      (if ¬ AllMove E N (orbit t s) then 1 else 0) :=
  filter_range_succ_length _ t

private theorem shift_from_cut_pos (cut y : Fin g) (hy : y ≠ cut) :
    0 < (cyclicShift g hg (-(cut.val : Int)) y).val := by
  have hcancel : (cut.val : Int) + -(cut.val : Int) = 0 := by omega
  let shift := cyclicShift g hg (-(cut.val : Int))
  have hz : shift cut = ⟨0, hg⟩ := by
    apply (cyclicShift_eq_iff g hg _ _ _).mpr
    simp [hcancel]
  apply Nat.pos_of_ne_zero
  intro h
  have hsame : shift y = shift cut := Fin.ext (h.trans (congrArg Fin.val hz).symm)
  have he := congrArg (cyclicShift g hg (cut.val : Int)) hsame
  have he' : y = cut := by
    simpa [shift, cyclicShift_add, hcancel] using he
  exact hy he'

private theorem shift_from_cut_prev (cut y : Fin g) :
    cyclicShift g hg (-(cut.val : Int)) (cyclicPrev g hg y) =
      cyclicPrev g hg (cyclicShift g hg (-(cut.val : Int)) y) := by
  simp only [← cyclicShift_neg_one, cyclicShift_add, Int.add_comm]

/-- B7.5. Every original CLASSIC car is blocked at most g−2 times in any
finite prefix. Its natural distance from the cut decreases by one for
each block and never reaches zero. -/
theorem low_density_tag_block_bound (s : Config (Position w h))
    (hm : 2 * carCount w h s < g) (sp : Species) (p : Position w h) (hp : s p = sp.cell)
    (T : Nat) : blockedTagCount hw hh s sp p T ≤ g - 2 := by
  have hsize : 2 * carCount w h (orbit T s) < g := by
    simpa only [iterate_torusStep_carCount] using hm
  obtain ⟨cut, hcut⟩ := corrected_emptyPair_of_sparse hw (orbit T s) T hsize
  let Y := fun t => correctedClass hw t (carTrace E N sp s t p)
  let rank := fun t => (cyclicShift g hg (-(cut.val : Int)) (Y t)).val
  have hpos (t : Nat) (ht : t ≤ T) : 0 < rank t := by
    apply shift_from_cut_pos hw
    intro h
    have hempty := (corrected_emptyPair_before hw hh s ht cut hcut).1
    have hcar := carTrace_preserves_car E N sp s p hp t
    exact hempty ⟨_, fun he => sp.cell_ne_empty (hcar.symm.trans he), h⟩
  have hstep (t : Nat) (ht : t < T) :
      rank (t + 1) + (if ¬ TraceCanMove hw hh s sp p t then 1 else 0) = rank t := by
    have hclass : Y (t + 1) = if TraceCanMove hw hh s sp p t then Y t
        else cyclicPrev g hg (Y t) :=
      correctedClass_roundTransport hw hh (orbit t s) sp t (carTrace E N sp s t p)
    by_cases hmove : TraceCanMove hw hh s sp p t
    · simp [rank, hclass, hmove]
    · have hne : rank t ≠ 0 := Nat.ne_of_gt (hpos t (by omega))
      simp only [hmove, ↓reduceIte] at hclass
      have hr : rank (t + 1) = rank t - 1 := by
        change (cyclicShift g hg (-(cut.val : Int)) (Y (t + 1))).val = rank t - 1
        rw [hclass, shift_from_cut_prev hw]
        change (cyclicPrev g hg (cyclicShift g hg (-(cut.val : Int)) (Y t))).val = rank t - 1
        have hn : (cyclicShift g hg (-(cut.val : Int)) (Y t)).val ≠ 0 := hne
        simp only [cyclicPrev, hn, ↓reduceDIte, rank]
      simp only [hmove, not_false_eq_true, ↓reduceIte, hr]
      omega
  have hbalance (n : Nat) (hn : n ≤ T) : rank n + blockedTagCount hw hh s sp p n = rank 0 := by
    induction n with
    | zero => simp [blockedTagCount]
    | succ n ih =>
      rw [blockedTagCount_succ hw hh]
      have hprev := ih (by omega)
      have hnext := hstep n (by omega)
      omega
  have hfinal := hbalance T (Nat.le_refl _)
  have hlo := hpos T (Nat.le_refl _)
  have hhi : rank 0 < g := (cyclicShift g hg (-(cut.val : Int)) (Y 0)).isLt
  omega

private theorem allMove_iff_traceCanMove (s : Config (Position w h)) (t : Nat) :
    AllMove E N (orbit t s) ↔ ∀ sp p, s p = sp.cell → TraceCanMove hw hh s sp p t := by
  constructor
  · intro hm sp p hp
    have hcar := carTrace_preserves_car E N sp s p hp t
    cases sp with
    | east => exact hm.1 _ hcar
    | north =>
      exact hm.2 _ ((other_species_unchanged E .east (orbit t s) _
        .north (by decide) (by decide)).mpr hcar)
  · intro hm
    constructor
    · intro q hq
      obtain ⟨p, hp, htrace⟩ := carTrace_surjective_on_cars E N .east s t q hq
      simpa only [TraceCanMove, RoundCanMove, htrace] using hm .east p hp
    · intro q hq
      have hcar := (other_species_unchanged E .east (orbit t s) q
        .north (by decide) (by decide)).mp hq
      obtain ⟨p, hp, htrace⟩ := carTrace_surjective_on_cars E N .north s t q hcar
      simpa only [TraceCanMove, RoundCanMove, htrace] using hm .north p hp

private def carTags (s : Config (Position w h)) : List (Species × Position w h) :=
  (speciesCells w h .east s).map (fun p => (.east, p)) ++
  (speciesCells w h .north s).map (fun p => (.north, p))

private theorem mem_carTags (s : Config (Position w h)) (sp : Species) (p : Position w h) :
    (sp, p) ∈ carTags s ↔ s p = sp.cell := by
  cases sp <;> simp [carTags, Species.cell]

private theorem length_carTags (s : Config (Position w h)) :
    (carTags s).length = carCount w h s := by
  simp only [carTags, List.length_append, List.length_map, carCount_eq_speciesCount,
    speciesCount_eq_length_speciesCells]

private theorem blockedRound_le_blockedTags (s : Config (Position w h)) (t : Nat) :
    (if ¬ AllMove E N (orbit t s) then 1 else 0) ≤
      ((carTags s).map (fun tag => if ¬ TraceCanMove hw hh s tag.1 tag.2 t then 1 else 0)).sum := by
  by_cases hall : AllMove E N (orbit t s)
  · simp [hall]
  · have hblocked : ∃ sp p, s p = sp.cell ∧ ¬ TraceCanMove hw hh s sp p t := by
      apply Classical.byContradiction
      intro hnone
      apply hall
      apply (allMove_iff_traceCanMove hw hh s t).mpr
      intro sp p hp
      exact Classical.byContradiction (fun h => hnone ⟨sp, p, hp, h⟩)
    obtain ⟨sp, p, hp, hb⟩ := hblocked
    have hpos : 0 < ((carTags s).map
        (fun tag => if ¬ TraceCanMove hw hh s tag.1 tag.2 t then 1 else 0)).sum := by
      apply List.sum_pos_iff_exists_pos_nat.mpr
      exact ⟨1, List.mem_map.mpr ⟨(sp, p), (mem_carTags s sp p).mpr hp, by simp [hb]⟩, by decide⟩
    simp only [hall, not_false_eq_true, ↓reduceIte]
    exact Nat.succ_le_of_lt hpos

/-- Across any finite time prefix, at most m(g−2) complete CLASSIC rounds
contain a blocked car. This counts blocked rounds, not elapsed time. -/
theorem low_density_block_bound (s : Config (Position w h))
    (hm : 2 * carCount w h s < g) (T : Nat) :
    blockedRoundCount hw hh s T ≤ carCount w h s * (g - 2) := by
  calc
    _ = ((List.range T).map (fun t => if ¬ AllMove E N (orbit t s) then 1 else 0)).sum :=
      length_filter_eq_indicator_sum _ _
    _ ≤ ((List.range T).map fun t => ((carTags s).map
        (fun tag => if ¬ TraceCanMove hw hh s tag.1 tag.2 t then 1 else 0)).sum).sum :=
      list_sum_map_le _ _ _ (fun t _ => blockedRound_le_blockedTags hw hh s t)
    _ = ((carTags s).map (fun tag => blockedTagCount hw hh s tag.1 tag.2 T)).sum := by
      rw [list_sum_map_swap]
      simp only [blockedTagCount, length_filter_eq_indicator_sum]
    _ ≤ ((carTags s).map (fun _ => g - 2)).sum := by
      apply list_sum_map_le
      intro ⟨sp, p⟩ hp
      exact low_density_tag_block_bound hw hh s hm sp p ((mem_carTags s sp p).mp hp) T
    _ = _ := by simp [List.map_const', List.sum_replicate_nat, length_carTags]

/-- If twice the car population is below the gcd of the positive side
lengths, the actual CLASSIC orbit eventually moves every car in every round. -/
theorem low_density_speed_one (s : Config (Position w h)) (hm : 2 * carCount w h s < g) :
    ∃ T, ∀ t ≥ T, AllMove E N (orbit t s) := by
  let budget := carCount w h s * (g - 2)
  let count := blockedRoundCount hw hh s
  have hbound (t : Nat) : count t ≤ budget := low_density_block_bound hw hh s hm t
  obtain ⟨k, ⟨T, hT⟩, _, hmin⟩ :=
    exists_minimum_le (fun k => ∃ t, budget - count t = k) budget ⟨0, by simp [count, blockedRoundCount]⟩
  have hmax (t : Nat) : count t ≤ count T := by
    apply Classical.byContradiction
    intro ht
    have hle := hbound t
    exact hmin (budget - count t) (by omega) ⟨t, rfl⟩
  have hmono (n : Nat) : count T ≤ count (T + n) := by
    induction n with
    | zero => exact Nat.le_refl _
    | succ n ih =>
      have hstep : count (T + n + 1) = count (T + n) +
          (if ¬ AllMove E N (orbit (T + n) s) then 1 else 0) :=
        blockedRoundCount_succ hw hh s (T + n)
      change count T ≤ count (T + n + 1)
      omega
  refine ⟨T, fun t ht => Classical.byContradiction (fun hb => ?_)⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
  have hstep := blockedRoundCount_succ hw hh s (T + n)
  change count (T + n + 1) = count (T + n) + (if ¬ AllMove E N (orbit (T + n) s) then 1 else 0) at hstep
  rw [ite_eq_left hb] at hstep
  have hle := hmax (T + n + 1)
  have hge := hmono n
  omega

end

end BML
