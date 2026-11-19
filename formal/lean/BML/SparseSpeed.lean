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

/-- An elapsed-time deadline for permanent CLASSIC free flow under the strict
sparse hypothesis. The lcm converts a blocked-round budget into full rounds. -/
def sparseSpeedDeadline (w h : Nat) (s : Config (Position w h)) : Nat :=
  Nat.lcm w h * (carCount w h s * (Nat.gcd w h - 2))

private theorem filter_range_succ_length (P : Nat → Prop) [DecidablePred P] (t : Nat) :
    ((List.range (t + 1)).filter fun i => decide (P i)).length =
      ((List.range t).filter fun i => decide (P i)).length + (if P t then 1 else 0) := by
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases hp : P t <;> simp [hp]

theorem blockedTagCount_succ (s : Config (Position w h)) (sp : Species)
    (p : Position w h) (t : Nat) :
    blockedTagCount hw hh s sp p (t + 1) = blockedTagCount hw hh s sp p t +
      (if ¬ TraceCanMove hw hh s sp p t then 1 else 0) :=
  filter_range_succ_length _ t

private theorem blockedRoundCount_succ (s : Config (Position w h)) (t : Nat) :
    blockedRoundCount hw hh s (t + 1) = blockedRoundCount hw hh s t +
      (if ¬ AllMove E N (orbit t s) then 1 else 0) :=
  filter_range_succ_length _ t

private theorem blockedRoundCount_mono (s : Config (Position w h))
    (a b : Nat) (hab : a ≤ b) :
    blockedRoundCount hw hh s a ≤ blockedRoundCount hw hh s b := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have hstep := blockedRoundCount_succ hw hh s (a + n)
    change blockedRoundCount hw hh s a ≤ blockedRoundCount hw hh s (a + n + 1)
    omega

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

/-- A corrected class avoided throughout a finite prefix bounds each
original car's block count by g−2 through natural rank decrease. -/
theorem tag_block_bound_of_corrected_cut (s : Config (Position w h))
    (sp : Species) (p : Position w h) (hp : s p = sp.cell) (T : Nat) (cut : Fin g)
    (hempty : ∀ t, t ≤ T → ¬ CorrectedOccupied hw (orbit t s) t cut) :
    blockedTagCount hw hh s sp p T ≤ g - 2 := by
  let Y := fun t => correctedClass hw t (carTrace E N sp s t p)
  let rank := fun t => (cyclicShift g hg (-(cut.val : Int)) (Y t)).val
  have hpos (t : Nat) (ht : t ≤ T) : 0 < rank t := by
    apply shift_from_cut_pos hw
    intro h
    have hcar := carTrace_preserves_car E N sp s p hp t
    exact hempty t ht ⟨_, fun he => sp.cell_ne_empty (hcar.symm.trans he), h⟩
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

/-- A pair empty before the final round supplies a cut through that round:
backward persistence covers the prefix and its first vacancy survives once. -/
theorem tag_block_bound_of_emptyPair_before (s : Config (Position w h))
    (sp : Species) (p : Position w h) (hp : s p = sp.cell) (T : Nat) (cut : Fin g)
    (hcut : CorrectedEmptyPair hw (orbit T s) T cut) :
    blockedTagCount hw hh s sp p (T + 1) ≤ g - 2 := by
  apply tag_block_bound_of_corrected_cut hw hh s sp p hp (T + 1) cut
  intro t ht
  by_cases hle : t ≤ T
  · exact (corrected_emptyPair_before hw hh s hle cut hcut).1
  · have heq : t = T + 1 := by omega
    subst t
    exact corrected_emptyPair_first_after hw hh (orbit T s) T cut hcut

/-- B7.5. Under strict sparsity every original CLASSIC car is blocked at
most g−2 times in any finite prefix. -/
theorem low_density_tag_block_bound (s : Config (Position w h))
    (hm : 2 * carCount w h s < g) (sp : Species) (p : Position w h) (hp : s p = sp.cell)
    (T : Nat) : blockedTagCount hw hh s sp p T ≤ g - 2 := by
  have hsize : 2 * carCount w h (orbit T s) < g := by
    simpa only [iterate_torusStep_carCount] using hm
  obtain ⟨cut, hcut⟩ := corrected_emptyPair_of_sparse hw (orbit T s) T hsize
  apply tag_block_bound_of_corrected_cut hw hh s sp p hp T cut
  exact fun t ht => (corrected_emptyPair_before hw hh s ht cut hcut).1

theorem allMove_iff_traceCanMove (s : Config (Position w h)) (t : Nat) :
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

/-- Summing a common original-tag blockage bound bounds blocked rounds. -/
theorem blockedRoundCount_le_of_tag_bound (s : Config (Position w h)) (T B : Nat)
    (hbound : ∀ sp p, s p = sp.cell → blockedTagCount hw hh s sp p T ≤ B) :
    blockedRoundCount hw hh s T ≤ carCount w h s * B := by
  calc
    _ = ((List.range T).map (fun t => if ¬ AllMove E N (orbit t s) then 1 else 0)).sum :=
      length_filter_eq_indicator_sum _ _
    _ ≤ ((List.range T).map fun t => ((carTags s).map
        (fun tag => if ¬ TraceCanMove hw hh s tag.1 tag.2 t then 1 else 0)).sum).sum :=
      list_sum_map_le _ _ _ (fun t _ => blockedRound_le_blockedTags hw hh s t)
    _ = ((carTags s).map (fun tag => blockedTagCount hw hh s tag.1 tag.2 T)).sum := by
      rw [list_sum_map_swap]
      simp only [blockedTagCount, length_filter_eq_indicator_sum]
    _ ≤ ((carTags s).map (fun _ => B)).sum := by
      apply list_sum_map_le
      intro ⟨sp, p⟩ hp
      exact hbound sp p ((mem_carTags s sp p).mp hp)
    _ = _ := by simp [List.map_const', List.sum_replicate_nat, length_carTags]

/-- Across any finite time prefix, at most m(g−2) complete CLASSIC rounds
contain a blocked car. This counts blocked rounds, not elapsed time. -/
theorem low_density_block_bound (s : Config (Position w h))
    (hm : 2 * carCount w h s < g) (T : Nat) :
    blockedRoundCount hw hh s T ≤ carCount w h s * (g - 2) :=
  blockedRoundCount_le_of_tag_bound hw hh s T (g - 2)
    (fun sp p hp => low_density_tag_block_bound hw hh s hm sp p hp T)

/-- A uniform budget of K blocked CLASSIC rounds gives entry into the static
free-flow set by lcm(w,h)*K. If that deadline were not static-free, each of the
K+1 preceding-or-starting lcm windows would contain a blocked round. -/
theorem staticFree_of_blockedRoundCount_bound (s : Config (Position w h))
    (K : Nat) (hbound : ∀ T, blockedRoundCount hw hh s T ≤ K) :
    StaticFree w h hw hh (orbit (Nat.lcm w h * K) s) := by
  classical
  apply Classical.byContradiction
  intro hnot
  let ell := Nat.lcm w h
  have hearlier (k : Nat) (hk : k ≤ K) :
      ¬ StaticFree w h hw hh (orbit (ell * k) s) := by
    intro hfree
    have hle : ell * k ≤ ell * K := Nat.mul_le_mul_left ell hk
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    have hlate := staticFree_iterate w h hw hh (orbit (ell * k) s) hfree d
    apply hnot
    simpa only [← iterate_add, ← hd] using hlate
  have hincrement (k : Nat) (hk : k ≤ K) :
      blockedRoundCount hw hh s (ell * k) + 1 ≤
        blockedRoundCount hw hh s (ell * (k + 1)) := by
    obtain ⟨j, hj, hblocked⟩ :=
      (not_staticFree_iff_blocked_before_lcm w h hw hh (orbit (ell * k) s)).mp
        (hearlier k hk)
    have hb : ¬ AllMove E N (orbit (ell * k + j) s) := by
      simpa only [iterate_add] using hblocked
    have hstart := blockedRoundCount_mono hw hh s (ell * k) (ell * k + j) (by omega)
    have hfinish := blockedRoundCount_mono hw hh s (ell * k + j + 1)
      (ell * (k + 1)) (by
        rw [Nat.mul_add, Nat.mul_one]
        change j < ell at hj
        omega)
    have hstep := blockedRoundCount_succ hw hh s (ell * k + j)
    rw [ite_eq_left hb] at hstep
    omega
  have hcount (k : Nat) (hk : k ≤ K + 1) :
      k ≤ blockedRoundCount hw hh s (ell * k) := by
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hprev := ih (by omega)
      have hnext := hincrement k (by omega)
      omega
  have htooMany := hcount (K + 1) (Nat.le_refl _)
  have hbudget := hbound (ell * (K + 1))
  omega

/-- Under 2m<gcd(w,h), the actual CLASSIC state is static-free at the
executable deadline lcm(w,h)*m*(gcd(w,h)-2). -/
theorem low_density_staticFree_deadline (s : Config (Position w h))
    (hm : 2 * carCount w h s < g) :
    StaticFree w h hw hh (orbit (sparseSpeedDeadline w h s) s) :=
  staticFree_of_blockedRoundCount_bound hw hh s (carCount w h s * (g - 2))
    (low_density_block_bound hw hh s hm)

/-- Every full round at or after the sparse deadline moves every original
car. The bound is on elapsed time, in addition to the B7 blockage budget. -/
theorem low_density_speed_one_deadline (s : Config (Position w h))
    (hm : 2 * carCount w h s < g) (t : Nat) (ht : sparseSpeedDeadline w h s ≤ t) :
    AllMove E N (orbit t s) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [iterate_add]
  exact staticFree_perpetual_allMove w h hw hh _
    (low_density_staticFree_deadline hw hh s hm) d

/-- On an n by n square, the sparse deadline simplifies to n*m*(n-2)
complete rounds, under the same strict population condition 2m<n. -/
theorem low_density_square_speed_one_deadline (n : Nat) (hn : 0 < n)
    (s : Config (Position n n)) (hm : 2 * carCount n n s < n)
    (t : Nat) (ht : n * (carCount n n s * (n - 2)) ≤ t) :
    AllMove (eastDirection n n hn) (northDirection n n hn)
      (iterate (torusStep n n hn hn) t s) := by
  apply low_density_speed_one_deadline hn hn s (by simpa only [Nat.gcd_self] using hm) t
  simpa only [sparseSpeedDeadline, Nat.lcm_self, Nat.gcd_self] using ht

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
