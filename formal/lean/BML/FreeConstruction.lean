import BML.FreePattern
import BML.PhaseCounts

/-!
Maximum free-flow witnesses on every finite torus.

For nontrivial gcd, saturate the occupied classes of `freePattern`.  For
coprime dimensions, use the larger of the alternating east-only and
north-only constructions.  Every construction is executable, and its
population and the static free-flow conditions are proved below.
-/

namespace BML

/-- A phase-constant board flows freely if east classes are followed by empty
classes and north classes are followed by east classes. -/
theorem phaseConfig_staticFree (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (pattern : Fin (Nat.gcd w h) → Cell)
    (hEast : ∀ i, pattern i = .east →
      pattern (cyclicNext (Nat.gcd w h) (Nat.gcd_pos_of_pos_left h hw) i) = .empty)
    (hNorth : ∀ i, pattern i = .north →
      pattern (cyclicNext (Nat.gcd w h) (Nat.gcd_pos_of_pos_left h hw) i) = .east) :
    StaticFree w h hw hh (phaseConfig w h hw pattern) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    change pattern (phaseIndex w h hw ((eastDirection w h hw).next p)) ≠ .east
    rw [phaseIndex_east, hEast _ hp]
    decide
  · intro p hp
    change pattern (phaseIndex w h hw ((northDirection w h hh).next p)) ≠ .north
    rw [phaseIndex_north, hNorth _ hp]
    decide
  · intro e q he hq
    change pattern (phaseIndex w h hw e) = .east at he
    change pattern (phaseIndex w h hw q) = .north at hq
    constructor
    · intro hc
      have hi : phaseIndex w h hw q = phaseIndex w h hw e := Fin.ext hc
      rw [hi, he] at hq
      contradiction
    · intro hc
      have hi : phaseIndex w h hw q =
          cyclicNext (Nat.gcd w h) (Nat.gcd_pos_of_pos_left h hw)
            (phaseIndex w h hw e) := by
        apply Fin.ext
        simpa only [phaseIndex_val, cyclicNext_val] using hc
      rw [hi, hEast _ he] at hq
      contradiction

/-- Saturate all occupied classes of the maximum cyclic pattern. -/
def phaseFreeConfig (w h : Nat) (hw : 0 < w) : Config (Position w h) :=
  phaseConfig w h hw (freePattern (Nat.gcd w h))

theorem phaseFreeConfig_staticFree (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (hg : 2 ≤ Nat.gcd w h) : StaticFree w h hw hh (phaseFreeConfig w h hw) := by
  apply phaseConfig_staticFree
  · exact freePattern_east_next _ hg
  · exact freePattern_north_next _ hg

theorem phaseFreeConfig_carCount (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (hg : 2 ≤ Nat.gcd w h) :
    carCount w h (phaseFreeConfig w h hw) =
      (w * h / Nat.gcd w h) * ((2 * Nat.gcd w h) / 3) := by
  rw [phaseFreeConfig, carCount_phaseConfig w h hw hh, freePattern_count _ hg]

/-- Every other coordinate, with the unpaired last coordinate omitted. -/
abbrev alternatingSlot (n : Nat) (i : Fin n) : Prop :=
  i.val < 2 * (n / 2) ∧ i.val % 2 = 0

theorem alternatingSlot_not_next (n : Nat) (hn : 0 < n) (i : Fin n)
    (hi : alternatingSlot n i) : ¬ alternatingSlot n (cyclicNext n hn i) := by
  have hnext : i.val + 1 < n := by have := i.isLt; dsimp [alternatingSlot] at hi; omega
  simp only [cyclicNext, hnext, ↓reduceDIte, alternatingSlot]
  dsimp [alternatingSlot] at hi
  omega

theorem alternatingSlot_count (n : Nat) :
    ((List.finRange n).filter (fun i => decide (alternatingSlot n i))).length = n / 2 := by
  let embed : Fin (n / 2) → Fin n := fun i => ⟨2 * i.val, by have := i.isLt; omega⟩
  let xs := (List.finRange n).filter (fun i => decide (alternatingSlot n i))
  let ys := (List.finRange (n / 2)).map embed
  have hinj : Function.Injective embed := by
    intro i j he
    apply Fin.ext
    have hv := congrArg Fin.val he
    change 2 * i.val = 2 * j.val at hv
    omega
  have hxnodup : xs.Nodup := (List.nodup_finRange n).filter _
  have hynodup : ys.Nodup := List.Pairwise.map embed
    (fun _ _ hne he => hne (hinj he)) (List.nodup_finRange _)
  have hmem : ∀ i, i ∈ xs ↔ i ∈ ys := by
    intro i
    simp only [xs, ys, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq, List.mem_map]
    constructor
    · intro hi
      refine ⟨⟨i.val / 2, by dsimp [alternatingSlot] at hi; omega⟩, ?_⟩
      apply Fin.ext
      change 2 * (i.val / 2) = i.val
      dsimp [alternatingSlot] at hi
      omega
    · rintro ⟨j, rfl⟩
      dsimp [alternatingSlot, embed]
      have := j.isLt
      omega
  have he := ((List.perm_ext_iff_of_nodup hxnodup hynodup).mpr hmem).length_eq
  simpa only [xs, ys, List.length_map, List.length_finRange] using he

/-- Alternating east cars in each row, including odd-width tori. -/
def alternatingEast (w h : Nat) : Config (Position w h) :=
  fun p => if alternatingSlot w p.1 then .east else .empty

/-- Alternating north cars in each column, including odd-height tori. -/
def alternatingNorth (w h : Nat) : Config (Position w h) :=
  fun p => if alternatingSlot h p.2 then .north else .empty

theorem alternatingEast_staticFree (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    StaticFree w h hw hh (alternatingEast w h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    have hslot : alternatingSlot w p.1 := by simpa [alternatingEast] using hp
    change (if alternatingSlot w (cyclicNext w hw p.1) then Cell.east else Cell.empty) ≠ .east
    rw [ite_eq_right (alternatingSlot_not_next w hw p.1 hslot)]
    decide
  · intro p hp
    unfold alternatingEast at hp
    split at hp <;> contradiction
  · intro e q _ hq
    unfold alternatingEast at hq
    split at hq <;> contradiction

theorem alternatingNorth_staticFree (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    StaticFree w h hw hh (alternatingNorth w h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    unfold alternatingNorth at hp
    split at hp <;> contradiction
  · intro p hp
    have hslot : alternatingSlot h p.2 := by simpa [alternatingNorth] using hp
    change (if alternatingSlot h (cyclicNext h hh p.2) then Cell.north else Cell.empty) ≠ .north
    rw [ite_eq_right (alternatingSlot_not_next h hh p.2 hslot)]
    decide
  · intro e q he _
    unfold alternatingNorth at he
    split at he <;> contradiction

private theorem count_position_first (w h : Nat) (P : Fin w → Prop) [DecidablePred P] :
    ((positions w h).filter (fun p => decide (P p.1))).length =
      h * ((List.finRange w).filter (fun i => decide (P i))).length := by
  simp only [positions, List.filter_flatMap, List.filter_map, Function.comp_def,
    List.length_flatMap, List.length_map]
  change ((List.finRange h).map (fun _ : Fin h =>
    ((List.finRange w).filter (fun i => decide (P i))).length)).sum = _
  rw [List.map_const', List.sum_replicate_nat, List.length_finRange]

private theorem sum_indicator_multiple (xs : List α) (P : α → Prop) [DecidablePred P]
    (m : Nat) :
    (xs.map (fun x => if P x then m else 0)).sum =
      m * (xs.filter (fun x => decide (P x))).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : P x <;> simp [hx, ih, Nat.mul_add, Nat.mul_succ, Nat.add_comm]

private theorem count_position_second (w h : Nat) (P : Fin h → Prop) [DecidablePred P] :
    ((positions w h).filter (fun p => decide (P p.2))).length =
      w * ((List.finRange h).filter (fun i => decide (P i))).length := by
  simp only [positions, List.filter_flatMap, List.length_flatMap]
  have hrow (y : Fin h) :
      (((List.finRange w).map (fun x => (x, y))).filter
        (fun p => decide (P p.2))).length = if P y then w else 0 := by
    simp only [List.filter_map, Function.comp_def, List.length_map]
    by_cases hy : P y
    · simp only [hy, decide_true, ↓reduceIte]
      rw [List.filter_eq_self.mpr (by intro x hx; rfl), List.length_finRange]
    · simp [hy]
  simp only [hrow]
  exact sum_indicator_multiple _ _ _

theorem alternatingEast_carCount (w h : Nat) :
    carCount w h (alternatingEast w h) = h * (w / 2) := by
  unfold carCount occupiedCells
  have he : (fun p : Position w h => decide (alternatingEast w h p ≠ .empty)) =
      (fun p => decide (alternatingSlot w p.1)) := by
    funext p
    by_cases hp : alternatingSlot w p.1 <;> simp [alternatingEast, hp]
  rw [he, count_position_first, alternatingSlot_count]

theorem alternatingNorth_carCount (w h : Nat) :
    carCount w h (alternatingNorth w h) = w * (h / 2) := by
  unfold carCount occupiedCells
  have he : (fun p : Position w h => decide (alternatingNorth w h p ≠ .empty)) =
      (fun p => decide (alternatingSlot h p.2)) := by
    funext p
    by_cases hp : alternatingSlot h p.2 <;> simp [alternatingNorth, hp]
  rw [he, count_position_second, alternatingSlot_count]

/-- The larger of the two alternating, single-species constructions. -/
def maxPureFreeConfig (w h : Nat) : Config (Position w h) :=
  if w * (h / 2) ≤ h * (w / 2) then alternatingEast w h else alternatingNorth w h

theorem maxPureFreeConfig_staticFree (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    StaticFree w h hw hh (maxPureFreeConfig w h) := by
  unfold maxPureFreeConfig
  split
  · exact alternatingEast_staticFree w h hw hh
  · exact alternatingNorth_staticFree w h hw hh

theorem maxPureFreeConfig_carCount (w h : Nat) :
    carCount w h (maxPureFreeConfig w h) = max (h * (w / 2)) (w * (h / 2)) := by
  unfold maxPureFreeConfig
  split <;> rename_i hc
  · rw [alternatingEast_carCount, Nat.max_eq_left hc]
  · rw [alternatingNorth_carCount, Nat.max_eq_right (by omega)]

/-- An executable configuration attaining the finite-torus free-flow maximum. -/
def maxFreeConfig (w h : Nat) (hw : 0 < w) : Config (Position w h) :=
  if Nat.gcd w h = 1 then maxPureFreeConfig w h else phaseFreeConfig w h hw

theorem maxFreeConfig_staticFree (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    StaticFree w h hw hh (maxFreeConfig w h hw) := by
  unfold maxFreeConfig
  split <;> rename_i hg
  · exact maxPureFreeConfig_staticFree w h hw hh
  · apply phaseFreeConfig_staticFree w h hw hh
    have := Nat.gcd_pos_of_pos_left h hw
    omega

theorem maxFreeConfig_carCount (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    carCount w h (maxFreeConfig w h hw) =
      if Nat.gcd w h = 1 then max (h * (w / 2)) (w * (h / 2))
      else (w * h / Nat.gcd w h) * ((2 * Nat.gcd w h) / 3) := by
  unfold maxFreeConfig
  split <;> rename_i hg
  · exact maxPureFreeConfig_carCount w h
  · apply phaseFreeConfig_carCount w h hw hh
    have := Nat.gcd_pos_of_pos_left h hw
    omega

end BML
