import BML.Enumeration
import BML.FiniteCycle
import BML.PathCore

/-!
The column construction of Theorem U for the CLASSIC east-then-north kernel.
The closed gate leaves one original north car alone in column 1.
-/
namespace BML.Gated

variable {w h : Nat}

abbrev gate (hw : 4 ≤ w) : Fin w := ⟨0, by omega⟩
abbrev free (hw : 4 ≤ w) : Fin w := ⟨1, by omega⟩
abbrev wall (hw : 4 ≤ w) : Fin w := ⟨2, by omega⟩
abbrev feeder (hw : 4 ≤ w) : Fin w := ⟨w - 1, by omega⟩
abbrev bottom (hh : 2 ≤ h) : Fin h := ⟨0, by omega⟩

private abbrev e (hw : 4 ≤ w) := eastDirection w h (by omega)
private abbrev n (hh : 2 ≤ h) := northDirection w h (by omega)
private abbrev f (hw : 4 ≤ w) (hh : 2 ≤ h) := torusStep w h (by omega) (by omega)

private theorem gate_ne_free (hw : 4 ≤ w) : gate hw ≠ free hw := by
  intro he
  have hv := congrArg Fin.val he
  change 0 = 1 at hv
  omega

private theorem gate_ne_wall (hw : 4 ≤ w) : gate hw ≠ wall hw := by
  intro he
  have hv := congrArg Fin.val he
  change 0 = 2 at hv
  omega

private theorem free_ne_wall (hw : 4 ≤ w) : free hw ≠ wall hw := by
  intro he
  have hv := congrArg Fin.val he
  change 1 = 2 at hv
  omega

private theorem feeder_ne_gate (hw : 4 ≤ w) : feeder hw ≠ gate hw := by
  intro he
  have hv := congrArg Fin.val he
  change w - 1 = 0 at hv
  omega

private theorem feeder_ne_free (hw : 4 ≤ w) : feeder hw ≠ free hw := by
  intro he
  have hv := congrArg Fin.val he
  change w - 1 = 1 at hv
  omega

private theorem feeder_ne_wall (hw : 4 ≤ w) : feeder hw ≠ wall hw := by
  intro he
  have hv := congrArg Fin.val he
  change w - 1 = 2 at hv
  omega

private theorem next_feeder (hw : 4 ≤ w) :
    cyclicNext w (by omega) (feeder hw) = gate hw := by
  simp [cyclicNext, show ¬ w - 1 + 1 < w by omega]

private theorem next_gate (hw : 4 ≤ w) :
    cyclicNext w (by omega) (gate hw) = free hw := by
  simp [cyclicNext, show 0 + 1 < w by omega]

private theorem next_free (hw : 4 ≤ w) :
    cyclicNext w (by omega) (free hw) = wall hw := by
  simp [cyclicNext, show 1 + 1 < w by omega]

/-- The board with a hole at the foot of the gate, in `(x,y)` coordinates. -/
def gatedX (hw : 4 ≤ w) (hh : 2 ≤ h) : Config (Position w h) := fun (x, y) =>
  if x = gate hw then (if y = bottom hh then .empty else .north)
  else if x = free hw then (if y = bottom hh then .north else .empty)
  else if x = wall hw then .north
  else if x = feeder hw then .east
  else .empty

/-- Close the gate by filling its hole with a single north car. -/
def gatedY (hw : 4 ≤ w) (hh : 2 ≤ h) : Config (Position w h) := fun p =>
  if p = (gate hw, bottom hh) then .north else gatedX hw hh p

theorem adds_one_north (hw : 4 ≤ w) (hh : 2 ≤ h) :
    gatedX hw hh (gate hw, bottom hh) = .empty ∧
    gatedY hw hh (gate hw, bottom hh) = .north ∧
    ∀ p, p ≠ (gate hw, bottom hh) → gatedY hw hh p = gatedX hw hh p := by
  exact ⟨by simp [gatedX], by simp [gatedY], fun p hp => by simp [gatedY, hp]⟩

private theorem gatedX_wall (hw : 4 ≤ w) (hh : 2 ≤ h) :
    FullNorthColumn (gatedX hw hh) (wall hw) := by
  intro y
  simp [gatedX, Ne.symm (gate_ne_wall hw), Ne.symm (free_ne_wall hw)]

private theorem gatedY_gate (hw : 4 ≤ w) (hh : 2 ≤ h) :
    FullNorthColumn (gatedY hw hh) (gate hw) := by
  intro y
  by_cases hy : y = bottom hh <;> simp [gatedY, gatedX, hy]

private theorem gatedY_wall (hw : 4 ≤ w) (hh : 2 ≤ h) :
    FullNorthColumn (gatedY hw hh) (wall hw) := by
  intro y
  simpa [gatedY, Ne.symm (gate_ne_wall hw)] using gatedX_wall hw hh y

private theorem next_row_ne_self (hh : 2 ≤ h) (y : Fin h) :
    cyclicNext h (by omega) y ≠ y := by
  intro he
  have hv := congrArg Fin.val he
  have hy := y.isLt
  simp only [cyclicNext] at hv
  split at hv <;> simp_all <;> omega

/-- The loner is at row `t % h`, with no wrap ambiguity on the seam. -/
def freeCar (hw : 4 ≤ w) (hh : 2 ≤ h) (t : Nat) : Position w h :=
  (free hw, iterate (cyclicNext h (by omega)) t (bottom hh))

@[simp] theorem freeCar_row (hw : 4 ≤ w) (hh : 2 ≤ h) (t : Nat) :
    (freeCar hw hh t).2.val = t % h := by
  simp [freeCar, iterate_cyclicNext_val]

private def SingleNorth (s : Config (Position w h)) (x : Fin w) (row : Fin h) : Prop :=
  ∀ y, s (x, y) = if y = row then .north else .empty

private theorem singleNorth_canMove (hh : 2 ≤ h) {s : Config (Position w h)}
    {x : Fin w} {row : Fin h} (hs : SingleNorth s x row) :
    CanMove (n hh) .north s (x, row) := by
  refine ⟨by simpa [Species.cell] using hs row, ?_⟩
  change s (x, cyclicNext h (by omega) row) = .empty
  rw [hs]
  simp [next_row_ne_self hh row]

private theorem singleNorth_north (hh : 2 ≤ h) {s : Config (Position w h)}
    {x : Fin w} {row : Fin h} (hs : SingleNorth s x row) :
    SingleNorth (halfStep (n hh) .north s) x (cyclicNext h (by omega) row) := by
  intro y
  have hm := singleNorth_canMove hh hs
  by_cases hy : y = row
  · subst y
    simpa [Ne.symm (next_row_ne_self hh row)] using
      moving_source_emptied (n hh) .north s (x, row) hm
  · have hprev : cyclicPrev h (by omega) y = row ↔ y = cyclicNext h (by omega) row := by
      constructor
      · intro he
        rw [← he, cyclicNext_prev]
      · intro he
        rw [he, cyclicPrev_next]
    by_cases ht : y = cyclicNext h (by omega) row
    · subst y
      simpa [northDirection, Species.cell] using moving_destination_filled (n hh) .north s (x, row) hm
    · have hp := hs (cyclicPrev h (by omega) y)
      simp [halfStep, northDirection, Species.cell, hs y, hy, hp, hprev, ht]

private theorem singleNorth_east (hw : 4 ≤ w) {s : Config (Position w h)}
    {row : Fin h} (hg : FullNorthColumn s (gate hw))
    (hs : SingleNorth s (free hw) row) :
    SingleNorth (halfStep (e hw) .east s) (free hw) row := by
  have hp : cyclicPrev w (by omega) (free hw) = gate hw := by
    rw [← next_gate hw, cyclicPrev_next]
  intro y
  have hwest : s (cyclicPrev w (by omega) (free hw), y) = .north := by
    rw [hp]
    exact hg y
  unfold halfStep
  change (if s (free hw, y) = .east then _ else
    if s (free hw, y) = .empty ∧ s (cyclicPrev w (by omega) (free hw), y) = .east
    then .east else s (free hw, y)) = _
  rw [hs y, hwest]
  split <;> simp_all

private theorem closed_gate_singleton (hw : 4 ≤ w) (hh : 2 ≤ h) (t : Nat) :
    SingleNorth (iterate (f hw hh) t (gatedY hw hh)) (free hw) (freeCar hw hh t).2 := by
  induction t with
  | zero =>
    intro y
    by_cases hy : y = bottom hh <;>
      simp [iterate, freeCar, gatedY, gatedX, Ne.symm (gate_ne_free hw), hy]
  | succ t ih =>
    have hg := fullNorthColumn_persists (by omega) (by omega) _ _
      (gatedY_gate hw hh) t
    exact singleNorth_north hh (singleNorth_east hw hg ih)

/-- Both full north rings persist, and their free lane contains only its original car. -/
theorem closed_gate (hw : 4 ≤ w) (hh : 2 ≤ h) (t : Nat) :
    let s := iterate (f hw hh) t (gatedY hw hh)
    FullNorthColumn s (gate hw) ∧ FullNorthColumn s (wall hw) ∧
      ∀ y, s (free hw, y) = if y = (freeCar hw hh t).2 then .north else .empty :=
  ⟨fullNorthColumn_persists (by omega) (by omega) _ _ (gatedY_gate hw hh) t,
   fullNorthColumn_persists (by omega) (by omega) _ _ (gatedY_wall hw hh) t,
   closed_gate_singleton hw hh t⟩

theorem freeCar_canMove (hw : 4 ≤ w) (hh : 2 ≤ h) (t : Nat) :
    CanMove (n hh) .north (halfStep (e hw) .east
      (iterate (f hw hh) t (gatedY hw hh))) (freeCar hw hh t) :=
  singleNorth_canMove hh (singleNorth_east hw (closed_gate hw hh t).1
    (closed_gate_singleton hw hh t))

theorem freeCar_is_original (hw : 4 ≤ w) (hh : 2 ≤ h) :
    gatedX hw hh (freeCar hw hh 0) = .north := by
  simp [freeCar, iterate, gatedX, Ne.symm (gate_ne_free hw)]

/-- The formula for the loner agrees with the kernel's tagged-car trace. -/
theorem freeCar_trace (hw : 4 ≤ w) (hh : 2 ≤ h) (t : Nat) :
    carTrace (e hw) (n hh) .north (gatedY hw hh) t (freeCar hw hh 0) =
      freeCar hw hh t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [carTrace, ih, roundTransport, transport]
    change (if CanMove (n hh) .north
      (halfStep (e hw) .east (iterate (f hw hh) t (gatedY hw hh))) (freeCar hw hh t)
      then (n hh).next (freeCar hw hh t) else freeCar hw hh t) = _
    simp only [freeCar_canMove hw hh t, ↓reduceIte]
    rfl

theorem gatedY_never_jams (hw : 4 ≤ w) (hh : 2 ≤ h) (t : Nat) :
    ¬ Jam (e hw) (n hh) (iterate (f hw hh) t (gatedY hw hh)) := by
  intro hj
  exact ((noMoves_iff_frozen _ _ _).mpr hj.2).2 _ (freeCar_canMove hw hh t)

/-! ## The open gate has a finite eastbound movement budget -/

private theorem gatedX_is_east (hw : 4 ≤ w) (hh : 2 ≤ h) (p : Position w h) :
    gatedX hw hh p = .east ↔ p.1 = feeder hw := by
  obtain ⟨x, y⟩ := p
  by_cases hf : x = feeder hw
  · subst x
    simp [gatedX, feeder_ne_gate hw, feeder_ne_free hw, feeder_ne_wall hw]
  · simp [gatedX, hf]
    split <;> (try split) <;> (try split) <;> simp_all

/-- Hypotheses for the eastbound budget. No restriction on the north phase is
needed beyond the persistent full wall. -/
def EastConfined (hw : 4 ≤ w) (s : Config (Position w h)) : Prop :=
  ∀ p, s p = .east → p.1 = feeder hw ∨ p.1 = gate hw ∨ p.1 = free hw

private theorem east_move_path (hw : 4 ≤ w) {s : Config (Position w h)}
    (hc : EastConfined hw s) (hwall : FullNorthColumn s (wall hw))
    {p : Position w h} (hm : CanMove (e hw) .east s p) :
    (p.1 = feeder hw ∧ ((e hw).next p).1 = gate hw) ∨
    (p.1 = gate hw ∧ ((e hw).next p).1 = free hw) := by
  rcases hc p hm.1 with hf | hg | hr
  · exact Or.inl ⟨hf, by simp [eastDirection, hf, next_feeder hw]⟩
  · exact Or.inr ⟨hg, by simp [eastDirection, hg, next_gate hw]⟩
  · have he : s (wall hw, p.2) = .empty := by
      simpa [eastDirection, hr, next_free hw] using hm.2
    rw [hwall p.2] at he
    cases he

private theorem eastConfined_step (hw : 4 ≤ w) (hh : 2 ≤ h)
    {s : Config (Position w h)} (hc : EastConfined hw s)
    (hwall : FullNorthColumn s (wall hw)) :
    EastConfined hw (f hw hh s) := by
  intro q hq
  obtain ⟨p, hp, ht⟩ := roundTransport_surjective_on_cars (e hw) (n hh) .east s q hq
  rw [← ht]
  change (transport (e hw) .east s p).1 = feeder hw ∨
    (transport (e hw) .east s p).1 = gate hw ∨ (transport (e hw) .east s p).1 = free hw
  by_cases hm : CanMove (e hw) .east s p
  · rcases east_move_path hw hc hwall hm with ⟨_, he⟩ | ⟨_, he⟩
    · exact Or.inr (Or.inl (by simpa [transport, hm] using he))
    · exact Or.inr (Or.inr (by simpa [transport, hm] using he))
  · simpa [transport, hm] using hc p hp

theorem gatedX_eastConfined (hw : 4 ≤ w) (hh : 2 ≤ h) (t : Nat) :
    EastConfined hw (iterate (f hw hh) t (gatedX hw hh)) := by
  induction t with
  | zero => exact fun p hp => Or.inl ((gatedX_is_east hw hh p).mp hp)
  | succ t ih =>
    exact eastConfined_step hw hh ih
      (fullNorthColumn_persists (by omega) (by omega) _ _ (gatedX_wall hw hh) t)

private def remaining (hw : 4 ≤ w) (p : Position w h) : Nat :=
  if p.1 = feeder hw then 2 else if p.1 = gate hw then 1 else 0

/-- Remaining east advances before the persistent wall, summed over actual east cars. -/
def eastPotential (hw : 4 ≤ w) (s : Config (Position w h)) : Nat :=
  ((speciesCells w h .east s).map (remaining hw)).sum

private theorem east_cell_transport_balance (hw : 4 ≤ w)
    {s : Config (Position w h)} (hc : EastConfined hw s)
    (hwall : FullNorthColumn s (wall hw)) (p : Position w h) :
    remaining hw (transport (e hw) .east s p) +
      (if CanMove (e hw) .east s p then 1 else 0) = remaining hw p := by
  by_cases hm : CanMove (e hw) .east s p
  · rcases east_move_path hw hc hwall hm with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · simp [remaining, transport, hm, hp, hq, Ne.symm (feeder_ne_gate hw)]
    · simp [remaining, transport, hm, hp, hq, Ne.symm (feeder_ne_gate hw),
        Ne.symm (feeder_ne_free hw), Ne.symm (gate_ne_free hw)]
  · simp [transport, hm]

private theorem east_moveCount_speciesCells (hw : 4 ≤ w) (s : Config (Position w h)) :
    ((speciesCells w h .east s).map (fun p => if CanMove (e hw) .east s p then 1 else 0)).sum =
      moveCount w h (e hw) .east s := by
  unfold moveCount
  rw [← length_filter_eq_indicator_sum, ← length_filter_eq_indicator_sum]
  rw [speciesCells, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro p _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun hp => hp.1, fun hp => ⟨hp, hp.1⟩⟩

/-- Each actual east mover spends one unit of potential, including the wrap from
the last column to the gate. North movement leaves this potential unchanged. -/
theorem eastPotential_step_balance (hw : 4 ≤ w) (hh : 2 ≤ h)
    {s : Config (Position w h)} (hc : EastConfined hw s)
    (hwall : FullNorthColumn s (wall hw)) :
    eastPotential hw (f hw hh s) + moveCount w h (e hw) .east s = eastPotential hw s := by
  let mid := halfStep (e hw) .east s
  have hcells : speciesCells w h .east (f hw hh s) = speciesCells w h .east mid := by
    apply List.filter_congr
    intro p _
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact other_species_unchanged (n hh) .north mid p .east (by decide) (by decide)
  have hperm := (speciesCells_transport_perm w h (e hw) .east s).map (remaining hw)
  unfold eastPotential
  rw [hcells, hperm.sum_nat, List.map_map, ← east_moveCount_speciesCells hw,
    ← capture_sum_map_add]
  congr 1
  apply List.map_congr_left
  intro p _
  exact east_cell_transport_balance hw hc hwall p

private theorem gatedX_eastPotential (hw : 4 ≤ w) (hh : 2 ≤ h) :
    eastPotential hw (gatedX hw hh) = 2 * h := by
  let column := (List.finRange h).map (fun y => (feeder hw, y))
  have hnodup : column.Nodup := by
    apply List.pairwise_map.mpr
    exact (List.nodup_finRange h).imp (fun hne he => hne (congrArg Prod.snd he))
  have hperm : (speciesCells w h .east (gatedX hw hh)).Perm column := by
    apply (List.perm_ext_iff_of_nodup (speciesCells_nodup w h .east _) hnodup).mpr
    intro p
    simp only [mem_speciesCells, Species.cell, gatedX_is_east, column, List.mem_map]
    constructor
    · intro hp
      exact ⟨p.2, List.mem_finRange p.2, Prod.ext hp.symm rfl⟩
    · rintro ⟨y, _, rfl⟩
      rfl
  rw [eastPotential, (hperm.map (remaining hw)).sum_nat]
  simp [column, List.map_map, Function.comp_def, remaining, List.map_const', List.sum_replicate_nat, Nat.mul_comm]

/-- Exact number of east moves in the first `t` full rounds of the open gate. -/
def eastMovesThrough (hw : 4 ≤ w) (hh : 2 ≤ h) : Nat → Nat
  | 0 => 0
  | t+1 => eastMovesThrough hw hh t +
      moveCount w h (e hw) .east (iterate (f hw hh) t (gatedX hw hh))

theorem gatedX_east_balance (hw : 4 ≤ w) (hh : 2 ≤ h) (t : Nat) :
    eastPotential hw (iterate (f hw hh) t (gatedX hw hh)) + eastMovesThrough hw hh t = 2 * h := by
  induction t with
  | zero => simpa [iterate, eastMovesThrough] using gatedX_eastPotential hw hh
  | succ t ih =>
    have hb := eastPotential_step_balance hw hh (gatedX_eastConfined hw hh t)
      (fullNorthColumn_persists (by omega) (by omega) _ _ (gatedX_wall hw hh) t)
    simp only [eastMovesThrough, iterate]
    omega

theorem gatedX_eastMoves_le (hw : 4 ≤ w) (hh : 2 ≤ h) (t : Nat) :
    eastMovesThrough hw hh t ≤ 2 * h := by
  have he := gatedX_east_balance hw hh t
  omega

private theorem east_blocked_of_moveCount_zero (hw : 4 ≤ w) (s : Config (Position w h))
    (hz : moveCount w h (e hw) .east s = 0) : Blocked (e hw) .east s := by
  intro p hp he
  have hm : CanMove (e hw) .east s p := ⟨hp, he⟩
  unfold moveCount at hz
  have hterm : (if CanMove (e hw) .east s p then 1 else 0) ∈
      (positions w h).map (fun q => if CanMove (e hw) .east s q then 1 else 0) :=
    List.mem_map_of_mem (mem_positions w h p)
  exact (by simpa [hm] using List.sum_eq_zero_iff_forall_eq_nat.mp hz _ hterm : False)

/-- The conserved lane data needed for the open gate to jam. The hole and the
single north car need not start in the bottom row for this argument. -/
private structure OpenGate (hw : 4 ≤ w) (s : Config (Position w h)) : Prop where
  wall_full : FullNorthColumn s (wall hw)
  east_confined : EastConfined hw s
  east_rows : ∀ y, ¬ EastFreeRow s y
  gate_not_full : ¬ FullNorthColumn s (gate hw)
  free_not_full : ¬ FullNorthColumn s (free hw)
  free_has_north : ¬ NorthFreeColumn s (free hw)
  north_columns : ∀ x, x ≠ gate hw → x ≠ free hw → x ≠ wall hw → NorthFreeColumn s x

private theorem gatedX_open (hw : 4 ≤ w) (hh : 2 ≤ h) :
    OpenGate hw (gatedX hw hh) := by
  refine ⟨gatedX_wall hw hh, gatedX_eastConfined hw hh 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact hy (feeder hw) ((gatedX_is_east hw hh _).mpr rfl)
  · intro hfull
    have hc := hfull (bottom hh)
    simp [gatedX] at hc
  · intro hfull
    let y : Fin h := ⟨1, by omega⟩
    have hy : y ≠ bottom hh := by
      intro he
      have hv : 1 = 0 := congrArg Fin.val he
      omega
    have hc := hfull y
    simp [gatedX, Ne.symm (gate_ne_free hw), hy] at hc
  · intro hnone
    exact hnone (bottom hh) (freeCar_is_original hw hh)
  · intro x hg hf hw' y
    simp only [gatedX, hg, hf, hw', ↓reduceIte]
    split <;> decide

private theorem OpenGate.iterate (hw : 4 ≤ w) (hh : 2 ≤ h)
    {s : Config (Position w h)} (hg : OpenGate hw s) (t : Nat) :
    OpenGate hw (BML.iterate (f hw hh) t s) := by
  have hwall (u : Nat) := fullNorthColumn_persists (by omega) (by omega) _ _ hg.wall_full u
  refine ⟨hwall t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · induction t with
    | zero => exact hg.east_confined
    | succ t ih => exact eastConfined_step hw hh ih (hwall t)
  · intro y hy
    exact hg.east_rows y ((eastFreeRow_iterate_iff (by omega) (by omega) s y t).mp hy)
  · intro hf
    exact hg.gate_not_full (fullNorthColumn_reflects (by omega) (by omega) s _ t hf)
  · intro hf
    exact hg.free_not_full (fullNorthColumn_reflects (by omega) (by omega) s _ t hf)
  · intro hz
    exact hg.free_has_north ((northFreeColumn_iterate_iff (by omega) (by omega) s _ t).mp hz)
  · intro x hgate hfree hw'
    exact (northFreeColumn_iterate_iff (by omega) (by omega) s x t).mpr
      (hg.north_columns x hgate hfree hw')

private theorem OpenGate.eventually_east_blocked (hw : 4 ≤ w) (hh : 2 ≤ h)
    {s : Config (Position w h)} (hg : OpenGate hw s) :
    ∃ start, ∀ t, Blocked (e hw) .east (BML.iterate (f hw hh) (start + t) s) := by
  obtain ⟨start, hs⟩ := eventually_zero_cost
    (fun t => eastPotential hw (BML.iterate (f hw hh) t s))
    (fun t => moveCount w h (e hw) .east (BML.iterate (f hw hh) t s))
    (fun t => eastPotential_step_balance hw hh (hg.iterate hw hh t).east_confined
      (hg.iterate hw hh t).wall_full)
  exact ⟨start, fun t => east_blocked_of_moveCount_zero hw _ (hs t)⟩

/-- The east phase is eventually always the identity, with no time bound asserted. -/
theorem gatedX_eventually_east_blocked (hw : 4 ≤ w) (hh : 2 ≤ h) :
    ∃ start, ∀ t, Blocked (e hw) .east (iterate (f hw hh) (start + t) (gatedX hw hh)) :=
  (gatedX_open hw hh).eventually_east_blocked hw hh

/-! ## The tail with stationary east cars reaches gridlock -/

/-- If all core sites of a column were north cars, a single such site would
force the whole column into the core. A non-full column thus needs an east
obstacle wherever the core meets it. -/
private theorem core_east_in_column (hw : 4 ≤ w) (hh : 2 ≤ h)
    {s : Config (Position w h)} (core : BlockingCore (e hw) (n hh) s) (x : Fin w)
    (hne : ∃ y, core.sites (x, y)) (hfull : ¬ FullNorthColumn s x) :
    ∃ y, core.sites (x, y) ∧ s (x, y) = .east := by
  classical
  apply Classical.byContradiction
  intro hno
  have hn (y : Fin h) (hy : core.sites (x, y)) : s (x, y) = .north := by
    cases hs : s (x, y) with
    | empty => exact False.elim (core.occupied _ hy hs)
    | east => exact False.elim (hno ⟨y, hy, hs⟩)
    | north => rfl
  obtain ⟨y, hy⟩ := hne
  have hall := Train.cyclic_all_of_step (by omega : 0 < h) (fun z => core.sites (x, z))
    (fun z hz => core.north_closed (x, z) hz (hn z hz)) y hy
  exact hfull (fun z => hn z (hall z))

private theorem OpenGate.terminal_obstacles (hw : 4 ≤ w) (hh : 2 ≤ h)
    {s : Config (Position w h)} (hg : OpenGate hw s)
    (core : BlockingCore (e hw) (n hh) s)
    (he : ∀ p, s p = .east → core.sites p) :
    (∃ y, core.sites (gate hw, y) ∧ s (gate hw, y) = .east) ∧
    (∃ y, core.sites (free hw, y) ∧ s (free hw, y) = .east) := by
  classical
  -- The free column has a north car. Its row has an east car elsewhere,
  -- so either the gate contains that car or it blocks its feeder predecessor.
  obtain ⟨y, hy⟩ : ∃ y, s (free hw, y) = .north := by
    simpa only [NorthFreeColumn, Classical.not_forall, Classical.not_not] using hg.free_has_north
  obtain ⟨x, hx⟩ : ∃ x, s (x, y) = .east := by
    simpa only [EastFreeRow, Classical.not_forall, Classical.not_not] using hg.east_rows y
  have hgate : ∃ z, core.sites (gate hw, z) := by
    rcases hg.east_confined (x,y) hx with hf | hz | hr
    · change x = feeder hw at hf
      subst x
      refine ⟨y, ?_⟩
      simpa [eastDirection, next_feeder hw] using core.east_closed _ (he _ hx) hx
    · change x = gate hw at hz
      subst x
      exact ⟨y, he _ hx⟩
    · change x = free hw at hr
      subst x
      rw [hy] at hx
      cases hx
  obtain ⟨z, hz, hze⟩ := core_east_in_column hw hh core (gate hw) hgate hg.gate_not_full
  have hfree : core.sites (free hw, z) := by
    simpa [eastDirection, next_gate hw] using core.east_closed _ hz hze
  exact ⟨⟨z, hz, hze⟩, core_east_in_column hw hh core (free hw) ⟨z, hfree⟩ hg.free_not_full⟩

/-- On any tail with a blocked east phase, east occupancy is constant. -/
private theorem tail_east_iff (hw : 4 ≤ w) (hh : 2 ≤ h)
    {s : Config (Position w h)} (hb : ∀ t, Blocked (e hw) .east (iterate (f hw hh) t s))
    (p : Position w h) (t : Nat) :
    iterate (f hw hh) t s p = .east ↔ s p = .east := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change halfStep (n hh) .north (halfStep (e hw) .east (iterate (f hw hh) t s)) p =
      .east ↔ s p = .east
    rw [halfStep_eq_of_blocked _ _ _ (hb t)]
    exact (other_species_unchanged (n hh) .north _ p .east (by decide) (by decide)).trans ih

private theorem OpenGate.reaches_terminal_core (hw : 4 ≤ w) (hh : 2 ≤ h)
    {s : Config (Position w h)} (hg : OpenGate hw s) :
    ∃ start, ∃ core : BlockingCore (e hw) (n hh) (BML.iterate (f hw hh) start s),
      (∀ p, BML.iterate (f hw hh) start s p = .east → core.sites p) ∧
      (∀ y, core.sites (wall hw, y)) ∧
      (∃ y, core.sites (gate hw, y) ∧ BML.iterate (f hw hh) start s (gate hw, y) = .east) ∧
      (∃ y, core.sites (free hw, y) ∧ BML.iterate (f hw hh) start s (free hw, y) = .east) := by
  obtain ⟨start, hs⟩ := hg.eventually_east_blocked hw hh
  let tail := BML.iterate (f hw hh) start s
  have hb (t : Nat) : Blocked (e hw) .east (BML.iterate (f hw hh) t tail) := by
    simpa only [tail, ← iterate_add] using hs t
  obtain ⟨u, core, hsites⟩ := future_blockingCore_of_eventually_permanent_sites (e hw) (n hh) tail
  have he (p : Position w h) (hp : BML.iterate (f hw hh) u tail p = .east) : core.sites p := by
    apply (hsites p).mpr
    refine ⟨.east, 0, fun t => ?_⟩
    simpa only [Nat.zero_add, f, torusStep, Species.cell] using
      (tail_east_iff hw hh hb p t).mpr ((tail_east_iff hw hh hb p u).mp hp)
  have ht := (hg.iterate hw hh start).iterate hw hh u
  have hwall (y : Fin h) : core.sites (wall hw, y) := by
    apply (hsites _).mpr
    refine ⟨.north, 0, fun t => ?_⟩
    simpa only [Nat.zero_add, f, torusStep, Species.cell, tail] using
      ((hg.iterate hw hh start).iterate hw hh t).wall_full y
  obtain ⟨hgate, hfree⟩ := ht.terminal_obstacles hw hh core he
  refine ⟨start+u, ?_⟩
  rw [iterate_add]
  exact ⟨core, he, hwall, hgate, hfree⟩

/-- An unconditional terminal-tail consequence for the specified open gate.
The core includes east obstacles in both north columns that could otherwise circulate. -/
theorem gatedX_terminal_obstacles (hw : 4 ≤ w) (hh : 2 ≤ h) :
    ∃ start, ∃ core : BlockingCore (e hw) (n hh) (iterate (f hw hh) start (gatedX hw hh)),
      (∃ y, core.sites (gate hw, y) ∧
        iterate (f hw hh) start (gatedX hw hh) (gate hw, y) = .east) ∧
      (∃ y, core.sites (free hw, y) ∧
        iterate (f hw hh) start (gatedX hw hh) (free hw, y) = .east) := by
  obtain ⟨t, core, _, _, hg, hf⟩ := (gatedX_open hw hh).reaches_terminal_core hw hh
  exact ⟨t, core, hg, hf⟩

/-- A permanent obstacle on a north car's route gives a finite movement
potential even when unused columns have no obstacles. -/
private theorem north_tag_stops (hw : 4 ≤ w) (hh : 2 ≤ h)
    {s : Config (Position w h)} (core : BlockingCore (e hw) (n hh) s)
    (p : Position w h) (hp : s p = .north) (row : Fin h) (hr : core.sites (p.1, row)) :
    TagEventuallyStopped (e hw) (n hh) .north s p := by
  let trace := fun t => carTrace (e hw) (n hh) .north s t p
  let orbit := fun t => iterate (f hw hh) t s
  let rank := fun t => cyclicDistance h (trace t).2 row
  let moves := fun t => RoundCanMove (e hw) (n hh) .north (orbit t) (trace t)
  have hcolumn (t : Nat) : (trace t).1 = p.1 := by
    induction t with
    | zero => rfl
    | succ t ih =>
      change (transport (n hh) .north (halfStep (e hw) .east (orbit t)) (trace t)).1 = _
      have hpair := north_transport_pair (by omega : 0 < h) (halfStep (e hw) .east (orbit t))
        (trace t).1 (trace t).2
      exact (congrArg Prod.fst hpair).trans ih
  have hbalance (t : Nat) : rank (t+1) + (if moves t then 1 else 0) = rank t := by
    by_cases hm : moves t
    · have hne : (trace t).2 ≠ row := by
        intro he
        have hsite : trace t = (p.1, row) := Prod.ext (hcolumn t) he
        exact core.no_round_move _ (core.persists t) .north _
          (hsite ▸ hr) hm
      have hnext : (trace (t+1)).2 = cyclicNext h (by omega) (trace t).2 := by
        change (transport (n hh) .north (halfStep (e hw) .east (orbit t)) (trace t)).2 = _
        have hc : CanMove (n hh) .north (halfStep (e hw) .east (orbit t)) (trace t) := hm
        simp only [transport, hc, ↓reduceIte]
        rfl
      simpa only [rank, hm, ↓reduceIte, hnext] using
        cyclicDistance_next h (by omega) (trace t).2 row hne
    · have hstay : trace (t+1) = trace t :=
        roundTransport_eq_of_no_round_move (e hw) (n hh) .north (orbit t) (trace t) hm
      simp [rank, hstay, hm]
  obtain ⟨start, hstop⟩ := eventually_zero_cost rank (fun t => if moves t then 1 else 0) hbalance
  refine (tagEventuallyStopped_iff_finitely_many_moves (e hw) (n hh) .north s p hp).mpr ⟨start, ?_⟩
  intro t hm
  have hz := hstop t
  have hc : moves (start+t) := hm
  simp [hc] at hz

private theorem OpenGate.eventually_jams (hw : 4 ≤ w) (hh : 2 ≤ h)
    {s : Config (Position w h)} (hg : OpenGate hw s) :
    EventuallyJammed (e hw) (n hh) s := by
  obtain ⟨start, core, he, hwall, ⟨gateRow, hgate, _⟩, ⟨freeRow, hfree, _⟩⟩ :=
    hg.reaches_terminal_core hw hh
  let u := BML.iterate (f hw hh) start s
  have ht := hg.iterate hw hh start
  have hstopped : AllCarsEventuallyStopped (e hw) (n hh) u := by
    intro sp p hp
    cases sp with
    | east =>
      exact tagEventuallyStopped_of_pathCoreMember (e hw) (n hh) .east u p hp 0
        (core.pathCoreMember (e hw) (n hh) (he p hp))
    | north =>
      by_cases h0 : p.1 = gate hw
      · exact north_tag_stops hw hh core p hp gateRow (by simpa [h0] using hgate)
      by_cases h1 : p.1 = free hw
      · exact north_tag_stops hw hh core p hp freeRow (by simpa [h1] using hfree)
      by_cases h2 : p.1 = wall hw
      · exact north_tag_stops hw hh core p hp p.2 (by simpa [h2] using hwall p.2)
      exact False.elim (ht.north_columns p.1 h0 h1 h2 p.2 hp)
  obtain ⟨t, hj⟩ := eventuallyJammed_of_all_cars_stopped (e hw) (n hh) u hstopped
    ⟨(wall hw, bottom hh), core.occupied _ (hwall _)⟩
  refine ⟨start+t, ?_⟩
  change Jam (e hw) (n hh) (BML.iterate (f hw hh) (start+t) s)
  rwa [iterate_add]

theorem gatedX_eventually_jams (hw : 4 ≤ w) (hh : 2 ≤ h) :
    EventuallyJammed (e hw) (n hh) (gatedX hw hh) :=
  (gatedX_open hw hh).eventually_jams hw hh

/-- Theorem U's column witness. The original north car moves in every round. -/
theorem gated_genuine (hw : 4 ≤ w) (hh : 2 ≤ h) :
    EventuallyJammed (e hw) (n hh) (gatedX hw hh) ∧
    (∀ t, ¬ Jam (e hw) (n hh) (iterate (f hw hh) t (gatedY hw hh))) ∧
    gatedX hw hh (freeCar hw hh 0) = .north ∧
    ∀ t, RoundCanMove (e hw) (n hh) .north (iterate (f hw hh) t (gatedY hw hh))
      (carTrace (e hw) (n hh) .north (gatedY hw hh) t (freeCar hw hh 0)) := by
  refine ⟨gatedX_eventually_jams hw hh, gatedY_never_jams hw hh, freeCar_is_original hw hh, ?_⟩
  intro t
  rw [freeCar_trace hw hh t]
  exact freeCar_canMove hw hh t

/-! ## Handoff to the phase-shifted row construction -/

private theorem OpenGate.north_halfStep (hw : 4 ≤ w) (hh : 2 ≤ h)
    {s : Config (Position w h)} (hg : OpenGate hw s) :
    OpenGate hw (halfStep (n hh) .north s) := by
  have hn := northColumnCount_north_halfStep (by omega : 0 < h) s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← northColumnCount_eq_height_iff, hn, northColumnCount_eq_height_iff]
    exact hg.wall_full
  · intro p hp
    exact hg.east_confined p
      ((other_species_unchanged (n hh) .north s p .east (by decide) (by decide)).mp hp)
  · intro y
    rw [← eastRowCount_eq_zero_iff, eastRowCount_north_halfStep, eastRowCount_eq_zero_iff]
    exact hg.east_rows y
  · rw [← northColumnCount_eq_height_iff, hn, northColumnCount_eq_height_iff]
    exact hg.gate_not_full
  · rw [← northColumnCount_eq_height_iff, hn, northColumnCount_eq_height_iff]
    exact hg.free_not_full
  · rw [← northColumnCount_eq_zero_iff, hn, northColumnCount_eq_zero_iff]
    exact hg.free_has_north
  · intro x h0 h1 h2
    rw [← northColumnCount_eq_zero_iff, hn, northColumnCount_eq_zero_iff]
    exact hg.north_columns x h0 h1 h2

/-- Starting at the north checkpoint changes the locations of the holes and
north cars but preserves the open gate's jamming argument. -/
theorem gatedX_after_north_eventually_jams (hw : 4 ≤ w) (hh : 2 ≤ h) :
    EventuallyJammed (e hw) (n hh) (halfStep (n hh) .north (gatedX hw hh)) :=
  ((gatedX_open hw hh).north_halfStep hw hh).eventually_jams hw hh

private theorem gatedY_east_in_feeder (hw : 4 ≤ w) (hh : 2 ≤ h)
    (p : Position w h) (hp : gatedY hw hh p = .east) : p.1 = feeder hw := by
  by_cases hz : p = (gate hw, bottom hh)
  · simp [gatedY, hz] at hp
  · exact (gatedX_is_east hw hh p).mp (by simpa [gatedY, hz] using hp)

/-- East motion along the entire closed-gate orbit is blocked at the feeder. -/
theorem gatedY_east_blocked (hw : 4 ≤ w) (hh : 2 ≤ h) (t : Nat) :
    Blocked (e hw) .east (iterate (f hw hh) t (gatedY hw hh)) := by
  let orbit := fun i => iterate (f hw hh) i (gatedY hw hh)
  have block (i : Nat) (hf : ∀ p, orbit i p = .east → p.1 = feeder hw) :
      Blocked (e hw) .east (orbit i) := by
    intro p hp
    have he : (e hw).next p = (gate hw, p.2) := by
      simp [eastDirection, hf p hp, next_feeder hw]
    rw [he]
    change iterate (f hw hh) i (gatedY hw hh) (gate hw, p.2) ≠ .empty
    rw [(closed_gate hw hh i).1 p.2]
    decide
  have hf (i : Nat) : ∀ p, orbit i p = .east → p.1 = feeder hw := by
    induction i with
    | zero => exact gatedY_east_in_feeder hw hh
    | succ i ih =>
      intro p hp
      apply ih p
      change halfStep (n hh) .north (halfStep (e hw) .east (orbit i)) p = .east at hp
      rw [halfStep_eq_of_blocked _ _ _ (block i ih)] at hp
      exact (other_species_unchanged (n hh) .north _ p .east (by decide) (by decide)).mp hp
  exact block t (hf t)

end BML.Gated
