import BML.Transport
import BML.Torus
import Train.Counting

/-!
Numerical lane invariants for the CLASSIC BML kernel.

`Train.Counting` imports only `BML.Torus` and supplies finite-list combinatorics.
No TRAIN transition, eligibility, conservation, or fixed-point theorem is used.
All transport facts below are the CLASSIC theorems from `BML.Transport`.
-/
namespace BML

/-- Conservation of the existing executable species-count sum under a CLASSIC phase. -/
theorem speciesCount_halfStep (w h : Nat) (d : Direction (Position w h))
    (moving counted : Species) (s : Config (Position w h)) :
    speciesCount w h counted (halfStep d moving s) = speciesCount w h counted s := by
  rw [Train.Counting.speciesCount_eq_filter_length,
    Train.Counting.speciesCount_eq_filter_length]
  by_cases hc : counted = moving
  · subst counted
    symm
    apply Train.Counting.filter_length_eq_of_bijection (positions w h)
      (Train.Counting.positions_nodup w h) (Train.Counting.mem_positions w h)
      (fun p => decide (s p = moving.cell))
      (fun p => decide (halfStep d moving s p = moving.cell))
      (transport d moving s)
    · intro p hp
      exact decide_eq_true (transport_preserves_car d moving s p (of_decide_eq_true hp))
    · intro p q hp hq heq
      exact transport_injective_on_cars d moving s p q
        (of_decide_eq_true hp) (of_decide_eq_true hq) heq
    · intro q hq
      obtain ⟨p, hp, heq⟩ := transport_surjective_on_cars d moving s q (of_decide_eq_true hq)
      exact ⟨p, decide_eq_true hp, heq⟩
  · have hcell : counted.cell ≠ moving.cell := by
      cases counted <;> cases moving <;> simp_all [Species.cell]
    have hf : (fun p => decide (halfStep d moving s p = counted.cell)) =
        (fun p => decide (s p = counted.cell)) := by
      funext p
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using
        other_species_unchanged d moving s p counted.cell counted.cell_ne_empty hcell
    rw [hf]

theorem speciesCount_step (w h : Nat) (east north : Direction (Position w h))
    (counted : Species) (s : Config (Position w h)) :
    speciesCount w h counted (step east north s) = speciesCount w h counted s := by
  simp only [step, speciesCount_halfStep]

theorem speciesCount_iterate (w h : Nat) (east north : Direction (Position w h))
    (counted : Species) (s : Config (Position w h)) (t : Nat) :
    speciesCount w h counted (iterate (step east north) t s) =
      speciesCount w h counted s := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [iterate, speciesCount_step] using ih

def eastRowCount {w h : Nat} (s : Config (Position w h)) (y : Fin h) : Nat :=
  (List.finRange w).countP fun x => decide (s (x,y) = .east)

def northColumnCount {w h : Nat} (s : Config (Position w h)) (x : Fin w) : Nat :=
  (List.finRange h).countP fun y => decide (s (x,y) = .north)

def eastLaneTransport {w h : Nat} (hw : 0 < w) (s : Config (Position w h))
    (y : Fin h) (x : Fin w) : Fin w :=
  if CanMove (eastDirection w h hw) .east s (x,y) then cyclicNext w hw x else x

def northLaneTransport {w h : Nat} (hh : 0 < h) (s : Config (Position w h))
    (x : Fin w) (y : Fin h) : Fin h :=
  if CanMove (northDirection w h hh) .north s (x,y) then cyclicNext h hh y else y

theorem east_transport_pair {w h : Nat} (hw : 0 < w) (s : Config (Position w h))
    (x : Fin w) (y : Fin h) :
    transport (eastDirection w h hw) .east s (x,y) = (eastLaneTransport hw s y x,y) := by
  unfold transport eastLaneTransport
  split <;> rfl

theorem north_transport_pair {w h : Nat} (hh : 0 < h) (s : Config (Position w h))
    (x : Fin w) (y : Fin h) :
    transport (northDirection w h hh) .north s (x,y) = (x,northLaneTransport hh s x y) := by
  unfold transport northLaneTransport
  split <;> rfl

/-- The numerical east count in each row is preserved by the actual east phase. -/
theorem eastRowCount_east_halfStep {w h : Nat} (hw : 0 < w)
    (s : Config (Position w h)) (y : Fin h) :
    eastRowCount (halfStep (eastDirection w h hw) .east s) y = eastRowCount s y := by
  simp only [eastRowCount, List.countP_eq_length_filter]
  symm
  apply Train.Counting.filter_length_eq_of_bijection (List.finRange w)
    (List.nodup_finRange w) (fun x => List.mem_finRange x)
    (fun x => decide (s (x,y) = .east))
    (fun x => decide (halfStep (eastDirection w h hw) .east s (x,y) = .east))
    (eastLaneTransport hw s y)
  · intro x hx
    have hp := transport_preserves_car (eastDirection w h hw) .east s (x,y)
      (of_decide_eq_true hx)
    rw [east_transport_pair] at hp
    exact decide_eq_true hp
  · intro x z hx hz heq
    have hpair : transport (eastDirection w h hw) .east s (x,y) =
        transport (eastDirection w h hw) .east s (z,y) := by
      simp only [east_transport_pair, heq]
    exact congrArg Prod.fst (transport_injective_on_cars (eastDirection w h hw) .east s
      (x,y) (z,y) (of_decide_eq_true hx) (of_decide_eq_true hz) hpair)
  · intro z hz
    obtain ⟨⟨x,v⟩, hx, heq⟩ := transport_surjective_on_cars
      (eastDirection w h hw) .east s (z,y) (of_decide_eq_true hz)
    rw [east_transport_pair] at heq
    have hv : v = y := congrArg Prod.snd heq
    subst v
    exact ⟨x, decide_eq_true hx, congrArg Prod.fst heq⟩

theorem northColumnCount_north_halfStep {w h : Nat} (hh : 0 < h)
    (s : Config (Position w h)) (x : Fin w) :
    northColumnCount (halfStep (northDirection w h hh) .north s) x = northColumnCount s x := by
  simp only [northColumnCount, List.countP_eq_length_filter]
  symm
  apply Train.Counting.filter_length_eq_of_bijection (List.finRange h)
    (List.nodup_finRange h) (fun y => List.mem_finRange y)
    (fun y => decide (s (x,y) = .north))
    (fun y => decide (halfStep (northDirection w h hh) .north s (x,y) = .north))
    (northLaneTransport hh s x)
  · intro y hy
    have hp := transport_preserves_car (northDirection w h hh) .north s (x,y)
      (of_decide_eq_true hy)
    rw [north_transport_pair] at hp
    exact decide_eq_true hp
  · intro y z hy hz heq
    have hpair : transport (northDirection w h hh) .north s (x,y) =
        transport (northDirection w h hh) .north s (x,z) := by
      simp only [north_transport_pair, heq]
    exact congrArg Prod.snd (transport_injective_on_cars (northDirection w h hh) .north s
      (x,y) (x,z) (of_decide_eq_true hy) (of_decide_eq_true hz) hpair)
  · intro z hz
    obtain ⟨⟨u,y⟩, hy, heq⟩ := transport_surjective_on_cars
      (northDirection w h hh) .north s (x,z) (of_decide_eq_true hz)
    rw [north_transport_pair] at heq
    have hu : u = x := congrArg Prod.fst heq
    subst u
    exact ⟨y, decide_eq_true hy, congrArg Prod.snd heq⟩

theorem eastRowCount_north_halfStep {w h : Nat} (north : Direction (Position w h))
    (s : Config (Position w h)) (y : Fin h) :
    eastRowCount (halfStep north .north s) y = eastRowCount s y := by
  have hf : (fun x : Fin w => decide (halfStep north .north s (x,y) = .east)) =
      (fun x : Fin w => decide (s (x,y) = .east)) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using
      other_species_unchanged north .north s (x,y) .east (by decide) (by decide)
  unfold eastRowCount
  rw [hf]

theorem northColumnCount_east_halfStep {w h : Nat} (east : Direction (Position w h))
    (s : Config (Position w h)) (x : Fin w) :
    northColumnCount (halfStep east .east s) x = northColumnCount s x := by
  have hf : (fun y : Fin h => decide (halfStep east .east s (x,y) = .north)) =
      (fun y : Fin h => decide (s (x,y) = .north)) := by
    funext y
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using
      other_species_unchanged east .east s (x,y) .north (by decide) (by decide)
  unfold northColumnCount
  rw [hf]

theorem eastRowCount_step {w h : Nat} (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (y : Fin h) :
    eastRowCount (torusStep w h hw hh s) y = eastRowCount s y := by
  simp only [torusStep, step, eastRowCount_north_halfStep, eastRowCount_east_halfStep]

theorem northColumnCount_step {w h : Nat} (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (x : Fin w) :
    northColumnCount (torusStep w h hw hh s) x = northColumnCount s x := by
  simp only [torusStep, step, northColumnCount_north_halfStep, northColumnCount_east_halfStep]

theorem eastRowCount_iterate {w h : Nat} (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (y : Fin h) (t : Nat) :
    eastRowCount (iterate (torusStep w h hw hh) t s) y = eastRowCount s y := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [iterate, eastRowCount_step] using ih

theorem northColumnCount_iterate {w h : Nat} (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (x : Fin w) (t : Nat) :
    northColumnCount (iterate (torusStep w h hw hh) t s) x = northColumnCount s x := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [iterate, northColumnCount_step] using ih

def FullEastRow {w h : Nat} (s : Config (Position w h)) (y : Fin h) : Prop :=
  ∀ x, s (x,y) = .east

def FullNorthColumn {w h : Nat} (s : Config (Position w h)) (x : Fin w) : Prop :=
  ∀ y, s (x,y) = .north

def EastFreeRow {w h : Nat} (s : Config (Position w h)) (y : Fin h) : Prop :=
  ∀ x, s (x,y) ≠ .east

def NorthFreeColumn {w h : Nat} (s : Config (Position w h)) (x : Fin w) : Prop :=
  ∀ y, s (x,y) ≠ .north

/-- A full CLASSIC east row has no hidden rotation of its car identities. -/
theorem fullEastRow_no_moves {w h : Nat} (hw : 0 < w) (s : Config (Position w h))
    (y : Fin h) (he : FullEastRow s y) (x : Fin w) :
    ¬ CanMove (eastDirection w h hw) .east s (x,y) := by
  intro hm
  have hc := he (cyclicNext w hw x)
  have hz : s (cyclicNext w hw x,y) = .empty := hm.2
  rw [hc] at hz
  cases hz

/-- A full north column remains occupied through the east phase and cannot move north. -/
theorem fullNorthColumn_no_moves {w h : Nat} (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (x : Fin w) (hn : FullNorthColumn s x) (y : Fin h) :
    ¬ CanMove (northDirection w h hh) .north
      (halfStep (eastDirection w h hw) .east s) (x,y) := by
  intro hm
  have hc := (other_species_unchanged (eastDirection w h hw) .east s
    (x,cyclicNext h hh y) .north (by decide) (by decide)).mpr
      (hn (cyclicNext h hh y))
  have hz : halfStep (eastDirection w h hw) .east s (x,cyclicNext h hh y) = .empty := hm.2
  rw [hc] at hz
  cases hz

theorem eastRowCount_le_width {w h : Nat} (s : Config (Position w h)) (y : Fin h) :
    eastRowCount s y ≤ w := by
  simpa [eastRowCount] using
    (List.countP_le_length (p := fun x : Fin w => decide (s (x,y) = .east))
      (l := List.finRange w))

theorem northColumnCount_le_height {w h : Nat} (s : Config (Position w h)) (x : Fin w) :
    northColumnCount s x ≤ h := by
  simpa [northColumnCount] using
    (List.countP_le_length (p := fun y : Fin h => decide (s (x,y) = .north))
      (l := List.finRange h))

theorem eastRowCount_eq_width_iff {w h : Nat} (s : Config (Position w h)) (y : Fin h) :
    eastRowCount s y = w ↔ FullEastRow s y := by
  simpa [eastRowCount, FullEastRow] using
    (List.countP_eq_length (p := fun x : Fin w => decide (s (x,y) = .east))
      (l := List.finRange w))

theorem northColumnCount_eq_height_iff {w h : Nat} (s : Config (Position w h)) (x : Fin w) :
    northColumnCount s x = h ↔ FullNorthColumn s x := by
  simpa [northColumnCount, FullNorthColumn] using
    (List.countP_eq_length (p := fun y : Fin h => decide (s (x,y) = .north))
      (l := List.finRange h))

theorem eastRowCount_eq_zero_iff {w h : Nat} (s : Config (Position w h)) (y : Fin h) :
    eastRowCount s y = 0 ↔ EastFreeRow s y := by
  simp [eastRowCount, EastFreeRow]

theorem northColumnCount_eq_zero_iff {w h : Nat} (s : Config (Position w h)) (x : Fin w) :
    northColumnCount s x = 0 ↔ NorthFreeColumn s x := by
  simp [northColumnCount, NorthFreeColumn]

/-- A completely eastbound row exists at a later time exactly when it existed initially. -/
theorem fullEastRow_iterate_iff {w h : Nat} (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (y : Fin h) (t : Nat) :
    FullEastRow (iterate (torusStep w h hw hh) t s) y ↔ FullEastRow s y := by
  rw [← eastRowCount_eq_width_iff, ← eastRowCount_eq_width_iff, eastRowCount_iterate]

theorem fullNorthColumn_iterate_iff {w h : Nat} (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (x : Fin w) (t : Nat) :
    FullNorthColumn (iterate (torusStep w h hw hh) t s) x ↔ FullNorthColumn s x := by
  rw [← northColumnCount_eq_height_iff, ← northColumnCount_eq_height_iff,
    northColumnCount_iterate]

theorem fullEastRow_persists {w h : Nat} (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (y : Fin h) (hfull : FullEastRow s y) (t : Nat) :
    FullEastRow (iterate (torusStep w h hw hh) t s) y :=
  (fullEastRow_iterate_iff hw hh s y t).mpr hfull

theorem fullEastRow_reflects {w h : Nat} (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (y : Fin h) (t : Nat)
    (hfull : FullEastRow (iterate (torusStep w h hw hh) t s) y) : FullEastRow s y :=
  (fullEastRow_iterate_iff hw hh s y t).mp hfull

theorem fullNorthColumn_persists {w h : Nat} (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (x : Fin w) (hfull : FullNorthColumn s x) (t : Nat) :
    FullNorthColumn (iterate (torusStep w h hw hh) t s) x :=
  (fullNorthColumn_iterate_iff hw hh s x t).mpr hfull

theorem fullNorthColumn_reflects {w h : Nat} (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (x : Fin w) (t : Nat)
    (hfull : FullNorthColumn (iterate (torusStep w h hw hh) t s) x) : FullNorthColumn s x :=
  (fullNorthColumn_iterate_iff hw hh s x t).mp hfull

def HasFullMonochromaticLane {w h : Nat} (s : Config (Position w h)) : Prop :=
  (∃ y, FullEastRow s y) ∨ (∃ x, FullNorthColumn s x)

theorem hasFullMonochromaticLane_iterate_iff {w h : Nat} (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (t : Nat) :
    HasFullMonochromaticLane (iterate (torusStep w h hw hh) t s) ↔
      HasFullMonochromaticLane s := by
  simp only [HasFullMonochromaticLane, fullEastRow_iterate_iff, fullNorthColumn_iterate_iff]

/-- The full-E-row and full-N-column exceptional events are mutually exclusive. -/
theorem fullEastRow_excludes_fullNorthColumn {w h : Nat} (s : Config (Position w h))
    (y : Fin h) (he : FullEastRow s y) : ¬ ∃ x, FullNorthColumn s x := by
  rintro ⟨x, hn⟩
  have hc := he x
  rw [hn y] at hc
  cases hc

theorem eastFreeRow_iterate_iff {w h : Nat} (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (y : Fin h) (t : Nat) :
    EastFreeRow (iterate (torusStep w h hw hh) t s) y ↔ EastFreeRow s y := by
  rw [← eastRowCount_eq_zero_iff, ← eastRowCount_eq_zero_iff, eastRowCount_iterate]

theorem northFreeColumn_iterate_iff {w h : Nat} (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (x : Fin w) (t : Nat) :
    NorthFreeColumn (iterate (torusStep w h hw hh) t s) x ↔ NorthFreeColumn s x := by
  rw [← northColumnCount_eq_zero_iff, ← northColumnCount_eq_zero_iff,
    northColumnCount_iterate]

/-- Any specified collection of north-free columns, including a wrapping strip. -/
def NorthFreeColumns {w h : Nat} (s : Config (Position w h)) (columns : Fin w → Prop) : Prop :=
  ∀ x, columns x → NorthFreeColumn s x

theorem northFreeColumns_iterate_iff {w h : Nat} (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (columns : Fin w → Prop) (t : Nat) :
    NorthFreeColumns (iterate (torusStep w h hw hh) t s) columns ↔
      NorthFreeColumns s columns := by
  simp only [NorthFreeColumns, northFreeColumn_iterate_iff]

/-- `length` consecutive north-free columns, with indices interpreted cyclically.
Persistence does not need `length ≤ w`; distinct-column probability arguments do. -/
def NorthFreeStrip {w h : Nat} (hw : 0 < w) (s : Config (Position w h))
    (start : Fin w) (length : Nat) : Prop :=
  ∀ i : Fin length, NorthFreeColumn s (iterate (cyclicNext w hw) i.val start)

theorem northFreeStrip_iterate_iff {w h : Nat} (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (start : Fin w) (length t : Nat) :
    NorthFreeStrip hw (iterate (torusStep w h hw hh) t s) start length ↔
      NorthFreeStrip hw s start length := by
  simp only [NorthFreeStrip, northFreeColumn_iterate_iff]

def EastRowsBelow {w h : Nat} (s : Config (Position w h)) (bound : Nat) : Prop :=
  ∀ y, eastRowCount s y < bound

theorem eastRowsBelow_iterate_iff {w h : Nat} (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (bound t : Nat) :
    EastRowsBelow (iterate (torusStep w h hw hh) t s) bound ↔ EastRowsBelow s bound := by
  simp only [EastRowsBelow, eastRowCount_iterate]

end BML
