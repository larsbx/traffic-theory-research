import Train.Kernel
import Train.Counting
import Train.Finite

namespace BML.Train

/-- Numeric conservation for the actual executable species-count sum. -/
theorem speciesCount_halfStep (w h : Nat) (d : CyclicDirection (Position w h))
    (moving counted : Species) (s : Config (Position w h)) :
    BML.speciesCount w h counted (halfStep d moving s) =
      BML.speciesCount w h counted s := by
  rw [Counting.speciesCount_eq_filter_length, Counting.speciesCount_eq_filter_length]
  by_cases hc : counted = moving
  · subst counted
    symm
    apply Counting.filter_length_eq_of_bijection (positions w h)
      (Counting.positions_nodup w h) (Counting.mem_positions w h)
      (fun p => decide (s p = moving.cell))
      (fun p => decide (halfStep d moving s p = moving.cell))
      (transport d moving s)
    · intro p hp
      exact decide_eq_true (transport_preserves_car d moving s p (of_decide_eq_true hp))
    · intro p q hp hq hpq
      exact transport_injective_on_cars d moving s p q
        (of_decide_eq_true hp) (of_decide_eq_true hq) hpq
    · intro q hq
      obtain ⟨p, hp, hpq⟩ := transport_surjective_on_cars d moving s q (of_decide_eq_true hq)
      exact ⟨p, decide_eq_true hp, hpq⟩
  · have hcell : counted.cell ≠ moving.cell := by
      cases counted <;> cases moving <;> simp_all [Species.cell]
    have hf : (fun p => decide (halfStep d moving s p = counted.cell)) =
        (fun p => decide (s p = counted.cell)) := by
      funext p
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using other_species_unchanged d moving s p
        counted.cell counted.cell_ne_empty hcell
    rw [hf]

theorem speciesCount_step (w h : Nat) (east north : CyclicDirection (Position w h))
    (counted : Species) (s : Config (Position w h)) :
    BML.speciesCount w h counted (step east north s) = BML.speciesCount w h counted s := by
  simp only [step, speciesCount_halfStep]

theorem speciesCount_iterate (w h : Nat) (east north : CyclicDirection (Position w h))
    (counted : Species) (s : Config (Position w h)) (n : Nat) :
    BML.speciesCount w h counted (BML.iterate (step east north) n s) =
      BML.speciesCount w h counted s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [BML.iterate, speciesCount_step] using ih

theorem population_eq_speciesCounts {w h : Nat} (s : Config (Position w h)) :
    population s = BML.speciesCount w h .east s + BML.speciesCount w h .north s := by
  unfold population occupiedPositions
  rw [← Counting.indicator_sum_eq_filter_length]
  unfold BML.speciesCount
  generalize positions w h = sites
  induction sites with
  | nil => rfl
  | cons p sites ih =>
    simp [Species.cell] at ih
    cases hp : s p <;> simp [hp, Species.cell] <;> omega

theorem population_halfStep {w h : Nat} (d : CyclicDirection (Position w h))
    (moving : Species) (s : Config (Position w h)) :
    population (halfStep d moving s) = population s := by
  simp only [population_eq_speciesCounts, speciesCount_halfStep]

theorem population_step {w h : Nat} (east north : CyclicDirection (Position w h))
    (s : Config (Position w h)) : population (step east north s) = population s := by
  simp only [population_eq_speciesCounts, speciesCount_step]

theorem population_iterate {w h : Nat} (east north : CyclicDirection (Position w h))
    (s : Config (Position w h)) (n : Nat) :
    population (BML.iterate (step east north) n s) = population s := by
  simp only [population_eq_speciesCounts, speciesCount_iterate]

/-- Actual movers, including cars in a homogeneous ring whose occupancy is unchanged. -/
def moveCount (w h : Nat) (d : CyclicDirection (Position w h)) (sp : Species)
    (s : Config (Position w h)) : Nat :=
  (positions w h).countP fun p => decide (CanMove d sp s p)

theorem moveCount_eq_zero_iff (w h : Nat) (d : CyclicDirection (Position w h))
    (sp : Species) (s : Config (Position w h)) :
    moveCount w h d sp s = 0 ↔ NoMovers d sp s := by
  simp [moveCount, List.countP_eq_zero, NoMovers, Counting.mem_positions]

def totalMoveCount (w h : Nat) (east north : CyclicDirection (Position w h))
    (s : Config (Position w h)) : Nat :=
  moveCount w h east .east s + moveCount w h north .north (halfStep east .east s)

theorem totalMoveCount_eq_zero_iff_stuck (w h : Nat)
    (east north : CyclicDirection (Position w h)) (s : Config (Position w h)) :
    totalMoveCount w h east north s = 0 ↔ Stuck east north s := by
  simp only [totalMoveCount, Nat.add_eq_zero_iff, moveCount_eq_zero_iff]
  exact noMoves_iff_stuck east north s

theorem jam_iff_positive_zero_moves (w h : Nat)
    (east north : CyclicDirection (Position w h)) (s : Config (Position w h)) :
    Jam east north s ↔ 0 < population s ∧ totalMoveCount w h east north s = 0 := by
  simp only [Jam, population_pos_iff, totalMoveCount_eq_zero_iff_stuck]

theorem full_species_moveCount (w h : Nat) (d : CyclicDirection (Position w h))
    (sp : Species) : moveCount w h d sp (fun _ => sp.cell) = w*h := by
  simp [moveCount, full_species_moves, positions_length]

theorem full_east_step_fixed (east north : CyclicDirection α) :
    step east north (fun _ => Cell.east) = (fun _ => Cell.east) := by
  have he := full_species_halfStep_fixed east .east
  change halfStep east .east (fun _ => Cell.east) = (fun _ => Cell.east) at he
  rw [step, he]
  apply halfStep_eq_of_no_movers
  intro p hm
  cases hm.1

/-- An occupancy fixed point need not be a zero-movement TRAIN state. -/
theorem fixed_occupancy_with_movement (east north : CyclicDirection α) (p : α) :
    step east north (fun _ => Cell.east) = (fun _ => Cell.east) ∧
      ¬ Stuck east north (fun _ => Cell.east) := by
  exact ⟨full_east_step_fixed east north,
    fun hs => hs.1 p (full_species_moves east .east p)⟩

end BML.Train
