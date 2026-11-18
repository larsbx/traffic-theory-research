import Train.Conservation

namespace BML.Train

/-- Every active car is counted among the cars of its species. -/
theorem moveCount_eq_selected_count (w h : Nat)
    (d : CyclicDirection (Position w h)) (sp : Species) (s : Config (Position w h)) :
    moveCount w h d sp s =
      ((positions w h).filter fun p => decide (s p = sp.cell)).countP
        (fun p => decide (CanMove d sp s p)) := by
  simp only [moveCount, List.countP_eq_length_filter, List.filter_filter]
  congr 2
  funext p
  apply Bool.eq_iff_iff.mpr
  simp [CanMove]
  intro hm
  exact (of_decide_eq_true hm).1

theorem moveCount_le_speciesCount (w h : Nat)
    (d : CyclicDirection (Position w h)) (sp : Species) (s : Config (Position w h)) :
    moveCount w h d sp s ≤ BML.speciesCount w h sp s := by
  rw [moveCount_eq_selected_count, Counting.speciesCount_eq_filter_length]
  exact List.countP_le_length

/-- Maximal numerical movement is exactly movement of every active-species car. -/
theorem moveCount_eq_speciesCount_iff (w h : Nat)
    (d : CyclicDirection (Position w h)) (sp : Species) (s : Config (Position w h)) :
    moveCount w h d sp s = BML.speciesCount w h sp s ↔
      ∀ p, s p = sp.cell → CanMove d sp s p := by
  rw [moveCount_eq_selected_count, Counting.speciesCount_eq_filter_length,
    List.countP_eq_length]
  simp [Counting.mem_positions]

/-- A car is offered exactly one move in a complete east-then-north round. -/
theorem totalMoveCount_le_population (w h : Nat)
    (east north : CyclicDirection (Position w h)) (s : Config (Position w h)) :
    totalMoveCount w h east north s ≤ population s := by
  have he := moveCount_le_speciesCount w h east .east s
  have hn := moveCount_le_speciesCount w h north .north (halfStep east .east s)
  rw [speciesCount_halfStep] at hn
  rw [totalMoveCount, population_eq_speciesCounts]
  exact Nat.add_le_add he hn

/-- Speed one means every car moves, including full-ring cars with fixed occupancy. -/
def FullSpeed (w h : Nat) (east north : CyclicDirection (Position w h))
    (s : Config (Position w h)) : Prop :=
  totalMoveCount w h east north s = population s

instance (w h : Nat) (east north : CyclicDirection (Position w h))
    (s : Config (Position w h)) : Decidable (FullSpeed w h east north s) :=
  inferInstanceAs (Decidable (totalMoveCount w h east north s = population s))

theorem fullSpeed_iff_all_phases_move (w h : Nat)
    (east north : CyclicDirection (Position w h)) (s : Config (Position w h)) :
    FullSpeed w h east north s ↔
      (∀ p, s p = Cell.east → CanMove east .east s p) ∧
      (∀ p, halfStep east .east s p = Cell.north →
        CanMove north .north (halfStep east .east s) p) := by
  have he := moveCount_le_speciesCount w h east .east s
  have hn := moveCount_le_speciesCount w h north .north (halfStep east .east s)
  have hc := speciesCount_halfStep w h east .east .north s
  have hsplit : FullSpeed w h east north s ↔
      moveCount w h east .east s = BML.speciesCount w h .east s ∧
      moveCount w h north .north (halfStep east .east s) =
        BML.speciesCount w h .north (halfStep east .east s) := by
    unfold FullSpeed totalMoveCount
    rw [population_eq_speciesCounts]
    omega
  rw [hsplit, moveCount_eq_speciesCount_iff, moveCount_eq_speciesCount_iff]
  rfl

def EventuallyFullSpeed (w h : Nat) (east north : CyclicDirection (Position w h))
    (s : Config (Position w h)) : Prop :=
  ∃ T, ∀ t, T ≤ t → FullSpeed w h east north (BML.iterate (step east north) t s)

theorem eventuallyFullSpeed_iff_moves_equal_initial_population (w h : Nat)
    (east north : CyclicDirection (Position w h)) (s : Config (Position w h)) :
    EventuallyFullSpeed w h east north s ↔
      ∃ T, ∀ t, T ≤ t →
        totalMoveCount w h east north (BML.iterate (step east north) t s) = population s := by
  simp only [EventuallyFullSpeed, FullSpeed, population_iterate]

end BML.Train
