import BML.LaneDeadlock

namespace BML.LaneDeadlock.Examples

private def noBox (_ : Fin 2) : Bool := false

private def ring (swapped : Bool) : Snapshot (Fin 2) (Fin 2) where
  pos k := some (if swapped then BML.cyclicNext 2 (by decide) k else k)
  occ c := some (if swapped then BML.cyclicNext 2 (by decide) c else c)
  plan k := ⟨some (if swapped then k else BML.cyclicNext 2 (by decide) k), .east, []⟩
  occ_iff_pos := by cases swapped <;> decide

private def directRing : Cycle noBox (ring false) where
  length := 2
  positive := by decide
  car i := i
  kind _ := .direct
  blocks i :=
    have selected : ∀ i : Fin 2,
        (ring false).blocker noBox i = some (BML.cyclicNext 2 (by decide) i, .direct) := by decide
    Snapshot.blocker_sound (selected i)

example : directRing.DirectOnAxis .east := fun _ => ⟨rfl, rfl⟩

/-- TRAIN admits an actual swap of tags with all cells occupied before and after. -/
theorem train_same_axis_swap : HalfStep .train noBox (ring false) (ring true) .east
    (fun _ => True) := by
  constructor
  · intro _ _ _ h
    exact (h trivial).elim
  · decide
  · decide
  · decide
  · intro k q _ _ hmem
    simp [ring] at hmem

example (k : Fin 2) : (ring false).pos k ≠ (ring true).pos k := by
  exact (show ∀ k : Fin 2, (ring false).pos k ≠ (ring true).pos k by decide) k

example : ¬ HalfStep .classic noBox (ring false) (ring true) .east (fun _ => True) := by
  intro step
  have rotation := directRing.moves_rotate step (fun _ => ⟨rfl, rfl⟩) (0 : Fin 2) trivial
  cases rotation.1

private def junction (c : Fin 4) : Bool := c == 1

-- Car 0 needs vacant cell 1 and its tail cell 2 (occupied by car 1).
-- Car 1 points back to car 0. Car 2 points to car 1, feeding the loop.
private def boxSnapshot : Snapshot (Fin 4) (Fin 3) where
  pos k := some (match k.val with | 0 => 0 | 1 => 2 | _ => 3)
  occ c := match c.val with | 0 => some 0 | 2 => some 1 | 3 => some 2 | _ => none
  plan k := match k.val with
    | 0 => ⟨some 1, .east, [2]⟩
    | 1 => ⟨some 0, .east, []⟩
    | _ => ⟨some 2, .north, []⟩
  occ_iff_pos := by decide

private def boxRingCar (i : Fin 2) : Fin 3 := i.castLE (by decide)

private def boxRingKind (i : Fin 2) : BlockKind := if i = 0 then .box else .direct

private def boxRing : Cycle junction boxSnapshot where
  length := 2
  positive := by decide
  car := boxRingCar
  kind := boxRingKind
  blocks i :=
    have selected : ∀ i : Fin 2, boxSnapshot.blocker junction (boxRingCar i) =
        some (boxRingCar (BML.cyclicNext 2 (by decide) i), boxRingKind i) := by decide
    Snapshot.blocker_sound (selected i)

private theorem boxRingNoRotation : ¬ ∃ axis, boxRing.DirectOnAxis axis := by
  rintro ⟨_, h⟩
  have impossible : BlockKind.box = .direct := (h (0 : Fin 2)).1
  cases impossible

private theorem twoEdgePath : Reaches junction boxSnapshot 2 0 :=
  .cons (Snapshot.blocker_sound (show boxSnapshot.blocker junction 2 = some (1, .direct) by decide))
    (.cons (boxRing.blocks (1 : Fin 2)) (.refl 0))

example : boxSnapshot.blocker (fun _ => false) 0 = none := by decide

/-- The captured tag is frozen for any legal CLASSIC trace from the example. -/
theorem classic_box_path (run : Trace (Cell := Fin 4) (Car := Fin 3) .classic junction)
    (initial : run.state 0 = boxSnapshot) : run.Immobile 2 := by
  have witness : ∃ (cycle : Cycle junction (run.state 0)) (i : Fin cycle.length),
      Reaches junction (run.state 0) 2 (cycle.car i) := by
    rw [initial]
    exact ⟨boxRing, (0 : Fin 2), twoEdgePath⟩
  obtain ⟨cycle, i, path⟩ := witness
  exact cycle.classic_capture run i path

/-- A single indirect edge prevents rotation of this otherwise same-axis cycle. -/
theorem train_box_path (run : Trace (Cell := Fin 4) (Car := Fin 3) .train junction)
    (initial : run.state 0 = boxSnapshot) : run.Immobile 2 := by
  have witness : ∃ (cycle : Cycle junction (run.state 0)) (i : Fin cycle.length),
      (¬ ∃ axis, cycle.DirectOnAxis axis) ∧ Reaches junction (run.state 0) 2 (cycle.car i) := by
    rw [initial]
    exact ⟨boxRing, (0 : Fin 2), boxRingNoRotation, twoEdgePath⟩
  obtain ⟨cycle, i, noRotation, path⟩ := witness
  exact cycle.train_capture run noRotation i path

end BML.LaneDeadlock.Examples
