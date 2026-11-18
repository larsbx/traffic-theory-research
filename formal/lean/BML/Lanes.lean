import BML.Ring

/-!
A cyclic lane containing both a car and a hole stays mixed under CLASSIC
updates when the whole board contains only that species. Such a lane has an
eligible car at every time, so the board can never become frozen or jammed.
-/
namespace BML

/-- An east-only board with an occupied and an empty site in the given row. -/
def EastMixedRow (w h : Nat) (s : Config (Position w h)) (y : Fin h) : Prop :=
  (∀ p, s p ≠ .north) ∧
  (∃ x, s (x, y) = .east) ∧ (∃ x, s (x, y) = .empty)

/-- A north-only board with an occupied and an empty site in the given column. -/
def NorthMixedColumn (w h : Nat) (s : Config (Position w h)) (x : Fin w) : Prop :=
  (∀ p, s p ≠ .east) ∧
  (∃ y, s (x, y) = .north) ∧ (∃ y, s (x, y) = .empty)

/-- A species with no cars has an identity phase. -/
theorem halfStep_eq_of_absent_species (d : Direction α) (sp : Species)
    (s : Config α) (ha : ∀ p, s p ≠ sp.cell) : halfStep d sp s = s := by
  apply halfStep_eq_of_blocked
  intro p hp
  exact False.elim (ha p hp)

/-- Car and hole witnesses remain in their original row after the east phase. -/
theorem EastMixedRow.halfStep (w h : Nat) (hw : 0 < w)
    (s : Config (Position w h)) (y : Fin h) (hmix : EastMixedRow w h s y) :
    EastMixedRow w h (BML.halfStep (eastDirection w h hw) .east s) y := by
  rcases hmix with ⟨hnorth, ⟨xcar, hcar⟩, ⟨xhole, hhole⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact hnorth p ((other_species_unchanged (eastDirection w h hw) .east s p
      .north (by decide) (by decide)).mp hp)
  · by_cases he : s ((eastDirection w h hw).next (xcar, y)) = .empty
    · exact ⟨cyclicNext w hw xcar,
        moving_destination_filled (eastDirection w h hw) .east s (xcar, y) ⟨hcar, he⟩⟩
    · exact ⟨xcar, by simp [BML.halfStep, Species.cell, hcar, he]⟩
  · by_cases hp : s ((eastDirection w h hw).prev (xhole, y)) = .east
    · refine ⟨cyclicPrev w hw xhole,
        moving_source_emptied (eastDirection w h hw) .east s
          ((eastDirection w h hw).prev (xhole, y)) ⟨hp, ?_⟩⟩
      simpa only [Direction.next_prev] using hhole
    · exact ⟨xhole, by simp [BML.halfStep, Species.cell, hhole, hp]⟩

/-- Car and hole witnesses remain in their original column after the north phase. -/
theorem NorthMixedColumn.halfStep (w h : Nat) (hh : 0 < h)
    (s : Config (Position w h)) (x : Fin w) (hmix : NorthMixedColumn w h s x) :
    NorthMixedColumn w h (BML.halfStep (northDirection w h hh) .north s) x := by
  rcases hmix with ⟨heast, ⟨ycar, hcar⟩, ⟨yhole, hhole⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact heast p ((other_species_unchanged (northDirection w h hh) .north s p
      .east (by decide) (by decide)).mp hp)
  · by_cases he : s ((northDirection w h hh).next (x, ycar)) = .empty
    · exact ⟨cyclicNext h hh ycar,
        moving_destination_filled (northDirection w h hh) .north s (x, ycar) ⟨hcar, he⟩⟩
    · exact ⟨ycar, by simp [BML.halfStep, Species.cell, hcar, he]⟩
  · by_cases hp : s ((northDirection w h hh).prev (x, yhole)) = .north
    · refine ⟨cyclicPrev h hh yhole,
        moving_source_emptied (northDirection w h hh) .north s
          ((northDirection w h hh).prev (x, yhole)) ⟨hp, ?_⟩⟩
      simpa only [Direction.next_prev] using hhole
    · exact ⟨yhole, by simp [BML.halfStep, Species.cell, hhole, hp]⟩

/-- With no north cars, the north phase leaves the mixed east row unchanged. -/
theorem EastMixedRow.step (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (y : Fin h) (hmix : EastMixedRow w h s y) :
    EastMixedRow w h (torusStep w h hw hh s) y := by
  have he := EastMixedRow.halfStep w h hw s y hmix
  change EastMixedRow w h
    (BML.halfStep (northDirection w h hh) .north
      (BML.halfStep (eastDirection w h hw) .east s)) y
  rw [halfStep_eq_of_absent_species (northDirection w h hh) .north _ he.1]
  exact he

/-- With no east cars, the identity east phase precedes the column's north phase. -/
theorem NorthMixedColumn.step (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (x : Fin w) (hmix : NorthMixedColumn w h s x) :
    NorthMixedColumn w h (torusStep w h hw hh s) x := by
  change NorthMixedColumn w h
    (BML.halfStep (northDirection w h hh) .north
      (BML.halfStep (eastDirection w h hw) .east s)) x
  rw [halfStep_eq_of_absent_species (eastDirection w h hw) .east s hmix.1]
  exact NorthMixedColumn.halfStep w h hh s x hmix

theorem EastMixedRow.iterate (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (y : Fin h) (hmix : EastMixedRow w h s y) (t : Nat) :
    EastMixedRow w h (BML.iterate (torusStep w h hw hh) t s) y := by
  induction t with
  | zero => exact hmix
  | succ t ih => exact EastMixedRow.step w h hw hh _ y ih

theorem NorthMixedColumn.iterate (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (x : Fin w) (hmix : NorthMixedColumn w h s x) (t : Nat) :
    NorthMixedColumn w h (BML.iterate (torusStep w h hw hh) t s) x := by
  induction t with
  | zero => exact hmix
  | succ t ih => exact NorthMixedColumn.step w h hw hh _ x ih

/-- A cyclic word made only of holes and one species has a car-to-hole edge
whenever both symbols occur. The proof follows a finite path to a known hole. -/
private theorem cyclic_lane_has_mover (n : Nat) (hn : 0 < n) (sp : Species)
    (s : Config (Fin n)) (honly : ∀ i, s i = .empty ∨ s i = sp.cell)
    (hcar : ∃ i, s i = sp.cell) (hhole : ∃ i, s i = .empty) :
    ∃ i, s i = sp.cell ∧ s (cyclicNext n hn i) = .empty := by
  obtain ⟨icar, hcar⟩ := hcar
  obtain ⟨ihole, hhole⟩ := hhole
  obtain ⟨k, hk⟩ := cyclicNext_reaches n hn icar ihole
  have path : ∀ k, s (BML.iterate (cyclicNext n hn) k icar) = .empty →
      ∃ i, s i = sp.cell ∧ s (cyclicNext n hn i) = .empty := by
    intro k
    induction k with
    | zero =>
        intro hz
        exact False.elim (sp.cell_ne_empty (hcar.symm.trans hz))
    | succ k ih =>
        intro hz
        rcases honly (BML.iterate (cyclicNext n hn) k icar) with he | hc
        · exact ih he
        · exact ⟨BML.iterate (cyclicNext n hn) k icar, hc, hz⟩
  apply path k
  simpa only [hk] using hhole

/-- An east car in this row can move in the actual east phase. -/
theorem EastMixedRow.has_mover (w h : Nat) (hw : 0 < w)
    (s : Config (Position w h)) (y : Fin h) (hmix : EastMixedRow w h s y) :
    ∃ x, CanMove (eastDirection w h hw) .east s (x, y) := by
  have honly : ∀ x, s (x, y) = .empty ∨ s (x, y) = Species.east.cell := by
    intro x
    cases hc : s (x, y) with
    | empty => exact Or.inl rfl
    | east => exact Or.inr rfl
    | north => exact False.elim (hmix.1 (x, y) hc)
  exact cyclic_lane_has_mover w hw .east (fun x => s (x, y)) honly hmix.2.1 hmix.2.2

/-- A north car in this column can move; the absent east phase is the identity. -/
theorem NorthMixedColumn.has_mover (w h : Nat) (hh : 0 < h)
    (s : Config (Position w h)) (x : Fin w) (hmix : NorthMixedColumn w h s x) :
    ∃ y, CanMove (northDirection w h hh) .north s (x, y) := by
  have honly : ∀ y, s (x, y) = .empty ∨ s (x, y) = Species.north.cell := by
    intro y
    cases hc : s (x, y) with
    | empty => exact Or.inl rfl
    | east => exact False.elim (hmix.1 (x, y) hc)
    | north => exact Or.inr rfl
  exact cyclic_lane_has_mover h hh .north (fun y => s (x, y)) honly hmix.2.1 hmix.2.2

theorem EastMixedRow.not_frozen (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (y : Fin h) (hmix : EastMixedRow w h s y) :
    ¬ Frozen (eastDirection w h hw) (northDirection w h hh) s := by
  intro hf
  obtain ⟨x, hm⟩ := EastMixedRow.has_mover w h hw s y hmix
  exact hf.1 (x, y) hm.1 hm.2

theorem NorthMixedColumn.not_frozen (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (x : Fin w) (hmix : NorthMixedColumn w h s x) :
    ¬ Frozen (eastDirection w h hw) (northDirection w h hh) s := by
  intro hf
  obtain ⟨y, hm⟩ := NorthMixedColumn.has_mover w h hh s x hmix
  exact hf.2 (x, y) hm.1 hm.2

theorem EastMixedRow.not_jam (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (y : Fin h) (hmix : EastMixedRow w h s y) :
    ¬ Jam (eastDirection w h hw) (northDirection w h hh) s :=
  fun hj => EastMixedRow.not_frozen w h hw hh s y hmix hj.2

theorem NorthMixedColumn.not_jam (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (x : Fin w) (hmix : NorthMixedColumn w h s x) :
    ¬ Jam (eastDirection w h hw) (northDirection w h hh) s :=
  fun hj => NorthMixedColumn.not_frozen w h hw hh s x hmix hj.2

/-- The persistent mixed row excludes gridlock at every full-step iterate. -/
theorem EastMixedRow.never_jam (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (y : Fin h) (hmix : EastMixedRow w h s y) (t : Nat) :
    ¬ Jam (eastDirection w h hw) (northDirection w h hh)
      (BML.iterate (torusStep w h hw hh) t s) :=
  EastMixedRow.not_jam w h hw hh _ y (EastMixedRow.iterate w h hw hh s y hmix t)

/-- The persistent mixed column excludes gridlock at every full-step iterate. -/
theorem NorthMixedColumn.never_jam (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (x : Fin w) (hmix : NorthMixedColumn w h s x) (t : Nat) :
    ¬ Jam (eastDirection w h hw) (northDirection w h hh)
      (BML.iterate (torusStep w h hw hh) t s) :=
  NorthMixedColumn.not_jam w h hw hh _ x (NorthMixedColumn.iterate w h hw hh s x hmix t)

end BML
