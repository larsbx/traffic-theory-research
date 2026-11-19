import BML.Counting

/-!
Explicit frozen configurations attaining the minimum side length: a full east
row or a full north column. This is the minimum-count existence part of G1,
not yet the construction at every larger prescribed car count.
-/
namespace BML

/-- East cars fill row zero; all other rows are empty. -/
def fullEastRow (w h : Nat) : Config (Position w h) := fun p =>
  if p.2.val = 0 then .east else .empty

/-- North cars fill column zero; all other columns are empty. -/
def fullNorthColumn (w h : Nat) : Config (Position w h) := fun p =>
  if p.1.val = 0 then .north else .empty

theorem fullEastRow_frozen (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    Frozen (eastDirection w h hw) (northDirection w h hh) (fullEastRow w h) := by
  constructor
  · intro p hp
    have hy : p.2.val = 0 := by simpa [fullEastRow, Species.cell] using hp
    simp [fullEastRow, eastDirection, hy]
  · intro p hp
    simp only [fullEastRow, Species.cell] at hp
    split at hp <;> cases hp

theorem fullNorthColumn_frozen (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    Frozen (eastDirection w h hw) (northDirection w h hh) (fullNorthColumn w h) := by
  constructor
  · intro p hp
    simp only [fullNorthColumn, Species.cell] at hp
    split at hp <;> cases hp
  · intro p hp
    have hx : p.1.val = 0 := by simpa [fullNorthColumn, Species.cell] using hp
    simp [fullNorthColumn, northDirection, hx]

theorem fullEastRow_nonempty (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    Nonempty (fullEastRow w h) := by
  exact ⟨(⟨0, hw⟩, ⟨0, hh⟩), by simp [fullEastRow]⟩

theorem fullNorthColumn_nonempty (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    Nonempty (fullNorthColumn w h) := by
  exact ⟨(⟨0, hw⟩, ⟨0, hh⟩), by simp [fullNorthColumn]⟩

theorem fullEastRow_is_jam (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    Jam (eastDirection w h hw) (northDirection w h hh) (fullEastRow w h) :=
  ⟨fullEastRow_nonempty w h hw hh, fullEastRow_frozen w h hw hh⟩

theorem fullNorthColumn_is_jam (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    Jam (eastDirection w h hw) (northDirection w h hh) (fullNorthColumn w h) :=
  ⟨fullNorthColumn_nonempty w h hw hh, fullNorthColumn_frozen w h hw hh⟩

/-- The occupied list is exactly one full row, up to enumeration order. -/
theorem fullEastRow_carCount (w h : Nat) (hh : 0 < h) :
    carCount w h (fullEastRow w h) = w := by
  let row : List (Position w h) :=
    (List.finRange w).map fun x => (x, (⟨0, hh⟩ : Fin h))
  have hn : row.Nodup :=
    List.Pairwise.map _ (fun a b hab heq => hab (congrArg Prod.fst heq))
      (List.nodup_finRange w)
  have hp : (occupiedCells w h (fullEastRow w h)).Perm row := by
    apply (List.perm_ext_iff_of_nodup (occupiedCells_nodup w h _) hn).mpr
    intro q
    rw [mem_occupiedCells]
    have he : fullEastRow w h q ≠ .empty ↔ q.2.val = 0 := by
      simp [fullEastRow]
    rw [he]
    constructor
    · intro hq
      exact List.mem_map.mpr ⟨q.1, List.mem_finRange q.1,
        Prod.ext rfl (Fin.ext hq.symm)⟩
    · intro hq
      obtain ⟨x, _, hx⟩ := List.mem_map.mp hq
      have hy := congrArg (fun p : Position w h => p.2.val) hx
      exact hy.symm
  simpa [carCount, row] using hp.length_eq

/-- The occupied list is exactly one full column, up to enumeration order. -/
theorem fullNorthColumn_carCount (w h : Nat) (hw : 0 < w) :
    carCount w h (fullNorthColumn w h) = h := by
  let column : List (Position w h) :=
    (List.finRange h).map fun y => ((⟨0, hw⟩ : Fin w), y)
  have hn : column.Nodup :=
    List.Pairwise.map _ (fun a b hab heq => hab (congrArg Prod.snd heq))
      (List.nodup_finRange h)
  have hp : (occupiedCells w h (fullNorthColumn w h)).Perm column := by
    apply (List.perm_ext_iff_of_nodup (occupiedCells_nodup w h _) hn).mpr
    intro q
    rw [mem_occupiedCells]
    have he : fullNorthColumn w h q ≠ .empty ↔ q.1.val = 0 := by
      simp [fullNorthColumn]
    rw [he]
    constructor
    · intro hq
      exact List.mem_map.mpr ⟨q.2, List.mem_finRange q.2,
        Prod.ext (Fin.ext hq.symm) rfl⟩
    · intro hq
      obtain ⟨y, _, hy⟩ := List.mem_map.mp hq
      have hx := congrArg (fun p : Position w h => p.1.val) hy
      exact hx.symm
  simpa [carCount, column] using hp.length_eq

/-- A nonempty frozen state attains exactly the shorter side's car count. -/
theorem exists_minimum_jam (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    ∃ s : Config (Position w h),
      Jam (eastDirection w h hw) (northDirection w h hh) s ∧
      carCount w h s = min w h := by
  by_cases hwh : w ≤ h
  · exact ⟨fullEastRow w h, fullEastRow_is_jam w h hw hh,
      by rw [fullEastRow_carCount w h hh, Nat.min_eq_left hwh]⟩
  · have hhw : h ≤ w := by omega
    exact ⟨fullNorthColumn w h, fullNorthColumn_is_jam w h hw hh,
      by rw [fullNorthColumn_carCount w h hw, Nat.min_eq_right hhw]⟩

end BML
