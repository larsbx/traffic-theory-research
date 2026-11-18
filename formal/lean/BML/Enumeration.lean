import BML.Counting

/-!
Explicit finite-torus rank bijections and exact prefix counts. These helpers
count selected positions without assuming a correspondence with an external
implementation's ordering of its cells.
-/
namespace BML

/-- Row-major rank with x as the fast coordinate. -/
def rowMajorRank (w h : Nat) (p : Position w h) : Fin (w * h) :=
  ⟨p.1.val + w * p.2.val, by
    have hcell := Nat.add_lt_add_left p.1.isLt (w * p.2.val)
    have hrow := Nat.mul_le_mul_left w (Nat.succ_le_of_lt p.2.isLt)
    simp only [Nat.mul_succ] at hrow
    omega⟩

/-- Decode a row-major rank using Euclidean quotient and remainder. -/
def rowMajorPosition (w h : Nat) (hw : 0 < w) (i : Fin (w * h)) : Position w h :=
  (⟨i.val % w, Nat.mod_lt _ hw⟩,
   ⟨i.val / w, Nat.div_lt_of_lt_mul i.isLt⟩)

@[simp] theorem rowMajorRank_val (w h : Nat) (p : Position w h) :
    (rowMajorRank w h p).val = p.1.val + w * p.2.val := rfl

@[simp] theorem rowMajorPosition_rank (w h : Nat) (hw : 0 < w) (p : Position w h) :
    rowMajorPosition w h hw (rowMajorRank w h p) = p := by
  apply Prod.ext
  · apply Fin.ext
    change (p.1.val + w * p.2.val) % w = p.1.val
    rw [Nat.add_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt p.1.isLt]
  · apply Fin.ext
    change (p.1.val + w * p.2.val) / w = p.2.val
    rw [Nat.add_comm, Nat.mul_add_div hw, Nat.div_eq_of_lt p.1.isLt, Nat.add_zero]

@[simp] theorem rowMajorRank_position (w h : Nat) (hw : 0 < w) (i : Fin (w * h)) :
    rowMajorRank w h (rowMajorPosition w h hw i) = i := by
  apply Fin.ext
  exact Nat.mod_add_div i.val w

/-- Enumerate from the top row down, with x increasing within each row. -/
def reverseRowRank (w h : Nat) (p : Position w h) : Fin (w * h) :=
  rowMajorRank w h (p.1, p.2.rev)

def reverseRowPosition (w h : Nat) (hw : 0 < w) (i : Fin (w * h)) : Position w h :=
  let p := rowMajorPosition w h hw i
  (p.1, p.2.rev)

@[simp] theorem reverseRowRank_val (w h : Nat) (p : Position w h) :
    (reverseRowRank w h p).val = p.1.val + w * (h - 1 - p.2.val) := by
  simp only [reverseRowRank, rowMajorRank_val, Fin.rev]
  congr 2
  omega

@[simp] theorem reverseRowPosition_rank (w h : Nat) (hw : 0 < w) (p : Position w h) :
    reverseRowPosition w h hw (reverseRowRank w h p) = p := by
  simp [reverseRowPosition, reverseRowRank]

@[simp] theorem reverseRowRank_position (w h : Nat) (hw : 0 < w) (i : Fin (w * h)) :
    reverseRowRank w h (reverseRowPosition w h hw i) = i := by
  simp only [reverseRowPosition, reverseRowRank, Fin.rev_rev]
  exact rowMajorRank_position w h hw i

/-- Enumerate from the rightmost column leftward, with y increasing within each column. -/
def reverseColumnRank (w h : Nat) (p : Position w h) : Fin (h * w) :=
  rowMajorRank h w (p.2, p.1.rev)

def reverseColumnPosition (w h : Nat) (hh : 0 < h) (i : Fin (h * w)) : Position w h :=
  let p := rowMajorPosition h w hh i
  (p.2.rev, p.1)

@[simp] theorem reverseColumnRank_val (w h : Nat) (p : Position w h) :
    (reverseColumnRank w h p).val = p.2.val + h * (w - 1 - p.1.val) := by
  simp only [reverseColumnRank, rowMajorRank_val, Fin.rev]
  congr 2
  omega

@[simp] theorem reverseColumnPosition_rank (w h : Nat) (hh : 0 < h)
    (p : Position w h) : reverseColumnPosition w h hh (reverseColumnRank w h p) = p := by
  simp [reverseColumnPosition, reverseColumnRank]

@[simp] theorem reverseColumnRank_position (w h : Nat) (hh : 0 < h)
    (i : Fin (h * w)) : reverseColumnRank w h (reverseColumnPosition w h hh i) = i := by
  simp only [reverseColumnPosition, reverseColumnRank, Fin.rev_rev]
  exact rowMajorRank_position h w hh i

/-- A configuration occupying exactly the first n ranks of a finite bijection
has exactly n cars, counted by the actual occupied-position list. -/
theorem carCount_of_rank (w h m : Nat) (s : Config (Position w h))
    (rank : Position w h → Fin m) (unrank : Fin m → Position w h)
    (hleft : ∀ p, unrank (rank p) = p) (hright : ∀ i, rank (unrank i) = i)
    (n : Nat) (hn : n ≤ m)
    (hocc : ∀ p, s p ≠ .empty ↔ (rank p).val < n) : carCount w h s = n := by
  let extend : Fin n → Fin m := fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩
  let selected := (List.finRange n).map (fun i => unrank (extend i))
  have hnd : selected.Nodup := by
    apply List.pairwise_map.mpr
    apply (List.nodup_finRange n).imp
    intro a b hab heq
    apply hab
    apply Fin.ext
    have hrank := congrArg (fun p => (rank p).val) heq
    simpa only [hright] using hrank
  have hperm : (occupiedCells w h s).Perm selected := by
    apply (List.perm_ext_iff_of_nodup (occupiedCells_nodup w h s) hnd).mpr
    intro p
    rw [mem_occupiedCells, hocc]
    constructor
    · intro hp
      let i : Fin n := ⟨(rank p).val, hp⟩
      refine List.mem_map.mpr ⟨i, List.mem_finRange i, ?_⟩
      exact hleft p
    · intro hp
      obtain ⟨i, _, hi⟩ := List.mem_map.mp hp
      have hlt : (rank (unrank (extend i))).val < n := by
        simpa only [hright] using i.isLt
      rw [hi] at hlt
      exact hlt
  simpa only [carCount, selected, List.length_map, List.length_finRange] using hperm.length_eq

/-- Exact count for any reverse-row-prefix occupancy predicate. -/
theorem carCount_of_reverseRowRank (w h : Nat) (hw : 0 < w)
    (s : Config (Position w h)) (n : Nat) (hn : n ≤ w * h)
    (hocc : ∀ p, s p ≠ .empty ↔ p.1.val + w * (h - 1 - p.2.val) < n) :
    carCount w h s = n := by
  apply carCount_of_rank w h (w*h) s (reverseRowRank w h) (reverseRowPosition w h hw)
    (reverseRowPosition_rank w h hw) (reverseRowRank_position w h hw) n hn
  intro p
  simpa only [reverseRowRank_val] using hocc p

/-- Exact count for any reverse-column-prefix occupancy predicate. -/
theorem carCount_of_reverseColumnRank (w h : Nat) (hh : 0 < h)
    (s : Config (Position w h)) (n : Nat) (hn : n ≤ w * h)
    (hocc : ∀ p, s p ≠ .empty ↔ p.2.val + h * (w - 1 - p.1.val) < n) :
    carCount w h s = n := by
  apply carCount_of_rank w h (h*w) s (reverseColumnRank w h) (reverseColumnPosition w h hh)
    (reverseColumnPosition_rank w h hh) (reverseColumnRank_position w h hh) n
    (by simpa only [Nat.mul_comm] using hn)
  intro p
  simpa only [reverseColumnRank_val] using hocc p

end BML
