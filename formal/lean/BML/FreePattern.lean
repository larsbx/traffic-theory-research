import BML.Counting
import BML.Ring

/-!
Explicit cyclic phase patterns attaining the free-flow packing bound.

There are two kinds of block: `north, east, empty` and `east, empty`.
A ring made from `k` blocks of the first kind and `r` of the second has
`3*k + 2*r` classes and `2*k + r` occupied classes.  The last class is empty,
so the local successor rules also hold at the cyclic seam.
-/

namespace BML

/-- The infinite word consisting of `k` copies of `north, east, empty`,
followed by copies of `east, empty`. -/
def freeBlockCell (k i : Nat) : Cell :=
  if i < 3 * k then
    if i % 3 = 0 then .north else if i % 3 = 1 then .east else .empty
  else
    if (i - 3 * k) % 2 = 0 then .east else .empty

theorem freeBlockCell_east_iff (k i : Nat) :
    freeBlockCell k i = .east ↔
      (i < 3 * k ∧ i % 3 = 1) ∨ (3 * k ≤ i ∧ (i - 3 * k) % 2 = 0) := by
  unfold freeBlockCell
  split <;> rename_i h
  · by_cases h0 : i % 3 = 0
    · simp [h0]; omega
    · simp [h0]; omega
  · simp; omega

theorem freeBlockCell_north_iff (k i : Nat) :
    freeBlockCell k i = .north ↔ i < 3 * k ∧ i % 3 = 0 := by
  unfold freeBlockCell
  split <;> rename_i h
  · by_cases h0 : i % 3 = 0
    · simp [h0, h]
    · simp only [h0, ↓reduceIte, and_false]
      split <;> simp
  · split <;> simp_all <;> omega

theorem freeBlockCell_empty_iff (k i : Nat) :
    freeBlockCell k i = .empty ↔
      (i < 3 * k ∧ i % 3 = 2) ∨ (3 * k ≤ i ∧ (i - 3 * k) % 2 = 1) := by
  unfold freeBlockCell
  split <;> rename_i h
  · by_cases h0 : i % 3 = 0
    · simp [h0]; omega
    · by_cases h1 : i % 3 = 1
      · simp [h1]; omega
      · simp [h0, h1]; omega
  · split <;> simp_all <;> omega

theorem freeBlockCell_occupied_iff (k i : Nat) :
    freeBlockCell k i ≠ .empty ↔
      (i < 3 * k ∧ i % 3 < 2) ∨ (3 * k ≤ i ∧ (i - 3 * k) % 2 = 0) := by
  change (¬ freeBlockCell k i = .empty) ↔ _
  rw [freeBlockCell_empty_iff]
  omega

theorem freeBlockCell_east_succ (k i : Nat) (hi : freeBlockCell k i = .east) :
    freeBlockCell k (i + 1) = .empty := by
  rw [freeBlockCell_east_iff] at hi
  rw [freeBlockCell_empty_iff]
  rcases hi with hi | hi
  · left; omega
  · right; omega

theorem freeBlockCell_north_succ (k i : Nat) (hi : freeBlockCell k i = .north) :
    freeBlockCell k (i + 1) = .east := by
  rw [freeBlockCell_north_iff] at hi
  rw [freeBlockCell_east_iff]
  left
  omega

theorem freeBlockCell_last_empty (n k r : Nat) (hn : 0 < n)
    (heq : n = 3 * k + 2 * r) : freeBlockCell k (n - 1) = .empty := by
  rw [freeBlockCell_empty_iff]
  by_cases hr : r = 0
  · left; omega
  · right; omega

theorem freeBlockCell_east_next (n k r : Nat) (hn : 0 < n)
    (heq : n = 3 * k + 2 * r) (i : Fin n) (hi : freeBlockCell k i.val = .east) :
    freeBlockCell k (cyclicNext n hn i).val = .empty := by
  unfold cyclicNext
  split <;> rename_i h
  · exact freeBlockCell_east_succ k i.val hi
  · have hv : i.val = n - 1 := by have := i.isLt; omega
    have hempty := freeBlockCell_last_empty n k r hn heq
    rw [← hv, hi] at hempty
    contradiction

theorem freeBlockCell_north_next (n k r : Nat) (hn : 0 < n)
    (heq : n = 3 * k + 2 * r) (i : Fin n) (hi : freeBlockCell k i.val = .north) :
    freeBlockCell k (cyclicNext n hn i).val = .east := by
  unfold cyclicNext
  split <;> rename_i h
  · exact freeBlockCell_north_succ k i.val hi
  · have hv : i.val = n - 1 := by have := i.isLt; omega
    have hempty := freeBlockCell_last_empty n k r hn heq
    rw [← hv, hi] at hempty
    contradiction

/-- Explicitly enumerate the two occupied slots of every triple block and
the occupied slot of every pair block. -/
private def freeBlockIndex (k r : Nat) (i : Fin (2 * k + r)) : Fin (3 * k + 2 * r) :=
  if hi : i.val < 2 * k then
    ⟨3 * (i.val / 2) + i.val % 2, by have := i.isLt; omega⟩
  else
    ⟨3 * k + 2 * (i.val - 2 * k), by have := i.isLt; omega⟩

private theorem freeBlockIndex_injective (k r : Nat) :
    Function.Injective (freeBlockIndex k r) := by
  intro i j he
  apply Fin.ext
  have hv := congrArg Fin.val he
  unfold freeBlockIndex at hv
  split at hv <;> split at hv <;> simp only at hv <;> omega

private theorem freeBlockIndex_occupied (k r : Nat) (i : Fin (2 * k + r)) :
    freeBlockCell k (freeBlockIndex k r i).val ≠ .empty := by
  rw [freeBlockCell_occupied_iff]
  unfold freeBlockIndex
  split <;> simp only
  · left; omega
  · right; omega

private theorem freeBlockIndex_surjective (k r : Nat) (i : Fin (3 * k + 2 * r))
    (hi : freeBlockCell k i.val ≠ .empty) :
    ∃ j : Fin (2 * k + r), freeBlockIndex k r j = i := by
  rw [freeBlockCell_occupied_iff] at hi
  rcases hi with hi | hi
  · let j : Fin (2 * k + r) := ⟨2 * (i.val / 3) + i.val % 3, by omega⟩
    refine ⟨j, ?_⟩
    apply Fin.ext
    have hj : j.val < 2 * k := by dsimp [j]; omega
    simp only [freeBlockIndex, hj, ↓reduceDIte]
    dsimp [j]
    omega
  · let j : Fin (2 * k + r) := ⟨2 * k + (i.val - 3 * k) / 2, by
      have := i.isLt; omega⟩
    refine ⟨j, ?_⟩
    apply Fin.ext
    have hj : ¬ j.val < 2 * k := by dsimp [j]; omega
    simp only [freeBlockIndex, hj, ↓reduceDIte]
    dsimp [j]
    omega

theorem freeBlockCell_count (k r : Nat) :
    ((List.finRange (3 * k + 2 * r)).filter
      (fun i => decide (freeBlockCell k i.val ≠ .empty))).length = 2 * k + r := by
  let xs := (List.finRange (3 * k + 2 * r)).filter
    (fun i => decide (freeBlockCell k i.val ≠ .empty))
  let ys := (List.finRange (2 * k + r)).map (freeBlockIndex k r)
  have hxnodup : xs.Nodup := (List.nodup_finRange _).filter _
  have hynodup : ys.Nodup := List.Pairwise.map (freeBlockIndex k r)
    (fun _ _ hne he => hne (freeBlockIndex_injective k r he)) (List.nodup_finRange _)
  have hmem : ∀ i, i ∈ xs ↔ i ∈ ys := by
    intro i
    simp only [xs, ys, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq, List.mem_map]
    constructor
    · exact freeBlockIndex_surjective k r i
    · rintro ⟨j, rfl⟩
      exact freeBlockIndex_occupied k r j
  have he := ((List.perm_ext_iff_of_nodup hxnodup hynodup).mpr hmem).length_eq
  simpa only [xs, ys, List.length_map, List.length_finRange] using he

/-- Number of three-class blocks in a maximum pattern. The remainder-one
case replaces the last triple and the extra class by two pair blocks. -/
def freeTripleBlocks (g : Nat) : Nat :=
  if g % 3 = 1 then g / 3 - 1 else g / 3

def freePairBlocks (g : Nat) : Nat :=
  if g % 3 = 1 then 2 else g % 3 / 2

theorem freeBlocks_size (g : Nat) (hg : 2 ≤ g) :
    g = 3 * freeTripleBlocks g + 2 * freePairBlocks g := by
  unfold freeTripleBlocks freePairBlocks
  by_cases h : g % 3 = 1 <;> simp only [h, ↓reduceIte] <;> omega

theorem freeBlocks_occupied (g : Nat) (hg : 2 ≤ g) :
    2 * freeTripleBlocks g + freePairBlocks g = (2 * g) / 3 := by
  unfold freeTripleBlocks freePairBlocks
  by_cases h : g % 3 = 1 <;> simp only [h, ↓reduceIte] <;> omega

/-- A maximum occupied phase pattern for every ring with at least two classes. -/
def freePattern (g : Nat) (i : Fin g) : Cell :=
  freeBlockCell (freeTripleBlocks g) i.val

theorem freePattern_east_next (g : Nat) (hg : 2 ≤ g) (i : Fin g)
    (hi : freePattern g i = .east) :
    freePattern g (cyclicNext g (by omega) i) = .empty :=
  freeBlockCell_east_next g (freeTripleBlocks g) (freePairBlocks g)
    (by omega) (freeBlocks_size g hg) i hi

theorem freePattern_north_next (g : Nat) (hg : 2 ≤ g) (i : Fin g)
    (hi : freePattern g i = .north) :
    freePattern g (cyclicNext g (by omega) i) = .east :=
  freeBlockCell_north_next g (freeTripleBlocks g) (freePairBlocks g)
    (by omega) (freeBlocks_size g hg) i hi

theorem freePattern_count (g : Nat) (hg : 2 ≤ g) :
    ((List.finRange g).filter (fun i => decide (freePattern g i ≠ .empty))).length =
      (2 * g) / 3 := by
  unfold freePattern
  have h := freeBlockCell_count (freeTripleBlocks g) (freePairBlocks g)
  rw [← freeBlocks_size g hg, freeBlocks_occupied g hg] at h
  exact h

end BML
