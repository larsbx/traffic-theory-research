import BML.Capture

/-!
One-round staircase preimages for the actual CLASSIC east-then-north kernel.
Theorems below are deterministic. They contain no probability or iid assumption.
The transfer-matrix integration and asymptotic bounds are proved in the research
note, not by these declarations.
-/
namespace BML

theorem halfStep_east_iff (east : Direction α) (s : Config α) (p : α) :
    halfStep east .east s p = .east ↔
      (s p = .east ∧ s (east.next p) ≠ .empty) ∨
      (s p = .empty ∧ s (east.prev p) = .east) := by
  cases hp : s p <;> simp [halfStep, Species.cell, hp]

theorem halfStep_east_empty_iff (east : Direction α) (s : Config α) (p : α) :
    halfStep east .east s p = .empty ↔
      (s p = .empty ∧ s (east.prev p) ≠ .east) ∨
      (s p = .east ∧ s (east.next p) = .empty) := by
  cases hp : s p <;> simp [halfStep, Species.cell, hp]

theorem north_filled_iff_of_east_target (north : Direction α) (s : Config α) (p : α)
    (htarget : s (north.next p) = .east) :
    halfStep north .north s p = .north ↔
      s p = .north ∨ (s p = .empty ∧ s (north.prev p) = .north) := by
  cases hp : s p <;> simp [halfStep, Species.cell, hp, htarget]

/-- B ends east and C=east(B) ends north exactly under this initial predicate,
provided the north target of C is east after the east half-step. -/
theorem staircase_pair_preimage_iff (east north : Direction α)
    (s : Config α) (b : α)
    (htarget : halfStep east .east s (north.next (east.next b)) = .east) :
    (step east north s b = .east ∧ step east north s (east.next b) = .north) ↔
      ((s b = .east ∧ s (east.next b) ≠ .empty) ∨
       (s b = .empty ∧ s (east.prev b) = .east)) ∧
      (s (east.next b) = .north ∨
       (s (north.prev (east.next b)) = .north ∧
        ((s (east.next b) = .empty ∧ s b ≠ .east) ∨
         (s (east.next b) = .east ∧ s (east.next (east.next b)) = .empty)))) := by
  have he := other_species_unchanged north .north (halfStep east .east s) b
    .east (by decide) (by decide)
  have hn := north_filled_iff_of_east_target north (halfStep east .east s)
    (east.next b) htarget
  have hc := other_species_unchanged east .east s (east.next b)
    .north (by decide) (by decide)
  have hd := other_species_unchanged east .east s (north.prev (east.next b))
    .north (by decide) (by decide)
  simp only [step]
  rw [he, hn, hc, hd, halfStep_east_iff, halfStep_east_empty_iff]
  simp only [east.prev_next]
  simp only [and_comm]

/-- A family of adjacent east/north sites satisfying the local initial predicate
forms its staircase simultaneously. The successor relation supplies each N
target; it is not an additional assumption about a later random state. -/
theorem staircase_formed (east north : Direction α) (s : Config α)
    (b : ι → α) (next : ι → ι)
    (hgeometry : ∀ i, north.next (east.next (b i)) = b (next i))
    (hlocal : ∀ i,
      ((s (b i) = .east ∧ s (east.next (b i)) ≠ .empty) ∨
       (s (b i) = .empty ∧ s (east.prev (b i)) = .east)) ∧
      (s (east.next (b i)) = .north ∨
       (s (north.prev (east.next (b i))) = .north ∧
        ((s (east.next (b i)) = .empty ∧ s (b i) ≠ .east) ∨
         (s (east.next (b i)) = .east ∧ s (east.next (east.next (b i))) = .empty))))) :
    ∀ i, step east north s (b i) = .east ∧
      step east north s (east.next (b i)) = .north := by
  intro i
  apply (staircase_pair_preimage_iff east north s (b i) ?_).mpr (hlocal i)
  rw [hgeometry i]
  exact (halfStep_east_iff east s (b (next i))).mpr (hlocal (next i)).1

/-- The formed staircase is an occupied successor-closed core. -/
def staircaseCore (east north : Direction α) (s : Config α)
    (b : ι → α) (next : ι → ι)
    (hgeometry : ∀ i, north.next (east.next (b i)) = b (next i))
    (hformed : ∀ i, s (b i) = .east ∧ s (east.next (b i)) = .north) :
    BlockingCore east north s where
  sites p := (∃ i, b i = p) ∨ (∃ i, east.next (b i) = p)
  occupied p hp := by
    rcases hp with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> simp [(hformed i).1, (hformed i).2]
  east_closed p hp he := by
    rcases hp with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact Or.inr ⟨i, rfl⟩
    · rw [(hformed i).2] at he
      cases he
  north_closed p hp hn := by
    rcases hp with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [(hformed i).1] at hn
      cases hn
    · exact Or.inl ⟨next i, (hgeometry i).symm⟩

end BML
