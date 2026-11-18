import Traffic.Core

namespace Traffic

/-- A cyclic successor on a nonempty finite coordinate, including the singleton. -/
def cyclicNext {n : Nat} (i : Fin (n + 1)) : Fin (n + 1) :=
  if h : i.val < n then ⟨i.val + 1, by omega⟩ else ⟨0, by omega⟩

/-- The corresponding predecessor, with explicit wraparound. -/
def cyclicPrev {n : Nat} (i : Fin (n + 1)) : Fin (n + 1) :=
  if h : i.val = 0 then ⟨n, by omega⟩ else ⟨i.val - 1, by omega⟩

@[simp] theorem cyclicNext_prev {n : Nat} (i : Fin (n + 1)) :
    cyclicNext (cyclicPrev i) = i := by
  apply Fin.ext
  have hi := i.isLt
  by_cases hz : i.val = 0
  · simp [cyclicPrev, hz, cyclicNext]
  · have hl : i.val - 1 < n := by omega
    simp [cyclicPrev, hz, cyclicNext, hl]
    omega

@[simp] theorem cyclicPrev_next {n : Nat} (i : Fin (n + 1)) :
    cyclicPrev (cyclicNext i) = i := by
  apply Fin.ext
  have hi := i.isLt
  by_cases hl : i.val < n
  · simp [cyclicNext, hl, cyclicPrev]
  · have he : i.val = n := by omega
    simp [cyclicNext, cyclicPrev, he]

/-- Width and height are successor naturals, so no zero-modulus convention is used. -/
def torusGrid (w h : Nat) : Grid (Fin (w + 1) × Fin (h + 1)) where
  next
    | .east, (x, y) => (cyclicNext x, y)
    | .north, (x, y) => (x, cyclicNext y)
  prev
    | .east, (x, y) => (cyclicPrev x, y)
    | .north, (x, y) => (x, cyclicPrev y)
  next_prev := by
    intro p x
    cases p <;> cases x <;> simp
  prev_next := by
    intro p x
    cases p <;> cases x <;> simp

end Traffic
