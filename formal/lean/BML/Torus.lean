import BML.Kernel

namespace BML

/-- A positive finite cyclic coordinate. The singleton case is supported. -/
def cyclicNext (n : Nat) (hn : 0 < n) (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1, h⟩ else ⟨0, hn⟩

def cyclicPrev (n : Nat) (hn : 0 < n) (i : Fin n) : Fin n :=
  if h : i.val = 0 then ⟨n - 1, by omega⟩ else ⟨i.val - 1, by omega⟩

theorem cyclicNext_prev (n : Nat) (hn : 0 < n) (i : Fin n) :
    cyclicNext n hn (cyclicPrev n hn i) = i := by
  apply Fin.ext
  have hi := i.isLt
  by_cases hz : i.val = 0
  · simp [cyclicPrev, hz, cyclicNext, show ¬n - 1 + 1 < n by omega]
  · simp only [cyclicPrev, hz, ↓reduceDIte, cyclicNext]
    split <;> simp_all <;> omega

theorem cyclicPrev_next (n : Nat) (hn : 0 < n) (i : Fin n) :
    cyclicPrev n hn (cyclicNext n hn i) = i := by
  apply Fin.ext
  have hi := i.isLt
  simp only [cyclicNext, cyclicPrev]
  split <;> split <;> simp_all <;> omega

abbrev Position (w h : Nat) := Fin w × Fin h

def eastDirection (w h : Nat) (hw : 0 < w) : Direction (Position w h) where
  next p := (cyclicNext w hw p.1, p.2)
  prev p := (cyclicPrev w hw p.1, p.2)
  next_prev p := by simp [cyclicNext_prev]
  prev_next p := by simp [cyclicPrev_next]

def northDirection (w h : Nat) (hh : 0 < h) : Direction (Position w h) where
  next p := (p.1, cyclicNext h hh p.2)
  prev p := (p.1, cyclicPrev h hh p.2)
  next_prev p := by simp [cyclicNext_prev]
  prev_next p := by simp [cyclicPrev_next]

def torusStep (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    Config (Position w h) → Config (Position w h) :=
  step (eastDirection w h hw) (northDirection w h hh)

def cellDigit : Cell → Nat
  | .empty => 0
  | .east => 1
  | .north => 2

def digitCell (n : Nat) : Cell :=
  if n % 3 = 0 then .empty else if n % 3 = 1 then .east else .north

/-- Base-three row-major encoding: index = x + width*y, as in `bml.exhaustive`. -/
def decode (w h code : Nat) : Config (Position w h) := fun p =>
  digitCell (code / 3 ^ (p.1.val + w * p.2.val))

def positions (w h : Nat) : List (Position w h) :=
  (List.finRange h).flatMap fun y => (List.finRange w).map fun x => (x, y)

def encode (w h : Nat) (s : Config (Position w h)) : Nat :=
  ((positions w h).map fun p => cellDigit (s p) * 3 ^ (p.1.val + w * p.2.val)).sum

def moveCount (w h : Nat) (d : Direction (Position w h)) (sp : Species)
    (s : Config (Position w h)) : Nat :=
  ((positions w h).map fun p => if CanMove d sp s p then 1 else 0).sum

def speciesCount (w h : Nat) (sp : Species) (s : Config (Position w h)) : Nat :=
  ((positions w h).map fun p => if s p = sp.cell then 1 else 0).sum

theorem torus_fixed_iff_blocked (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) :
    torusStep w h hw hh s = s ↔
      (∀ p, s p = .east → s ((eastDirection w h hw).next p) ≠ .empty) ∧
      (∀ p, s p = .north → s ((northDirection w h hh).next p) ≠ .empty) :=
  step_eq_iff_frozen _ _ _

end BML
