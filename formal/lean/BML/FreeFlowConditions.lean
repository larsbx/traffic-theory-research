import BML.Cosets

/-!
The static CLASSIC free-flow conditions. Phase separation is stated directly
on the canonical residues, avoiding natural-number subtraction at wraparound.
-/
namespace BML

/-- Same-species adjacency is forbidden, and each north/east pair avoids the
equal phase class and the east-translated next phase class. -/
def StaticFree (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) : Prop :=
  (∀ p, s p = .east → s ((eastDirection w h hw).next p) ≠ .east) ∧
  (∀ p, s p = .north → s ((northDirection w h hh).next p) ≠ .north) ∧
  (∀ e q, s e = .east → s q = .north →
    phaseClass w h q ≠ phaseClass w h e ∧
    phaseClass w h q ≠ (phaseClass w h e + 1) % Nat.gcd w h)

end BML
