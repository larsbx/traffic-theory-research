import Traffic.Core

/-!
# Elementary geometry and Fibonacci word algebra for BML

The results here concern explicit configurations and finite words.  In
particular, the integer-pair algebra below is not a formalization of real
angles, irrational frequency limits, model-set diffraction, or percolation.
-/

namespace Traffic.Geometry

/-! ## Finite Fibonacci substitution and its count matrix -/

/-- The Fibonacci substitution on the two traffic directions. -/
def substitute : List Phase → List Phase
  | [] => []
  | .east :: w => .east :: .north :: substitute w
  | .north :: w => .east :: substitute w

def eastCount : List Phase → Nat
  | [] => 0
  | .east :: w => eastCount w + 1
  | .north :: w => eastCount w

def northCount : List Phase → Nat
  | [] => 0
  | .east :: w => northCount w
  | .north :: w => northCount w + 1

theorem counts_add (w : List Phase) : eastCount w + northCount w = w.length := by
  induction w with
  | nil => rfl
  | cons p w ih => cases p <;> simp only [eastCount, northCount, List.length_cons] <;> omega

/-- Counting the substituted letters proves the Fibonacci matrix action. -/
theorem substitute_counts (w : List Phase) :
    eastCount (substitute w) = eastCount w + northCount w ∧
    northCount (substitute w) = eastCount w := by
  induction w with
  | nil => exact ⟨rfl, rfl⟩
  | cons p w ih =>
    cases p <;> simp only [substitute, eastCount, northCount] <;> omega

/-- Action of the integer matrix `[[1,1],[1,0]]` on a count column. -/
def fibonacciMatrix (v : Nat × Nat) : Nat × Nat := (v.1 + v.2, v.1)

theorem substitute_count_vector (w : List Phase) :
    (eastCount (substitute w), northCount (substitute w)) =
      fibonacciMatrix (eastCount w, northCount w) := by
  exact Prod.ext (substitute_counts w).1 (substitute_counts w).2

def fibonacciWord : Nat → List Phase
  | 0 => [.east]
  | n + 1 => substitute (fibonacciWord n)

/-- Fibonacci numbers, with initial values `F₀ = 0`, `F₁ = 1`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

theorem fibonacciWord_counts (n : Nat) :
    eastCount (fibonacciWord n) = fib (n + 1) ∧
    northCount (fibonacciWord n) = fib n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    have hs := substitute_counts (fibonacciWord n)
    simp only [fibonacciWord] at *
    constructor
    · rw [hs.1, ih.1, ih.2]
      rfl
    · exact hs.2.trans ih.1

theorem fibonacciWord_length (n : Nat) :
    (fibonacciWord n).length = fib (n + 2) := by
  have hc := counts_add (fibonacciWord n)
  rw [(fibonacciWord_counts n).1, (fibonacciWord_counts n).2] at hc
  exact hc.symm

/-! ## Exact algebraic lengths

An integer pair `(a,b)` denotes the formal expression `a + b φ`.  Multiplication
by `φ` uses the relation `φ² = φ + 1`.  We prove that this endomorphism satisfies
that relation on every integer pair, and that finite word substitution scales
the exact length by it.  No interpretation in the real numbers is asserted.
-/

abbrev PhiCoord := Int × Int

def coordAdd (x y : PhiCoord) : PhiCoord := (x.1 + y.1, x.2 + y.2)

def timesPhi (x : PhiCoord) : PhiCoord := (x.2, x.1 + x.2)

def conjugate (x : PhiCoord) : PhiCoord := (x.1 + x.2, -x.2)

def longLength : PhiCoord := (0, 1)

def shortLength : PhiCoord := (1, 0)

theorem timesPhi_add (x y : PhiCoord) :
    timesPhi (coordAdd x y) = coordAdd (timesPhi x) (timesPhi y) := by
  apply Prod.ext <;> simp only [timesPhi, coordAdd] <;> omega

theorem timesPhi_quadratic_relation (x : PhiCoord) :
    timesPhi (timesPhi x) = coordAdd (timesPhi x) x := by
  apply Prod.ext <;> simp only [timesPhi, coordAdd] <;> omega

theorem conjugate_involution (x : PhiCoord) : conjugate (conjugate x) = x := by
  apply Prod.ext <;> simp only [conjugate] <;> omega

theorem inflate_long : timesPhi longLength = coordAdd longLength shortLength := by
  decide

theorem inflate_short : timesPhi shortLength = longLength := by
  decide

def letterLength : Phase → PhiCoord
  | .east => longLength
  | .north => shortLength

def wordLength : List Phase → PhiCoord
  | [] => (0, 0)
  | p :: w => coordAdd (letterLength p) (wordLength w)

theorem wordLength_counts (w : List Phase) :
    wordLength w = ((northCount w : Int), (eastCount w : Int)) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    cases p <;>
      simp [wordLength, ih, letterLength, coordAdd, longLength, shortLength,
        eastCount, northCount, Int.add_comm]

/-- The substitution's exact length scaling follows from its letter counts. -/
theorem substitution_inflates_length (w : List Phase) :
    wordLength (substitute w) = timesPhi (wordLength w) := by
  rw [wordLength_counts, wordLength_counts]
  apply Prod.ext
  · simp only [timesPhi]
    exact congrArg (fun n : Nat => (n : Int)) (substitute_counts w).2
  · simp only [timesPhi]
    rw [(substitute_counts w).1]
    simp [Int.add_comm]

/-- Integer coordinates map to the rescaled projected expression `x φ + y`. -/
def algebraicProjection (r : Position) : PhiCoord := (r.2, r.1)

theorem algebraicProjection_next (p : Phase) (r : Position) :
    algebraicProjection (squareGrid.next p r) =
      coordAdd (algebraicProjection r) (letterLength p) := by
  cases p <;>
    simp [algebraicProjection, squareGrid, coordAdd, letterLength, longLength, shortLength]

/-! ## An actual bi-infinite occupied staircase -/

def coordinateSum (r : Position) : Int := r.1 + r.2

theorem coordinateSum_next (p : Phase) (r : Position) :
    coordinateSum (squareGrid.next p r) = coordinateSum r + 1 := by
  cases p <;> simp only [coordinateSum, squareGrid] <;> omega

theorem coordinateSum_prev (p : Phase) (r : Position) :
    coordinateSum (squareGrid.prev p r) = coordinateSum r - 1 := by
  cases p <;> simp only [coordinateSum, squareGrid] <;> omega

def forwardVertices (u : Int → Phase) : Nat → Position
  | 0 => (0, 0)
  | n + 1 => squareGrid.next (u (n : Int)) (forwardVertices u n)

def backwardVertices (u : Int → Phase) : Nat → Position
  | 0 => (0, 0)
  | n + 1 => squareGrid.prev (u (Int.negSucc n)) (backwardVertices u n)

/-- The origin is vertex zero; negative indices are built with inverse steps. -/
def staircase (u : Int → Phase) : Int → Position
  | .ofNat n => forwardVertices u n
  | .negSucc n => backwardVertices u (n + 1)

theorem coordinateSum_forward (u : Int → Phase) (n : Nat) :
    coordinateSum (forwardVertices u n) = (n : Int) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [forwardVertices, coordinateSum_next, ih]
    omega

theorem coordinateSum_backward (u : Int → Phase) (n : Nat) :
    coordinateSum (backwardVertices u n) = -(n : Int) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardVertices, coordinateSum_prev, ih]
    omega

theorem staircase_sum (u : Int → Phase) (n : Int) :
    coordinateSum (staircase u n) = n := by
  cases n with
  | ofNat n => exact coordinateSum_forward u n
  | negSucc n =>
    simp only [staircase, coordinateSum_backward, Int.negSucc_eq]
    omega

theorem staircase_injective (u : Int → Phase) : Function.Injective (staircase u) := by
  intro m n h
  have hs := congrArg coordinateSum h
  simpa only [staircase_sum] using hs

theorem staircase_next (u : Int → Phase) (n : Int) :
    staircase u (n + 1) = squareGrid.next (u n) (staircase u n) := by
  cases n with
  | ofNat n => rfl
  | negSucc n =>
    cases n with
    | zero =>
      change (0, 0) = squareGrid.next (u (-1))
        (squareGrid.prev (u (-1)) (0, 0))
      exact (squareGrid.next_prev _ _).symm
    | succ n =>
      have hn : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
      rw [hn]
      change backwardVertices u (n + 1) =
        squareGrid.next (u (Int.negSucc (n + 1)))
          (squareGrid.prev (u (Int.negSucc (n + 1))) (backwardVertices u (n + 1)))
      exact (squareGrid.next_prev _ _).symm

/-- The coordinate sum recovers a possible vertex index without any choice. -/
def staircaseConfiguration (u : Int → Phase) : Configuration :=
  fun x => if staircase u (coordinateSum x) = x
    then (u (coordinateSum x)).car else .empty

theorem staircaseConfiguration_at (u : Int → Phase) (n : Int) :
    staircaseConfiguration u (staircase u n) = (u n).car := by
  simp [staircaseConfiguration, staircase_sum]

theorem staircaseConfiguration_support (u : Int → Phase) (x : Position) :
    staircaseConfiguration u x ≠ .empty ↔ ∃ n, staircase u n = x := by
  constructor
  · intro hx
    by_cases h : staircase u (coordinateSum x) = x
    · exact ⟨coordinateSum x, h⟩
    · simp [staircaseConfiguration, h] at hx
  · rintro ⟨n, rfl⟩
    rw [staircaseConfiguration_at]
    exact (u n).car_ne_empty

/-- This is semantic freezing for the actual half-step transition, for every
bi-infinite direction word, not an assumed blocking hypothesis. -/
theorem staircase_frozen (u : Int → Phase) :
    Frozen squareGrid (staircaseConfiguration u) := by
  apply frozen_of_occupied_path squareGrid (staircaseConfiguration u) (staircase u) u
  · exact staircaseConfiguration_at u
  · intro x hx
    exact (staircaseConfiguration_support u x).mp hx
  · exact staircase_next u

theorem staircase_evolve (u : Int → Phase) (n : Nat) :
    evolve squareGrid (staircaseConfiguration u) n = staircaseConfiguration u := by
  exact frozen_evolve squareGrid _ (staircase_frozen u) n

theorem staircase_projected_step (u : Int → Phase) (n : Int) :
    algebraicProjection (staircase u (n + 1)) =
      coordAdd (algebraicProjection (staircase u n)) (letterLength (u n)) := by
  rw [staircase_next, algebraicProjection_next]

/-! ## Finite paths and torus winding

Closure here is explicitly equality modulo the two side lengths.  The
conclusion supplies nonnegative integer winding counts for the lifted word.
It does not claim that every word is a closed path or that arbitrary traffic
reaches such a path.
-/

def walk (start : Position) : List Phase → Position
  | [] => start
  | p :: w => walk (squareGrid.next p start) w

theorem walk_displacement (start : Position) (w : List Phase) :
    walk start w = (start.1 + (eastCount w : Int), start.2 + (northCount w : Int)) := by
  induction w generalizing start with
  | nil => simp [walk, eastCount, northCount]
  | cons p w ih =>
    rw [walk, ih]
    cases p <;> apply Prod.ext <;>
      simp only [squareGrid, eastCount, northCount, Int.natCast_add, Int.natCast_one] <;>
      omega

theorem algebraicProjection_walk (start : Position) (w : List Phase) :
    algebraicProjection (walk start w) = coordAdd (algebraicProjection start) (wordLength w) := by
  rw [walk_displacement, wordLength_counts]
  rfl

/-- Substituting a finite path scales its rescaled formal projected displacement. -/
theorem substituted_walk_projection (w : List Phase) :
    algebraicProjection (walk (0, 0) (substitute w)) =
      timesPhi (algebraicProjection (walk (0, 0) w)) := by
  rw [algebraicProjection_walk, algebraicProjection_walk]
  simpa only [algebraicProjection, coordAdd, Int.zero_add, Prod.eta] using
    substitution_inflates_length w

def closesModulo (width height : Nat) (start : Position) (w : List Phase) : Prop :=
  (walk start w).1 % (width : Int) = start.1 % (width : Int) ∧
  (walk start w).2 % (height : Int) = start.2 % (height : Int)

theorem counts_divisible_of_closed (width height : Nat) (start : Position)
    (w : List Phase) (h : closesModulo width height start w) :
    width ∣ eastCount w ∧ height ∣ northCount w := by
  rcases h with ⟨hx, hy⟩
  rw [walk_displacement] at hx hy
  have hx' := (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp hx
  have hy' := (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp hy
  have hx0 : eastCount w % width = 0 := by
    have he : ((eastCount w : Int) % (width : Int)) = 0 := by
      have heq : start.1 + (eastCount w : Int) - start.1 = (eastCount w : Int) := by omega
      simpa only [Prod.fst, heq] using hx'
    exact_mod_cast he
  have hy0 : northCount w % height = 0 := by
    have he : ((northCount w : Int) % (height : Int)) = 0 := by
      have heq : start.2 + (northCount w : Int) - start.2 = (northCount w : Int) := by omega
      simpa only [Prod.snd, heq] using hy'
    exact_mod_cast he
  exact ⟨Nat.dvd_of_mod_eq_zero hx0, Nat.dvd_of_mod_eq_zero hy0⟩

theorem torus_winding (width height : Nat) (start : Position) (w : List Phase)
    (h : closesModulo width height start w) :
    ∃ a b : Nat, eastCount w = a * width ∧ northCount w = b * height ∧
      w.length = a * width + b * height := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := counts_divisible_of_closed width height start w h
  have he : eastCount w = a * width := by simpa only [Nat.mul_comm] using ha
  have hn : northCount w = b * height := by simpa only [Nat.mul_comm] using hb
  refine ⟨a, b, he, hn, ?_⟩
  rw [← he, ← hn]
  exact (counts_add w).symm

theorem nonempty_torus_winding (width height : Nat) (start : Position) (w : List Phase)
    (hw : w ≠ []) (h : closesModulo width height start w) :
    ∃ a b : Nat, eastCount w = a * width ∧ northCount w = b * height ∧
      (0 < a ∨ 0 < b) := by
  obtain ⟨a, b, he, hn, hlen⟩ := torus_winding width height start w h
  refine ⟨a, b, he, hn, ?_⟩
  by_cases ha : 0 < a
  · exact Or.inl ha
  · right
    have haz : a = 0 := by omega
    by_cases hb : 0 < b
    · exact hb
    · have hbz : b = 0 := by omega
      have hz : w.length = 0 := by simpa [haz, hbz] using hlen
      exact False.elim (hw (List.length_eq_zero_iff.mp hz))

end Traffic.Geometry
