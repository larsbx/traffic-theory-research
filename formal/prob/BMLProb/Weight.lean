import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import BML.Torus

/-!
The iid initial law of the CLASSIC model as an exact rational weight.

Each cell is independently empty, east or north with weights `1 - p`,
`p/2`, `p/2`. `prob p A` is the total weight of the configurations in `A`.
This package depends on Mathlib; the kernel in `formal/lean` does not.
-/
namespace BML.Prob

open Finset

instance : Fintype Cell := ⟨{.empty, .east, .north}, fun c => by cases c <;> simp⟩

theorem sum_cell (f : Cell → ℚ) : ∑ c, f c = f .empty + f .east + f .north := by
  change ∑ c ∈ ({.empty, .east, .north} : Finset Cell), f c = _
  simp [add_assoc]

/-- Weight of one cell at density `p`. -/
def cellWeight (p : ℚ) : Cell → ℚ
  | .empty => 1 - p
  | .east => p / 2
  | .north => p / 2

theorem cellWeight_nonneg {p : ℚ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (c : Cell) :
    0 ≤ cellWeight p c := by
  cases c <;> simp only [cellWeight] <;> linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The product weight of a configuration on any finite index set. -/
def weight (p : ℚ) (s : ι → Cell) : ℚ := ∏ i, cellWeight p (s i)

omit [DecidableEq ι] in
theorem weight_nonneg {p : ℚ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (s : ι → Cell) : 0 ≤ weight p s :=
  prod_nonneg fun i _ => cellWeight_nonneg h0 h1 (s i)

/-- Total iid weight of an event. Only the membership test is classical. -/
noncomputable def prob (p : ℚ) (A : (ι → Cell) → Prop) : ℚ :=
  ∑ s, open Classical in if A s then weight p s else 0

theorem prob_mono {p : ℚ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {A B : (ι → Cell) → Prop}
    (hAB : ∀ s, A s → B s) : prob p A ≤ prob p B := by
  apply sum_le_sum
  intro s _
  by_cases hA : A s
  · simp [hA, hAB s hA]
  · by_cases hB : B s <;> simp [hA, hB, weight_nonneg h0 h1 s]

theorem prob_or_le {p : ℚ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (A B : (ι → Cell) → Prop) :
    prob p (fun s => A s ∨ B s) ≤ prob p A + prob p B := by
  unfold prob
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro s _
  have := weight_nonneg h0 h1 s
  by_cases hA : A s <;> by_cases hB : B s <;> simp [hA, hB, this]

theorem prob_congr (p : ℚ) {A B : (ι → Cell) → Prop} (hAB : ∀ s, A s ↔ B s) :
    prob p A = prob p B := by
  have : A = B := funext fun s => propext (hAB s)
  rw [this]

theorem prob_or_disjoint (p : ℚ) {A B : (ι → Cell) → Prop} (hAB : ∀ s, ¬ (A s ∧ B s)) :
    prob p (fun s => A s ∨ B s) = prob p A + prob p B := by
  unfold prob
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro s _
  by_cases hA : A s <;> by_cases hB : B s <;> simp [hA, hB]
  exact (hAB s ⟨hA, hB⟩).elim

theorem prob_and_not (p : ℚ) {A B : (ι → Cell) → Prop} (hBA : ∀ s, B s → A s) :
    prob p (fun s => A s ∧ ¬ B s) = prob p A - prob p B := by
  unfold prob
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro s _
  by_cases hA : A s <;> by_cases hB : B s <;> simp [hA, hB]
  exact (hA (hBA s hB)).elim

/-- An event defined cell by cell has product weight. -/
theorem prob_forall (p : ℚ) (P : Cell → Prop) :
    prob p (fun s : ι → Cell => ∀ i, P (s i)) =
      (∑ c, open Classical in if P c then cellWeight p c else 0) ^ Fintype.card ι := by
  let _ : DecidablePred P := fun c => Classical.propDecidable (P c)
  unfold prob
  refine (Finset.sum_congr rfl fun s _ => ?_ :
    _ = ∑ s : ι → Cell, ∏ i, if P (s i) then cellWeight p (s i) else 0).trans ?_
  · by_cases h : ∀ i, P (s i)
    · simp [h, weight]
    · simp only [h, ↓reduceIte]
      obtain ⟨i, hi⟩ := not_forall.mp h
      exact (Finset.prod_eq_zero (mem_univ i) (by simp [hi])).symm
  · rw [← Fintype.prod_sum (fun _ c => if P c then cellWeight p c else 0)]
    simp

theorem prob_true (p : ℚ) : prob p (fun _ : ι → Cell => True) = 1 := by
  have h := prob_forall (ι := ι) p (fun _ => True)
  simp only [ite_true, sum_cell, cellWeight] at h
  have hone : (1 - p + p / 2 + p / 2 : ℚ) = 1 := by ring
  rw [hone, one_pow] at h
  simpa using h

theorem prob_not (p : ℚ) (A : (ι → Cell) → Prop) :
    prob p (fun s => ¬ A s) = 1 - prob p A := by
  rw [← prob_true (ι := ι) p, ← prob_and_not p (A := fun _ => True) (fun _ _ => trivial)]
  exact prob_congr p fun s => by simp

/-- No north car anywhere. -/
theorem prob_north_free (p : ℚ) :
    prob p (fun s : ι → Cell => ∀ i, s i ≠ .north) = (1 - p / 2) ^ Fintype.card ι := by
  rw [prob_forall p (fun c => c ≠ .north)]
  congr 1
  simp [sum_cell, cellWeight]
  ring

/-- Every cell holds a north car. -/
theorem prob_all_north (p : ℚ) :
    prob p (fun s : ι → Cell => ∀ i, s i = .north) = (p / 2) ^ Fintype.card ι := by
  rw [prob_forall p (fun c => c = .north)]
  congr 1
  simp [sum_cell, cellWeight]

end BML.Prob
