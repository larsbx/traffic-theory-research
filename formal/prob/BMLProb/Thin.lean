import BMLProb.Weight
import BML.ThinRigidity

/-!
Exact iid bounds on the CLASSIC gridlock probability from full-lane rigidity
(blueprint B10.5, first identity, and the lower half of Theorem A).

`q = prob p EventuallyJammed` is the total iid weight of the initial states
that reach a nonempty frozen state. All statements are for every positive
`w × h` torus; `h = 2` gives the thin-torus bound `L_W ≤ q_W`.
-/
namespace BML.Prob

open Finset

variable {w h : Nat}

/-- The cells of one column. -/
def column (s : Config (Position w h)) (x : Fin w) : Fin h → Cell := fun y => s (x,y)

/-- The columns are independent: an event imposed on every column has the
`w`-th power of the one-column weight. -/
theorem prob_forall_column (p : ℚ) (C : (Fin h → Cell) → Prop) :
    prob p (fun s : Config (Position w h) => ∀ x, C (column s x)) = prob p C ^ w := by
  let _ : DecidablePred C := fun col => Classical.propDecidable (C col)
  let G : (Fin h → Cell) → ℚ := fun col => if C col then weight p col else 0
  have hR : ∑ g : Fin w → Fin h → Cell, ∏ x, G (g x) = (∑ col, G col) ^ w := by
    rw [← Fintype.prod_sum (fun (_ : Fin w) (col : Fin h → Cell) => G col)]
    simp
  have hC : prob p C = ∑ col, G col := by
    unfold prob
    exact Finset.sum_congr rfl fun col _ => by by_cases hc : C col <;> simp [G, hc]
  rw [hC, ← hR]
  unfold prob
  refine Fintype.sum_equiv (Equiv.curry (Fin w) (Fin h) Cell) _
    (fun g => ∏ x, G (g x)) fun s => ?_
  have hw : weight p s = ∏ x, weight p (column s x) := by
    unfold weight
    rw [Fintype.prod_prod_type]
    rfl
  change _ = ∏ x, G (column s x)
  by_cases hall : ∀ x, C (column s x)
  · rw [ite_eq_left hall, hw]
    exact Finset.prod_congr rfl fun x _ => by simp [G, hall x]
  · rw [ite_eq_right hall]
    obtain ⟨x, hx⟩ := not_forall.mp hall
    exact (Finset.prod_eq_zero (mem_univ x) (by simp [G, hx])).symm

/-- B10.5, first identity, at every height: the weight of "some full north
column, and every north car in a full north column". On two rows this is
"a plug and no lone column", with `a = (p/2)²` and `c = (1-p/2)²`. -/
theorem prob_plug_no_lone (hh : 0 < h) (p : ℚ) :
    prob p (fun s : Config (Position w h) =>
      (∃ x, FullNorthColumn s x) ∧ ∀ q, s q = .north → FullNorthColumn s q.1) =
      ((p / 2) ^ h + (1 - p / 2) ^ h) ^ w - ((1 - p / 2) ^ h) ^ w := by
  have hgood : prob p (fun col : Fin h → Cell =>
      (∀ y, col y = .north) ∨ ∀ y, col y ≠ .north) = (p / 2) ^ h + (1 - p / 2) ^ h := by
    rw [prob_or_disjoint p (A := fun col : Fin h → Cell => ∀ y, col y = .north)
      (B := fun col => ∀ y, col y ≠ .north) fun col hc => hc.2 ⟨0, hh⟩ (hc.1 ⟨0, hh⟩),
      prob_all_north,
      prob_north_free, Fintype.card_fin]
  have hfree : prob p (fun col : Fin h → Cell => ∀ y, col y ≠ .north) = (1 - p / 2) ^ h := by
    rw [prob_north_free, Fintype.card_fin]
  rw [← hgood, ← hfree, ← prob_forall_column (w := w), ← prob_forall_column (w := w),
    ← prob_and_not]
  · apply prob_congr
    intro s
    constructor
    · rintro ⟨⟨x, hx⟩, hall⟩
      refine ⟨fun x' => ?_, fun hfree => hfree x ⟨0, hh⟩ (hx ⟨0, hh⟩)⟩
      by_cases hn : ∃ y, s (x',y) = .north
      · obtain ⟨y, hy⟩ := hn
        exact Or.inl (hall (x',y) hy)
      · exact Or.inr fun y hy => hn ⟨y, hy⟩
    · rintro ⟨hgood, hnot⟩
      have hfull : ∀ q, s q = .north → FullNorthColumn s q.1 := by
        intro q hq
        rcases hgood q.1 with hf | hf
        · exact hf
        · exact (hf q.2 hq).elim
      obtain ⟨x, hx⟩ := not_forall.mp hnot
      obtain ⟨y, hy⟩ := not_forall.mp hx
      exact ⟨⟨x, hfull (x,y) (not_not.mp hy)⟩, hfull⟩
  · intro s hfree x
    exact Or.inr (hfree x)

/-- The gridlock probability of the iid law at density `p`. -/
noncomputable def jamProb (hw : 0 < w) (hh : 0 < h) (p : ℚ) : ℚ :=
  prob p (fun s : Config (Position w h) =>
    EventuallyJammed (eastDirection w h hw) (northDirection w h hh) s)

/-- Lower half of Theorem A at every height. -/
theorem jamProb_lower_bound (hw : 0 < w) (hh : 0 < h) {p : ℚ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ((p / 2) ^ h + (1 - p / 2) ^ h) ^ w - ((1 - p / 2) ^ h) ^ w ≤ jamProb hw hh p := by
  rw [← prob_plug_no_lone hh p]
  exact prob_mono h0 h1 fun s ⟨⟨q, hq⟩, hall⟩ =>
    eventuallyJammed_of_north_in_full_columns hw hh s q hq hall

/-- Theorem A, lower bound, as stated for the 2×W torus: `L_W(p) ≤ q_W(p)`. -/
theorem thin_lower_bound (hw : 0 < w) {p : ℚ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    (1 - p + p ^ 2 / 2) ^ w - (1 - p / 2) ^ (2 * w) ≤ jamProb hw (h := 2) (by decide) p := by
  have h := jamProb_lower_bound hw (h := 2) (by decide) h0 h1
  have ha : (p / 2) ^ 2 + (1 - p / 2) ^ 2 = 1 - p + p ^ 2 / 2 := by ring
  rwa [ha, ← pow_mul] at h

/-- The weight of "some full north column". -/
theorem prob_exists_fullNorthColumn (p : ℚ) :
    prob p (fun s : Config (Position w h) => ∃ x, FullNorthColumn s x) =
      1 - (1 - (p / 2) ^ h) ^ w := by
  have hcol : prob p (fun col : Fin h → Cell => ¬ ∀ y, col y = .north) = 1 - (p / 2) ^ h := by
    rw [prob_not, prob_all_north, Fintype.card_fin]
  rw [← hcol, ← prob_forall_column (w := w), ← prob_not]
  exact prob_congr p fun s =>
    ⟨fun ⟨x, hx⟩ hall => hall x hx, fun hn => by
      obtain ⟨x, hx⟩ := not_forall.mp hn
      exact ⟨x, not_not.mp hx⟩⟩

/-- A coarse upper bound at every height: gridlock needs `w` east cars or a
full north column (B10.3, first step). Theorem A's upper bound replaces the
second term by the weight of the gap condition. -/
theorem jamProb_upper_bound (hw : 0 < w) (hh : 0 < h) {p : ℚ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    jamProb hw hh p ≤
      prob p (fun s : Config (Position w h) => w ≤ speciesCount w h .east s) +
        (1 - (1 - (p / 2) ^ h) ^ w) := by
  rw [← prob_exists_fullNorthColumn]
  refine le_trans (prob_mono h0 h1 fun s hj => ?_) (prob_or_le h0 h1 _ _)
  by_cases hfew : speciesCount w h .east s < w
  · exact Or.inr (eventuallyJammed_fullNorthColumn_of_few_east hw hh s hj hfew)
  · exact Or.inl (not_lt.mp hfew)

end BML.Prob
