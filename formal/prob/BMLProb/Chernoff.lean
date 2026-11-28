import BMLProb.Thin

/-!
An exact exponential-moment (Chernoff) bound on the number of east cars
(blueprint B10.7, first step).

The east-car count `E` of an iid configuration satisfies, for every `θ ≥ 1`,
`prob (k ≤ E) ≤ (1 - p/2 + pθ/2)^n / θ^k` on `n` cells: the indicator of
`k ≤ E` is at most `θ^(E-k)`, and the weighted sum of `θ^E` factorises over
the cells. On the `2 × W` torus the choice `θ = (2-p)/p` gives `(p(2-p))^W`,
which replaces the east-car term of `jamProb_upper_bound`.
-/
namespace BML.Prob

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The number of east cars of a configuration on any finite index set. -/
def eastCount (s : ι → Cell) : ℕ := #{i | s i = .east}

/-- The exponential moment of the east-car count factorises over the cells. -/
theorem sum_weight_mul_pow_eastCount (p θ : ℚ) :
    ∑ s : ι → Cell, weight p s * θ ^ eastCount s = (1 - p / 2 + p * θ / 2) ^ Fintype.card ι := by
  let F : Cell → ℚ := fun c => cellWeight p c * if c = .east then θ else 1
  have hF : ∑ c, F c = 1 - p / 2 + p * θ / 2 := by
    simp [F, sum_cell, cellWeight]
    ring
  have hs : ∀ s : ι → Cell, weight p s * θ ^ eastCount s = ∏ i, F (s i) := fun s => by
    rw [prod_mul_distrib, prod_ite, prod_const, prod_const_one, mul_one]
    rfl
  simp_rw [hs]
  rw [← hF, ← Fintype.prod_sum (fun (_ : ι) c => F c)]
  simp

/-- Chernoff bound: for `θ ≥ 1`, at least `k` east cars has weight at most
`(1 - p/2 + pθ/2)^n / θ^k` on `n` cells. -/
theorem prob_eastCount_ge {p θ : ℚ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hθ : 1 ≤ θ) (k : ℕ) :
    prob p (fun s : ι → Cell => k ≤ eastCount s) ≤
      (1 - p / 2 + p * θ / 2) ^ Fintype.card ι / θ ^ k := by
  have hθk : 0 < θ ^ k := pow_pos (by linarith) k
  rw [← sum_weight_mul_pow_eastCount, sum_div]
  apply sum_le_sum
  intro s _
  have hw := weight_nonneg h0 h1 s
  by_cases hk : k ≤ eastCount s
  · simp only [hk, ↓reduceIte]
    rw [le_div_iff₀ hθk]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hθ hk) hw
  · simp only [hk, ↓reduceIte]
    exact div_nonneg (mul_nonneg hw (pow_nonneg (by linarith) _)) hθk.le

variable {w h : Nat}

/-- The kernel's list count of a species is the cardinality of its cells. -/
theorem speciesCount_eq_card (sp : Species) (s : Config (Position w h)) :
    speciesCount w h sp s = #{q | s q = sp.cell} := by
  have huniv : (positions w h).toFinset = univ :=
    eq_univ_of_forall fun q => List.mem_toFinset.mpr (mem_positions w h q)
  rw [card_filter, ← huniv, List.sum_toFinset _ (positions_nodup w h)]
  rfl

/-- The Chernoff bound on the torus: at least `w` east cars. -/
theorem prob_speciesCount_east_ge {p θ : ℚ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hθ : 1 ≤ θ) :
    prob p (fun s : Config (Position w h) => w ≤ speciesCount w h .east s) ≤
      (1 - p / 2 + p * θ / 2) ^ (w * h) / θ ^ w := by
  have hcard : Fintype.card (Position w h) = w * h := by simp
  rw [← hcard]
  refine le_of_eq_of_le (prob_congr p (B := fun s => w ≤ eastCount s) fun s => ?_)
    (prob_eastCount_ge h0 h1 hθ w)
  rw [speciesCount_eq_card]
  rfl

/-- On two rows, `θ = (2-p)/p` gives: at least `w` east cars has weight at
most `(p(2-p))^w`. At `p = 0` and `w > 0` the event has weight zero. -/
theorem prob_speciesCount_east_ge_thin {p : ℚ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    prob p (fun s : Config (Position w 2) => w ≤ speciesCount w 2 .east s) ≤
      (p * (2 - p)) ^ w := by
  rcases h0.eq_or_lt with rfl | hp
  · rcases Nat.eq_zero_or_pos w with rfl | hw
    · rw [pow_zero, ← prob_true (ι := Position 0 2) 0]
      exact prob_mono le_rfl zero_le_one fun _ _ => trivial
    · rw [zero_mul, zero_pow hw.ne']
      refine le_of_eq (sum_eq_zero fun s _ => ?_)
      split_ifs with hk
      · beta_reduce at hk
        rw [speciesCount_eq_card] at hk
        obtain ⟨q, hq⟩ := card_pos.mp (hw.trans_le hk)
        exact prod_eq_zero (mem_univ q) (by simp [(mem_filter.mp hq).2, cellWeight, Species.cell])
      · rfl
  · have hθ : 1 ≤ (2 - p) / p := by rw [le_div_iff₀ hp]; linarith
    have hb : (1 - p / 2 + p * ((2 - p) / p) / 2) ^ 2 / ((2 - p) / p) = p * (2 - p) := by
      have : 2 - p ≠ 0 := by linarith
      field_simp
      ring
    have h := prob_speciesCount_east_ge (w := w) (h := 2) h0 h1 hθ
    rwa [pow_mul', ← div_pow, hb] at h

/-- The thin-torus upper bound with the Chernoff estimate for the east cars:
`q_W ≤ (p(2-p))^W + 1 - (1 - (p/2)²)^W`. -/
theorem thin_upper_bound_chernoff (hw : 0 < w) {p : ℚ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    jamProb hw (h := 2) (by decide) p ≤ (p * (2 - p)) ^ w + (1 - (1 - (p / 2) ^ 2) ^ w) := by
  have hj := jamProb_upper_bound hw (h := 2) (by decide) h0 h1
  have he := prob_speciesCount_east_ge_thin (w := w) h0 h1
  linarith

end BML.Prob
