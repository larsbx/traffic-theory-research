import BMLProb.Thin

/-! Candidate B10.5 increment. Requires compilation against the pinned package.
The exact cyclic geometry/weight correspondence is a separate obligation. -/
namespace BML.Prob
open Finset

/-- All plug-bounded runs satisfy the east-count requirement. This formulation
avoids choosing a canonical origin for each gap. With a plug present it is
mathematically equivalent to the maximal-gap test (see accompanying proof). -/
def runGapCondition {w : Nat} (hw : 0 < w) (s : Config (Position w 2)) : Prop :=
  (∃ x, FullNorthColumn s x) ∧
  ∀ (G : Fin w → Prop) [DecidablePred G], PlugBounded hw G s →
    ∀ (c : Fin w), northColumnCount s c = 1 →
      ∀ d : Nat, d ≤ w →
        (∀ i, i < d → G (iterate (cyclicNext w hw) i c) ∧
          ¬ FullNorthColumn s (iterate (cyclicNext w hw) i c)) →
        d ≤ eastCountIn G s

theorem eventuallyJammed_runGapCondition {w : Nat} (hw : 0 < w)
    (s : Config (Position w 2))
    (hj : EventuallyJammed (eastDirection w 2 hw) (northDirection w 2 (by decide)) s)
    (hfew : speciesCount w 2 .east s < w) : runGapCondition hw s := by
  refine ⟨eventuallyJammed_fullNorthColumn_of_few_east hw (by decide) s hj hfew, ?_⟩
  intro G inst hb c hc d hd hr
  exact two_row_gap_condition hw G s hj hb c hc d hd hr

noncomputable def runGapMass {w : Nat} (hw : 0 < w) (p : ℚ) : ℚ :=
  prob p (runGapCondition hw)

/-- Sharper event-level upper bound, without replacing the event mass by an
unproved numerical identity. -/
theorem jamProb_runGap_upper {w : Nat} (hw : 0 < w) {p : ℚ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    jamProb hw (h := 2) (by decide) p ≤
      prob p (fun s : Config (Position w 2) => w ≤ speciesCount w 2 .east s) +
        runGapMass hw p := by
  unfold runGapMass
  refine le_trans (prob_mono h0 h1 fun s hj => ?_) (prob_or_le h0 h1 _ _)
  by_cases hfew : speciesCount w 2 .east s < w
  · exact Or.inr (eventuallyJammed_runGapCondition hw s hj hfew)
  · exact Or.inl (not_lt.mp hfew)

/-- Raw gap mass: no division by the non-plug probability. Index 0 is
nearest the downstream plug. Requiring every lone distance <= total east
count is equivalent to the farthest-lone criterion. -/
def rawGapOK {g : Nat} (s : Fin g × Fin 2 → Cell) : Prop :=
  (∀ x : Fin g, ¬ (∀ y : Fin 2, s (x,y) = .north)) ∧
  ∀ x : Fin g, (∃ y : Fin 2, s (x,y) = .north) →
    x.val + 1 ≤ (Finset.univ.filter fun i : Fin g × Fin 2 => s i = .east).card

noncomputable def rawGapWeight (g : Nat) (p : ℚ) : ℚ :=
  prob p (rawGapOK (g := g))

noncomputable def blockWeight (p : ℚ) (g : Nat) : ℚ :=
  (p / 2)^2 * rawGapWeight g p

/-- Weighted transport along a supplied finite equivalence. The actual
canonical block decomposition must construct this equivalence, not assume it
as an axiom. This lemma only transports weights. -/
theorem renewal_weight_transport {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : A → ℚ) (g : B → ℚ)
    (hw : ∀ x, f x = g (e x)) : (∑ x, f x) = ∑ y, g y := by
  exact Fintype.sum_equiv e f g hw

/-- For a length-indexed block, the offset of column zero has exactly l
choices. This is the algebraic factor in the cyclic renewal identity. -/
theorem marked_block_factor (l : Nat) (b c : ℚ) :
    (∑ _ : Fin l, b * c) = (l : ℚ) * b * c := by
  simp [nsmul_eq_mul, mul_assoc]

/-- The weighted marked-block identity once the finite geometry equivalence
and the product-weight law have been constructed. `i` encodes length i+1.
Neither the equivalence nor the product law is silently postulated. -/
theorem marked_renewal_identity {S : Type*} [Fintype S] {W : Nat}
    (A B : Fin W → Type*) [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (e : S ≃ (Σ i : Fin W, Fin (i.val+1) × (A i × B i)))
    (f : S → ℚ) (b : ∀ i, A i → ℚ) (c : ∀ i, B i → ℚ)
    (hf : ∀ x, f x = b (e x).1 (e x).2.2.1 * c (e x).1 (e x).2.2.2) :
    (∑ x, f x) = ∑ i : Fin W, (i.val+1 : ℚ) * (∑ a, b i a) * (∑ t, c i t) := by
  classical
  calc
    (∑ x, f x) = ∑ z : (Σ i : Fin W, Fin (i.val+1) × (A i × B i)),
        b z.1 z.2.2.1 * c z.1 z.2.2.2 :=
      renewal_weight_transport e _ _ hf
    _ = ∑ i : Fin W, (i.val+1 : ℚ) * (∑ a, b i a) * (∑ t, c i t) := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_prod_type]
      have hprod : (∑ z : A i × B i, b i z.1 * c i z.2) =
          (∑ a, b i a) * (∑ t, c i t) := by
        rw [Fintype.sum_prod_type, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
      simp only [hprod]
      simpa [mul_assoc] using marked_block_factor (i.val+1) (∑ a, b i a) (∑ t, c i t)

/-- An isolated nonplug column with a north car and no east car can never
jam. No low-east-count hypothesis is necessary. -/
theorem noJam_isolated_north {w : Nat} (hw : 0 < w)
    (s : Config (Position w 2)) (c : Fin w)
    (hleft : FullNorthColumn s (cyclicPrev w hw c))
    (hright : FullNorthColumn s (cyclicNext w hw c))
    (hnorth : ∃ y, s (c,y) = .north)
    (hnonplug : ¬ FullNorthColumn s c)
    (hnoeast : ∀ y, s (c,y) ≠ .east) :
    ¬ EventuallyJammed (eastDirection w 2 hw) (northDirection w 2 (by decide)) s := by
  classical
  intro hj
  let G : Fin w → Prop := fun x => x = c
  have hb : PlugBounded hw G s := by
    intro x hx
    by_cases hxc : x = c
    · right
      rw [hxc]
      exact hright
    · have hn : cyclicNext w hw x = c := by
        by_contra hne
        exact hx (by simp [G, hxc, hne])
      have hp : x = cyclicPrev w hw c := by
        rw [← hn, cyclicPrev_next]
      left
      rw [hp]
      exact hleft
  have hrun : ∀ i, i < 1 → G (iterate (cyclicNext w hw) i c) ∧
      ¬ FullNorthColumn s (iterate (cyclicNext w hw) i c) := by
    intro i hi
    have heq : i = 0 := by omega
    subst i
    exact ⟨rfl, hnonplug⟩
  have hlower := gap_east_count_lower_bound hw (by decide) G s hj hb c hnorth 1 hw hrun
  have hzero : eastCountIn G s = 0 := by
    unfold eastCountIn
    rw [List.countP_eq_length_filter]
    have hnil : ((speciesCells w 2 .east s).filter fun q => decide (G q.1)) = [] := by
      cases hlist : ((speciesCells w 2 .east s).filter fun q => decide (G q.1)) with
      | nil => rfl
      | cons q qs =>
        exfalso
        have hm : q ∈ ((speciesCells w 2 .east s).filter fun q => decide (G q.1)) := by
          rw [hlist]
          simp
        obtain ⟨hmem, hg⟩ := List.mem_filter.mp hm
        have hcar := (mem_speciesCells w 2 .east s q).mp hmem
        have hqc : q.1 = c := of_decide_eq_true hg
        exact hnoeast q.2 (by simpa [← hqc] using hcar)
    rw [hnil]
    rfl
  omega

/-- Finite coefficient comparison once the recurrence is established. -/
theorem marked_sum_le (W : Nat) (f : Fin W → ℚ)
    (hf : ∀ i, 0 ≤ f i) :
    (∑ i : Fin W, (i.val + 1 : ℚ) * f i) ≤ (W : ℚ) * ∑ i, f i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (hf i)
  exact_mod_cast (Nat.succ_le_of_lt i.isLt)

end BML.Prob
