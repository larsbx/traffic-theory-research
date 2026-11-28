import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
Renewal sums over words (blueprint B10.5, second identity, and the counting
form of B10.8).

Letters `a : α` carry weights `wt a`; a word's weight is the product. Some
letters are *plugs* (`P`). In a cyclic word with a plug, the *gap* after a
plug is the run of non-plug letters up to the next plug. For any predicate
`Good` on gap words, the total weight of the cyclic words of length `n + 1`
with a plug and every gap good is the renewal sum

  `∑_{l=1}^{n+1} l · b_l · C_{n+1-l}`,  `b_l = A · G_{l-1}`,

where `A` is the weight of a plug letter, `G_j` the weight of the good gap
words of length `j`, and `C_0 = 1`, `C_m = ∑_{l=1}^{m} b_l C_{m-l}`. This is
`plug_jam_counts` in `bml/thin_exact.py`.

The proof works with lists. `wsum n F` is the weighted sum of `F` over words
of length `n`. A linear word is split at its first plug; a cyclic word is
rotated so that its last plug comes first, which weights it by the length of
its first block.
-/
namespace BML.Prob.Renewal

open Finset

variable {α : Type*} [Fintype α] (wt : α → ℚ) (P : α → Prop) [DecidablePred P]

/-! ### Weighted sums over words of a given length -/

/-- `∑` over words `l` of length `n` of `weight l * F l`. -/
def wsum : ℕ → (List α → ℚ) → ℚ
  | 0, F => F []
  | n+1, F => ∑ a, wt a * wsum n (fun l => F (a :: l))

/-- `wsum` is the sum over tuples. -/
theorem wsum_eq (n : ℕ) (F : List α → ℚ) :
    wsum wt n F = ∑ v : Fin n → α, (∏ i, wt (v i)) * F (List.ofFn v) := by
  induction n generalizing F with
  | zero => simp [wsum]
  | succ n ih =>
    rw [wsum, ← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
    refine sum_congr rfl fun a _ => ?_
    rw [ih, mul_sum]
    refine sum_congr rfl fun v _ => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ, List.ofFn_succ, mul_assoc]

theorem wsum_congr {n : ℕ} {F G : List α → ℚ} (h : ∀ l : List α, l.length = n → F l = G l) :
    wsum wt n F = wsum wt n G := by
  rw [wsum_eq, wsum_eq]
  exact sum_congr rfl fun v _ => by rw [h _ (List.length_ofFn)]

theorem wsum_add (n : ℕ) (F G : List α → ℚ) :
    wsum wt n (fun l => F l + G l) = wsum wt n F + wsum wt n G := by
  simp only [wsum_eq, mul_add, sum_add_distrib]

theorem wsum_mul_left (n : ℕ) (c : ℚ) (F : List α → ℚ) :
    wsum wt n (fun l => c * F l) = c * wsum wt n F := by
  simp only [wsum_eq, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

theorem wsum_mul_right (n : ℕ) (c : ℚ) (F : List α → ℚ) :
    wsum wt n (fun l => F l * c) = wsum wt n F * c := by
  simp only [wsum_eq, sum_mul]
  exact sum_congr rfl fun _ _ => by ring

theorem wsum_sum {ι : Type*} (s : Finset ι) (n : ℕ) (F : ι → List α → ℚ) :
    wsum wt n (fun l => ∑ i ∈ s, F i l) = ∑ i ∈ s, wsum wt n (F i) := by
  simp only [wsum_eq, mul_sum]
  exact sum_comm

/-! ### Leading non-plug runs -/

/-- All letters are non-plugs. -/
def Free (l : List α) : Prop := ∀ a ∈ l, ¬ P a

instance : DecidablePred (Free P) := fun l => inferInstanceAs (Decidable (∀ a ∈ l, ¬ P a))

/-- The length of the leading run of non-plug letters. -/
def lead : List α → ℕ
  | [] => 0
  | a :: l => if P a then 0 else lead l + 1

omit [Fintype α] in
theorem lead_le (l : List α) : lead P l ≤ l.length := by
  induction l with
  | nil => simp [lead]
  | cons a l ih => unfold lead; split <;> simp; omega

omit [Fintype α] in
theorem lead_append_free {u : List α} (hu : Free P u) (a : α) (ha : P a) (r : List α) :
    lead P (u ++ a :: r) = u.length := by
  induction u with
  | nil => simp [lead, ha]
  | cons b u ih =>
    have hb : ¬ P b := hu b (by simp)
    simp [lead, hb, ih fun c hc => hu c (by simp [hc])]

omit [Fintype α] in
theorem lead_free {u : List α} (hu : Free P u) : lead P u = u.length := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    have hb : ¬ P b := hu b (by simp)
    simp [lead, hb, ih fun c hc => hu c (by simp [hc])]

omit [Fintype α] in
/-- Every word is a free word, or a free word, a plug and a rest. -/
theorem split_first (l : List α) :
    Free P l ∨ ∃ u a r, Free P u ∧ P a ∧ l = u ++ a :: r := by
  induction l with
  | nil => exact Or.inl fun _ h => absurd h (by simp)
  | cons b l ih =>
    by_cases hb : P b
    · exact Or.inr ⟨[], b, l, fun _ h => absurd h (by simp), hb, rfl⟩
    · rcases ih with hf | ⟨u, a, r, hu, ha, rfl⟩
      · exact Or.inl fun c hc => by
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hb
          · exact hf c hc
      · refine Or.inr ⟨b :: u, a, r, fun c hc => ?_, ha, rfl⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hb
        · exact hu c hc

omit [Fintype α] in
/-- The number of prefixes `take j l`, `j ≤ length l`, that are free. -/
theorem sum_free_take (l : List α) :
    ∑ j ∈ range (l.length + 1), (if Free P (l.take j) then (1 : ℚ) else 0) = lead P l + 1 := by
  induction l with
  | nil => simp [lead, Free]
  | cons a l ih =>
    rw [List.length_cons, sum_range_succ']
    simp only [List.take_succ_cons, List.take_zero]
    have h0 : Free P ([] : List α) := fun _ h => absurd h (by simp)
    by_cases ha : P a
    · have : ∀ j, ¬ Free P (a :: l.take j) := fun j hf => hf a (by simp) ha
      simp [this, h0, lead, ha]
    · have : ∀ j, Free P (a :: l.take j) ↔ Free P (l.take j) := fun j =>
        ⟨fun hf c hc => hf c (by simp [hc]), fun hf c hc => by
          rcases List.mem_cons.mp hc with rfl | hc
          · exact ha
          · exact hf c hc⟩
      simp only [this, ih, h0, ite_true, lead, ha, ite_false]
      push_cast
      ring

/-! ### Splitting at the first plug -/

/-- The weight of the plug letters. -/
def plugWeight : ℚ := ∑ a, if P a then wt a else 0

/-- B10.5 (linear form): a word of length `n` is free, or a free word of
length `j < n`, a plug, and a word of length `n - 1 - j`. -/
theorem wsum_split (n : ℕ) (F : List α → ℚ) :
    wsum wt n F =
      ∑ j ∈ range n, wsum wt j (fun u => if Free P u then
          ∑ a, (if P a then wt a else 0) * wsum wt (n - 1 - j) (fun r => F (u ++ a :: r))
        else 0) +
      wsum wt n (fun u => if Free P u then F u else 0) := by
  induction n generalizing F with
  | zero => simp [wsum, Free]
  | succ n ih =>
    have hfree : ∀ (b : α) u, Free P (b :: u) ↔ ¬ P b ∧ Free P u := fun b u =>
      ⟨fun h => ⟨h b (by simp), fun c hc => h c (by simp [hc])⟩, fun ⟨hb, hu⟩ c hc => by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hb
        · exact hu c hc⟩
    have h0 : Free P ([] : List α) := fun _ h => absurd h (by simp)
    -- inner sum of the induction hypothesis, for a first letter `b`
    let X : α → ℕ → ℚ := fun b j => wsum wt j (fun u => if Free P u then
      ∑ a, (if P a then wt a else 0) * wsum wt (n - 1 - j) (fun r => F (b :: (u ++ a :: r)))
      else 0)
    let Y : α → ℚ := fun b => wsum wt n (fun u => if Free P u then F (b :: u) else 0)
    have lhs : wsum wt (n+1) F = ∑ b, (if P b then wt b else 0) * wsum wt n (fun r => F (b :: r)) +
        ∑ b, (if P b then 0 else wt b) * (∑ j ∈ range n, X b j + Y b) := by
      rw [wsum, ← sum_add_distrib]
      refine sum_congr rfl fun b _ => ?_
      rw [ih (fun r => F (b :: r))]
      split <;> simp [X, Y]
    have e0 : wsum wt 0 (fun u => if Free P u then
        ∑ a, (if P a then wt a else 0) * wsum wt (n + 1 - 1 - 0) (fun r => F (u ++ a :: r))
        else 0) = ∑ b, (if P b then wt b else 0) * wsum wt n (fun r => F (b :: r)) := by
      simp [wsum, h0]
    have e1 : ∀ j, wsum wt (j+1) (fun u => if Free P u then
        ∑ a, (if P a then wt a else 0) * wsum wt (n + 1 - 1 - (j+1)) (fun r => F (u ++ a :: r))
        else 0) = ∑ b, (if P b then 0 else wt b) * X b j := fun j => by
      rw [wsum]
      refine sum_congr rfl fun b _ => ?_
      by_cases hb : P b
      · simp only [hb, ite_true, hfree, not_true_eq_false, false_and, ite_false]
        simp [wsum_eq]
      · simp only [hb, ite_false, hfree, not_false_eq_true, true_and, X]
        congr 1
        refine wsum_congr wt fun u _ => ?_
        simp only [List.cons_append, show n + 1 - 1 - (j + 1) = n - 1 - j by omega]
    have e2 : wsum wt (n+1) (fun u => if Free P u then F u else 0) =
        ∑ b, (if P b then 0 else wt b) * Y b := by
      rw [wsum]
      refine sum_congr rfl fun b _ => ?_
      by_cases hb : P b
      · simp [hb, hfree, wsum_eq]
      · simp [hb, hfree, Y]
    rw [lhs, sum_range_succ', e0, e2]
    simp only [e1, mul_add, sum_add_distrib, mul_sum]
    rw [sum_comm (s := range n)]
    ring

/-! ### Linear words: every gap good -/

variable (Good : List α → Prop)

set_option linter.unusedVariables false in
/-- Every gap of a linear word is good: the leading free run, and, after each
plug, the free run up to the next plug or the end. -/
def LinE (l : List α) : Prop :=
  Good (l.take (lead P l)) ∧
    match hd : l.drop (lead P l) with
    | [] => True
    | _ :: r => LinE r
termination_by l.length
decreasing_by
  have := congrArg List.length hd
  simp only [List.length_drop, List.length_cons] at this
  omega

omit [Fintype α] in
theorem linE_free {u : List α} (hu : Free P u) : LinE P Good u ↔ Good u := by
  rw [LinE]
  have h1 : u.take (lead P u) = u := by rw [lead_free P hu, List.take_length]
  have h2 : u.drop (lead P u) = [] := by rw [lead_free P hu, List.drop_length]
  constructor
  · intro ⟨hg, _⟩; rwa [h1] at hg
  · intro hg
    refine ⟨by rw [h1]; exact hg, ?_⟩
    split
    · trivial
    · rename_i h; rw [h2] at h; cases h

omit [Fintype α] in
theorem linE_split {u : List α} (hu : Free P u) {a : α} (ha : P a) (r : List α) :
    LinE P Good (u ++ a :: r) ↔ Good u ∧ LinE P Good r := by
  rw [LinE]
  have hl := lead_append_free P hu a ha r
  have h1 : (u ++ a :: r).take (lead P (u ++ a :: r)) = u := by
    rw [hl, List.take_left]
  have h2 : (u ++ a :: r).drop (lead P (u ++ a :: r)) = a :: r := by
    rw [hl, List.drop_left]
  rw [h1]
  refine and_congr Iff.rfl ?_
  split
  · rename_i h; rw [h2] at h; cases h
  · rename_i b r' h
    rw [h2] at h
    cases h
    exact Iff.rfl

open Classical

/-- Weight of the linear words of length `m` with every gap good. -/
noncomputable def Φ (m : ℕ) : ℚ := wsum wt m fun l => if LinE P Good l then 1 else 0

/-- Weight of the good gap words of length `j`. -/
noncomputable def Gw (j : ℕ) : ℚ := wsum wt j fun u => if Free P u ∧ Good u then 1 else 0

/-- Weight of the linear words of length `m` with every gap good, each
counted with the length of its first block. -/
noncomputable def D (m : ℕ) : ℚ := wsum wt m fun l => if LinE P Good l then (lead P l + 1 : ℚ) else 0

/-- The first-plug split applied to a word with every gap good. -/
private theorem split_linE (m : ℕ) (f : ℕ → ℚ) (k : ℕ → ℚ)
    (hF : ∀ j, wsum wt (m - 1 - j) (fun r => if LinE P Good r then f j else 0) = k j) :
    wsum wt m (fun l => if LinE P Good l then f (lead P l) else 0) =
      ∑ j ∈ range m, Gw wt P Good j * plugWeight wt P * k j +
        Gw wt P Good m * f m := by
  rw [wsum_split wt P]
  congr 1
  · refine sum_congr rfl fun j hj => ?_
    rw [Gw, ← wsum_mul_right, ← wsum_mul_right]
    refine wsum_congr wt fun u hu => ?_
    by_cases hfu : Free P u
    · simp only [hfu, true_and, ite_true]
      rw [plugWeight, mul_sum, sum_mul]
      refine sum_congr rfl fun a _ => ?_
      by_cases ha : P a
      · have hw : (wsum wt (m - 1 - j) fun r => if LinE P Good (u ++ a :: r) then
            f (lead P (u ++ a :: r)) else 0) = (if Good u then 1 else 0) * k j := by
          rw [← hF j, ← wsum_mul_left]
          refine wsum_congr wt fun r _ => ?_
          by_cases hg : Good u <;>
            simp [linE_split P Good hfu ha, hg, lead_append_free P hfu a ha, hu]
        simp only [ha, ite_true, hw]
        ring
      · simp [ha]
    · simp [hfu]
  · rw [Gw, ← wsum_mul_right]
    refine wsum_congr wt fun u hu => ?_
    by_cases hfu : Free P u
    · simp [hfu, linE_free P Good hfu, lead_free P hfu, hu]
    · simp [hfu]

theorem Φ_rec (m : ℕ) :
    Φ wt P Good m = ∑ j ∈ range m, Gw wt P Good j * plugWeight wt P * Φ wt P Good (m - 1 - j) +
      Gw wt P Good m := by
  have := split_linE wt P Good m (fun _ => 1) (fun j => Φ wt P Good (m - 1 - j)) fun j => rfl
  simpa [Φ] using this

theorem D_rec (m : ℕ) :
    D wt P Good m = ∑ j ∈ range m,
        Gw wt P Good j * plugWeight wt P * ((j + 1 : ℚ) * Φ wt P Good (m - 1 - j)) +
      Gw wt P Good m * (m + 1 : ℚ) := by
  refine split_linE wt P Good m (fun j => (j + 1 : ℚ)) _ fun j => ?_
  rw [Φ, ← wsum_mul_left]
  exact wsum_congr wt fun r _ => by split <;> simp

/-- The renewal sequence of `bml/thin_exact.py`: `C 0 = 1`,
`C m = ∑_{l=1}^{m} b_l C_{m-l}` with `b_l = A · G_{l-1}`. -/
noncomputable def C : ℕ → ℚ
  | 0 => 1
  | m + 1 => ∑ l : Fin (m + 1), plugWeight wt P * Gw wt P Good l * C (m - l)
termination_by m => m
decreasing_by omega

theorem C_succ (m : ℕ) : C wt P Good (m + 1) = plugWeight wt P * Φ wt P Good m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [C, Fin.sum_univ_eq_sum_range (fun l => plugWeight wt P * Gw wt P Good l * C wt P Good (m - l)),
      sum_range_succ, Φ_rec, Nat.sub_self, C, mul_add, mul_sum]
    congr 1
    · refine sum_congr rfl fun j hj => ?_
      have hj := mem_range.mp hj
      rw [show m - j = (m - 1 - j) + 1 by omega, ih _ (by omega)]
      ring
    · ring

/-- The first-block-weighted sum in closed form. -/
theorem plugWeight_mul_D (n : ℕ) :
    plugWeight wt P * D wt P Good n =
      ∑ l ∈ range (n + 1), (l + 1 : ℚ) * (plugWeight wt P * Gw wt P Good l) * C wt P Good (n - l) := by
  rw [D_rec, sum_range_succ, Nat.sub_self, C, mul_add, mul_sum]
  congr 1
  · refine sum_congr rfl fun j hj => ?_
    rw [show n - j = (n - 1 - j) + 1 by have := mem_range.mp hj; omega, C_succ]
    ring
  · ring

/-! ### Cyclic words -/

open scoped Fin.NatCast

variable {n : ℕ}

/-- `x` is a plug, the next `g` letters are not, and the one after is. -/
def IsGapC (c : Fin (n+1) → α) (x : Fin (n+1)) (g : ℕ) : Prop :=
  P (c x) ∧ (∀ i : ℕ, 1 ≤ i → i ≤ g → ¬ P (c (x + (i : Fin (n+1))))) ∧
    P (c (x + ((g + 1 : ℕ) : Fin (n+1))))

/-- The gap word after `x`, of length `g`. -/
def wordC (c : Fin (n+1) → α) (x : Fin (n+1)) (g : ℕ) : List α :=
  List.ofFn fun i : Fin g => c (x + ((i.val + 1 : ℕ) : Fin (n+1)))

/-- A cyclic word with a plug and every gap good. -/
def Cyc (c : Fin (n+1) → α) : Prop :=
  (∃ x, P (c x)) ∧ ∀ x g, IsGapC P c x g → Good (wordC c x g)

omit [Fintype α] [DecidablePred P] in
theorem IsGapC.unique {c : Fin (n+1) → α} {x : Fin (n+1)} {g g' : ℕ} (h : IsGapC P c x g)
    (h' : IsGapC P c x g') : g = g' := by
  rcases Nat.lt_trichotomy g g' with hlt | heq | hgt
  · exact absurd h.2.2 (h'.2.1 (g + 1) (by omega) (by omega))
  · exact heq
  · exact absurd h'.2.2 (h.2.1 (g' + 1) (by omega) (by omega))

private theorem val_add_cast (x : Fin (n+1)) (i : ℕ) : (x + (i : Fin (n+1))).val = (x.val + i) % (n+1) := by
  rw [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod]

private theorem add_cast_eq (k i : ℕ) (hk : k ≤ n) (hle : k + i ≤ n) :
    (⟨k, by omega⟩ : Fin (n+1)) + (i : Fin (n+1)) = ⟨k + i, by omega⟩ :=
  Fin.ext (by rw [val_add_cast, Nat.mod_eq_of_lt (by simp; omega)])

private theorem add_cast_wrap (k i : ℕ) (hk : k ≤ n) (hm : k + i = n + 1) :
    (⟨k, by omega⟩ : Fin (n+1)) + (i : Fin (n+1)) = 0 :=
  Fin.ext (by rw [val_add_cast]; simp [hm])

/-- The tail of `c` as a list: letters `1, …, n`. -/
def tailList (c : Fin (n+1) → α) : List α := List.ofFn fun i : Fin n => c i.succ

omit [Fintype α] in
private theorem getElem_drop_tail (c : Fin (n+1) → α) (k i : ℕ) (hi : i < ((tailList c).drop k).length) :
    ((tailList c).drop k)[i] = c ⟨k + i + 1, by simp [tailList] at hi; omega⟩ := by
  simp only [tailList, List.getElem_drop, List.getElem_ofFn]
  rfl

omit [Fintype α] [DecidablePred P] in
private theorem cfin (c : Fin (n+1) → α) {a b : ℕ} (h : a = b) (ha : a < n + 1) :
    c ⟨a, ha⟩ = c ⟨b, h ▸ ha⟩ := by
  subst h; rfl

omit [Fintype α] in
private theorem length_drop_tail (c : Fin (n+1) → α) (k : ℕ) :
    ((tailList c).drop k).length = n - k := by
  simp [tailList]

omit [Fintype α] in
/-- The suffix after a plug at `k`: its gaps are good as a linear word iff
every gap after a plug at or beyond `k` is good. -/
private theorem suffix_linE (c : Fin (n+1) → α) (h0 : P (c 0)) :
    ∀ d k, n - k = d → (hk : k ≤ n) → P (c ⟨k, by omega⟩) →
      (LinE P Good ((tailList c).drop k) ↔
        ∀ x g, k ≤ x.val → IsGapC P c x g → Good (wordC c x g)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro k hd hk hpk
  -- letters of the suffix, and plugs strictly inside it
  have hget : ∀ i (hi : i < ((tailList c).drop k).length),
      ((tailList c).drop k)[i] = c ⟨k + i + 1, by rw [length_drop_tail] at hi; omega⟩ :=
    fun i hi => getElem_drop_tail c k i hi
  have inside : ∀ x : Fin (n+1), k < x.val → ∃ i, ∃ hi : i < ((tailList c).drop k).length,
      c x = ((tailList c).drop k)[i] := fun x hx =>
    ⟨x.val - k - 1, by rw [length_drop_tail]; omega, by
      rw [hget]; congr 1; ext; simp; omega⟩
  have atk : ∀ x : Fin (n+1), k ≤ x.val → x.val ≤ k → x = ⟨k, by omega⟩ := fun x h1 h2 =>
    Fin.ext (by simp; omega)
  rcases split_first P ((tailList c).drop k) with hfree | ⟨u, a, r, hu, ha, hl⟩
  · -- no further plug: one gap, of length `n - k`, ended by the plug at `0`
    have gapA : IsGapC P c ⟨k, by omega⟩ (n - k) := by
      refine ⟨hpk, fun i h1 h2 => ?_, ?_⟩
      · rw [add_cast_eq k i hk (by omega)]
        have := (hget (i - 1) (by rw [length_drop_tail]; omega)).trans
          (cfin c (show k + (i - 1) + 1 = k + i by omega) _)
        rw [← this]
        exact hfree _ (List.getElem_mem _)
      · rw [add_cast_wrap k _ hk (by omega)]; exact h0
    have wordA : wordC c ⟨k, by omega⟩ (n - k) = (tailList c).drop k := by
      refine List.ext_getElem (by simp [wordC, tailList]) fun i h1 h2 => ?_
      rw [hget]
      simp only [wordC, List.getElem_ofFn]
      rw [add_cast_eq k _ hk (by simp [wordC] at h1; omega)]
      rfl
    rw [linE_free P Good hfree]
    constructor
    · intro hg x g hx hgap
      have hxk : x = ⟨k, by omega⟩ := by
        refine atk x hx ?_
        rcases Nat.lt_or_ge k x.val with hlt | hge
        · obtain ⟨i, hi, he⟩ := inside x hlt
          exact absurd (he ▸ hgap.1) (hfree _ (List.getElem_mem _))
        · exact hge
      rw [hxk] at hgap ⊢
      rw [← IsGapC.unique P gapA hgap, wordA]
      exact hg
    · intro h
      rw [← wordA]
      exact h _ _ (Nat.le_refl _) gapA
  · -- the next plug is at `k + J + 1`, `J = length u`
    have hlen := length_drop_tail c k
    rw [hl] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    have hJ : k + u.length + 1 ≤ n := by omega
    have hgetU : ∀ i (hi : i < u.length), u[i] = c ⟨k + i + 1, by omega⟩ := fun i hi => by
      have := hget i (by rw [length_drop_tail]; omega)
      simp only [hl, List.getElem_append_left hi] at this
      exact this
    have hgetA : a = c ⟨k + u.length + 1, by omega⟩ := by
      have := hget u.length (by rw [length_drop_tail]; omega)
      simp only [hl, List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_cons_zero] at this
      exact this
    have hr : r = (tailList c).drop (k + u.length + 1) := by
      have : ((tailList c).drop k).drop (u.length + 1) = r := by rw [hl]; simp
      rw [← this, List.drop_drop]
      congr 1
    have gapB : IsGapC P c ⟨k, by omega⟩ u.length := by
      refine ⟨hpk, fun i h1 h2 => ?_, ?_⟩
      · rw [add_cast_eq k i hk (by omega)]
        have := (hgetU (i - 1) (by omega)).trans
          (cfin c (show k + (i - 1) + 1 = k + i by omega) _)
        rw [← this]
        exact hu _ (List.getElem_mem _)
      · rw [add_cast_eq k _ hk (by omega)]
        have : (⟨k + (u.length + 1), by omega⟩ : Fin (n+1)) = ⟨k + u.length + 1, by omega⟩ := rfl
        rw [this, ← hgetA]
        exact ha
    have wordB : wordC c ⟨k, by omega⟩ u.length = u := by
      refine List.ext_getElem (by simp [wordC]) fun i h1 h2 => ?_
      rw [hgetU]
      simp only [wordC, List.getElem_ofFn]
      rw [add_cast_eq k _ hk (by simp [wordC] at h1; omega)]
      rfl
    have ih' := ih (n - (k + u.length + 1)) (by omega) (k + u.length + 1) rfl hJ
      (by rw [← hgetA]; exact ha)
    rw [hl, linE_split P Good hu ha, hr, ih']
    constructor
    · rintro ⟨hg, hrest⟩ x g hx hgap
      rcases Nat.lt_or_ge (k + u.length) x.val with hfar | hnear
      · exact hrest x g (by omega) hgap
      · rcases Nat.lt_or_ge k x.val with hlt | hge
        · -- a plug inside `u`: impossible
          have := hgetU (x.val - k - 1) (by omega)
          rw [show (⟨k + (x.val - k - 1) + 1, _⟩ : Fin (n+1)) = x from Fin.ext (by simp; omega)]
            at this
          exact absurd (this ▸ hgap.1) (hu _ (List.getElem_mem _))
        · have hxk := atk x hx hge
          rw [hxk] at hgap ⊢
          rw [← IsGapC.unique P gapB hgap, wordB]
          exact hg
    · intro h
      exact ⟨wordB ▸ h _ _ (Nat.le_refl _) gapB, fun x g hx => h x g (by omega)⟩

omit [Fintype α] in
/-- B10.8 in word form: with a plug at `0`, every gap of the cyclic word is
good iff every gap of its tail, read as a linear word, is good. -/
theorem cyc_iff_linE (c : Fin (n+1) → α) (h0 : P (c 0)) :
    Cyc P Good c ↔ LinE P Good (tailList c) := by
  rw [show tailList c = (tailList c).drop 0 from rfl, suffix_linE P Good c h0 n 0 (by omega) (by omega) h0]
  exact ⟨fun h x g _ => h.2 x g, fun h => ⟨⟨0, h0⟩, fun x g => h x g (Nat.zero_le _)⟩⟩

/-! ### Rotating the last plug to the front -/

/-- The word read from position `k`. -/
def shift (k : Fin (n+1)) (c : Fin (n+1) → α) : Fin (n+1) → α := fun z => c (z + k)

omit [Fintype α] [DecidablePred P] in
theorem isGapC_shift (k : Fin (n+1)) (c : Fin (n+1) → α) (x : Fin (n+1)) (g : ℕ) :
    IsGapC P (shift k c) x g ↔ IsGapC P c (x + k) g := by
  simp only [IsGapC, shift, add_right_comm _ k]

omit [Fintype α] [DecidablePred P] in
theorem wordC_shift (k : Fin (n+1)) (c : Fin (n+1) → α) (x : Fin (n+1)) (g : ℕ) :
    wordC (shift k c) x g = wordC c (x + k) g := by
  simp only [wordC, shift, add_right_comm _ k]

omit [Fintype α] [DecidablePred P] in
theorem cyc_shift (k : Fin (n+1)) (c : Fin (n+1) → α) : Cyc P Good (shift k c) ↔ Cyc P Good c := by
  simp only [Cyc, isGapC_shift, wordC_shift]
  constructor
  · rintro ⟨⟨x, hx⟩, h⟩
    exact ⟨⟨_, hx⟩, fun y g => by simpa using h (y - k) g⟩
  · rintro ⟨⟨x, hx⟩, h⟩
    exact ⟨⟨x - k, by simpa [shift] using hx⟩, fun y g => h (y + k) g⟩

omit [Fintype α] [DecidablePred P] in
theorem prod_shift (k : Fin (n+1)) (c : Fin (n+1) → α) :
    ∏ z, wt (shift k c z) = ∏ z, wt (c z) :=
  Fintype.prod_equiv (Equiv.addRight k) _ _ fun _ => rfl

/-- Shifting is a bijection of words. -/
def shiftEquiv (k : Fin (n+1)) : (Fin (n+1) → α) ≃ (Fin (n+1) → α) where
  toFun := shift k
  invFun := shift (-k)
  left_inv c := funext fun z => by simp [shift]
  right_inv c := funext fun z => by simp [shift]

/-- `k` is the last plug. -/
def IsLast (c : Fin (n+1) → α) (k : Fin (n+1)) : Prop := P (c k) ∧ ∀ i, k < i → ¬ P (c i)

omit [Fintype α] in
theorem sum_isLast (c : Fin (n+1) → α) (h : ∃ x, P (c x)) :
    ∑ k, (if IsLast P c k then (1 : ℚ) else 0) = 1 := by
  have hne : (univ.filter fun x => P (c x)).Nonempty := by
    obtain ⟨x, hx⟩ := h
    exact ⟨x, by simp [hx]⟩
  set m := (univ.filter fun x => P (c x)).max' hne
  have hm : P (c m) := by simpa using max'_mem _ hne
  have key : ∀ k, IsLast P c k ↔ k = m := fun k => by
    constructor
    · rintro ⟨hk, hlast⟩
      have hle : k ≤ m := le_max' _ k (by simp [hk])
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact absurd hm (hlast m hlt)
      · exact heq
    · rintro rfl
      exact ⟨hm, fun i hi hpi => absurd (le_max' _ i (by simp [hpi])) (not_le.mpr hi)⟩
  simp [key]

omit [Fintype α] [DecidablePred P] in
theorem getElem_tailList (c : Fin (n+1) → α) (j : ℕ) (hj : j < (tailList c).length) :
    (tailList c)[j] = c ⟨j + 1, by simp [tailList] at hj; omega⟩ := by
  simp [tailList]

omit [Fintype α] [DecidablePred P] in
/-- After rotating the last plug `k` to the front, the letters after it are
the first `n - k` letters of the tail. -/
theorem isLast_shift (k : Fin (n+1)) (c : Fin (n+1) → α) :
    IsLast P (shift (-k) c) k ↔ P (c 0) ∧ Free P ((tailList c).take (n - k.val)) := by
  simp only [IsLast, shift, add_neg_cancel]
  refine and_congr Iff.rfl ⟨fun h a ha => ?_, fun h i hi => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    have hjn : j < n - k.val := by simp [tailList] at hj; omega
    rw [List.getElem_take, getElem_tailList]
    have hi : k < (⟨k.val + j + 1, by omega⟩ : Fin (n+1)) :=
      Fin.lt_def.mpr (by show k.val < k.val + j + 1; omega)
    have := h _ hi
    rwa [← sub_eq_add_neg, show (⟨k.val + j + 1, _⟩ : Fin (n+1)) - k = ⟨j + 1, by omega⟩ from
      Fin.ext (by rw [Fin.coe_sub_iff_le.mpr (by simp [Fin.le_def]; omega)]; simp; omega)] at this
  · rw [← sub_eq_add_neg]
    have hik : k ≤ i := le_of_lt hi
    have hv : (i - k).val = i.val - k.val := Fin.coe_sub_iff_le.mpr hik
    have hpos : 1 ≤ i.val - k.val := by rw [Fin.lt_def] at hi; omega
    have hlen : i.val - k.val - 1 < ((tailList c).take (n - k.val)).length := by
      simp [tailList]; have := i.isLt; omega
    have e : ((tailList c).take (n - k.val))[i.val - k.val - 1] = c (i - k) := by
      rw [List.getElem_take, getElem_tailList]
      congr 1
      exact Fin.ext (by simp only [hv]; omega)
    have hmem : c (i - k) ∈ (tailList c).take (n - k.val) := e ▸ List.getElem_mem hlen
    exact h _ hmem

omit [Fintype α] [DecidablePred P] in
theorem tailList_cons (a : α) (t : Fin n → α) : tailList (Fin.cons a t : Fin (n+1) → α) = List.ofFn t := by
  simp [tailList]

/-- B10.5, second identity, in word form: the weight of the cyclic words of
length `n + 1` with a plug and every gap good is `A · D n`. -/
theorem sum_cyc (n : ℕ) :
    ∑ c : Fin (n+1) → α, (∏ i, wt (c i)) * (if Cyc P Good c then 1 else 0) =
      plugWeight wt P * D wt P Good n := by
  let W : (Fin (n+1) → α) → ℚ := fun c => ∏ i, wt (c i)
  -- every cyclic word with a plug has exactly one last plug
  have step1 : ∀ c : Fin (n+1) → α, W c * (if Cyc P Good c then 1 else 0) =
      ∑ k, W c * (if Cyc P Good c then 1 else 0) * (if IsLast P c k then 1 else 0) := fun c => by
    rw [← mul_sum]
    by_cases hc : Cyc P Good c
    · rw [sum_isLast P c hc.1, mul_one]
    · simp [hc]
  -- rotate the last plug to the front
  have step2 : ∀ k : Fin (n+1), ∑ c, W c * (if Cyc P Good c then 1 else 0) *
        (if IsLast P c k then 1 else 0) =
      ∑ c, W c * (if Cyc P Good c then 1 else 0) *
        (if P (c 0) ∧ Free P ((tailList c).take (n - k.val)) then 1 else 0) := fun k => by
    rw [← (shiftEquiv (-k)).sum_comp]
    refine sum_congr rfl fun c _ => ?_
    simp only [shiftEquiv, Equiv.coe_fn_mk, W, prod_shift, cyc_shift, isLast_shift]
  -- count the rotations: the length of the first block
  have step3 : ∀ c : Fin (n+1) → α, ∑ k : Fin (n+1),
      (if P (c 0) ∧ Free P ((tailList c).take (n - k.val)) then (1 : ℚ) else 0) =
      (if P (c 0) then (lead P (tailList c) + 1 : ℚ) else 0) := fun c => by
    by_cases h0 : P (c 0)
    · simp only [h0, true_and, ite_true]
      rw [Fin.sum_univ_eq_sum_range (fun k => if Free P ((tailList c).take (n - k)) then (1 : ℚ) else 0),
        ← sum_range_reflect, ← sum_free_take P (tailList c)]
      have hl : (tailList c).length = n := by simp [tailList]
      rw [hl]
      exact sum_congr rfl fun j hj => by
        rw [show n - (n + 1 - 1 - j) = j by have := mem_range.mp hj; omega]
    · simp [h0]
  calc ∑ c, W c * (if Cyc P Good c then 1 else 0)
      = ∑ k, ∑ c, W c * (if Cyc P Good c then 1 else 0) * (if IsLast P c k then 1 else 0) := by
        rw [sum_comm]; exact sum_congr rfl fun c _ => step1 c
    _ = ∑ c, W c * (if Cyc P Good c then 1 else 0) *
          (if P (c 0) then (lead P (tailList c) + 1 : ℚ) else 0) := by
        simp only [step2]
        rw [sum_comm]
        exact sum_congr rfl fun c _ => by rw [← mul_sum, step3]
    _ = ∑ a, (if P a then wt a else 0) * D wt P Good n := by
        rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
        refine sum_congr rfl fun a _ => ?_
        rw [D, wsum_eq, mul_sum]
        refine sum_congr rfl fun t _ => ?_
        change (∏ i, wt ((Fin.cons a t : Fin (n+1) → α) i)) *
            (if Cyc P Good (Fin.cons a t : Fin (n+1) → α) then (1 : ℚ) else 0) *
            (if P ((Fin.cons a t : Fin (n+1) → α) 0) then
              (lead P (tailList (Fin.cons a t : Fin (n+1) → α)) + 1 : ℚ) else 0) = _
        rw [Fin.prod_univ_succ, tailList_cons]
        simp only [Fin.cons_zero, Fin.cons_succ]
        by_cases ha : P a
        · rw [if_congr (cyc_iff_linE P Good (Fin.cons a t : Fin (n+1) → α) (by simpa using ha))
            rfl rfl, tailList_cons]
          simp only [ha, ite_true]
          split <;> ring
        · simp [ha]
    _ = plugWeight wt P * D wt P Good n := by rw [plugWeight, sum_mul]

/-- B10.5, second identity: the renewal sum of `bml/thin_exact.py`. -/
theorem sum_cyc_renewal (n : ℕ) :
    ∑ c : Fin (n+1) → α, (∏ i, wt (c i)) * (if Cyc P Good c then 1 else 0) =
      ∑ l ∈ range (n + 1), (l + 1 : ℚ) * (plugWeight wt P * Gw wt P Good l) * C wt P Good (n - l) := by
  rw [sum_cyc, plugWeight_mul_D]

end BML.Prob.Renewal
