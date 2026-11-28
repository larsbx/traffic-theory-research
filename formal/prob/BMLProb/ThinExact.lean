import BMLProb.Thin
import BMLProb.Renewal
import BML.GapIndependence

/-!
Exact thin-torus jam probabilities by gap independence (blueprint B10.5,
second identity, and B10.8; the reduction behind Theorem S).

With a full north column present, `s` eventually jams iff every gap after a
full north column jams as a walled gap (`BML.eventuallyJammed_iff_gaps`). Read
column by column, that is the cyclic-word event of `Renewal`, with plugs the
full north columns and good gaps the walled gaps that jam. So

  `P(plug ∧ jam) = ∑_{l=1}^{w} l · b_l · C_{w-l}`,  `b_l = (p/2)^h · J_{l-1}`,

where `J_g = gapJamProb g` is the weight of the walled gaps of length `g` that
jam, and `C` is the renewal sequence. This is `plug_jam_counts` of
`bml/thin_exact.py`, whose `J_g` for `g ≤ 14` come from the enumeration in
`bml/native/gap_jam.c` (not checked in Lean). Without a full north column a jam
needs `w` east cars (B10.3), which gives the sandwich of `thin_exact_sandwich`.
All statements hold at every height.
-/
namespace BML.Prob

open Finset Renewal

open scoped Fin.NatCast

variable {h : Nat} (hh : 0 < h)

/-- A column is a plug: every cell holds a north car. -/
def IsPlug (col : Fin h → Cell) : Prop := ∀ y, col y = .north

instance : DecidablePred (IsPlug (h := h)) := fun col =>
  inferInstanceAs (Decidable (∀ y, col y = .north))

private theorem ite_iff {P Q : Prop} {dP : Decidable P} {dQ : Decidable Q} (h : P ↔ Q) (a b : ℚ) :
    @ite ℚ P dP a b = @ite ℚ Q dQ a b := by
  by_cases hp : P
  · have hq := h.mp hp
    simp [hp, hq]
  · have hq : ¬ Q := fun hq => hp (h.mpr hq)
    simp [hp, hq]

/-- A gap word is good when its walled gap jams. -/
def GoodGap (l : List (Fin h → Cell)) : Prop := GapJams hh l.length fun i => l.get i

theorem goodGap_ofFn {g : Nat} (F : Fin g → Fin h → Cell) : GoodGap hh (List.ofFn F) ↔ GapJams hh g F := by
  have key : ∀ m (e : m = g) (G : Fin m → Fin h → Cell), (∀ i, G i = F (Fin.cast e i)) →
      (GapJams hh m G ↔ GapJams hh g F) := by
    rintro m rfl G hG
    rw [show G = F from funext fun i => by simpa using hG i]
  exact key _ (List.length_ofFn) _ fun i => by simp; rfl

/-- The `i`-th column east of `x` is `x + i`. -/
theorem eastOf_eq_add {n : Nat} (x : Fin (n+1)) (i : Nat) :
    eastOf (Nat.succ_pos n) x i = x + (i : Fin (n+1)) :=
  Fin.ext (by rw [iterate_cyclicNext_val, Fin.val_add, Fin.val_natCast, Nat.add_mod_mod])

/-- B10.8, read column by column: a configuration has a full north column and
eventually jams iff its column word has a plug and every gap good. -/
theorem plug_and_jam_iff_cyc {n : Nat} (s : Config (Position (n+1) h)) :
    ((∃ x, FullNorthColumn s x) ∧
      EventuallyJammed (eastDirection (n+1) h (Nat.succ_pos n)) (northDirection (n+1) h hh) s) ↔
    Cyc IsPlug (GoodGap hh) (column s) := by
  have hgap : ∀ x g, IsGapAfter (Nat.succ_pos n) s x g ↔ IsGapC IsPlug (column s) x g := by
    intro x g
    simp only [IsGapAfter, IsGapC, eastOf_eq_add]
    rfl
  have hword : ∀ x g, GapJams hh g (gapWord (Nat.succ_pos n) s x g) ↔
      GoodGap hh (wordC (column s) x g) := by
    intro x g
    rw [wordC, goodGap_ofFn]
    refine Iff.of_eq (congrArg _ (funext fun i => funext fun y => ?_))
    show s (eastOf _ x (i.val + 1), y) = s (x + ((i.val + 1 : ℕ) : Fin (n+1)), y)
    rw [eastOf_eq_add]
  constructor
  · rintro ⟨hplug, hj⟩
    refine ⟨hplug, fun x g hx => ?_⟩
    rw [← hword]
    exact (eventuallyJammed_iff_gaps (Nat.succ_pos n) hh s hplug).mp hj x g ((hgap x g).mpr hx)
  · rintro ⟨hplug, hall⟩
    exact ⟨hplug, (eventuallyJammed_iff_gaps (Nat.succ_pos n) hh s hplug).mpr fun x g hx =>
      (hword x g).mpr (hall x g ((hgap x g).mp hx))⟩

/-- The iid weight as a sum over column words. -/
theorem prob_eq_sum_columns {w : Nat} (p : ℚ) (A : Config (Position w h) → Prop) :
    prob p A = ∑ c : Fin w → Fin h → Cell,
      (∏ x, weight p (c x)) * (open Classical in if A (fun q => c q.1 q.2) then 1 else 0) := by
  classical
  unfold prob
  refine Fintype.sum_equiv (Equiv.curry (Fin w) (Fin h) Cell) _ _ fun s => ?_
  have hw : weight p s = ∏ x, weight p (column s x) := by
    unfold weight
    rw [Fintype.prod_prod_type]
    rfl
  rw [hw]
  by_cases hA : A s
  · simp [hA]; rfl
  · simp [hA]

/-- The weight of the walled gaps of length `g` that jam. -/
noncomputable def gapJamProb (p : ℚ) (g : Nat) : ℚ :=
  prob p fun u : Config (Position g h) =>
    (∀ x, ¬ FullNorthColumn u x) ∧ GapJams hh g fun i y => u (i, y)

theorem plugWeight_eq (p : ℚ) : plugWeight (weight p) (IsPlug (h := h)) = (p / 2) ^ h := by
  have := prob_all_north (ι := Fin h) p
  rw [Fintype.card_fin] at this
  rw [← this, plugWeight, prob]
  exact sum_congr rfl fun a _ => ite_iff Iff.rfl _ _

theorem Gw_eq (p : ℚ) (g : Nat) :
    Gw (weight p) IsPlug (GoodGap hh) g = gapJamProb hh p g := by
  classical
  rw [gapJamProb, prob_eq_sum_columns, Gw, wsum_eq]
  refine sum_congr rfl fun c _ => ?_
  congr 1
  have hfree : Free IsPlug (List.ofFn c) ↔ ∀ x, ¬ FullNorthColumn (fun q : Position g h => c q.1 q.2) x :=
    ⟨fun hf x hx => hf (c x) (List.mem_ofFn.mpr ⟨x, rfl⟩) hx,
      fun hf a ha hpa => by obtain ⟨x, rfl⟩ := List.mem_ofFn.mp ha; exact hf x hpa⟩
  exact ite_iff (and_congr hfree (goodGap_ofFn hh c)) _ _

/-- The renewal sequence of `bml/thin_exact.py` at density `p`. -/
noncomputable def thinC (p : ℚ) : Nat → ℚ := C (weight p) (IsPlug (h := h)) (GoodGap hh)

theorem thinC_zero (p : ℚ) : thinC hh p 0 = 1 := by rw [thinC, C]

theorem thinC_succ (p : ℚ) (m : Nat) :
    thinC hh p (m + 1) = ∑ l : Fin (m + 1), (p / 2) ^ h * gapJamProb hh p l * thinC hh p (m - l) := by
  rw [thinC, C]
  simp only [plugWeight_eq, Gw_eq]

/-- B10.5, second identity, and the counting form of B10.8: the weight of the
configurations with a full north column that eventually jam is the renewal
sum of `plug_jam_counts` in `bml/thin_exact.py`. -/
theorem prob_plug_and_jam (p : ℚ) (n : Nat) :
    prob p (fun s : Config (Position (n+1) h) => (∃ x, FullNorthColumn s x) ∧
        EventuallyJammed (eastDirection (n+1) h (Nat.succ_pos n)) (northDirection (n+1) h hh) s) =
      ∑ l ∈ range (n + 1), (l + 1 : ℚ) * ((p / 2) ^ h * gapJamProb hh p l) * thinC hh p (n - l) := by
  classical
  rw [prob_eq_sum_columns]
  have := sum_cyc_renewal (weight p) (IsPlug (h := h)) (GoodGap hh) n
  simp only [plugWeight_eq, Gw_eq] at this
  rw [show thinC hh p = C (weight p) IsPlug (GoodGap hh) from rfl, ← this]
  refine sum_congr rfl fun c _ => ?_
  congr 1
  exact ite_iff (plug_and_jam_iff_cyc hh (fun q => c q.1 q.2)) _ _

/-- The sandwich behind Theorem S: the plug part bounds `q` from below, and
with the weight of the plug-free states holding `w` east cars, from above. -/
theorem thin_exact_sandwich {p : ℚ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (n : Nat) :
    prob p (fun s : Config (Position (n+1) h) => (∃ x, FullNorthColumn s x) ∧
        EventuallyJammed (eastDirection (n+1) h (Nat.succ_pos n)) (northDirection (n+1) h hh) s) ≤
      jamProb (Nat.succ_pos n) hh p ∧
    jamProb (Nat.succ_pos n) hh p ≤
      prob p (fun s : Config (Position (n+1) h) => (∃ x, FullNorthColumn s x) ∧
        EventuallyJammed (eastDirection (n+1) h (Nat.succ_pos n)) (northDirection (n+1) h hh) s) +
      prob p (fun s : Config (Position (n+1) h) =>
        (∀ x, ¬ FullNorthColumn s x) ∧ n + 1 ≤ speciesCount (n+1) h .east s) := by
  refine ⟨prob_mono h0 h1 fun s hs => hs.2, ?_⟩
  refine le_trans (prob_mono h0 h1 fun s hj => ?_) (prob_or_le h0 h1 _ _)
  by_cases hplug : ∃ x, FullNorthColumn s x
  · exact Or.inl ⟨hplug, hj⟩
  · refine Or.inr ⟨fun x hx => hplug ⟨x, hx⟩, ?_⟩
    rcases Nat.lt_or_ge (speciesCount (n+1) h .east s) (n+1) with hfew | hmany
    · exact absurd (eventuallyJammed_fullNorthColumn_of_few_east (Nat.succ_pos n) hh s hj hfew)
        hplug
    · exact hmany

end BML.Prob
