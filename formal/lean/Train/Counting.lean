import BML.Torus

namespace BML.Train.Counting

/-- Finite cardinality is preserved by a bijection between the selected sites. -/
theorem filter_length_eq_of_bijection (sites : List α) (hn : sites.Nodup)
    (complete : ∀ x, x ∈ sites) (p q : α → Bool) (f : α → α)
    (preserves : ∀ x, p x = true → q (f x) = true)
    (injective : ∀ x y, p x = true → p y = true → f x = f y → x = y)
    (surjective : ∀ y, q y = true → ∃ x, p x = true ∧ f x = y) :
    (sites.filter p).length = (sites.filter q).length := by
  have hp : (sites.filter p).Nodup := hn.filter p
  have hq : (sites.filter q).Nodup := hn.filter q
  have hm : ((sites.filter p).map f).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem ?_ hp
    intro x y hx hy hne heq
    exact hne (injective x y (List.mem_filter.mp hx).2 (List.mem_filter.mp hy).2 heq)
  have perm : ((sites.filter p).map f).Perm (sites.filter q) := by
    apply (List.perm_ext_iff_of_nodup hm hq).mpr
    intro y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      exact List.mem_filter.mpr ⟨complete _, preserves x (List.mem_filter.mp hx).2⟩
    · intro hy
      obtain ⟨x, hx, hxy⟩ := surjective y (List.mem_filter.mp hy).2
      exact List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨complete x, hx⟩, hxy⟩
  simpa using perm.length_eq

theorem indicator_sum_eq_filter_length (sites : List α) (p : α → Prop)
    [DecidablePred p] :
    (sites.map fun x => if p x then 1 else 0).sum =
      (sites.filter fun x => decide (p x)).length := by
  induction sites with
  | nil => rfl
  | cons a sites ih =>
    by_cases ha : p a <;> simp [ha, ih, Nat.add_comm]

theorem mem_positions (w h : Nat) (p : BML.Position w h) :
    p ∈ BML.positions w h := by
  rcases p with ⟨x, y⟩
  apply List.mem_flatMap.mpr
  exact ⟨y, List.mem_finRange y, List.mem_map.mpr ⟨x, List.mem_finRange x, rfl⟩⟩

theorem positions_nodup (w h : Nat) : (BML.positions w h).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro y hy
    apply List.Pairwise.map _ ?_ (List.nodup_finRange w)
    intro x₁ x₂ hne heq
    exact hne (Prod.mk.inj heq).1
  · apply List.Pairwise.imp ?_ (List.nodup_finRange h)
    intro y₁ y₂ hne p hp q hq heq
    obtain ⟨x₁, hx₁, rfl⟩ := List.mem_map.mp hp
    obtain ⟨x₂, hx₂, rfl⟩ := List.mem_map.mp hq
    exact hne (Prod.mk.inj heq).2

theorem speciesCount_eq_filter_length (w h : Nat) (sp : BML.Species)
    (s : BML.Config (BML.Position w h)) :
    BML.speciesCount w h sp s =
      ((BML.positions w h).filter fun p => decide (s p = sp.cell)).length :=
  indicator_sum_eq_filter_length _ _

end BML.Train.Counting
