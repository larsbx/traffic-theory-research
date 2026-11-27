import BML.NetFree

/-!
# Counting cars on a net

Over a finite enumeration of the cells, every tick conserves the number of
cars of each class, provided no route has an exit.
-/
namespace BML.Net

variable {Cell Class : Type} [DecidableEq Class]

/-- An injection of a duplicate-free list into another list bounds its length. -/
theorem length_le_of_injOn {α β : Type} (l : List α) (l' : List β) (hl : l.Nodup) (f : α → β)
    (hinj : ∀ a, a ∈ l → ∀ b, b ∈ l → f a = f b → a = b) (hmem : ∀ a, a ∈ l → f a ∈ l') :
    l.length ≤ l'.length := by
  have hnd : (l.map f).Nodup := by
    rw [List.nodup_iff_pairwise_ne] at hl ⊢
    refine List.pairwise_map.mpr (hl.imp_of_mem fun ha hb hne heq => hne (hinj _ ha _ hb heq))
  have := hnd.length_le_of_subset fun b hb => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact hmem a ha
  simpa using this

/-- The number of class-`k` cars, over the cell list `cells`. -/
def count (cells : List Cell) (s : Config Cell Class) (k : Class) : Nat :=
  (cells.filter fun c => decide (s c = some k)).length

/-- Every car has somewhere to go: no car of this state sits at an exit. -/
def Valid (net : Net Cell Class) (s : Config Cell Class) : Prop :=
  ∀ p k, s p = some k → (net.next k p).isSome = true

/-- A car that arrives somewhere along its route can continue from there. -/
def RouteClosed (net : Net Cell Class) : Prop :=
  ∀ k p c, net.next k p = some c → (net.next k c).isSome = true

variable {net : Net Cell Class} {s : Config Cell Class} {t : Nat}

theorem leaves_target (hx : Valid net s) {p : Cell} {k : Class} (hp : s p = some k)
    (hl : leaves net t s p = true) : ∃ d, net.next k p = some d ∧ winner net t s d = some k := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hx p k hp)
  refine ⟨d, hd, ?_⟩
  simpa [leaves, hp, hd] using hl

theorem step_some_iff {c : Cell} {k : Class} :
    step net t s c = some k ↔
      winner net t s c = some k ∨ (s c = some k ∧ leaves net t s c = false) := by
  unfold step
  cases hw : winner net t s c with
  | some j =>
    have hv := winner_vacant hw
    simp [hv]
  | none =>
    cases hl : leaves net t s c <;> simp

/-- **Conservation.** If no car sits at an exit, a tick conserves the number of
cars of each class. -/
theorem count_step (cells : List Cell) (hnd : cells.Nodup) (hall : ∀ c, c ∈ cells)
    (hx : Valid net s) (k : Class) : count cells (step net t s) k = count cells s k := by
  apply Nat.le_antisymm
  · -- after → before: a newcomer goes back to its source, a stayer stays
    let back : Cell → Cell := fun c =>
      if winner net t s c = some k then (net.prev k c).getD c else c
    refine length_le_of_injOn _ _ (hnd.sublist List.filter_sublist) back ?_ ?_
    · intro a ha b hb hab
      have ha' := step_some_iff.mp (of_decide_eq_true (List.mem_filter.mp ha).2)
      have hb' := step_some_iff.mp (of_decide_eq_true (List.mem_filter.mp hb).2)
      have src : ∀ {c}, winner net t s c = some k →
          ∃ p, net.prev k c = some p ∧ s p = some k ∧ leaves net t s p = true := by
        intro c hc
        obtain ⟨_, _, p, hn, hp⟩ := winner_spec hc
        exact ⟨p, (net.prev_iff k p c).mpr hn, hp, by simp [leaves, hp, hn, hc]⟩
      simp only [back] at hab
      rcases ha' with hwa | ⟨hsa, hla⟩ <;> rcases hb' with hwb | ⟨hsb, hlb⟩
      · obtain ⟨p, hpa, _⟩ := src hwa
        obtain ⟨q, hqb, _⟩ := src hwb
        simp only [hwa, hwb, ↓reduceIte, hpa, hqb, Option.getD_some] at hab
        subst hab
        have h1 := (net.prev_iff k p a).mp hpa
        have h2 := (net.prev_iff k p b).mp hqb
        rw [h1] at h2
        exact Option.some.inj h2
      · obtain ⟨p, hpa, _, hlp⟩ := src hwa
        have hwb : winner net t s b ≠ some k := by
          intro h
          rw [winner_vacant h] at hsb
          cases hsb
        simp only [hwa, ↓reduceIte, hpa, Option.getD_some, hwb] at hab
        subst hab
        rw [hlp] at hlb
        cases hlb
      · obtain ⟨p, hpb, _, hlp⟩ := src hwb
        have hwa : winner net t s a ≠ some k := by
          intro h
          rw [winner_vacant h] at hsa
          cases hsa
        simp only [hwb, ↓reduceIte, hpb, Option.getD_some, hwa] at hab
        subst hab
        rw [hlp] at hla
        cases hla
      · have hwa : winner net t s a ≠ some k := by
          intro h
          rw [winner_vacant h] at hsa
          cases hsa
        have hwb : winner net t s b ≠ some k := by
          intro h
          rw [winner_vacant h] at hsb
          cases hsb
        simpa [hwa, hwb] using hab
    · intro a ha
      refine List.mem_filter.mpr ⟨hall _, decide_eq_true ?_⟩
      have ha' := step_some_iff.mp (of_decide_eq_true (List.mem_filter.mp ha).2)
      rcases ha' with hwa | ⟨hsa, _⟩
      · obtain ⟨_, _, p, hn, hp⟩ := winner_spec hwa
        simp [back, hwa, (net.prev_iff k p a).mpr hn, hp]
      · have hwa : winner net t s a ≠ some k := by
          intro h
          rw [winner_vacant h] at hsa
          cases hsa
        simp [back, hwa, hsa]
  · -- before → after: a leaver goes to its target, a stayer stays
    let fwd : Cell → Cell := fun c => if leaves net t s c then (net.next k c).getD c else c
    refine length_le_of_injOn _ _ (hnd.sublist List.filter_sublist) fwd ?_ ?_
    · intro a ha b hb hab
      have hsa := of_decide_eq_true (List.mem_filter.mp ha).2
      have hsb := of_decide_eq_true (List.mem_filter.mp hb).2
      simp only [fwd] at hab
      cases hla : leaves net t s a <;> cases hlb : leaves net t s b
      · simpa [hla, hlb] using hab
      · obtain ⟨d, hd, hwd⟩ := leaves_target hx hsb hlb
        simp only [hla, hlb, Bool.false_eq_true, ↓reduceIte, hd, Option.getD_some] at hab
        subst hab
        rw [winner_vacant hwd] at hsa
        cases hsa
      · obtain ⟨d, hd, hwd⟩ := leaves_target hx hsa hla
        simp only [hla, hlb, Bool.false_eq_true, ↓reduceIte, hd, Option.getD_some] at hab
        subst hab
        rw [winner_vacant hwd] at hsb
        cases hsb
      · obtain ⟨d, hd, _⟩ := leaves_target hx hsa hla
        obtain ⟨e, he, _⟩ := leaves_target hx hsb hlb
        simp only [hla, hlb, ↓reduceIte, hd, he, Option.getD_some] at hab
        subst hab
        have h1 := (net.prev_iff k a d).mpr hd
        have h2 := (net.prev_iff k b d).mpr he
        rw [h1] at h2
        exact Option.some.inj h2
    · intro a ha
      have hsa := of_decide_eq_true (List.mem_filter.mp ha).2
      refine List.mem_filter.mpr ⟨hall _, decide_eq_true (step_some_iff.mpr ?_)⟩
      cases hla : leaves net t s a with
      | true =>
        obtain ⟨d, hd, hwd⟩ := leaves_target hx hsa hla
        simp [fwd, hla, hd, hwd]
      | false =>
        right
        simp [fwd, hla, hsa]

theorem valid_step (hr : RouteClosed net) (hx : Valid net s) : Valid net (step net t s) := by
  intro c k hc
  rcases step_some_iff.mp hc with hw | ⟨hs, _⟩
  · obtain ⟨_, _, p, hn, _⟩ := winner_spec hw
    exact hr k p c hn
  · exact hx c k hs

theorem valid_run (hr : RouteClosed net) (hx : Valid net s) (t : Nat) : Valid net (run net s t) := by
  induction t with
  | zero => exact hx
  | succ t ih => exact valid_step hr ih

/-- On a route-closed net, a valid state keeps its number of cars of each
class for ever. -/
theorem count_run (cells : List Cell) (hnd : cells.Nodup) (hall : ∀ c, c ∈ cells)
    (hr : RouteClosed net) (hx : Valid net s) (k : Class) (t : Nat) :
    count cells (run net s t) k = count cells s k := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run, count_step cells hnd hall (valid_run hr hx t), ih]

end BML.Net
