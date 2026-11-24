import Train.Finite

namespace BML.Train.Diagonals

/-- Two adjacent corrected classes are both empty. -/
def EmptyPair {N : Nat} (hn : 0<N) (O : Nat → Fin N → Prop) (t : Nat) (b : Fin N) : Prop :=
  ¬O t b ∧ ¬O t (cyclicNext N hn b)

/-- Support transport and release before an empty class force every adjacent
empty pair at the next time to have existed at the current time. -/
theorem emptyPair_backwards {N : Nat} (hn : 0<N) (O : Nat → Fin N → Prop)
    (forward : ∀ t x, O t x → O (t+1) x ∨ O (t+1) (cyclicPrev N hn x))
    (release : ∀ t x, O t x → ¬O t (cyclicNext N hn x) → O (t+1) x)
    (t : Nat) (b : Fin N) (hb : EmptyPair hn O (t+1) b) : EmptyPair hn O t b := by
  have h₁ : ¬O t (cyclicNext N hn b) := by
    intro h
    rcases forward t _ h with h | h
    · exact hb.2 h
    · exact hb.1 (by simpa only [cyclicPrev_next] using h)
  have h₀ : ¬O t b := by
    intro h
    exact hb.1 (release t _ h h₁)
  exact ⟨h₀,h₁⟩

theorem backwards_le {α : Type} (P : Nat → α → Prop)
    (step : ∀ t x, P (t+1) x → P t x) {s t : Nat} (hst : s≤t) (x : α) :
    P t x → P s x := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hst
  clear hst
  induction k with
  | zero => exact fun h => h
  | succ k ih =>
    intro h
    apply ih
    exact step (s+k) x h

/-- A nonempty descending family of subsets of a fixed finite list has a
point present at every time. No choice of a stabilization time is assumed. -/
theorem exists_persistent_of_list {α : Type} (P : Nat → α → Prop)
    (step : ∀ t x, P (t+1) x → P t x) (xs : List α)
    (nonempty : ∀ t, ∃ x, x∈xs ∧ P t x) :
    ∃ x, x∈xs ∧ ∀ t, P t x := by
  classical
  induction xs with
  | nil =>
    obtain ⟨x,hx,_⟩ := nonempty 0
    cases hx
  | cons a xs ih =>
    by_cases ha : ∀t, P t a
    · exact ⟨a,by simp,ha⟩
    · obtain ⟨T,hT⟩ := Classical.not_forall.mp ha
      have tail_nonempty : ∀t, ∃x, x∈xs ∧ P t x := by
        intro t
        obtain ⟨x,hx,hp⟩ := nonempty (T+t)
        have hxa : x≠a := by
          intro he
          subst x
          exact hT (backwards_le P step (by omega) a hp)
        refine ⟨x, ?_, backwards_le P step (by omega) x hp⟩
        simpa [hxa] using hx
      obtain ⟨x,hx,hp⟩ := ih tail_nonempty
      exact ⟨x,by simp [hx],hp⟩

theorem exists_persistent_emptyPair {N : Nat} (hn : 0<N) (O : Nat → Fin N → Prop)
    (step : ∀ t b, EmptyPair hn O (t+1) b → EmptyPair hn O t b)
    (nonempty : ∀t, ∃b, EmptyPair hn O t b) :
    ∃b, ∀t, EmptyPair hn O t b := by
  have hall : ∀t, ∃b, b∈List.finRange N ∧ EmptyPair hn O t b := by
    intro t
    obtain ⟨b,hb⟩ := nonempty t
    exact ⟨b,by simp,hb⟩
  obtain ⟨b,_,hb⟩ := exists_persistent_of_list (EmptyPair hn O) step (List.finRange N) hall
  exact ⟨b,hb⟩

/-- A sparse list of occupied classes leaves two adjacent classes empty.
Duplicate entries are allowed; the empty list is included. -/
theorem exists_emptyPair_of_sparse_list {N : Nat} (hn : 0<N) (xs : List (Fin N))
    (hsize : 2*xs.length<N) : ∃b, b∉xs ∧ cyclicNext N hn b∉xs := by
  classical
  by_cases hb : ∃b, b∉xs ∧ cyclicNext N hn b∉xs
  · exact hb
  · have hall : ∀x, x∈xs ∨ cyclicNext N hn x∈xs := by
      intro x
      by_cases hx : x∈xs
      · exact Or.inl hx
      · by_cases hnxt : cyclicNext N hn x∈xs
        · exact Or.inr hnxt
        · exact False.elim (hb ⟨x,hx,hnxt⟩)
    have hcover : List.finRange N ⊆ xs ++ xs.map (cyclicPrev N hn) := by
      intro x _
      rcases hall x with hx | hx
      · exact List.mem_append_left _ hx
      · apply List.mem_append_right
        exact List.mem_map.mpr ⟨cyclicNext N hn x,hx,cyclicPrev_next N hn x⟩
    have hlength := (List.nodup_finRange N).length_le_of_subset hcover
    simp only [List.length_finRange, List.length_append, List.length_map] at hlength
    omega

/-- Clockwise distance from a fixed cut, represented as a natural number. -/
def cutRank {N : Nat} (a x : Fin N) : Nat :=
  if a.val≤x.val then x.val-a.val else N+x.val-a.val

theorem cutRank_prev {N : Nat} (hn : 0<N) (a x : Fin N)
    (hx : x≠a) (hp : cyclicPrev N hn x≠a) :
    cutRank a (cyclicPrev N hn x) + 1 = cutRank a x := by
  have ha := a.isLt
  have hxl := x.isLt
  have hxn : x.val≠a.val := fun h => hx (Fin.ext h)
  have hpn : (cyclicPrev N hn x).val≠a.val := fun h => hp (Fin.ext h)
  by_cases hz : x.val=0
  · have hv : (cyclicPrev N hn x).val=N-1 := by simp [cyclicPrev,hz]
    simp only [cutRank,hv]
    split <;> split <;> omega
  · have hv : (cyclicPrev N hn x).val=x.val-1 := by simp [cyclicPrev,hz]
    simp only [cutRank,hv]
    split <;> split <;> omega

/-- Every sequence of natural numbers has an attained least value. -/
theorem exists_min_value (f : Nat → Nat) : ∃T, ∀t, f T≤f t := by
  have aux : ∀n, (∃t, f t=n) → ∃T, ∀t, f T≤f t := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      by_cases hlt : ∃t, f t<n
      · obtain ⟨t,ht⟩ := hlt
        exact ih (f t) ht ⟨t,rfl⟩
      · obtain ⟨T,hT⟩ := hn
        refine ⟨T, ?_⟩
        intro t
        have hnot : ¬f t<n := fun ht => hlt ⟨t,ht⟩
        omega
  exact aux (f 0) ⟨0,rfl⟩

theorem decreasing_le (f : Nat → Nat) (step : ∀t, f (t+1)≤f t)
    {s t : Nat} (hst : s≤t) : f t≤f s := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hst
  clear hst
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih => exact Nat.le_trans (step (s+k)) ih

theorem decreasing_eventually_constant (f : Nat → Nat) (step : ∀t, f (t+1)≤f t) :
    ∃T, ∀t, T≤t → f t=f T := by
  obtain ⟨T,hT⟩ := exists_min_value f
  refine ⟨T, ?_⟩
  intro t ht
  exact Nat.le_antisymm (decreasing_le f step ht) (hT t)

/-- A trace that can only stay or move one predecessor step cannot keep
moving backwards while avoiding a fixed point of the finite cycle. -/
theorem avoiding_trace_eventually_stable {N : Nat} (hn : 0<N)
    (a : Fin N) (Y : Nat → Fin N)
    (avoid : ∀t, Y t≠a)
    (step : ∀t, Y (t+1)=Y t ∨ Y (t+1)=cyclicPrev N hn (Y t)) :
    ∃T, ∀t, T≤t → Y (t+1)=Y t := by
  let f := fun t => cutRank a (Y t)
  have hmono : ∀t, f (t+1)≤f t := by
    intro t
    rcases step t with he | he
    · simp only [f,he]
      exact Nat.le_refl _
    · have hp : cyclicPrev N hn (Y t)≠a := by simpa only [←he] using avoid (t+1)
      have hr := cutRank_prev hn a (Y t) (avoid t) hp
      change cutRank a (Y (t+1))≤cutRank a (Y t)
      rw [he]
      omega
  obtain ⟨T,hT⟩ := decreasing_eventually_constant f hmono
  refine ⟨T, ?_⟩
  intro t ht
  rcases step t with he | he
  · exact he
  · have hp : cyclicPrev N hn (Y t)≠a := by simpa only [←he] using avoid (t+1)
    have hr := cutRank_prev hn a (Y t) (avoid t) hp
    have h₀ := hT t ht
    have h₁ := hT (t+1) (by omega)
    simp only [f,he] at h₁ h₀
    omega

/-- Finitely many eventual properties have a common starting time. -/
theorem finite_eventually_all {ι : Type} (xs : List ι) (P : Nat → ι → Prop)
    (each : ∀i, i∈xs → ∃T, ∀t, T≤t → P t i) :
    ∃T, ∀t, T≤t → ∀i, i∈xs → P t i := by
  induction xs with
  | nil => exact ⟨0,by simp⟩
  | cons a xs ih =>
    obtain ⟨A,hA⟩ := each a (by simp)
    have htail : ∀i, i∈xs → ∃T, ∀t, T≤t → P t i := by
      intro i hi
      exact each i (by simp [hi])
    obtain ⟨B,hB⟩ := ih htail
    refine ⟨max A B, ?_⟩
    intro t ht i hi
    rcases List.mem_cons.mp hi with hi | hi
    · subst i
      exact hA t (by omega)
    · exact hB t (by omega) i hi

/-- Counting saturation at the boundary `2m ≤ N`: if no two adjacent classes
are both empty, then occupied and empty classes alternate. Duplicate entries
are allowed; a class occupied together with its successor would be covered
twice, leaving a cover of all `N` classes by only `2m-1` entries. -/
theorem saturated_alternating {N : Nat} (hn : 0<N) (xs : List (Fin N))
    (hsize : 2*xs.length≤N) (hcover : ∀b, b∈xs ∨ cyclicNext N hn b∈xs) :
    ∀b, b∈xs → cyclicNext N hn b∉xs := by
  intro b hb hnext
  have hsub : List.finRange N ⊆ xs.erase b ++ xs.map (cyclicPrev N hn) := by
    intro x _
    have hprev : ∀y, cyclicNext N hn y∈xs → y∈xs.map (cyclicPrev N hn) :=
      fun y hy => List.mem_map.mpr ⟨cyclicNext N hn y,hy,cyclicPrev_next N hn y⟩
    rcases hcover x with hx | hx
    · by_cases hxb : x=b
      · exact List.mem_append_right _ (hprev x (hxb ▸ hnext))
      · exact List.mem_append_left _ ((List.mem_erase_of_ne hxb).mpr hx)
    · exact List.mem_append_right _ (hprev x hx)
  have hlength := (List.nodup_finRange N).length_le_of_subset hsub
  have hpos := List.length_pos_of_mem hb
  simp only [List.length_finRange, List.length_append, List.length_map,
    List.length_erase_of_mem hb] at hlength
  omega

/-- A saturated time at the boundary `2m ≤ N` is followed by a saturated time
at which no label has changed its corrected class. -/
theorem saturated_step {ι : Type} (N : Nat) (hn : 0<N)
    (xs : List ι) (Y : Nat → ι → Fin N)
    (hstep : ∀t i, i∈xs →
      Y (t+1) i=Y t i ∨ Y (t+1) i=cyclicPrev N hn (Y t i))
    (hrelease : ∀t b, (∃i, i∈xs ∧ Y t i=b) →
      (∀i, i∈xs → Y t i≠cyclicNext N hn b) → ∃i, i∈xs ∧ Y (t+1) i=b)
    (half : 2*xs.length≤N) (t : Nat)
    (hsat : ∀b, ¬EmptyPair hn (fun t b => ∃i, i∈xs ∧ Y t i=b) t b) :
    (∀b, ¬EmptyPair hn (fun t b => ∃i, i∈xs ∧ Y t i=b) (t+1) b) ∧
      ∀i, i∈xs → Y (t+1) i=Y t i := by
  classical
  let O := fun t b => ∃i, i∈xs ∧ Y t i=b
  have halt : ∀s, (∀b, ¬EmptyPair hn O s b) →
      ∀b, O s b → ¬O s (cyclicNext N hn b) := by
    intro s hs b hb hnext
    refine saturated_alternating hn (xs.map (Y s)) (by simpa using half) ?_ b
      (List.mem_map.mpr hb) (List.mem_map.mpr hnext)
    intro c
    by_cases hc : O s c
    · exact Or.inl (List.mem_map.mpr hc)
    · by_cases hc' : O s (cyclicNext N hn c)
      · exact Or.inr (List.mem_map.mpr hc')
      · exact False.elim (hs c ⟨hc,hc'⟩)
  have hkeep : ∀b, O t b → O (t+1) b := fun b hb =>
    hrelease t b hb fun i hi he => halt t hsat b hb ⟨i,hi,he⟩
  have hsat' : ∀b, ¬EmptyPair hn O (t+1) b := fun b hb =>
    hsat b ⟨fun h => hb.1 (hkeep b h), fun h => hb.2 (hkeep _ h)⟩
  refine ⟨hsat', ?_⟩
  intro i hi
  rcases hstep t i hi with he | he
  · exact he
  · have hnext : O (t+1) (cyclicNext N hn (cyclicPrev N hn (Y t i))) := by
      rw [cyclicNext_prev]
      exact hkeep _ ⟨i,hi,rfl⟩
    exact False.elim (halt (t+1) hsat' _ ⟨i,hi,he⟩ hnext)

/-- The cyclic combinatorial core of the Austin--Benjamini argument, including
the boundary `2m = N`. Either an adjacent empty pair exists at every time, and
a permanent cut ranks the labels; or some time is saturated, and from then on
occupied and empty classes alternate and every label keeps its class.
Labels may share a corrected class, and the label list may be empty. -/
theorem half_eventual_stable {ι : Type} (N : Nat) (hn : 0<N)
    (xs : List ι) (Y : Nat → ι → Fin N)
    (hstep : ∀t i, i∈xs →
      Y (t+1) i=Y t i ∨ Y (t+1) i=cyclicPrev N hn (Y t i))
    (hrelease : ∀t b, (∃i, i∈xs ∧ Y t i=b) →
      (∀i, i∈xs → Y t i≠cyclicNext N hn b) → ∃i, i∈xs ∧ Y (t+1) i=b)
    (half : 2*xs.length≤N) :
    ∃T, ∀t, T≤t → ∀i, i∈xs → Y (t+1) i=Y t i := by
  classical
  let O := fun t b => ∃i, i∈xs ∧ Y t i=b
  by_cases hex : ∀t, ∃b, EmptyPair hn O t b
  · have hforward : ∀t b, O t b → O (t+1) b ∨ O (t+1) (cyclicPrev N hn b) := by
      intro t b hb
      obtain ⟨i,hi,hb⟩ := hb
      rcases hstep t i hi with he | he
      · exact Or.inl ⟨i,hi,he.trans hb⟩
      · exact Or.inr ⟨i,hi,he.trans (congrArg (cyclicPrev N hn) hb)⟩
    have hrel : ∀t b, O t b → ¬O t (cyclicNext N hn b) → O (t+1) b := by
      intro t b hb hempty
      apply hrelease t b hb
      intro i hi he
      exact hempty ⟨i,hi,he⟩
    obtain ⟨b,hb⟩ := exists_persistent_emptyPair hn O
      (emptyPair_backwards hn O hforward hrel) hex
    apply finite_eventually_all xs (fun t i => Y (t+1) i=Y t i)
    intro i hi
    apply avoiding_trace_eventually_stable hn b (fun t => Y t i)
    · intro t he
      exact (hb t).1 ⟨i,hi,he⟩
    · exact fun t => hstep t i hi
  · obtain ⟨T,hT⟩ := Classical.not_forall.mp hex
    have hsat : ∀k, ∀b, ¬EmptyPair hn O (T+k) b := by
      intro k
      induction k with
      | zero => exact fun b hb => hT ⟨b,hb⟩
      | succ k ih => exact (saturated_step N hn xs Y hstep hrelease half (T+k) ih).1
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le ht
    exact (saturated_step N hn xs Y hstep hrelease half (T+k) (hsat k)).2

/-- The strict case `2m < N` of `half_eventual_stable`. -/
theorem sparse_eventual_stable {ι : Type} (N : Nat) (hn : 0<N)
    (xs : List ι) (Y : Nat → ι → Fin N)
    (hstep : ∀t i, i∈xs →
      Y (t+1) i=Y t i ∨ Y (t+1) i=cyclicPrev N hn (Y t i))
    (hrelease : ∀t b, (∃i, i∈xs ∧ Y t i=b) →
      (∀i, i∈xs → Y t i≠cyclicNext N hn b) → ∃i, i∈xs ∧ Y (t+1) i=b)
    (sparse : 2*xs.length<N) :
    ∃T, ∀t, T≤t → ∀i, i∈xs → Y (t+1) i=Y t i :=
  half_eventual_stable N hn xs Y hstep hrelease (Nat.le_of_lt sparse)

end BML.Train.Diagonals
