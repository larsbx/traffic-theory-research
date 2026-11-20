import BML.Kernel

/-!
Finite closed-carrier cycle extraction. The carrier may contain duplicates;
the positive period is bounded by its supplied length. The selected period is
minimal at its starting point, so the list of cycle vertices has no duplicates.
-/
namespace BML

/-- Every point of an orbit stays in a carrier that is closed under its successor. -/
theorem iterate_mem_of_closed (f : α → α) (carrier : List α)
    (hclosed : ∀ p, p ∈ carrier → f p ∈ carrier)
    (p : α) (hp : p ∈ carrier) (t : Nat) : iterate f t p ∈ carrier := by
  induction t with
  | zero => exact hp
  | succ t ih => exact hclosed _ ih

/-- Pigeonhole principle for a finite orbit prefix in a supplied carrier. -/
theorem orbit_prefix_repeats (f : α → α) (carrier : List α) (p : α)
    (members : ∀ t ≤ carrier.length, iterate f t p ∈ carrier) :
    ∃ i j, i < j ∧ j ≤ carrier.length ∧ iterate f i p = iterate f j p := by
  classical
  apply Classical.byContradiction
  intro hnone
  let orbit := List.ofFn (fun i : Fin (carrier.length + 1) => iterate f i.val p)
  have hsub : orbit ⊆ carrier := by
    intro x hx
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hx
    rw [← hi]
    exact members i.val (by have := i.isLt; omega)
  have hnodup : orbit.Nodup := by
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j hi hj heq
    have hi' : i < carrier.length + 1 := by simpa [orbit] using hi
    have hj' : j < carrier.length + 1 := by simpa [orbit] using hj
    have he : iterate f i p = iterate f j p := by simpa only [orbit, List.getElem_ofFn] using heq
    by_cases hij : i < j
    · exact False.elim (hnone ⟨i, j, hij, by omega, he⟩)
    · by_cases hji : j < i
      · exact False.elim (hnone ⟨j, i, hji, by omega, he.symm⟩)
      · omega
  have hlen := hnodup.length_le_of_subset hsub
  simp only [orbit, List.length_ofFn] at hlen
  omega

/-- A forward orbit in a finite closed carrier must repeat. -/
theorem closed_orbit_repeats (f : α → α) (carrier : List α)
    (hclosed : ∀ p, p ∈ carrier → f p ∈ carrier)
    (p : α) (hp : p ∈ carrier) :
    ∃ i j, i < j ∧ j ≤ carrier.length ∧ iterate f i p = iterate f j p :=
  orbit_prefix_repeats f carrier p (fun t _ => iterate_mem_of_closed f carrier hclosed p hp t)

/-- A witnessed natural-number property has a least witness no larger than this one. -/
theorem exists_minimum_le (P : Nat → Prop) (n : Nat) (hn : P n) :
    ∃ k, P k ∧ k ≤ n ∧ ∀ j, j < k → ¬ P j := by
  classical
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hsmaller : ∃ j, j < n ∧ P j
    · obtain ⟨j, hj, hjP⟩ := hsmaller
      obtain ⟨k, hk, hkj, hminimal⟩ := ih j hj hjP
      exact ⟨k, hk, by omega, hminimal⟩
    · exact ⟨n, hn, Nat.le_refl n, fun j hj hjP => hsmaller ⟨j, hj, hjP⟩⟩

/-- A minimal positive return time gives a simple orbit, with no repeated vertex. -/
theorem minimal_period_nodup (f : α → α) (p : α) (k : Nat)
    (hreturn : iterate f k p = p)
    (hminimal : ∀ j, j < k → ¬ (0 < j ∧ iterate f j p = p)) :
    (List.ofFn (fun i : Fin k => iterate f i.val p)).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj heq
  have hi' : i < k := by simpa using hi
  have hj' : j < k := by simpa using hj
  have he : iterate f i p = iterate f j p := by simpa using heq
  have not_lt : ∀ a b, a < b → b < k → iterate f a p = iterate f b p → False := by
    intro a b hab hbk habEq
    have hshift := congrArg (iterate f (k - b)) habEq
    rw [← iterate_add, ← iterate_add] at hshift
    have hbkEq : b + (k - b) = k := by omega
    rw [hbkEq, hreturn] at hshift
    exact hminimal (a + (k - b)) (by omega) ⟨by omega, hshift⟩
  by_cases hij : i < j
  · exact False.elim (not_lt i j hij hj' he)
  · by_cases hji : j < i
    · exact False.elim (not_lt j i hji hi' he.symm)
    · omega

/-- Every endofunction on a nonempty finite closed carrier has a positive simple
cycle. Its period is bounded by the length of the supplied carrier. -/
theorem finite_closed_cycle (f : α → α) (carrier : List α)
    (hne : carrier ≠ []) (hclosed : ∀ p, p ∈ carrier → f p ∈ carrier) :
    ∃ p k, p ∈ carrier ∧ 0 < k ∧ k ≤ carrier.length ∧ iterate f k p = p ∧
      (List.ofFn (fun i : Fin k => iterate f i.val p)).Nodup := by
  obtain ⟨seed, hseed⟩ : ∃ p, p ∈ carrier := by
    cases carrier with
    | nil => exact False.elim (hne rfl)
    | cons p ps => exact ⟨p, List.mem_cons_self⟩
  obtain ⟨i, j, hij, hj, hrepeat⟩ := closed_orbit_repeats f carrier hclosed seed hseed
  let p := iterate f i seed
  have hp : p ∈ carrier := iterate_mem_of_closed f carrier hclosed seed hseed i
  have hreturn : iterate f (j - i) p = p := by
    change iterate f (j - i) (iterate f i seed) = iterate f i seed
    rw [← iterate_add]
    have heq : i + (j - i) = j := by omega
    rw [heq]
    exact hrepeat.symm
  obtain ⟨k, hk, hbound, hminimal⟩ :=
    exists_minimum_le (fun k => 0 < k ∧ iterate f k p = p) (j - i) ⟨by omega, hreturn⟩
  exact ⟨p, k, hp, hk.1, by omega, hk.2, minimal_period_nodup f p k hk.2 hminimal⟩

end BML
