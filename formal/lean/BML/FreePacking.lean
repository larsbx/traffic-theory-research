import BML.FiniteSums

/-!
Cyclic weighted packing for the diagonal classes in the finite-torus free-flow
bound.  The argument is independent of the torus geometry: its inputs are the
five local capacity and direction-exclusion inequalities.
-/
namespace BML

private def prefixSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => prefixSum f n + f n

private theorem sumFin_eq_prefixSum (n : Nat) (f : Nat → Nat) :
    sumFin n (fun i => f i.val) = prefixSum f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [sumFin, List.finRange_succ_last, List.map_append,
        List.sum_append, List.map_map, Function.comp_def, Fin.val_castSucc,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Fin.val_last, Nat.add_zero, prefixSum] using congrArg (· + f n) ih

private theorem prefixSum_triples (f : Nat → Nat) (M k : Nat)
    (h : ∀ j, f j + f (j + 1) + f (j + 2) ≤ 2 * M) :
    prefixSum f (3 * k) ≤ (2 * M) * k := by
  induction k with
  | zero => simp [prefixSum]
  | succ k ih =>
      have ht := h (3 * k)
      have he : 3 * (k + 1) = 3 * k + 2 + 1 := by omega
      rw [he]
      simp only [prefixSum]
      rw [Nat.mul_succ]
      omega

/-- An empty last entry lets the local triple cap round down exactly. -/
private theorem prefixSum_empty_last_bound (n : Nat) (_hn : 0 < n)
    (f : Nat → Nat) (M : Nat) (hcap : ∀ j, f j ≤ M)
    (htriple : ∀ j, f j + f (j + 1) + f (j + 2) ≤ 2 * M)
    (hlast : f (n - 1) = 0) :
    prefixSum f n ≤ M * ((2 * n) / 3) := by
  have hbase := prefixSum_triples f M (n / 3) htriple
  have hrem : n % 3 < 3 := Nat.mod_lt _ (by omega)
  have hdiv : n % 3 + 3 * (n / 3) = n := Nat.mod_add_div n 3
  have cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases cases with hzero | hone | htwo
  · have hn' : n = 3 * (n / 3) := by omega
    have hr : (2 * n) / 3 = 2 * (n / 3) := by omega
    calc
      prefixSum f n = prefixSum f (3 * (n / 3)) := congrArg (prefixSum f) hn'
      _ ≤ (2 * M) * (n / 3) := hbase
      _ = M * ((2 * n) / 3) := by
        rw [hr]
        simp only [Nat.mul_assoc, Nat.mul_comm]
  · have hn' : n = 3 * (n / 3) + 1 := by omega
    have hr : (2 * n) / 3 = 2 * (n / 3) := by omega
    have hz : f (3 * (n / 3)) = 0 := by
      have hi : n - 1 = 3 * (n / 3) := by omega
      rwa [hi] at hlast
    calc
      prefixSum f n = prefixSum f (3 * (n / 3) + 1) := congrArg (prefixSum f) hn'
      _ = prefixSum f (3 * (n / 3)) := by rw [prefixSum, hz, Nat.add_zero]
      _ ≤ (2 * M) * (n / 3) := hbase
      _ = M * ((2 * n) / 3) := by
        rw [hr]
        simp only [Nat.mul_assoc, Nat.mul_comm]
  · have hn' : n = 3 * (n / 3) + 1 + 1 := by omega
    have hr : (2 * n) / 3 = 2 * (n / 3) + 1 := by omega
    have hz : f (3 * (n / 3) + 1) = 0 := by
      have hi : n - 1 = 3 * (n / 3) + 1 := by omega
      rwa [hi] at hlast
    have hp := hcap (3 * (n / 3))
    calc
      prefixSum f n = prefixSum f (3 * (n / 3) + 1 + 1) := congrArg (prefixSum f) hn'
      _ = prefixSum f (3 * (n / 3)) + f (3 * (n / 3)) := by
        rw [prefixSum, prefixSum, hz, Nat.add_zero]
      _ ≤ (2 * M) * (n / 3) + M := by omega
      _ = M * ((2 * n) / 3) := by
        rw [hr, Nat.mul_add, Nat.mul_one]
        simp only [Nat.mul_assoc, Nat.mul_comm]

/-- Each three consecutive classes carry at most two class capacities. -/
theorem cyclic_weighted_packing_triple (g : Nat) (hg : 0 < g) (M : Nat)
    (a b : Fin g → Nat)
    (hcap : ∀ i, a i + b i ≤ M)
    (ha : ∀ i, a i + a (cyclicNext g hg i) ≤ M)
    (hb : ∀ i, b i + b (cyclicNext g hg i) ≤ M)
    (cross0 : ∀ i, a i = 0 ∨ b i = 0)
    (cross1 : ∀ i, a i = 0 ∨ b (cyclicNext g hg i) = 0)
    (i : Fin g) :
    (a i + b i) + (a (cyclicNext g hg i) + b (cyclicNext g hg i)) +
      (a (cyclicNext g hg (cyclicNext g hg i)) +
        b (cyclicNext g hg (cyclicNext g hg i))) ≤ 2 * M := by
  by_cases hi : a i = 0
  · by_cases hj : a (cyclicNext g hg i) = 0
    · have hh := hb i
      have hc := hcap (cyclicNext g hg (cyclicNext g hg i))
      omega
    · have hz := cross0 (cyclicNext g hg i)
      have hz' := cross1 (cyclicNext g hg i)
      have hh := ha (cyclicNext g hg i)
      have hc := hcap i
      omega
  · have hz := cross0 i
    have hz' := cross1 i
    have hh := ha i
    have hc := hcap (cyclicNext g hg (cyclicNext g hg i))
    omega

private theorem cyclic_weighted_packing_empty (g : Nat) (hg : 0 < g) (M : Nat)
    (a b : Fin g → Nat)
    (hcap : ∀ i, a i + b i ≤ M)
    (ha : ∀ i, a i + a (cyclicNext g hg i) ≤ M)
    (hb : ∀ i, b i + b (cyclicNext g hg i) ≤ M)
    (cross0 : ∀ i, a i = 0 ∨ b i = 0)
    (cross1 : ∀ i, a i = 0 ∨ b (cyclicNext g hg i) = 0)
    (z : Fin g) (hz : a z + b z = 0) :
    sumFin g (fun i => a i + b i) ≤ M * ((2 * g) / 3) := by
  let next := cyclicNext g hg
  let f := fun k => a (iterate next k (next z)) + b (iterate next k (next z))
  have hlast : f (g - 1) = 0 := by
    have he : iterate next (g - 1) (next z) = z := by
      calc
        iterate next (g - 1) (next z) = iterate next (1 + (g - 1)) z :=
          (iterate_add next z 1 (g - 1)).symm
        _ = iterate next g z := by congr 1; omega
        _ = z := iterate_cyclicNext_period g hg z
    simpa only [f, he] using hz
  have htriple : ∀ j, f j + f (j + 1) + f (j + 2) ≤ 2 * M := by
    intro j
    exact cyclic_weighted_packing_triple g hg M a b hcap ha hb cross0 cross1
      (iterate next j (next z))
  have hbound := prefixSum_empty_last_bound g hg f M
    (fun j => hcap (iterate next j (next z))) htriple hlast
  have hs : sumFin g (fun i => a i + b i) = prefixSum f g := by
    calc
      _ = sumFin g (fun i => f i.val) :=
        (sumFin_rotation g hg (fun i => a i + b i) (next z)).symm
      _ = prefixSum f g := sumFin_eq_prefixSum g f
  rwa [hs]

/-- Without an empty class, the direction exclusions force a single species. -/
theorem cyclic_weighted_packing_no_empty (g : Nat) (hg : 0 < g)
    (a b : Fin g → Nat)
    (cross0 : ∀ i, a i = 0 ∨ b i = 0)
    (cross1 : ∀ i, a i = 0 ∨ b (cyclicNext g hg i) = 0)
    (hne : ∀ i, a i + b i ≠ 0) :
    (∀ i, a i = 0) ∨ (∀ i, b i = 0) := by
  by_cases hall : ∀ i, a i = 0
  · exact Or.inl hall
  · apply Or.inr
    have hex : ∃ i, a i ≠ 0 := Classical.not_forall.mp hall
    obtain ⟨i, hi⟩ := hex
    have hpos : ∀ k, a (iterate (cyclicNext g hg) k i) ≠ 0 := by
      intro k
      induction k with
      | zero => exact hi
      | succ k ih =>
          have hb0 := (cross1 (iterate (cyclicNext g hg) k i)).resolve_left ih
          have hnonempty := hne (cyclicNext g hg (iterate (cyclicNext g hg) k i))
          change a (cyclicNext g hg (iterate (cyclicNext g hg) k i)) ≠ 0
          omega
    intro j
    obtain ⟨k, hk⟩ := cyclicNext_reaches g hg i j
    have hj : a j ≠ 0 := by simpa only [hk] using hpos k
    exact (cross0 j).resolve_left hj

/-- Sharp weighted packing bound for a cyclic set of at least two classes. -/
theorem cyclic_weighted_packing_bound (g : Nat) (hg : 0 < g) (hg2 : 2 ≤ g)
    (M : Nat) (a b : Fin g → Nat)
    (hcap : ∀ i, a i + b i ≤ M)
    (ha : ∀ i, a i + a (cyclicNext g hg i) ≤ M)
    (hb : ∀ i, b i + b (cyclicNext g hg i) ≤ M)
    (cross0 : ∀ i, a i = 0 ∨ b i = 0)
    (cross1 : ∀ i, a i = 0 ∨ b (cyclicNext g hg i) = 0) :
    sumFin g (fun i => a i + b i) ≤ M * ((2 * g) / 3) := by
  by_cases hempty : ∃ z, a z + b z = 0
  · obtain ⟨z, hz⟩ := hempty
    exact cyclic_weighted_packing_empty g hg M a b hcap ha hb cross0 cross1 z hz
  · have hne : ∀ i, a i + b i ≠ 0 := by
      intro i hi
      exact hempty ⟨i, hi⟩
    have hpairs : ∀ i, (a i + b i) +
        (a (cyclicNext g hg i) + b (cyclicNext g hg i)) ≤ M := by
      rcases cyclic_weighted_packing_no_empty g hg a b cross0 cross1 hne with h | h
      · intro i
        simpa only [h, Nat.zero_add] using hb i
      · intro i
        simpa only [h, Nat.add_zero] using ha i
    have hs := sumFin_twice_le_of_adjacent g hg M (fun i => a i + b i) hpairs
    have hround : g ≤ 2 * ((2 * g) / 3) := by omega
    have hmul := Nat.mul_le_mul_left M hround
    have hm : g * M ≤ 2 * (M * ((2 * g) / 3)) := by
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
    omega

end BML
