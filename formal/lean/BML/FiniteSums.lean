import BML.Ring

/-!
Elementary natural-number sums over the actual finite cyclic coordinates.
These helpers use duplicate-free lists and introduce no finite-set library.
-/
namespace BML

def sumFin (n : Nat) (f : Fin n → Nat) : Nat :=
  ((List.finRange n).map f).sum

theorem list_sum_map_add (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_assoc, Nat.add_left_comm]

theorem list_sum_map_mul_left (xs : List α) (c : Nat) (f : α → Nat) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.mul_add]

theorem list_sum_map_le (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem sumFin_congr (n : Nat) (f g : Fin n → Nat) (h : ∀ i, f i = g i) :
    sumFin n f = sumFin n g := by
  congr 1
  exact funext h

theorem sumFin_add (n : Nat) (f g : Fin n → Nat) :
    sumFin n (fun i => f i + g i) = sumFin n f + sumFin n g :=
  list_sum_map_add _ _ _

theorem sumFin_mul_left (n c : Nat) (f : Fin n → Nat) :
    sumFin n (fun i => c * f i) = c * sumFin n f :=
  list_sum_map_mul_left _ _ _

theorem list_sum_map_swap (xs : List α) (ys : List β) (f : α → β → Nat) :
    (xs.map (fun x => (ys.map (f x)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil => simp [List.map_const', List.sum_replicate_nat]
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [list_sum_map_add, ih]

theorem sumFin_swap (m n : Nat) (f : Fin m → Fin n → Nat) :
    sumFin m (fun i => sumFin n (f i)) =
      sumFin n (fun j => sumFin m (fun i => f i j)) :=
  list_sum_map_swap _ _ _

theorem sumFin_le (n : Nat) (f g : Fin n → Nat) (h : ∀ i, f i ≤ g i) :
    sumFin n f ≤ sumFin n g :=
  list_sum_map_le _ _ _ (fun i _ => h i)

@[simp] theorem sumFin_const (n c : Nat) : sumFin n (fun _ => c) = n * c := by
  simp [sumFin, List.map_const', List.sum_replicate_nat]

theorem sumFin_reindex (n : Nat) (f : Fin n → Nat) (e : Fin n → Fin n)
    (hinj : Function.Injective e) (hsurj : Function.Surjective e) :
    sumFin n (fun i => f (e i)) = sumFin n f := by
  have hn : ((List.finRange n).map e).Nodup :=
    List.Pairwise.map e (fun _ _ hne he => hne (hinj he)) (List.nodup_finRange n)
  have hp : ((List.finRange n).map e).Perm (List.finRange n) := by
    apply (List.perm_ext_iff_of_nodup hn (List.nodup_finRange n)).mpr
    intro i
    constructor
    · intro _
      exact List.mem_finRange i
    · intro _
      obtain ⟨j, rfl⟩ := hsurj i
      exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
  simpa only [sumFin, List.map_map, Function.comp_def] using (hp.map f).sum_nat

theorem sumFin_next (n : Nat) (hn : 0 < n) (f : Fin n → Nat) :
    sumFin n (fun i => f (cyclicNext n hn i)) = sumFin n f := by
  apply sumFin_reindex
  · intro i j he
    have hi := congrArg (cyclicPrev n hn) he
    simpa only [cyclicPrev_next] using hi
  · intro i
    exact ⟨cyclicPrev n hn i, cyclicNext_prev n hn i⟩

theorem sumFin_iterate_next (n : Nat) (hn : 0 < n) (k : Nat) (f : Fin n → Nat) :
    sumFin n (fun i => f (iterate (cyclicNext n hn) k i)) = sumFin n f := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
      change sumFin n (fun i => (fun j => f (cyclicNext n hn j))
        (iterate (cyclicNext n hn) k i)) = sumFin n f
      exact (ih (fun j => f (cyclicNext n hn j))).trans (sumFin_next n hn f)

/-- Reading a whole cyclic coordinate from any starting point preserves its sum. -/
theorem sumFin_rotation (n : Nat) (hn : 0 < n) (f : Fin n → Nat) (start : Fin n) :
    sumFin n (fun i => f (iterate (cyclicNext n hn) i.val start)) = sumFin n f := by
  have he : ∀ i : Fin n,
      iterate (cyclicNext n hn) i.val start =
        iterate (cyclicNext n hn) start.val i := by
    intro i
    apply Fin.ext
    simp only [iterate_cyclicNext_val, Nat.add_comm]
  calc
    _ = sumFin n (fun i => f (iterate (cyclicNext n hn) start.val i)) :=
      sumFin_congr _ _ _ (fun i => congrArg f (he i))
    _ = sumFin n f := sumFin_iterate_next n hn start.val f

/-- Double-counting cyclic adjacent pairs, including the one-cell ring. -/
theorem sumFin_twice_le_of_adjacent (n : Nat) (hn : 0 < n) (M : Nat)
    (f : Fin n → Nat) (h : ∀ i, f i + f (cyclicNext n hn i) ≤ M) :
    2 * sumFin n f ≤ n * M := by
  have hs := sumFin_le n (fun i => f i + f (cyclicNext n hn i)) (fun _ => M) h
  rw [sumFin_add, sumFin_next, sumFin_const] at hs
  omega

theorem sumFin_le_half_of_adjacent (n : Nat) (hn : 0 < n) (f : Fin n → Nat)
    (h : ∀ i, f i + f (cyclicNext n hn i) ≤ 1) :
    sumFin n f ≤ n / 2 := by
  have hs := sumFin_twice_le_of_adjacent n hn 1 f h
  omega

end BML
