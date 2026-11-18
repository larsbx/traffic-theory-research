import BML.Torus

namespace BML.Train

def occupiedPositions {w h : Nat} (s : Config (Position w h)) : List (Position w h) :=
  (positions w h).filter fun p => decide (s p ≠ .empty)

def population {w h : Nat} (s : Config (Position w h)) : Nat :=
  (occupiedPositions s).length

theorem mem_positions (p : Position w h) : p ∈ positions w h := by
  rcases p with ⟨x, y⟩
  simp [positions]

theorem nodup_map_of_injective {α β : Type} (f : α → β) (hf : Function.Injective f)
    {l : List α} (hl : l.Nodup) : (l.map f).Nodup :=
  List.Pairwise.map f (fun _ _ hne heq => hne (hf heq)) hl

theorem positions_nodup (w h : Nat) : (positions w h).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro y _
    exact nodup_map_of_injective (fun x : Fin w => (x,y))
      (fun _ _ heq => congrArg Prod.fst heq) (List.nodup_finRange w)
  · apply (List.nodup_finRange h).imp
    intro y z hyz p hp q hq hpq
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hp
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hq
    exact hyz (congrArg Prod.snd hpq)

theorem positions_length (w h : Nat) : (positions w h).length = w*h := by
  simp [positions, List.length_flatMap, List.map_const', List.sum_replicate_nat,
    Nat.mul_comm]

theorem mem_occupiedPositions {w h : Nat} (s : Config (Position w h)) (p) :
    p ∈ occupiedPositions s ↔ s p ≠ .empty := by
  simp [occupiedPositions, mem_positions]

theorem occupiedPositions_nodup {w h : Nat} (s : Config (Position w h)) :
    (occupiedPositions s).Nodup :=
  (positions_nodup w h).filter _

theorem population_le_area {w h : Nat} (s : Config (Position w h)) :
    population s ≤ w*h := by
  have hl := List.length_filter_le (fun p => decide (s p ≠ .empty)) (positions w h)
  simpa only [population, occupiedPositions, positions_length] using hl

theorem population_pos_iff {w h : Nat} (s : Config (Position w h)) :
    0 < population s ↔ BML.Nonempty s := by
  constructor
  · intro hp
    obtain ⟨p, hp⟩ := List.exists_mem_of_length_pos hp
    exact ⟨p, (mem_occupiedPositions s p).mp hp⟩
  · rintro ⟨p, hp⟩
    exact List.length_pos_of_mem ((mem_occupiedPositions s p).mpr hp)

/-- An explicit duplicate-free listing computes the numerical population. -/
theorem population_eq_listing {w h : Nat} (s : Config (Position w h))
    (l : List (Position w h)) (hl : l.Nodup)
    (hm : ∀ p, p ∈ l ↔ s p ≠ .empty) : population s = l.length := by
  have hp : List.Perm (occupiedPositions s) l :=
    (List.perm_ext_iff_of_nodup (occupiedPositions_nodup s) hl).mpr
      (fun p => (mem_occupiedPositions s p).trans (hm p).symm)
  exact hp.length_eq

/-- One east car in each column and one north car in each row are distinct
occupied witnesses, so they give an additive numerical lower bound. -/
theorem population_ge_rows_columns {w h : Nat} (s : Config (Position w h))
    (he : ∀ x : Fin w, ∃ y : Fin h, s (x,y) = .east)
    (hn : ∀ y : Fin h, ∃ x : Fin w, s (x,y) = .north) :
    w+h ≤ population s := by
  classical
  let ef : Fin w → Position w h := fun x => (x, Classical.choose (he x))
  let nf : Fin h → Position w h := fun y => (Classical.choose (hn y), y)
  have hec : ∀ x, s (ef x) = .east := fun x => Classical.choose_spec (he x)
  have hnc : ∀ y, s (nf y) = .north := fun y => Classical.choose_spec (hn y)
  have hei : Function.Injective ef := fun _ _ h => congrArg Prod.fst h
  have hni : Function.Injective nf := fun _ _ h => congrArg Prod.snd h
  let es := (List.finRange w).map ef
  let ns := (List.finRange h).map nf
  have hd : (es ++ ns).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨nodup_map_of_injective ef hei (List.nodup_finRange w),
      nodup_map_of_injective nf hni (List.nodup_finRange h), ?_⟩
    intro p hp q hq hpq
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hp
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hq
    have hb := congrArg s hpq
    rw [hec, hnc] at hb
    cases hb
  have hs : es ++ ns ⊆ occupiedPositions s := by
    intro p hp
    apply (mem_occupiedPositions s p).mpr
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hp
      rw [hec]
      decide
    · obtain ⟨y, _, rfl⟩ := List.mem_map.mp hp
      rw [hnc]
      decide
  have hl := hd.length_le_of_subset hs
  simpa [es, ns, population] using hl

/-- Forward-invariant predicates on a finite cyclic coordinate are constant. -/
theorem cyclic_all_of_step {n : Nat} (hn : 0<n) (P : Fin n → Prop)
    (step : ∀ x, P x → P (cyclicNext n hn x))
    (x : Fin n) (hx : P x) : ∀ y, P y := by
  cases n with
  | zero => omega
  | succ n =>
    have htozero : ∀ z : Fin (n+1), P z → P 0 := by
      apply Fin.reverseInduction
      · intro hz
        have hs := step (Fin.last n) hz
        simpa [cyclicNext] using hs
      · intro i ih hi
        apply ih
        have hs := step i.castSucc hi
        have hnxt : cyclicNext (n+1) hn i.castSucc = i.succ := by
          apply Fin.ext
          simp [cyclicNext, show i.val+1<n+1 by omega]
        simpa only [hnxt] using hs
    have hzero := htozero x hx
    apply Fin.induction
    · exact hzero
    · intro i ih
      have hs := step i.castSucc ih
      have hnxt : cyclicNext (n+1) hn i.castSucc = i.succ := by
        apply Fin.ext
        simp [cyclicNext, show i.val+1<n+1 by omega]
      simpa only [hnxt] using hs

end BML.Train
