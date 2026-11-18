import Train.Finite
import Train.Torus

namespace BML.Train

/-- The rectangular winding core, extended by an initial segment of interior
north cars.  The definition is total; its jam and population theorems require
both dimensions at least two and the indicated capacity bound. -/
def stuckConfig (w h k : Nat) : Config (Position w h) := fun p =>
  if p.1.val = w-1 then
    if p.2.val = h-1 then .east else .north
  else if p.2.val = 0 then .east
  else if p.1.val * (h-1) + (h-1-p.2.val) ≤ k then .north else .empty

def eastCorePos (w h : Nat) (hh : 0<h) (x : Fin w) : Position w h :=
  (x, if x.val = w-1 then ⟨h-1, by omega⟩ else ⟨0,hh⟩)

def rightCorePos (w h : Nat) (hw : 0<w) (y : Fin (h-1)) : Position w h :=
  (⟨w-1,by omega⟩, ⟨y.val,by have := y.isLt; omega⟩)

def interiorIndex (h : Nat) (p : Position w h) : Nat :=
  p.1.val * (h-1) + (h-1-p.2.val)

def interiorPos (w h k : Nat) (hw : 2≤w) (hh : 2≤h)
    (hk : k < (w-1)*(h-1)) (t : Fin (k+1)) : Position w h :=
  (⟨t.val / (h-1), by
      have ht := t.isLt
      have hdiv : t.val / (h-1) < w-1 :=
        (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
      omega⟩,
   ⟨h-1-t.val % (h-1), by
      have hm := Nat.mod_lt t.val (show 0<h-1 by omega)
      omega⟩)

theorem interiorPos_fst_lt (hw : 2≤w) (hh : 2≤h)
    (hk : k < (w-1)*(h-1)) (t : Fin (k+1)) :
    (interiorPos w h k hw hh hk t).1.val < w-1 := by
  exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (by have := t.isLt; omega)

theorem interiorPos_snd_pos (hw : 2≤w) (hh : 2≤h)
    (hk : k < (w-1)*(h-1)) (t : Fin (k+1)) :
    0 < (interiorPos w h k hw hh hk t).2.val := by
  have hm := Nat.mod_lt t.val (show 0<h-1 by omega)
  simp only [interiorPos]
  omega

theorem interiorPos_index (hw : 2≤w) (hh : 2≤h)
    (hk : k < (w-1)*(h-1)) (t : Fin (k+1)) :
    interiorIndex h (interiorPos w h k hw hh hk t) = t.val := by
  have hm := Nat.mod_lt t.val (show 0<h-1 by omega)
  simp only [interiorIndex, interiorPos]
  rw [show h-1-(h-1-t.val%(h-1)) = t.val%(h-1) by omega]
  exact Nat.div_add_mod' _ _

theorem interiorPos_injective (hw : 2≤w) (hh : 2≤h)
    (hk : k < (w-1)*(h-1)) :
    Function.Injective (interiorPos w h k hw hh hk) := by
  intro a b hab
  apply Fin.ext
  have he := congrArg (interiorIndex h) hab
  simpa only [interiorPos_index] using he

theorem interiorPos_inverse (hw : 2≤w) (hh : 2≤h)
    (hk : k < (w-1)*(h-1)) (p : Position w h)
    (_hx : p.1.val < w-1) (hy : 0<p.2.val) (hi : interiorIndex h p ≤ k) :
    interiorPos w h k hw hh hk ⟨interiorIndex h p, by omega⟩ = p := by
  have hp := p.2.isLt
  have hr : h-1-p.2.val < h-1 := by omega
  apply Prod.ext
  · apply Fin.ext
    simp only [interiorPos, interiorIndex]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr]
    simp
  · apply Fin.ext
    simp only [interiorPos, interiorIndex]
    rw [Nat.mul_add_mod_of_lt hr]
    omega

theorem stuckConfig_eastCore (_hw : 2≤w) (hh : 2≤h) (x : Fin w) :
    stuckConfig w h k (eastCorePos w h (by omega) x) = .east := by
  by_cases hx : x.val = w-1 <;> simp [stuckConfig, eastCorePos, hx]

theorem stuckConfig_rightCore (hw : 2≤w) (_hh : 2≤h) (y : Fin (h-1)) :
    stuckConfig w h k (rightCorePos w h (by omega) y) = .north := by
  have hy := y.isLt
  simp [stuckConfig, rightCorePos, show y.val ≠ h-1 by omega]

theorem stuckConfig_interior (hw : 2≤w) (hh : 2≤h)
    (hk : k < (w-1)*(h-1)) (t : Fin (k+1)) :
    stuckConfig w h k (interiorPos w h k hw hh hk t) = .north := by
  have hx := interiorPos_fst_lt hw hh hk t
  have hy := interiorPos_snd_pos hw hh hk t
  have hj := interiorPos_index hw hh hk t
  have ht := t.isLt
  simp only [stuckConfig]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  change (if interiorIndex h _ ≤ k then Cell.north else Cell.empty) = .north
  rw [ite_eq_left (by omega)]

def coreListing (w h k : Nat) (hw : 2≤w) (hh : 2≤h)
    (hk : k < (w-1)*(h-1)) : List (Position w h) :=
  (List.finRange w).map (eastCorePos w h (by omega)) ++
  ((List.finRange (h-1)).map (rightCorePos w h (by omega)) ++
   (List.finRange (k+1)).map (interiorPos w h k hw hh hk))

theorem coreListing_nodup (hw : 2≤w) (hh : 2≤h)
    (hk : k < (w-1)*(h-1)) : (coreListing w h k hw hh hk).Nodup := by
  unfold coreListing
  apply List.nodup_append.mpr
  refine ⟨nodup_map_of_injective (eastCorePos w h (by omega))
      (fun _ _ he => congrArg Prod.fst he)
      (List.nodup_finRange w), ?_, ?_⟩
  · apply List.nodup_append.mpr
    refine ⟨nodup_map_of_injective _ ?_ (List.nodup_finRange (h-1)),
      nodup_map_of_injective _ (interiorPos_injective hw hh hk)
        (List.nodup_finRange (k+1)), ?_⟩
    · intro a b he
      apply Fin.ext
      exact congrArg (fun p : Position w h => p.2.val) he
    · intro p hp q hq he
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hp
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hq
      have ht := interiorPos_fst_lt hw hh hk t
      have hx := congrArg (fun p : Position w h => p.1.val) he
      simp only [rightCorePos] at hx
      omega
  · intro p hp q hq he
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hp
    have hec := stuckConfig_eastCore (k:=k) hw hh x
    have hnc : stuckConfig w h k q = .north := by
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨y, _, rfl⟩ := List.mem_map.mp hq
        exact stuckConfig_rightCore hw hh y
      · obtain ⟨t, _, rfl⟩ := List.mem_map.mp hq
        exact stuckConfig_interior hw hh hk t
    rw [he] at hec
    rw [hnc] at hec
    cases hec

theorem mem_coreListing (hw : 2≤w) (hh : 2≤h)
    (hk : k < (w-1)*(h-1)) (p : Position w h) :
    p ∈ coreListing w h k hw hh hk ↔ stuckConfig w h k p ≠ .empty := by
  constructor
  · intro hp
    simp only [coreListing, List.mem_append] at hp
    rcases hp with hp | hp | hp
    · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hp
      rw [stuckConfig_eastCore hw hh]
      decide
    · obtain ⟨y, _, rfl⟩ := List.mem_map.mp hp
      rw [stuckConfig_rightCore hw hh]
      decide
    · obtain ⟨t, _, rfl⟩ := List.mem_map.mp hp
      rw [stuckConfig_interior hw hh hk]
      decide
  · intro hp
    have px := p.1.isLt
    have py := p.2.isLt
    simp only [coreListing, List.mem_append, List.mem_map, List.mem_finRange,
      true_and]
    by_cases hx : p.1.val = w-1
    · by_cases hy : p.2.val = h-1
      · apply Or.inl
        refine ⟨p.1, ?_⟩
        apply Prod.ext
        · rfl
        · apply Fin.ext
          simp [eastCorePos, hx, hy]
      · apply Or.inr ∘ Or.inl
        refine ⟨⟨p.2.val,by omega⟩, ?_⟩
        apply Prod.ext
        · apply Fin.ext
          exact hx.symm
        · rfl
    · by_cases hy : p.2.val = 0
      · apply Or.inl
        refine ⟨p.1, ?_⟩
        apply Prod.ext
        · rfl
        · apply Fin.ext
          simp [eastCorePos, hx, hy]
      · have hi : interiorIndex h p ≤ k := by
          simpa [stuckConfig, hx, hy, interiorIndex] using hp
        apply Or.inr ∘ Or.inr
        refine ⟨⟨interiorIndex h p,by omega⟩, ?_⟩
        exact interiorPos_inverse hw hh hk p (by omega) (by omega) hi

theorem stuckConfig_population (hw : 2≤w) (hh : 2≤h)
    (hk : k < (w-1)*(h-1)) : population (stuckConfig w h k) = w+h+k := by
  rw [population_eq_listing _ _ (coreListing_nodup hw hh hk)
    (mem_coreListing hw hh hk)]
  simp only [coreListing, List.length_append, List.length_map, List.length_finRange]
  omega

theorem stuckConfig_frozen (hw : 2≤w) (hh : 2≤h) (k : Nat) :
    BML.Frozen (eastDirection w h (by omega)) (northDirection w h (by omega))
      (stuckConfig w h k) := by
  constructor
  · intro p hp
    rcases p with ⟨x,y⟩
    have hxlt := x.isLt
    have hylt := y.isLt
    change stuckConfig w h k (cyclicNext w _ x, y) ≠ .empty
    change stuckConfig w h k (x,y) = .east at hp
    by_cases hx : x.val = w-1
    · have hy : y.val = h-1 := by simpa [stuckConfig,hx] using hp
      have hnxt : (cyclicNext w (by omega) x).val = 0 := by
        simp [cyclicNext, show ¬x.val+1<w by omega]
      simp [stuckConfig, hnxt, hy, show 0≠w-1 by omega, show h-1≠0 by omega]
    · have hy : y.val = 0 := by
        by_cases hy : y.val = 0
        · exact hy
        · simp only [stuckConfig,hx,hy,↓reduceIte] at hp
          split at hp <;> cases hp
      simp [stuckConfig, hy, show 0≠h-1 by omega]
      split <;> decide
  · intro p hp
    rcases p with ⟨x,y⟩
    have hxlt := x.isLt
    have hylt := y.isLt
    change stuckConfig w h k (x, cyclicNext h _ y) ≠ .empty
    change stuckConfig w h k (x,y) = .north at hp
    by_cases hx : x.val = w-1
    · simp [stuckConfig,hx]
      split <;> decide
    · have hyp : y.val ≠ 0 ∧ x.val*(h-1)+(h-1-y.val)≤k := by
        by_cases hy : y.val = 0
        · simp [stuckConfig,hx,hy] at hp
        · refine ⟨hy, ?_⟩
          by_cases hi : x.val*(h-1)+(h-1-y.val)≤k
          · exact hi
          · simp [stuckConfig,hx,hy,hi] at hp
      by_cases hy : y.val = h-1
      · have hnxt : (cyclicNext h (by omega) y).val = 0 := by
          simp [cyclicNext, show ¬y.val+1<h by omega]
        simp [stuckConfig,hx,hnxt]
      · have hnxt : (cyclicNext h (by omega) y).val = y.val+1 := by
          simp [cyclicNext, show y.val+1<h by omega]
        have hi : x.val*(h-1)+(h-1-(y.val+1))≤k := by omega
        simp [stuckConfig,hx,hnxt,hi]

theorem stuckConfig_east_each_column (hw : 2≤w) (hh : 2≤h) (k : Nat) :
    ∀ x : Fin w, ∃ y : Fin h, stuckConfig w h k (x,y) = .east := by
  intro x
  exact ⟨(eastCorePos w h (by omega) x).2, stuckConfig_eastCore hw hh x⟩

theorem stuckConfig_north_each_row (hw : 2≤w) (hh : 2≤h) (k : Nat) :
    ∀ y : Fin h, ∃ x : Fin w, stuckConfig w h k (x,y) = .north := by
  intro y
  have hylt := y.isLt
  by_cases hy : y.val = h-1
  · refine ⟨⟨0,by omega⟩, ?_⟩
    simp [stuckConfig, hy, show 0≠w-1 by omega, show h-1≠0 by omega]
  · exact ⟨⟨w-1,by omega⟩,
      stuckConfig_rightCore hw hh ⟨y.val,by omega⟩⟩

/-- Occupied-successor blocking and an opposite-species blocker on each
occupied orbit force east cars into every column and north cars into every
row. The TRAIN kernel supplies the orbit-blocker hypotheses below. -/
theorem rows_columns_of_blockers (hw : 0<w) (hh : 0<h)
    (s : Config (Position w h)) (hne : BML.Nonempty s)
    (hf : BML.Frozen (eastDirection w h hw) (northDirection w h hh) s)
    (he : ∀ x y, s (x,y) = .east → ∃ x', s (x',y) = .north)
    (hn : ∀ x y, s (x,y) = .north → ∃ y', s (x,y') = .east) :
    (∀ x : Fin w, ∃ y : Fin h, s (x,y) = .east) ∧
    (∀ y : Fin h, ∃ x : Fin w, s (x,y) = .north) := by
  have firstE : ∃ x y, s (x,y) = .east := by
    obtain ⟨⟨x,y⟩,hp⟩ := hne
    cases hc : s (x,y) with
    | empty => exact False.elim (hp hc)
    | east => exact ⟨x,y,hc⟩
    | north =>
      obtain ⟨y',hy'⟩ := hn x y hc
      exact ⟨x,y',hy'⟩
  obtain ⟨x₀,y₀,h₀⟩ := firstE
  constructor
  · apply cyclic_all_of_step hw (fun x => ∃ y, s (x,y) = .east) _ x₀ ⟨y₀,h₀⟩
    intro x hx
    obtain ⟨y,hy⟩ := hx
    have hb := hf.1 (x,y) hy
    change s (cyclicNext w hw x,y) ≠ .empty at hb
    cases hc : s (cyclicNext w hw x,y) with
    | empty => exact False.elim (hb hc)
    | east => exact ⟨y,hc⟩
    | north => exact hn _ _ hc
  · obtain ⟨x₁,h₁⟩ := he x₀ y₀ h₀
    apply cyclic_all_of_step hh (fun y => ∃ x, s (x,y) = .north) _ y₀ ⟨x₁,h₁⟩
    intro y hy
    obtain ⟨x,hx⟩ := hy
    have hb := hf.2 (x,y) hx
    change s (x,cyclicNext h hh y) ≠ .empty at hb
    cases hc : s (x,cyclicNext h hh y) with
    | empty => exact False.elim (hb hc)
    | east => exact he _ _ hc
    | north => exact ⟨x,hc⟩

theorem interior_capacity (hw : 2≤w) (hh : 2≤h) :
    (w-1)*(h-1) + w+h = w*h+1 := by
  have ha : w-1+1=w := by omega
  have hb : h-1+1=h := by omega
  have he : (w-1+1)*(h-1+1) = w*h := by rw [ha,hb]
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at he
  omega

theorem threshold_parameter (hw : 2≤w) (hh : 2≤h)
    (hlo : w+h≤n) (hhi : n≤w*h) :
    n-(w+h) < (w-1)*(h-1) ∧ w+h+(n-(w+h)) = n := by
  have hc := interior_capacity hw hh
  omega

/-- Every member of the explicit family is a nonempty zero-movement TRAIN
state. This conclusion uses the executable queue-and-ring TRAIN kernel. -/
theorem stuckConfig_jam (hw : 2≤w) (hh : 2≤h) (k : Nat) :
    Jam (eastRing w h (by omega)) (northRing w h (by omega))
      (stuckConfig w h k) := by
  constructor
  · let x : Fin w := ⟨0,by omega⟩
    refine ⟨eastCorePos w h (by omega) x, ?_⟩
    rw [stuckConfig_eastCore hw hh]
    decide
  · apply (torus_stuck_iff w h (by omega) (by omega) _).mpr
    refine ⟨stuckConfig_frozen hw hh k, ?_, ?_⟩
    · intro y hall
      obtain ⟨x,hx⟩ := stuckConfig_north_each_row hw hh k y
      have he := hall x
      rw [hx] at he
      cases he
    · intro x hall
      obtain ⟨y,hy⟩ := stuckConfig_east_each_column hw hh k x
      have hn := hall y
      rw [hy] at hn
      cases hn

/-- A nonempty zero-movement TRAIN state has an east car in every column
and a north car in every row, including on singleton tori. -/
theorem jam_rows_columns (w h : Nat) (hw : 0<w) (hh : 0<h)
    (s : Config (Position w h))
    (hj : Jam (eastRing w h hw) (northRing w h hh) s) :
    (∀ x : Fin w, ∃ y : Fin h, s (x,y) = .east) ∧
    (∀ y : Fin h, ∃ x : Fin w, s (x,y) = .north) := by
  apply rows_columns_of_blockers hw hh s hj.1
    ((torus_stuck_iff w h hw hh s).mp hj.2).1
  · exact stuck_east_has_north w h hw hh s hj.2
  · exact stuck_north_has_east w h hw hh s hj.2

theorem jam_population_lower (w h : Nat) (hw : 0<w) (hh : 0<h)
    (s : Config (Position w h))
    (hj : Jam (eastRing w h hw) (northRing w h hh) s) :
    w+h ≤ population s := by
  have hr := jam_rows_columns w h hw hh s hj
  exact population_ge_rows_columns s hr.1 hr.2

/-- The full rectangular threshold: for both dimensions at least two,
every integer population from `w+h` through `w*h` occurs, and no other
population can occur in a nonempty zero-movement TRAIN state. -/
theorem jam_population_iff (w h : Nat) (hw : 2≤w) (hh : 2≤h) (n : Nat) :
    (∃ s : Config (Position w h),
      Jam (eastRing w h (by omega)) (northRing w h (by omega)) s ∧
      population s = n) ↔ w+h≤n ∧ n≤w*h := by
  constructor
  · rintro ⟨s,hj,hn⟩
    have hlo := jam_population_lower w h (by omega) (by omega) s hj
    have hhi := population_le_area s
    omega
  · rintro ⟨hlo,hhi⟩
    have hk := threshold_parameter hw hh hlo hhi
    refine ⟨stuckConfig w h (n-(w+h)), stuckConfig_jam hw hh _, ?_⟩
    rw [stuckConfig_population hw hh hk.1]
    exact hk.2

/-- No singleton-width or singleton-height torus has a nonempty TRAIN jam.
Full homogeneous rings rotate; occupancy fixed points do not invalidate
this movement statement. -/
theorem no_jam_singleton (w h : Nat) (hw : 0<w) (hh : 0<h)
    (hs : w=1 ∨ h=1) (s : Config (Position w h)) :
    ¬Jam (eastRing w h hw) (northRing w h hh) s := by
  intro hj
  have hlo := jam_population_lower w h hw hh s hj
  have hhi := population_le_area s
  rcases hs with hs | hs <;> subst_vars <;> simp at hhi <;> omega

/-- An equivalent statement covering every positive rectangle. The numerical
interval is empty when a dimension is one. -/
theorem jam_population_iff_positive (w h : Nat) (hw : 0<w) (hh : 0<h) (n : Nat) :
    (∃ s : Config (Position w h),
      Jam (eastRing w h hw) (northRing w h hh) s ∧ population s = n) ↔
      w+h≤n ∧ n≤w*h := by
  by_cases hwm : 2≤w
  · by_cases hhm : 2≤h
    · exact jam_population_iff w h hwm hhm n
    · have hs : h=1 := by omega
      constructor
      · rintro ⟨s,hj,_⟩
        exact False.elim (no_jam_singleton w h hw hh (Or.inr hs) s hj)
      · rintro ⟨hlo,hhi⟩
        subst h
        simp at hhi
        omega
  · have hs : w=1 := by omega
    constructor
    · rintro ⟨s,hj,_⟩
      exact False.elim (no_jam_singleton w h hw hh (Or.inl hs) s hj)
    · rintro ⟨hlo,hhi⟩
      subst w
      simp at hhi
      omega

/-- The threshold stated directly in terms of the two successive TRAIN
half-steps, with no appeal to occupancy fixed points. -/
theorem noMoves_population_iff (w h : Nat) (hw : 0<w) (hh : 0<h) (n : Nat) :
    (∃ s : Config (Position w h), BML.Nonempty s ∧
      NoMoves (eastRing w h hw) (northRing w h hh) s ∧ population s = n) ↔
      w+h≤n ∧ n≤w*h := by
  simp only [noMoves_iff_stuck]
  simpa only [Jam, and_assoc] using jam_population_iff_positive w h hw hh n

end BML.Train
