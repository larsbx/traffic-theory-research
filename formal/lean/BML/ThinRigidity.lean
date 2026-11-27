import BML.FiniteCycle
import BML.Fixation
import BML.Counting
import BML.Ring

/-!
Full-lane rigidity of CLASSIC jams (blueprint B10.1–B10.4).

A jam with fewer than `w` east cars contains a full north column, which was
already present initially. Conversely a full north column whose complement
holds no north car forces eventual gridlock. Both statements hold at every
height; on two rows a full north column is a *plug*, and a column with
exactly one north car is *lone*. The mirrored statements exchange species
and axes.
-/
namespace BML

/-- A tagged car whose cyclic coordinate advances with each move, and which
cannot move from one obstacle coordinate, moves finitely often. -/
theorem stopped_by_coordinate_obstacle {α : Type}
    (east north : Direction α) (sp : Species) (s : Config α) (p : α)
    (hp : s p = sp.cell) {n : Nat} (hn : 0 < n) (coordinate : α → Fin n)
    (obstacle : Fin n)
    (advance : ∀ u q, RoundCanMove east north sp u q →
      coordinate (roundTransport east north sp u q) = cyclicNext n hn (coordinate q))
    (blocked : ∀ t, coordinate (carTrace east north sp s t p) = obstacle →
      ¬ RoundCanMove east north sp (iterate (step east north) t s)
        (carTrace east north sp s t p)) :
    TagEventuallyStopped east north sp s p := by
  let trace := fun t => carTrace east north sp s t p
  let orbit := fun t => iterate (step east north) t s
  let rank := fun t => cyclicDistance n (coordinate (trace t)) obstacle
  let moving := fun t => RoundCanMove east north sp (orbit t) (trace t)
  have balance (t : Nat) : rank (t+1) + (if moving t then 1 else 0) = rank t := by
    by_cases hm : moving t
    · have hnext : coordinate (trace (t+1)) = cyclicNext n hn (coordinate (trace t)) :=
        advance (orbit t) (trace t) hm
      have hne : coordinate (trace t) ≠ obstacle := fun h => blocked t h hm
      simpa only [rank, hnext, hm, ↓reduceIte] using
        cyclicDistance_next n hn (coordinate (trace t)) obstacle hne
    · have hstay : trace (t+1) = trace t :=
        roundTransport_eq_of_no_round_move east north sp (orbit t) (trace t) hm
      simp [rank, hstay, hm]
  obtain ⟨start, hstop⟩ := eventually_zero_cost rank (fun t => if moving t then 1 else 0) balance
  refine (tagEventuallyStopped_iff_finitely_many_moves east north sp s p hp).mpr ⟨start, ?_⟩
  intro t hm
  have hc : moving (start+t) := hm
  simpa [hc] using hstop t

section Structure

variable {w h : Nat} (hw : 0 < w) (hh : 0 < h) (s : Config (Position w h))

/-- In a frozen state a north car lies in a full north column or shares its
column with an east car. -/
theorem frozen_north_column
    (hf : Frozen (eastDirection w h hw) (northDirection w h hh) s)
    (x : Fin w) (y : Fin h) (hn : s (x,y) = .north) :
    FullNorthColumn s x ∨ ∃ y', s (x,y') = .east := by
  classical
  by_cases he : ∃ y', s (x,y') = .east
  · exact Or.inr he
  · refine Or.inl (Train.cyclic_all_of_step hh (fun y => s (x,y) = .north) ?_ y hn)
    intro y' hy'
    have hb : s (x, cyclicNext h hh y') ≠ .empty := hf.2 (x,y') hy'
    match hc : s (x, cyclicNext h hh y') with
    | .empty => exact False.elim (hb hc)
    | .east => exact False.elim (he ⟨_, hc⟩)
    | .north => rfl

/-- The mirrored statement: a frozen east car lies in a full east row or
shares its row with a north car. -/
theorem frozen_east_row
    (hf : Frozen (eastDirection w h hw) (northDirection w h hh) s)
    (x : Fin w) (y : Fin h) (he : s (x,y) = .east) :
    FullEastRow s y ∨ ∃ x', s (x',y) = .north := by
  classical
  by_cases hn : ∃ x', s (x',y) = .north
  · exact Or.inr hn
  · refine Or.inl (Train.cyclic_all_of_step hw (fun x => s (x,y) = .east) ?_ x he)
    intro x' hx'
    have hb : s (cyclicNext w hw x', y) ≠ .empty := hf.1 (x',y) hx'
    match hc : s (cyclicNext w hw x', y) with
    | .empty => exact False.elim (hb hc)
    | .east => rfl
    | .north => exact False.elim (hn ⟨_, hc⟩)

/-- A frozen east car is followed, in the next column, by a full north column
or by another east car. -/
theorem frozen_east_successor_column
    (hf : Frozen (eastDirection w h hw) (northDirection w h hh) s)
    (x : Fin w) (y : Fin h) (he : s (x,y) = .east) :
    FullNorthColumn s (cyclicNext w hw x) ∨ ∃ y', s (cyclicNext w hw x, y') = .east := by
  have hb : s (cyclicNext w hw x, y) ≠ .empty := hf.1 (x,y) he
  match hc : s (cyclicNext w hw x, y) with
  | .empty => exact False.elim (hb hc)
  | .east => exact Or.inr ⟨y, hc⟩
  | .north => exact frozen_north_column hw hh s hf _ y hc

theorem frozen_north_successor_row
    (hf : Frozen (eastDirection w h hw) (northDirection w h hh) s)
    (x : Fin w) (y : Fin h) (hn : s (x,y) = .north) :
    FullEastRow s (cyclicNext h hh y) ∨ ∃ x', s (x', cyclicNext h hh y) = .north := by
  have hb : s (x, cyclicNext h hh y) ≠ .empty := hf.2 (x,y) hn
  match hc : s (x, cyclicNext h hh y) with
  | .empty => exact False.elim (hb hc)
  | .east => exact frozen_east_row hw hh s hf x _ hc
  | .north => exact Or.inr ⟨x, hc⟩

/-- B10.2: a jam without a full north column has an east car in every column. -/
theorem jam_east_every_column
    (hj : Jam (eastDirection w h hw) (northDirection w h hh) s)
    (hno : ∀ x, ¬ FullNorthColumn s x) : ∀ x, ∃ y, s (x,y) = .east := by
  obtain ⟨⟨p, hp⟩, hf⟩ := hj
  have hstart : ∃ y, s (p.1,y) = .east := by
    match hc : s p with
    | .empty => exact False.elim (hp hc)
    | .east => exact ⟨p.2, hc⟩
    | .north => exact (frozen_north_column hw hh s hf p.1 p.2 hc).resolve_left (hno _)
  exact Train.cyclic_all_of_step hw (fun x => ∃ y, s (x,y) = .east)
    (fun x ⟨y, hy⟩ => (frozen_east_successor_column hw hh s hf x y hy).resolve_left (hno _))
    p.1 hstart

theorem jam_north_every_row
    (hj : Jam (eastDirection w h hw) (northDirection w h hh) s)
    (hno : ∀ y, ¬ FullEastRow s y) : ∀ y, ∃ x, s (x,y) = .north := by
  obtain ⟨⟨p, hp⟩, hf⟩ := hj
  have hstart : ∃ x, s (x,p.2) = .north := by
    match hc : s p with
    | .empty => exact False.elim (hp hc)
    | .east => exact (frozen_east_row hw hh s hf p.1 p.2 hc).resolve_left (hno _)
    | .north => exact ⟨p.1, hc⟩
  exact Train.cyclic_all_of_step hh (fun y => ∃ x, s (x,y) = .north)
    (fun y ⟨x, hx⟩ => (frozen_north_successor_row hw hh s hf x y hx).resolve_left (hno _))
    p.2 hstart

omit hw hh in
theorem width_le_east_count (hall : ∀ x, ∃ y, s (x,y) = .east) :
    w ≤ speciesCount w h .east s := by
  rw [speciesCount_eq_length_speciesCells]
  have hsub : List.finRange w ⊆ (speciesCells w h .east s).map Prod.fst := by
    intro x _
    obtain ⟨y, hy⟩ := hall x
    exact List.mem_map.mpr ⟨(x,y), by simp [speciesCells, mem_positions, hy, Species.cell], rfl⟩
  simpa using (List.nodup_finRange w).length_le_of_subset hsub

omit hw hh in
theorem height_le_north_count (hall : ∀ y, ∃ x, s (x,y) = .north) :
    h ≤ speciesCount w h .north s := by
  rw [speciesCount_eq_length_speciesCells]
  have hsub : List.finRange h ⊆ (speciesCells w h .north s).map Prod.snd := by
    intro y _
    obtain ⟨x, hx⟩ := hall y
    exact List.mem_map.mpr ⟨(x,y), by simp [speciesCells, mem_positions, hx, Species.cell], rfl⟩
  simpa using (List.nodup_finRange h).length_le_of_subset hsub

/-- B10.2, counting form: a jam with fewer than `w` east cars has a full
north column. On two rows this column is a plug. -/
theorem jam_fullNorthColumn_of_few_east
    (hj : Jam (eastDirection w h hw) (northDirection w h hh) s)
    (hfew : speciesCount w h .east s < w) : ∃ x, FullNorthColumn s x := by
  classical
  apply Classical.byContradiction
  intro hno
  have hall := jam_east_every_column hw hh s hj (fun x hx => hno ⟨x, hx⟩)
  exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (width_le_east_count s hall) hfew)

theorem jam_fullEastRow_of_few_north
    (hj : Jam (eastDirection w h hw) (northDirection w h hh) s)
    (hfew : speciesCount w h .north s < h) : ∃ y, FullEastRow s y := by
  classical
  apply Classical.byContradiction
  intro hno
  have hall := jam_north_every_row hw hh s hj (fun y hy => hno ⟨y, hy⟩)
  exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (height_le_north_count s hall) hfew)

/-- B10.3, first step: an initial state with fewer than `w` east cars that
ever jams already contains a full north column. -/
theorem eventuallyJammed_fullNorthColumn_of_few_east
    (hj : EventuallyJammed (eastDirection w h hw) (northDirection w h hh) s)
    (hfew : speciesCount w h .east s < w) : ∃ x, FullNorthColumn s x := by
  obtain ⟨t, ht⟩ := hj
  have hcount : speciesCount w h .east (iterate (torusStep w h hw hh) t s) < w := by
    rw [iterate_torusStep_speciesCount]
    exact hfew
  obtain ⟨x, hx⟩ := jam_fullNorthColumn_of_few_east hw hh _ ht hcount
  exact ⟨x, fullNorthColumn_reflects hw hh s x t hx⟩

theorem eventuallyJammed_fullEastRow_of_few_north
    (hj : EventuallyJammed (eastDirection w h hw) (northDirection w h hh) s)
    (hfew : speciesCount w h .north s < h) : ∃ y, FullEastRow s y := by
  obtain ⟨t, ht⟩ := hj
  have hcount : speciesCount w h .north (iterate (torusStep w h hw hh) t s) < h := by
    rw [iterate_torusStep_speciesCount]
    exact hfew
  obtain ⟨y, hy⟩ := jam_fullEastRow_of_few_north hw hh _ ht hcount
  exact ⟨y, fullEastRow_reflects hw hh s y t hy⟩

end Structure

section Sufficiency

variable {w h : Nat} (hw : 0 < w) (hh : 0 < h) (s : Config (Position w h))

/-- A north car keeps its column along its actual trace. -/
theorem north_carTrace_column (p : Position w h) (t : Nat) :
    (carTrace (eastDirection w h hw) (northDirection w h hh) .north s t p).1 = p.1 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [carTrace, roundTransport, transport]
    split <;> simpa [northDirection] using ih

/-- An east car keeps its row along its actual trace. -/
theorem east_carTrace_row (p : Position w h) (t : Nat) :
    (carTrace (eastDirection w h hw) (northDirection w h hh) .east s t p).2 = p.2 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [carTrace, roundTransport, transport]
    split <;> simpa [eastDirection] using ih

/-- B10.4 at every height: a full north column, with every north car in
such a column, forces eventual nonempty gridlock. The east cars queue behind
the column; the north cars never move. -/
theorem eventuallyJammed_of_north_in_full_columns (q : Fin w)
    (hfull : FullNorthColumn s q)
    (hall : ∀ p, s p = .north → FullNorthColumn s p.1) :
    EventuallyJammed (eastDirection w h hw) (northDirection w h hh) s := by
  let e := eastDirection w h hw
  let n := northDirection w h hh
  apply eventuallyJammed_of_all_cars_stopped e n s _ ⟨(q, ⟨0, hh⟩), by simp [hfull _]⟩
  intro sp p hp
  cases sp with
  | east =>
    apply stopped_by_coordinate_obstacle e n .east s p hp hw Prod.fst q
    · intro u r hm
      change CanMove e .east u r at hm
      simp only [roundTransport, transport, hm, ↓reduceIte]
      rfl
    · intro t hpos hm
      let r := carTrace e n .east s t p
      have hwall := fullNorthColumn_persists hw hh s q hfull t r.2
      have he : iterate (step e n) t s r = .east :=
        carTrace_preserves_car e n .east s p hp t
      have hpos' : r.1 = q := hpos
      have hr : (q, r.2) = r := Prod.ext hpos'.symm rfl
      change iterate (step e n) t s (q, r.2) = .north at hwall
      rw [hr, he] at hwall
      cases hwall
  | north =>
    refine (tagEventuallyStopped_iff_finitely_many_moves e n .north s p hp).mpr ⟨0, ?_⟩
    intro t hm
    let r := carTrace e n .north s (0+t) p
    have hcol : r.1 = p.1 := north_carTrace_column hw hh s p (0+t)
    have hwall := fullNorthColumn_persists hw hh s p.1 (hall p hp) (0+t)
    have hr : (p.1, r.2) = r := Prod.ext hcol.symm rfl
    have hmr : CanMove n .north (halfStep e .east (iterate (torusStep w h hw hh) (0+t) s))
        (p.1, r.2) := by
      rw [hr]
      exact hm
    exact fullNorthColumn_no_moves hw hh _ p.1 hwall r.2 hmr

/-- The mirrored statement: a full east row, with every east car in such a
row, forces eventual nonempty gridlock. -/
theorem eventuallyJammed_of_east_in_full_rows (q : Fin h)
    (hfull : FullEastRow s q)
    (hall : ∀ p, s p = .east → FullEastRow s p.2) :
    EventuallyJammed (eastDirection w h hw) (northDirection w h hh) s := by
  let e := eastDirection w h hw
  let n := northDirection w h hh
  apply eventuallyJammed_of_all_cars_stopped e n s _ ⟨(⟨0, hw⟩, q), by simp [hfull _]⟩
  intro sp p hp
  cases sp with
  | east =>
    refine (tagEventuallyStopped_iff_finitely_many_moves e n .east s p hp).mpr ⟨0, ?_⟩
    intro t hm
    let r := carTrace e n .east s (0+t) p
    have hrow : r.2 = p.2 := east_carTrace_row hw hh s p (0+t)
    have hwall := fullEastRow_persists hw hh s p.2 (hall p hp) (0+t)
    have hr : (r.1, p.2) = r := Prod.ext rfl hrow.symm
    have hmr : CanMove e .east (iterate (torusStep w h hw hh) (0+t) s) (r.1, p.2) := by
      rw [hr]
      exact hm
    exact fullEastRow_no_moves hw _ p.2 hwall r.1 hmr
  | north =>
    apply stopped_by_coordinate_obstacle e n .north s p hp hh Prod.snd q
    · intro u r hm
      change CanMove n .north (halfStep e .east u) r at hm
      simp only [roundTransport, transport, hm, ↓reduceIte]
      rfl
    · intro t hpos hm
      let r := carTrace e n .north s t p
      have hwall := fullEastRow_persists hw hh s q hfull t r.1
      have hn' : iterate (step e n) t s r = .north :=
        carTrace_preserves_car e n .north s p hp t
      have hpos' : r.2 = q := hpos
      have hr : (r.1, q) = r := Prod.ext rfl hpos'.symm
      change iterate (step e n) t s (r.1, q) = .east at hwall
      rw [hr, hn'] at hwall
      cases hwall

end Sufficiency

section Gaps

variable {w h : Nat} (hw : 0 < w) (hh : 0 < h)

/-- The number of east cars in the columns selected by `G`. -/
def eastCountIn (G : Fin w → Prop) [DecidablePred G] (s : Config (Position w h)) : Nat :=
  (speciesCells w h .east s).countP fun p => decide (G p.1)

/-- Every edge of the column set `G` lies at a full north column. A gap
between consecutive plugs, and the whole torus, are of this kind. -/
def PlugBounded (G : Fin w → Prop) (s : Config (Position w h)) : Prop :=
  ∀ x, ¬ (G x ↔ G (cyclicNext w hw x)) →
    FullNorthColumn s x ∨ FullNorthColumn s (cyclicNext w hw x)

theorem plugBounded_iterate_iff (G : Fin w → Prop) (s : Config (Position w h)) (t : Nat) :
    PlugBounded hw G (iterate (torusStep w h hw hh) t s) ↔ PlugBounded hw G s := by
  simp only [PlugBounded, fullNorthColumn_iterate_iff]

/-- B10.1: no east car crosses a full north column, so the east cars of a
plug-bounded column set are conserved. -/
theorem eastCountIn_step (G : Fin w → Prop) [DecidablePred G] (s : Config (Position w h))
    (hb : PlugBounded hw G s) :
    eastCountIn G (torusStep w h hw hh s) = eastCountIn G s := by
  have hnorth : speciesCells w h .east (torusStep w h hw hh s) =
      speciesCells w h .east (halfStep (eastDirection w h hw) .east s) := by
    unfold speciesCells torusStep step
    apply List.filter_congr
    intro p _
    exact decide_eq_decide.mpr (other_species_unchanged (northDirection w h hh) .north _ p
      .east (by decide) (by decide))
  unfold eastCountIn
  rw [hnorth, (speciesCells_transport_perm w h _ .east s).countP_eq, List.countP_map]
  apply List.countP_congr
  intro p hp
  have hcar : s p = .east := (mem_speciesCells w h .east s p).mp hp
  simp only [Function.comp, decide_eq_true_eq]
  unfold transport
  split
  · rename_i hm
    change G (cyclicNext w hw p.1) ↔ G p.1
    by_cases hiff : G p.1 ↔ G (cyclicNext w hw p.1)
    · exact hiff.symm
    · rcases hb p.1 hiff with hfull | hfull
      · have hn : s p = .north := hfull p.2
        rw [hcar] at hn
        cases hn
      · have hn : s (cyclicNext w hw p.1, p.2) = .north := hfull p.2
        have hz : s (cyclicNext w hw p.1, p.2) = .empty := hm.2
        rw [hz] at hn
        cases hn
  · exact Iff.rfl

theorem eastCountIn_iterate (G : Fin w → Prop) [DecidablePred G] (s : Config (Position w h))
    (hb : PlugBounded hw G s) (t : Nat) :
    eastCountIn G (iterate (torusStep w h hw hh) t s) = eastCountIn G s := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [← ih]
    exact eastCountIn_step hw hh G _ ((plugBounded_iterate_iff hw hh G s t).mpr hb)

/-- In a frozen state, east cars continue through every run of columns that
are not full north columns. -/
theorem frozen_east_along_run (s : Config (Position w h))
    (hf : Frozen (eastDirection w h hw) (northDirection w h hh) s)
    (c : Fin w) (hc : ∃ y, s (c,y) = .east) (k : Nat)
    (hrun : ∀ i, i ≤ k → ¬ FullNorthColumn s (iterate (cyclicNext w hw) i c)) :
    ∃ y, s (iterate (cyclicNext w hw) k c, y) = .east := by
  induction k with
  | zero => exact hc
  | succ k ih =>
    obtain ⟨y, hy⟩ := ih (fun i hi => hrun i (Nat.le_succ_of_le hi))
    exact (frozen_east_successor_column hw hh s hf _ y hy).resolve_left
      (hrun (k+1) (Nat.le_refl _))

omit hh in
/-- Fewer than `w` successive columns are distinct. -/
theorem iterate_cyclicNext_injective_lt (c : Fin w) {a b : Nat} (ha : a < w) (hb : b < w)
    (heq : iterate (cyclicNext w hw) a c = iterate (cyclicNext w hw) b c) : a = b := by
  have hc := c.isLt
  have key : ∀ k, k < w → (c.val + k) % w =
      if c.val + k < w then c.val + k else c.val + k - w := by
    intro k hk
    split
    · exact Nat.mod_eq_of_lt (by assumption)
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have hv := congrArg Fin.val heq
  rw [iterate_cyclicNext_val, iterate_cyclicNext_val, key a ha, key b hb] at hv
  split at hv <;> split at hv <;> omega

/-- B10.3, the gap condition, at every height. Let the state jam, let `G`
be a plug-bounded column set, and let `c, c+1, …, c+d-1` be columns of `G`
that are not full north columns, with a north car in `c`. Then `G` holds at
least `d` east cars initially. On two rows `c` is a lone column at distance
`d` from the plug ending its gap. -/
theorem gap_east_count_lower_bound (G : Fin w → Prop) [DecidablePred G]
    (s : Config (Position w h))
    (hj : EventuallyJammed (eastDirection w h hw) (northDirection w h hh) s)
    (hb : PlugBounded hw G s) (c : Fin w) (hnorth : ∃ y, s (c,y) = .north)
    (d : Nat) (hd : d ≤ w)
    (hrun : ∀ i, i < d → G (iterate (cyclicNext w hw) i c) ∧
      ¬ FullNorthColumn s (iterate (cyclicNext w hw) i c)) :
    d ≤ eastCountIn G s := by
  classical
  cases d with
  | zero => exact Nat.zero_le _
  | succ d =>
  obtain ⟨t, ht⟩ := hj
  let u := iterate (torusStep w h hw hh) t s
  have hfullu : ∀ x, FullNorthColumn u x ↔ FullNorthColumn s x :=
    fun x => fullNorthColumn_iterate_iff hw hh s x t
  have hnorthu : ∃ y, u (c,y) = .north := by
    apply Classical.byContradiction
    intro hno
    have hfree : NorthFreeColumn u c := fun y hy => hno ⟨y, hy⟩
    obtain ⟨y, hy⟩ := hnorth
    exact (northFreeColumn_iterate_iff hw hh s c t).mp hfree y hy
  have heast0 : ∃ y, u (c,y) = .east := by
    obtain ⟨y, hy⟩ := hnorthu
    exact (frozen_north_column hw hh u ht.2 c y hy).resolve_left
      (fun hfull => (hrun 0 (Nat.succ_pos d)).2 ((hfullu c).mp hfull))
  have heast : ∀ i, i < d+1 → ∃ y, u (iterate (cyclicNext w hw) i c, y) = .east := by
    intro i hi
    apply frozen_east_along_run hw hh u ht.2 c heast0 i
    intro k hk hfull
    exact (hrun k (Nat.lt_of_le_of_lt hk hi)).2 ((hfullu _).mp hfull)
  rw [← eastCountIn_iterate hw hh G s hb t]
  let cols := (List.finRange (d+1)).map fun i => iterate (cyclicNext w hw) i.val c
  have hnodup : cols.Nodup := by
    apply List.pairwise_map.mpr
    apply (List.nodup_finRange (d+1)).imp
    intro a b hab heq
    exact hab (Fin.ext (iterate_cyclicNext_injective_lt hw c
      (Nat.lt_of_lt_of_le a.isLt hd) (Nat.lt_of_lt_of_le b.isLt hd) heq))
  have hsub : cols ⊆ ((speciesCells w h .east u).filter fun p => decide (G p.1)).map
      Prod.fst := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨y, hy⟩ := heast i.val i.isLt
    refine List.mem_map.mpr ⟨(_, y), List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · exact (mem_speciesCells w h .east u _).mpr hy
    · exact decide_eq_true (hrun i.val i.isLt).1
  have hlen := hnodup.length_le_of_subset hsub
  simpa [cols, eastCountIn, List.countP_eq_length_filter] using hlen

/-- B10.3 as stated for the 2×W torus, with `c` a lone column. -/
theorem two_row_gap_condition {w : Nat} (hw : 0 < w) (G : Fin w → Prop) [DecidablePred G]
    (s : Config (Position w 2))
    (hj : EventuallyJammed (eastDirection w 2 hw) (northDirection w 2 (by decide)) s)
    (hb : PlugBounded hw G s) (c : Fin w) (hlone : northColumnCount s c = 1)
    (d : Nat) (hd : d ≤ w)
    (hrun : ∀ i, i < d → G (iterate (cyclicNext w hw) i c) ∧
      ¬ FullNorthColumn s (iterate (cyclicNext w hw) i c)) :
    d ≤ eastCountIn G s := by
  classical
  apply gap_east_count_lower_bound hw (by decide) G s hj hb c ?_ d hd hrun
  apply Classical.byContradiction
  intro hno
  have hzero := (northColumnCount_eq_zero_iff s c).mpr (fun y hy => hno ⟨y, hy⟩)
  omega

end Gaps

section TwoLanes

/-- On two rows, no column holds exactly one north car iff every north car
lies in a plug. -/
theorem no_lone_column_iff {w : Nat} (s : Config (Position w 2)) :
    (∀ x, northColumnCount s x ≠ 1) ↔ ∀ p, s p = .north → FullNorthColumn s p.1 := by
  have hcount : ∀ x, northColumnCount s x =
      (if s (x,0) = .north then 1 else 0) + (if s (x,1) = .north then 1 else 0) := by
    intro x
    simp [northColumnCount, List.finRange_succ, List.countP_cons]
    split <;> split <;> simp_all
  constructor
  · intro hno ⟨x, y⟩ hp y'
    have h1 := hno x
    rw [hcount] at h1
    match y, y' with
    | 0, 0 => exact hp
    | 1, 1 => exact hp
    | 0, 1 => simp only [hp] at h1; split at h1 <;> simp_all
    | 1, 0 => simp only [hp] at h1; split at h1 <;> simp_all
  · intro hall x hone
    rw [hcount] at hone
    by_cases h0 : s (x,0) = .north
    · have := hall (x,0) h0 1
      simp_all
    · by_cases h1 : s (x,1) = .north
      · exact h0 (hall (x,1) h1 0)
      · simp [h0, h1] at hone

/-- On two columns, no row holds exactly one east car iff every east car
lies in a full east row. -/
theorem no_lone_row_iff {h : Nat} (s : Config (Position 2 h)) :
    (∀ y, eastRowCount s y ≠ 1) ↔ ∀ p, s p = .east → FullEastRow s p.2 := by
  have hcount : ∀ y, eastRowCount s y =
      (if s (0,y) = .east then 1 else 0) + (if s (1,y) = .east then 1 else 0) := by
    intro y
    simp [eastRowCount, List.finRange_succ, List.countP_cons]
    split <;> split <;> simp_all
  constructor
  · intro hno ⟨x, y⟩ hp x'
    have h1 := hno y
    rw [hcount] at h1
    match x, x' with
    | 0, 0 => exact hp
    | 1, 1 => exact hp
    | 0, 1 => simp only [hp] at h1; split at h1 <;> simp_all
    | 1, 0 => simp only [hp] at h1; split at h1 <;> simp_all
  · intro hall y hone
    rw [hcount] at hone
    by_cases h0 : s (0,y) = .east
    · have := hall (0,y) h0 1
      simp_all
    · by_cases h1 : s (1,y) = .east
      · exact h0 (hall (1,y) h1 0)
      · simp [h0, h1] at hone

/-- B10.4 as stated for the 2×W torus: a plug and no lone column jam. -/
theorem two_row_plug_no_lone_jams {w : Nat} (hw : 0 < w) (s : Config (Position w 2))
    (q : Fin w) (hplug : FullNorthColumn s q) (hlone : ∀ x, northColumnCount s x ≠ 1) :
    EventuallyJammed (eastDirection w 2 hw) (northDirection w 2 (by decide)) s :=
  eventuallyJammed_of_north_in_full_columns hw (by decide) s q hplug
    ((no_lone_column_iff s).mp hlone)

theorem two_column_plug_no_lone_jams {h : Nat} (hh : 0 < h) (s : Config (Position 2 h))
    (q : Fin h) (hplug : FullEastRow s q) (hlone : ∀ y, eastRowCount s y ≠ 1) :
    EventuallyJammed (eastDirection 2 h (by decide)) (northDirection 2 h hh) s :=
  eventuallyJammed_of_east_in_full_rows (by decide) hh s q hplug
    ((no_lone_row_iff s).mp hlone)

end TwoLanes

end BML
