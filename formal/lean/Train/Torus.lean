import Train.Kernel
import Train.Finite

namespace BML.Train

theorem cyclicNext_val (n : Nat) (hn : 0 < n) (i : Fin n) :
    (BML.cyclicNext n hn i).val = (i.val + 1) % n := by
  by_cases hl : i.val + 1 < n
  · simp [BML.cyclicNext, hl, Nat.mod_eq_of_lt hl]
  · have he : i.val + 1 = n := by have hi := i.isLt; omega
    simp [BML.cyclicNext, he]

theorem cyclic_iterate_val (n : Nat) (hn : 0 < n) (k : Nat) (i : Fin n) :
    (BML.iterate (BML.cyclicNext n hn) k i).val = (i.val + k) % n := by
  induction k with
  | zero => simp [BML.iterate, Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    simp only [BML.iterate, cyclicNext_val, ih, Nat.mod_add_mod]
    rw [Nat.add_assoc]

theorem cyclic_iterate_period (n : Nat) (hn : 0 < n) (i : Fin n) :
    BML.iterate (BML.cyclicNext n hn) n i = i := by
  apply Fin.ext
  rw [cyclic_iterate_val, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

theorem east_iterate (w h : Nat) (hw : 0 < w) (k : Nat) (p : Position w h) :
    BML.iterate (eastDirection w h hw).next k p =
      (BML.iterate (BML.cyclicNext w hw) k p.1, p.2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (eastDirection w h hw).next (BML.iterate (eastDirection w h hw).next k p) =
      (BML.cyclicNext w hw (BML.iterate (BML.cyclicNext w hw) k p.1), p.2)
    rw [ih]
    rfl

theorem north_iterate (w h : Nat) (hh : 0 < h) (k : Nat) (p : Position w h) :
    BML.iterate (northDirection w h hh).next k p =
      (p.1, BML.iterate (BML.cyclicNext h hh) k p.2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (northDirection w h hh).next (BML.iterate (northDirection w h hh).next k p) =
      (p.1, BML.cyclicNext h hh (BML.iterate (BML.cyclicNext h hh) k p.2))
    rw [ih]
    rfl

def eastRing (w h : Nat) (hw : 0 < w) : CyclicDirection (Position w h) where
  toDirection := eastDirection w h hw
  period := w
  positive := hw
  closes p := by rw [east_iterate, cyclic_iterate_period]

def northRing (w h : Nat) (hh : 0 < h) : CyclicDirection (Position w h) where
  toDirection := northDirection w h hh
  period := h
  positive := hh
  closes p := by rw [north_iterate, cyclic_iterate_period]

def torusStep (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    Config (Position w h) → Config (Position w h) :=
  step (eastRing w h hw) (northRing w h hh)

theorem east_fullRing_iff_row (w h : Nat) (hw : 0 < w)
    (s : Config (Position w h)) (x : Fin w) (y : Fin h) :
    FullRing (eastRing w h hw) .east s (x,y) ↔ ∀ z : Fin w, s (z,y) = .east := by
  constructor
  · intro hfull
    have hall : ∀ z : Fin w, FullRing (eastRing w h hw) .east s (z,y) := by
      apply cyclic_all_of_step hw (fun z => FullRing (eastRing w h hw) .east s (z,y))
      · intro z hz
        exact fullRing_next (eastRing w h hw) .east s (z,y) hz
      · exact hfull
    intro z
    exact allOwn_head _ _ _ _ hw _ (hall z)
  · intro hall
    apply (allOwn_iff_iterates _ _ _ _ _).mpr
    intro k _
    change s (BML.iterate (eastDirection w h hw).next k (x,y)) = .east
    rw [east_iterate]
    exact hall _

theorem north_fullRing_iff_column (w h : Nat) (hh : 0 < h)
    (s : Config (Position w h)) (x : Fin w) (y : Fin h) :
    FullRing (northRing w h hh) .north s (x,y) ↔ ∀ z : Fin h, s (x,z) = .north := by
  constructor
  · intro hfull
    have hall : ∀ z : Fin h, FullRing (northRing w h hh) .north s (x,z) := by
      apply cyclic_all_of_step hh (fun z => FullRing (northRing w h hh) .north s (x,z))
      · intro z hz
        exact fullRing_next (northRing w h hh) .north s (x,z) hz
      · exact hfull
    intro z
    exact allOwn_head _ _ _ _ hh _ (hall z)
  · intro hall
    apply (allOwn_iff_iterates _ _ _ _ _).mpr
    intro k _
    change s (BML.iterate (northDirection w h hh).next k (x,y)) = .north
    rw [north_iterate]
    exact hall _

/-- Movement-based TRAIN gridlock is CLASSIC blockage with homogeneous rings excluded. -/
theorem torus_stuck_iff (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) :
    Stuck (eastRing w h hw) (northRing w h hh) s ↔
      BML.Frozen (eastDirection w h hw) (northDirection w h hh) s ∧
      (∀ y : Fin h, ¬ ∀ x : Fin w, s (x,y) = .east) ∧
      (∀ x : Fin w, ¬ ∀ y : Fin h, s (x,y) = .north) := by
  rw [stuck_iff_classic_no_fullRing]
  constructor
  · rintro ⟨hf, he, hn⟩
    refine ⟨hf, ?_, ?_⟩
    · intro y hy
      exact he (⟨0,hw⟩,y) ((east_fullRing_iff_row w h hw s ⟨0,hw⟩ y).mpr hy)
    · intro x hx
      exact hn (x,⟨0,hh⟩) ((north_fullRing_iff_column w h hh s x ⟨0,hh⟩).mpr hx)
  · rintro ⟨hf, he, hn⟩
    refine ⟨hf, ?_, ?_⟩
    · intro p hp
      exact he p.2 ((east_fullRing_iff_row w h hw s p.1 p.2).mp hp)
    · intro p hp
      exact hn p.1 ((north_fullRing_iff_column w h hh s p.1 p.2).mp hp)

theorem stuck_east_has_north (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h))
    (hstuck : Stuck (eastRing w h hw) (northRing w h hh) s)
    (x : Fin w) (y : Fin h) (hp : s (x,y) = .east) :
    ∃ z : Fin w, s (z,y) = .north := by
  obtain ⟨k, _, _, hb⟩ := stopped_car_has_blocker (eastRing w h hw) .east s (x,y)
    hp (hstuck.1 (x,y))
  change s (BML.iterate (eastDirection w h hw).next k (x,y)) = .north at hb
  rw [east_iterate] at hb
  exact ⟨_, hb⟩

theorem stuck_north_has_east (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h))
    (hstuck : Stuck (eastRing w h hw) (northRing w h hh) s)
    (x : Fin w) (y : Fin h) (hp : s (x,y) = .north) :
    ∃ z : Fin h, s (x,z) = .east := by
  obtain ⟨k, _, _, hb⟩ := stopped_car_has_blocker (northRing w h hh) .north s (x,y)
    hp (hstuck.2 (x,y))
  change s (BML.iterate (northDirection w h hh).next k (x,y)) = .east at hb
  rw [north_iterate] at hb
  exact ⟨_, hb⟩

theorem full_east_torus_fixed (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    torusStep w h hw hh (fun _ => .east) = (fun _ => .east) := by
  have he := full_species_halfStep_fixed (eastRing w h hw) .east
  change halfStep (eastRing w h hw) .east (fun _ => Cell.east) = (fun _ => Cell.east) at he
  have hn : NoMovers (northRing w h hh) .north (fun _ => .east) := by
    intro p hp
    have hi := hp.1
    cases hi
  unfold torusStep step
  rw [he]
  exact halfStep_eq_of_no_movers (northRing w h hh) .north _ hn

/-- Even the singleton ring is an occupancy fixed point with a genuine mover. -/
theorem singleton_full_ring_counterexample :
    torusStep 1 1 (by decide) (by decide) (fun _ => .east) = (fun _ => .east) ∧
    CanMove (eastRing 1 1 (by decide)) .east (fun _ => .east) (0,0) ∧
    ¬ Stuck (eastRing 1 1 (by decide)) (northRing 1 1 (by decide)) (fun _ => .east) := by
  refine ⟨full_east_torus_fixed 1 1 (by decide) (by decide), ?_, ?_⟩
  · exact full_species_moves (eastRing 1 1 (by decide)) .east (0,0)
  · intro h
    exact h.1 (0,0) (full_species_moves (eastRing 1 1 (by decide)) .east (0,0))

end BML.Train
