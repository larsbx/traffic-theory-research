import BML.Delay

/-!
A guarded north queue supplies an empty northeast corner at a prescribed
full-round boundary. An east wall aimed at that corner stays fixed while
the corner is occupied; a longer north queue supplies the other wall.
The proof uses the actual east-then-north kernel and leaves the exterior
unrestricted. Spatial placement, initial-iid weights and path exploration
are separate arguments in the logarithmic-barriers research note.
-/
namespace BML.Barrier

/-- Consecutive north cars, listed from the southern end. -/
def northRun (north : Direction α) (n : Nat) (p : α) (s : Config α) : Prop :=
  ∀ i, i < n → s (iterate north.next i p) = .north

theorem northRun_mono (north : Direction α) (m n : Nat) (p : α) (s : Config α)
    (hmn : m ≤ n) (h : northRun north n p s) : northRun north m p s := by
  intro i hi
  exact h i (by omega)

/-- All but the leading north car remain, regardless of the exterior. -/
theorem northRun_step (east north : Direction α) (n : Nat) (p : α) (s : Config α)
    (h : northRun north (n + 1) p s) : northRun north n p (step east north s) := by
  intro i hi
  have hp := (other_species_unchanged east .east s _ .north (by decide) (by decide)).mpr
    (h i (by omega))
  have hnext := (other_species_unchanged east .east s _ .north (by decide) (by decide)).mpr
    (h (i + 1) (by omega))
  change halfStep east .east s (north.next (iterate north.next i p)) = .north at hnext
  change halfStep north .north (halfStep east .east s) _ = .north
  rw [halfStep]
  simp [Species.cell, hp, hnext]

theorem northRun_iterate (east north : Direction α) (t n : Nat) (p : α) (s : Config α)
    (h : northRun north (n + t) p s) :
    northRun north n p (iterate (step east north) t s) := by
  induction t generalizing n with
  | zero => exact h
  | succ t ih =>
    have hstart : northRun north ((n + 1) + t) p s := by
      simpa only [Nat.add_assoc, Nat.add_comm 1 t] using h
    exact northRun_step east north n p _ (ih (n + 1) hstart)

/-- The guard starts one row above the eventual hole, so it does not
conflict with the east wall immediately west of that hole. -/
structure GuardedNorthHole (east north : Direction α) (T : Nat)
    (q : α) (s : Config α) : Prop where
  main : northRun north T q s
  guard : northRun north T (east.prev (north.next q)) s
  hole : s (iterate north.next T q) = .empty

private theorem west_north_iterate (east north : Direction α)
    (commute : ∀ q, east.prev (north.next q) = north.next (east.prev q))
    (q : α) (n : Nat) :
    east.prev (iterate north.next (n + 1) q) =
      iterate north.next n (east.prev (north.next q)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change east.prev (north.next (iterate north.next (n + 1) q)) =
      north.next (iterate north.next n (east.prev (north.next q)))
    rw [commute, ih]

/-- During the east phase the old hole has a north guard immediately west.
The north phase then empties the next queue cell, moving the hole south. -/
theorem GuardedNorthHole.step (east north : Direction α)
    (commute : ∀ q, east.prev (north.next q) = north.next (east.prev q))
    (n : Nat) (q : α) (s : Config α)
    (h : GuardedNorthHole east north (n + 1) q s) :
    GuardedNorthHole east north n q (step east north s) := by
  refine ⟨northRun_step east north n q s h.main,
    northRun_step east north n _ s h.guard, ?_⟩
  let p := iterate north.next n q
  have hsource : s p = .north := h.main n (by omega)
  have hwest : s (east.prev (north.next p)) = .north := by
    change s (east.prev (iterate north.next (n + 1) q)) = .north
    rw [west_north_iterate east north commute q n]
    exact h.guard n (by omega)
  have htarget : s (north.next p) = .empty := h.hole
  have htargetAfter : halfStep east .east s (north.next p) = .empty := by
    simp [halfStep, Species.cell, htarget, hwest]
  have hsourceAfter : halfStep east .east s p = .north :=
    (other_species_unchanged east .east s p .north (by decide) (by decide)).mpr hsource
  exact moving_source_emptied north .north (halfStep east .east s) p
    ⟨hsourceAfter, htargetAfter⟩

theorem GuardedNorthHole.iterate (east north : Direction α)
    (commute : ∀ q, east.prev (north.next q) = north.next (east.prev q))
    (t n : Nat) (q : α) (s : Config α)
    (h : GuardedNorthHole east north (n + t) q s) :
    GuardedNorthHole east north n q (BML.iterate (BML.step east north) t s) := by
  induction t generalizing n with
  | zero => exact h
  | succ t ih =>
    have hstart : GuardedNorthHole east north ((n + 1) + t) q s := by
      simpa only [Nat.add_assoc, Nat.add_comm 1 t] using h
    exact GuardedNorthHole.step east north commute n q _ (ih (n + 1) hstart)

/-- The prescribed corner is empty at exactly the requested full boundary. -/
theorem GuardedNorthHole.empty_at_deadline (east north : Direction α)
    (commute : ∀ q, east.prev (north.next q) = north.next (east.prev q))
    (T : Nat) (q : α) (s : Config α)
    (h : GuardedNorthHole east north T q s) :
    BML.iterate (BML.step east north) T s q = .empty := by
  have hstart : GuardedNorthHole east north (0 + T) q s := by simpa using h
  exact (GuardedNorthHole.iterate east north commute T 0 q s hstart).hole

private theorem eastRun_step_of_end_occupied (east north : Direction α)
    (a : Nat) (p : α) (s : Config α) (h : eastRun east a p s)
    (endOccupied : s (iterate east.next a p) ≠ .empty) :
    eastRun east a p (step east north s) := by
  intro i hi
  have hp := h i hi
  have hn : s (east.next (iterate east.next i p)) ≠ .empty := by
    by_cases hlast : i + 1 < a
    · have hnorth : s (east.next (iterate east.next i p)) = .east := h (i + 1) hlast
      simp [hnorth]
    · have heq : i + 1 = a := by omega
      simpa only [← heq, iterate] using endOccupied
  apply (other_species_unchanged north .north _ _ .east (by decide) (by decide)).mpr
  simp [halfStep, Species.cell, hp, hn]

/-- A north run at the endpoint blocks the entire east wall for T rounds. -/
theorem eastWall_preserved (east north : Direction α) (T a : Nat) (p q : α)
    (s : Config α) (eastEnd : iterate east.next a p = q)
    (eastWall : eastRun east a p s) (northQueue : northRun north T q s)
    (t : Nat) (ht : t ≤ T) :
    eastRun east a p (iterate (step east north) t s) := by
  induction t with
  | zero => exact eastWall
  | succ t ih =>
    apply eastRun_step_of_end_occupied east north a p _ (ih (by omega))
    rw [eastEnd]
    have hshort := northRun_mono north (1 + t) T q s (by omega) northQueue
    have hhead := northRun_iterate east north t 1 q s hshort 0 (by decide)
    simpa only [iterate] using (show
      iterate (step east north) t s (iterate north.next 0 q) ≠ .empty from by simp [hhead])

/-- Two initial walls and a short shifted guard force an actual L-shaped
snapshot barrier ending at one vacant corner. All lengths may be zero. -/
theorem draining_l_barrier (east north : Direction α)
    (commute : ∀ q, east.prev (north.next q) = north.next (east.prev q))
    (T a b : Nat) (eastStart northStart corner : α) (s : Config α)
    (eastEnd : iterate east.next a eastStart = corner)
    (northEnd : iterate north.next b northStart = corner)
    (eastWall : eastRun east a eastStart s)
    (northWall : northRun north (b + T) northStart s)
    (guard : northRun north T (east.prev (north.next corner)) s)
    (hole : s (iterate north.next T corner) = .empty) :
    eastRun east a eastStart (iterate (step east north) T s) ∧
      northRun north b northStart (iterate (step east north) T s) ∧
      iterate (step east north) T s corner = .empty := by
  have hqueue : northRun north T corner s := by
    intro i hi
    have h := northWall (b + i) (by omega)
    simpa only [iterate_add, northEnd] using h
  exact ⟨eastWall_preserved east north T a eastStart corner s eastEnd eastWall hqueue T
      (Nat.le_refl T),
    northRun_iterate east north T b northStart s northWall,
    GuardedNorthHole.empty_at_deadline east north commute T corner s ⟨hqueue, guard, hole⟩⟩

/-- The actual rectangular torus directions satisfy the required commutation. -/
theorem torus_draining_l_barrier (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (T a b : Nat) (eastStart northStart corner : Position w h)
    (s : Config (Position w h))
    (eastEnd : iterate (eastDirection w h hw).next a eastStart = corner)
    (northEnd : iterate (northDirection w h hh).next b northStart = corner)
    (eastWall : eastRun (eastDirection w h hw) a eastStart s)
    (northWall : northRun (northDirection w h hh) (b + T) northStart s)
    (guard : northRun (northDirection w h hh) T
      ((eastDirection w h hw).prev ((northDirection w h hh).next corner)) s)
    (hole : s (iterate (northDirection w h hh).next T corner) = .empty) :
    eastRun (eastDirection w h hw) a eastStart (iterate (torusStep w h hw hh) T s) ∧
      northRun (northDirection w h hh) b northStart (iterate (torusStep w h hw hh) T s) ∧
      iterate (torusStep w h hw hh) T s corner = .empty :=
  draining_l_barrier (eastDirection w h hw) (northDirection w h hh) (fun _ => rfl)
    T a b eastStart northStart corner s eastEnd northEnd eastWall northWall guard hole

end BML.Barrier
