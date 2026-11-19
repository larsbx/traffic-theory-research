import BML.Delay

/-!
# A protected hole delays gridlock

The main eastbound queue occupies offsets `0,...,T`, followed by a hole at
`T+1`. The preceding north row has prescribed east cars at offsets `1,...,T`.
Each round moves the main hole one site toward the rear. The guard car below
the new hole may itself move east, but the east phase cannot turn it into a
north car, so no north car can fill that hole during the following phase.

The original rear tag first moves in round `T`, independently of every
unspecified cell. Hence any nonempty jam must occur strictly later than `T`.
The generic kernel statements assume only that east-next and north-previous
commute. Actual torus directions satisfy this premise definitionally.

Distinct sites are unnecessary for the deterministic proof. An iid pattern
probability additionally requires two distinct rows and `T+2` distinct columns;
no probability or independence assertion is built into these declarations.
-/

namespace BML

/-- A queue ending in a hole, protected by the shorter east run below it.
The guard is empty when `T=0`. -/
structure GuardedEastQueue (east north : Direction α) (T : Nat)
    (p : α) (s : Config α) : Prop where
  main : eastRun east (T + 1) p s
  guard : eastRun east T (north.prev (east.next p)) s
  hole : s (BML.iterate east.next (T + 1) p) = .empty

private theorem guardedQueue_prev_east_iterate (east north : Direction α)
    (hcomm : ∀ q, north.prev (east.next q) = east.next (north.prev q))
    (p : α) (n : Nat) :
    north.prev (BML.iterate east.next (n + 1) p) =
      BML.iterate east.next n (north.prev (east.next p)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change north.prev (east.next (BML.iterate east.next (n + 1) p)) =
      east.next (BML.iterate east.next n (north.prev (east.next p)))
    rw [hcomm, ih]

/-- One actual east-then-north round shortens both runs and moves the hole
one site west. The exterior is unrestricted. -/
theorem GuardedEastQueue.step (east north : Direction α)
    (hcomm : ∀ q, north.prev (east.next q) = east.next (north.prev q))
    (n : Nat) (p : α) (s : Config α)
    (hq : GuardedEastQueue east north (n + 1) p s) :
    GuardedEastQueue east north n p (BML.step east north s) := by
  refine ⟨eastRun_step east north (n + 1) p s hq.main,
    eastRun_step east north n (north.prev (east.next p)) s hq.guard, ?_⟩
  let q := BML.iterate east.next (n + 1) p
  have hm : CanMove east .east s q :=
    ⟨hq.main (n + 1) (by omega), hq.hole⟩
  have hempty : halfStep east .east s q = .empty :=
    moving_source_emptied east .east s q hm
  have hbelow : s (north.prev q) = .east := by
    change s (north.prev (BML.iterate east.next (n + 1) p)) = .east
    rw [guardedQueue_prev_east_iterate east north hcomm p n]
    exact hq.guard n (by omega)
  have hn : halfStep east .east s (north.prev q) ≠ .north := by
    intro hnorth
    have hbefore := (other_species_unchanged east .east s (north.prev q)
      .north (by decide) (by decide)).mp hnorth
    rw [hbelow] at hbefore
    cases hbefore
  change halfStep north .north (halfStep east .east s) q = .empty
  rw [halfStep]
  simp [Species.cell, hempty, hn]

/-- After `t` rounds, an initial queue with parameter `n+t` has parameter `n`.
In particular, its prescribed hole has moved exactly `t` sites west. -/
theorem GuardedEastQueue.iterate (east north : Direction α)
    (hcomm : ∀ q, north.prev (east.next q) = east.next (north.prev q))
    (t n : Nat) (p : α) (s : Config α)
    (hq : GuardedEastQueue east north (n + t) p s) :
    GuardedEastQueue east north n p (BML.iterate (BML.step east north) t s) := by
  induction t generalizing n with
  | zero => exact hq
  | succ t ih =>
    have hstart : GuardedEastQueue east north ((n + 1) + t) p s := by
      simpa only [Nat.add_assoc, Nat.add_comm 1 t] using hq
    exact GuardedEastQueue.step east north hcomm n p _ (ih (n + 1) hstart)

/-- Before round `T`, the main run alone blocks the rear coordinate. -/
theorem GuardedEastQueue.rear_blocked_before (east north : Direction α)
    (T : Nat) (p : α) (s : Config α)
    (hq : GuardedEastQueue east north T p s) (t : Nat) (ht : t < T) :
    BML.iterate (BML.step east north) t s p = .east ∧
      ¬ CanMove east .east (BML.iterate (BML.step east north) t s) p := by
  have hrun : eastRun east (t + 2) p s :=
    eastRun_mono east (t + 2) (T + 1) p s (by omega) hq.main
  exact eastRun_delay east north t p s hrun

/-- The original rear car stays at its initial coordinate through time `T`. -/
theorem GuardedEastQueue.rear_trace (east north : Direction α)
    (T : Nat) (p : α) (s : Config α)
    (hq : GuardedEastQueue east north T p s) (t : Nat) (ht : t ≤ T) :
    carTrace east north .east s t p = p := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have htrace := ih (by omega)
    have hblocked := (GuardedEastQueue.rear_blocked_before
      east north T p s hq t (by omega)).2
    change transport east .east (BML.iterate (BML.step east north) t s)
      (carTrace east north .east s t p) = p
    rw [htrace]
    simp only [transport, ite_eq_right hblocked]

/-- The hole reaches the rear car's successor at round `T`, so that car moves. -/
theorem GuardedEastQueue.rear_canMove (east north : Direction α)
    (hcomm : ∀ q, north.prev (east.next q) = east.next (north.prev q))
    (T : Nat) (p : α) (s : Config α)
    (hq : GuardedEastQueue east north T p s) :
    CanMove east .east (BML.iterate (BML.step east north) T s) p := by
  have hstart : GuardedEastQueue east north (0 + T) p s := by
    simpa only [Nat.zero_add] using hq
  have hfinal := GuardedEastQueue.iterate east north hcomm T 0 p s hstart
  exact ⟨hfinal.main 0 (by decide), hfinal.hole⟩

/-- Exact first movement of the original rear tag, not a replacement car.
The final inequality also rules out a degenerate self-successor move. -/
theorem GuardedEastQueue.rear_first_move (east north : Direction α)
    (hcomm : ∀ q, north.prev (east.next q) = east.next (north.prev q))
    (T : Nat) (p : α) (s : Config α)
    (hq : GuardedEastQueue east north T p s) :
    (∀ t, t ≤ T → carTrace east north .east s t p = p) ∧
      carTrace east north .east s (T + 1) p = east.next p ∧ east.next p ≠ p := by
  have htrace := GuardedEastQueue.rear_trace east north T p s hq
  have hm := GuardedEastQueue.rear_canMove east north hcomm T p s hq
  refine ⟨htrace, ?_, ?_⟩
  · change transport east .east (BML.iterate (BML.step east north) T s)
      (carTrace east north .east s T p) = east.next p
    rw [htrace T (Nat.le_refl T)]
    simp only [transport, ite_eq_left hm]
  · intro heq
    have hempty := hm.2
    rw [heq] at hempty
    have hfalse : Cell.east = .empty := hm.1.symm.trans hempty
    cases hfalse

/-- Any nonempty jam occurs strictly later than the guaranteed moving round. -/
theorem GuardedEastQueue.jam_after (east north : Direction α)
    (hcomm : ∀ q, north.prev (east.next q) = east.next (north.prev q))
    (T : Nat) (p : α) (s : Config α)
    (hq : GuardedEastQueue east north T p s) (U : Nat)
    (hjam : Jam east north (BML.iterate (BML.step east north) U s)) : T < U := by
  by_cases hUT : U ≤ T
  · have hsame : BML.iterate (BML.step east north) T s =
        BML.iterate (BML.step east north) U s := by
      rw [show T = U + (T - U) by omega]
      exact reached_frozen_persists east north s U hjam.2 (T - U)
    have hm := GuardedEastQueue.rear_canMove east north hcomm T p s hq
    rw [hsame] at hm
    exact False.elim (hjam.2.1 p hm.1 hm.2)
  · omega

/-- The local pattern excludes gridlock at every time through `T`, inclusive. -/
theorem GuardedEastQueue.no_jam_through (east north : Direction α)
    (hcomm : ∀ q, north.prev (east.next q) = east.next (north.prev q))
    (T : Nat) (p : α) (s : Config α)
    (hq : GuardedEastQueue east north T p s) (U : Nat) (hU : U ≤ T) :
    ¬ Jam east north (BML.iterate (BML.step east north) U s) := by
  intro hjam
  have hafter := GuardedEastQueue.jam_after east north hcomm T p s hq U hjam
  omega

/-- Torus directions discharge the generic commutation premise. The pattern
itself contains every deterministic hypothesis; no exterior condition remains. -/
theorem torus_guardedEastQueue_first_move (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (T : Nat) (p : Position w h) (s : Config (Position w h))
    (hq : GuardedEastQueue (eastDirection w h hw) (northDirection w h hh) T p s) :
    (∀ t, t ≤ T → carTrace (eastDirection w h hw) (northDirection w h hh)
      .east s t p = p) ∧
      carTrace (eastDirection w h hw) (northDirection w h hh) .east s (T + 1) p =
        (eastDirection w h hw).next p ∧ (eastDirection w h hw).next p ≠ p :=
  GuardedEastQueue.rear_first_move _ _ (fun _ => rfl) T p s hq

theorem torus_guardedEastQueue_jam_after (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (T : Nat) (p : Position w h) (s : Config (Position w h))
    (hq : GuardedEastQueue (eastDirection w h hw) (northDirection w h hh) T p s)
    (U : Nat) (hjam : Jam (eastDirection w h hw) (northDirection w h hh)
      (BML.iterate (torusStep w h hw hh) U s)) : T < U :=
  GuardedEastQueue.jam_after _ _ (fun _ => rfl) T p s hq U hjam

theorem torus_guardedEastQueue_no_jam_through (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (T : Nat) (p : Position w h) (s : Config (Position w h))
    (hq : GuardedEastQueue (eastDirection w h hw) (northDirection w h hh) T p s)
    (U : Nat) (hU : U ≤ T) :
    ¬ Jam (eastDirection w h hw) (northDirection w h hh)
      (BML.iterate (torusStep w h hw hh) U s) :=
  GuardedEastQueue.no_jam_through _ _ (fun _ => rfl) T p s hq U hU

end BML
