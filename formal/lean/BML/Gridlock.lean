import BML.Blocking
import BML.Counting
import BML.Extremal
import BML.FiniteCycle

/-!
The CLASSIC G1 lower bound on every positive finite torus. The finite carrier
is the actual list of occupied positions, not an assumed number of cars.
Cycle extraction, torus winding, and numerical count conservation are composed
here to rule out eventual gridlock below the shorter side's length.
-/
namespace BML

/-- A nonempty frozen torus contains a simple occupied blocker cycle. Its
length lies between the shorter torus side and the actual number of cars. -/
theorem jam_has_simple_blocker_cycle (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h))
    (hj : Jam (eastDirection w h hw) (northDirection w h hh) s) :
    ∃ p k, 0 < k ∧ min w h ≤ k ∧ k ≤ carCount w h s ∧
      iterate (blocker w h hw hh s) k p = p ∧
      (List.ofFn (fun i : Fin k => iterate (blocker w h hw hh s) i.val p)).Nodup ∧
      (∀ i : Fin k, s (iterate (blocker w h hw hh s) i.val p) ≠ .empty) := by
  have hne : occupiedCells w h s ≠ [] :=
    (occupiedCells_nonempty_iff w h s).mpr hj.1
  have hclosed : ∀ p, p ∈ occupiedCells w h s →
      blocker w h hw hh s p ∈ occupiedCells w h s := by
    intro p hp
    exact (mem_occupiedCells w h s _).mpr
      (blocker_preserves_occupied w h hw hh s hj.2 p
        ((mem_occupiedCells w h s p).mp hp))
  obtain ⟨p, k, hp, hk, hcount, hreturn, hdistinct⟩ :=
    finite_closed_cycle (blocker w h hw hh s) (occupiedCells w h s) hne hclosed
  have hp' := (mem_occupiedCells w h s p).mp hp
  exact ⟨p, k, hk, blocker_closed_length_lower_bound w h hw hh s p k hk hreturn,
    hcount, hreturn, hdistinct,
    fun i => blocker_iterate_occupied w h hw hh s hj.2 p hp' i.val⟩

/-- G1 necessity, for the executable torus's actual occupied-cell count. -/
theorem jam_carCount_lower_bound (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h))
    (hj : Jam (eastDirection w h hw) (northDirection w h hh) s) :
    min w h ≤ carCount w h s := by
  obtain ⟨_, _, _, hside, hcount, _⟩ := jam_has_simple_blocker_cycle w h hw hh s hj
  exact Nat.le_trans hside hcount

/-- The same G1 bound in terms of the kernel's existing executable species sums. -/
theorem jam_speciesCount_lower_bound (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h))
    (hj : Jam (eastDirection w h hw) (northDirection w h hh) s) :
    min w h ≤ speciesCount w h .east s + speciesCount w h .north s := by
  rw [← carCount_eq_speciesCount]
  exact jam_carCount_lower_bound w h hw hh s hj

/-- A torus with fewer than min(W,H) cars cannot ever reach a nonempty frozen
state. This does not assert that every car eventually moves at every phase. -/
theorem few_cars_never_jam (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (hcount : carCount w h s < min w h) (t : Nat) :
    ¬ Jam (eastDirection w h hw) (northDirection w h hh)
      (iterate (torusStep w h hw hh) t s) := by
  intro hj
  have hbound := jam_carCount_lower_bound w h hw hh _ hj
  rw [iterate_torusStep_carCount] at hbound
  omega

/-- Exact minimum jam size, expressed as a budget. This does not replace the
separate construction of a jam with every exact count above the minimum. -/
theorem exists_jam_at_most_iff (w h : Nat) (hw : 0 < w) (hh : 0 < h) (n : Nat) :
    (∃ s : Config (Position w h),
      Jam (eastDirection w h hw) (northDirection w h hh) s ∧ carCount w h s ≤ n) ↔
      min w h ≤ n := by
  constructor
  · rintro ⟨s, hj, hn⟩
    exact Nat.le_trans (jam_carCount_lower_bound w h hw hh s hj) hn
  · intro hn
    obtain ⟨s, hj, hcount⟩ := exists_minimum_jam w h hw hh
    exact ⟨s, hj, by rw [hcount]; exact hn⟩

end BML
