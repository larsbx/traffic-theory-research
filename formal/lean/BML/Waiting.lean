import BML.Fixation
import BML.Gridlock

/-!
A finite wait forces a long occupied blocker prefix in an actual snapshot.
A prefix as long as the conserved population forces the waiting tag to stay
forever. Both species are tested at their own attempt phases.
-/
namespace BML

section Directions

variable {α : Type} (east north : Direction α)

/-- The same species is present at this site throughout a full-round window. -/
def CellStays (s : Config α) (sp : Species) (p : α) (start length : Nat) : Prop :=
  ∀ i < length, iterate (step east north) (start + i) s p = sp.cell

/-- An occupied sequence with one absorbing color is constant on one of
two windows of length `m` inside its first `2*m-1` observations. -/
private theorem stable_half_of_one_way (u : Nat → Cell) (absorbing other : Species)
    (different : other ≠ absorbing) (m : Nat) (positive : 0 < m)
    (occupied : ∀ i < 2 * m - 1, u i ≠ .empty)
    (persist : ∀ i, i + 1 < 2 * m - 1 → u i = absorbing.cell → u (i+1) = absorbing.cell) :
    (∀ i < m, u i = other.cell) ∨ (∀ i < m, u (m - 1 + i) = absorbing.cell) := by
  have propagate (j : Nat) (hj : u j = absorbing.cell) (i : Nat)
      (hi : j + i < 2 * m - 1) : u (j + i) = absorbing.cell := by
    induction i with
    | zero => simpa using hj
    | succ i ih => exact persist (j+i) (by omega) (ih (by omega))
  by_cases hmid : u (m-1) = absorbing.cell
  · exact Or.inr (fun i hi => propagate (m-1) hmid i (by omega))
  · left
    intro i hi
    have hn : u i ≠ absorbing.cell := by
      intro ha
      have h := propagate i ha (m - 1 - i) (by omega)
      exact hmid (by simpa only [show i + (m - 1 - i) = m - 1 by omega] using h)
    have ho := occupied i (by omega)
    cases absorbing <;> cases other <;> cases h : u i <;> simp_all [Species.cell]

theorem successor_stays_for_half (s : Config α) (sp : Species) (p : α)
    (start m : Nat) (positive : 0 < m) (stay : CellStays east north s sp p start (2*m)) :
    ∃ other offset, offset + m ≤ 2*m ∧
      CellStays east north s other (if sp = .east then east.next p else north.next p)
        (start+offset) m := by
  let board := fun i => iterate (step east north) (start+i) s
  have after (i : Nat) : board (i+1) = step east north (board i) := rfl
  have stopped (i : Nat) (hi : i < 2*m-1) :
      ¬ RoundCanMove east north sp (board i) p := by
    apply same_cell_no_round_move east north sp _ p (stay i (by omega))
    rw [← after i]
    exact stay (i+1) (by omega)
  cases sp with
  | east =>
    let u := fun i => board i (east.next p)
    have occupied (i : Nat) (hi : i < 2*m-1) : u i ≠ .empty :=
      fun hv => stopped i hi ⟨stay i (by omega), hv⟩
    have persist (i : Nat) (hi : i+1 < 2*m-1) (ha : u i = .north) : u (i+1) = .north :=
      step_north_of_occupied east north (board i) _ ha (occupied (i+1) hi)
    rcases stable_half_of_one_way u .north .east (by decide) m positive occupied persist with h | h
    · exact ⟨.east, 0, by omega, fun i hi => by simpa using h i hi⟩
    · exact ⟨.north, m-1, by omega, fun i hi => by
        simpa [u, board, Nat.add_assoc] using h i hi⟩
  | north =>
    let mid := fun i => halfStep east .east (board i)
    let u := fun i => mid i (north.next p)
    have occupied (i : Nat) (hi : i < 2*m-1) : u i ≠ .empty := by
      intro hv
      exact stopped i hi ⟨(other_species_unchanged east .east _ p .north
        (by decide) (by decide)).mpr (stay i (by omega)), hv⟩
    have nextEast (i : Nat) (he : u i = .east) : board (i+1) (north.next p) = .east :=
      (other_species_unchanged north .north (mid i) _ .east (by decide) (by decide)).mpr he
    have persist (i : Nat) (hi : i+1 < 2*m-1) (he : u i = .east) : u (i+1) = .east :=
      halfStep_own_of_occupied east .east (board (i+1)) _ (nextEast i he) (occupied (i+1) hi)
    rcases stable_half_of_one_way u .east .north (by decide) m positive occupied persist with h | h
    · refine ⟨.north, 0, by omega, fun i hi => ?_⟩
      simpa [board, Species.cell] using (other_species_unchanged east .east (board i) _ .north
        (by decide) (by decide)).mp (h i hi)
    · refine ⟨.east, m, by omega, fun i hi => ?_⟩
      have he := nextEast (m-1+i) (h i hi)
      simpa [board, Species.cell, Nat.add_assoc, show m - 1 + i + 1 = m + i by omega] using he

end Directions

section Torus

variable {w h : Nat} (hw : 0 < w) (hh : 0 < h)

local notation "F" => torusStep w h hw hh
local notation "E" => eastDirection w h hw
local notation "N" => northDirection w h hh

/-- `2^d` consecutive full-round snapshots of a stationary car force an
occupied direct blocker walk of `d` edges from that site in the window. -/
theorem occupied_path_during_wait (s : Config (Position w h)) (d : Nat)
    (sp : Species) (p : Position w h) (start : Nat)
    (stay : CellStays E N s sp p start (2^d)) :
    ∃ offset < 2^d, ∀ k ≤ d,
      let u := iterate F (start+offset) s
      u (iterate (blocker w h hw hh u) k p) ≠ .empty := by
  induction d generalizing sp p start with
  | zero =>
    refine ⟨0, by decide, fun k hk => ?_⟩
    have he : k = 0 := by omega
    subst k
    exact fun hz => sp.cell_ne_empty ((stay 0 (by decide)).symm.trans hz)
  | succ d ih =>
    have hpow : 2^(d+1) = 2*2^d := by rw [Nat.pow_succ, Nat.mul_comm]
    obtain ⟨other, offset, hbound, hnext⟩ := successor_stays_for_half E N s sp p
      start (2^d) (by simp [Nat.pow_pos_iff]) (hpow ▸ stay)
    obtain ⟨j, hj, hpath⟩ := ih other _ (start+offset) hnext
    have hinside : offset+j < 2^(d+1) := by omega
    let u := iterate F (start+(offset+j)) s
    have color : u p = sp.cell := stay (offset+j) hinside
    have edge : blocker w h hw hh u p = (if sp = .east then (E).next p else (N).next p) := by
      cases sp <;> simp [blocker, color, Species.cell]
    refine ⟨offset+j, hinside, fun k hk => ?_⟩
    cases k with
    | zero => exact fun hz => sp.cell_ne_empty (color.symm.trans hz)
    | succ k =>
      change u (iterate (blocker w h hw hh u) (k+1) p) ≠ .empty
      rw [Nat.add_comm k 1, iterate_add]
      have hstep : iterate (blocker w h hw hh u) 1 p = blocker w h hw hh u p := rfl
      rw [hstep, edge]
      simpa only [Nat.add_assoc] using hpath k (by omega)

/-- A prefix with one more occupied vertex than cars already supplies an
occupied successor-closed set containing the root. -/
private theorem blocker_core_of_prefix (s : Config (Position w h)) (p : Position w h)
    (path : ∀ i ≤ carCount w h s, s (iterate (blocker w h hw hh s) i p) ≠ .empty) :
    ∃ core : BlockingCore E N s, core.sites p := by
  let walk := blocker w h hw hh s
  let m := carCount w h s
  obtain ⟨i, j, hij, hj, same⟩ := orbit_prefix_repeats walk (occupiedCells w h s) p
    (fun k hk => (mem_occupiedCells w h s _).mpr (path k hk))
  change j ≤ m at hj
  have always (k : Nat) : s (iterate walk k p) ≠ .empty := by
    induction k using Nat.strongRecOn with
    | ind k ih =>
      by_cases hk : k ≤ m
      · exact path k hk
      have eq := congrArg (iterate walk (k-j)) same
      rw [← iterate_add, ← iterate_add, show j + (k-j) = k by omega] at eq
      rw [← eq]
      exact ih (i+(k-j)) (by omega)
  let core : BlockingCore E N s := {
    sites := fun q => ∃ k, iterate walk k p = q
    occupied := by
      rintro q ⟨k, rfl⟩
      exact always k
    east_closed := by
      rintro q ⟨k, rfl⟩ he
      refine ⟨k+1, ?_⟩
      change blocker w h hw hh s (iterate walk k p) = _
      simp [blocker, he]
    north_closed := by
      rintro q ⟨k, rfl⟩ hn
      refine ⟨k+1, ?_⟩
      change blocker w h hw hh s (iterate walk k p) = _
      simp [blocker, hn] }
  exact ⟨core, 0, rfl⟩

/-- A wait of `2^m-1` rounds, where `m` is the population, already puts the
stationary car on a permanent core within those `2^m` snapshots. -/
theorem blocking_core_during_wait (s : Config (Position w h))
    (sp : Species) (p : Position w h) (start : Nat)
    (stay : CellStays E N s sp p start (2^carCount w h s)) :
    ∃ offset < 2^carCount w h s,
      ∃ core : BlockingCore E N (iterate F (start+offset) s), core.sites p := by
  obtain ⟨offset, ho, path⟩ := occupied_path_during_wait hw hh s (carCount w h s) sp p start stay
  refine ⟨offset, ho, blocker_core_of_prefix hw hh _ p ?_⟩
  simpa only [iterate_torusStep_carCount] using path

/-- Outside the initial full-lane event, the finite wait supplies permanent
blocking sites on every route by the end of the window. -/
theorem route_cover_during_wait (s : Config (Position w h))
    (sp : Species) (p : Position w h) (start : Nat)
    (stay : CellStays E N s sp p start (2^carCount w h s))
    (noLane : ¬ HasFullMonochromaticLane s) :
    ∃ offset < 2^carCount w h s,
      _root_.Nonempty (RouteCover w h hw hh (iterate F (start+offset) s)) := by
  obtain ⟨offset, within, core, member⟩ := blocking_core_during_wait hw hh s sp p start stay
  refine ⟨offset, within, core.routeCover_of_no_full_lane ⟨p, member⟩ ?_⟩
  exact fun lane => noLane ((hasFullMonochromaticLane_iterate_iff hw hh s _).mp lane)

theorem tagged_wait_iff_stays_forever (s : Config (Position w h))
    (sp : Species) (origin : Position w h) (hcar : s origin = sp.cell) (start : Nat) :
    (∀ i < 2^carCount w h s, carTrace E N sp s (start+i) origin = carTrace E N sp s start origin) ↔
      ∀ i, carTrace E N sp s (start+i) origin = carTrace E N sp s start origin := by
  refine ⟨?_, fun all i _ => all i⟩
  intro wait
  let p := carTrace E N sp s start origin
  have stay : CellStays E N s sp p start (2^carCount w h s) := by
    intro i hi
    simpa only [wait i hi] using carTrace_preserves_car E N sp s origin hcar (start+i)
  obtain ⟨offset, ho, core, member⟩ := blocking_core_during_wait hw hh s sp p start stay
  have forever (i : Nat) : carTrace E N sp s (start+offset+i) origin = p := by
    induction i with
    | zero => simpa using wait offset ho
    | succ i ih =>
      change roundTransport E N sp (iterate F (start+offset+i) s)
        (carTrace E N sp s (start+offset+i) origin) = p
      rw [ih]
      apply roundTransport_eq_of_no_round_move E N sp _ p
      rw [iterate_add]
      exact core.no_round_move _ (core.persists i) sp p member
  intro i
  by_cases earlier : i < offset
  · exact wait i (by omega)
  · simpa only [show start+offset+(i-offset) = start+i by omega] using forever (i-offset)

end Torus

end BML
