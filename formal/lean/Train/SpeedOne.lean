import Train.FreeFlow
import Train.DiagonalDynamics
import Train.Diagonals
import Train.Torus

namespace BML.Train

/-- The observable maximum movement count agrees with movement of every car. -/
theorem fullSpeed_iff_all_cars_move (w h : Nat)
    (east north : CyclicDirection (Position w h)) (s : Config (Position w h)) :
    FullSpeed w h east north s ↔ ∀ p, s p ≠ .empty → FullCanMove east north s p := by
  rw [fullSpeed_iff_all_phases_move]
  constructor
  · rintro ⟨he, hn⟩ p hp
    cases hc : s p with
    | empty => exact False.elim (hp hc)
    | east => simpa only [FullCanMove, hc] using he p hc
    | north =>
      have hnc : halfStep east .east s p = .north :=
        (other_species_unchanged east .east s p .north (by decide) (by decide)).mpr hc
      simpa only [FullCanMove, hc] using hn p hnc
  · intro hall
    constructor
    · intro p hp
      simpa only [FullCanMove, hp] using hall p (by rw [hp]; decide)
    · intro p hp
      have hnc : s p = .north :=
        (other_species_unchanged east .east s p .north (by decide) (by decide)).mp hp
      simpa only [FullCanMove, hnc] using hall p (by rw [hnc]; decide)

/-- Original labels cover exactly the current cars, so eventual label movement
can be expressed by the actual numerical counter at each complete update. -/
theorem fullSpeed_at_time_iff_tags (w h : Nat)
    (east north : CyclicDirection (Position w h)) (s : Config (Position w h)) (t : Nat) :
    FullSpeed w h east north (BML.iterate (step east north) t s) ↔
      ∀ p, p ∈ occupiedPositions s →
        FullCanMove east north (BML.iterate (step east north) t s)
          (trace east north s t p) := by
  rw [fullSpeed_iff_all_cars_move]
  constructor
  · intro hall p hp
    have ho := (mem_occupiedPositions s p).mp hp
    apply hall
    rw [trace_cell east north s t p ho]
    exact ho
  · intro hall q hq
    obtain ⟨p, hp, htrace⟩ := trace_coverage east north s t q hq
    simpa only [htrace] using hall p ((mem_occupiedPositions s p).mpr hp)

theorem eventuallyFullSpeed_iff_tags (w h : Nat)
    (east north : CyclicDirection (Position w h)) (s : Config (Position w h)) :
    EventuallyFullSpeed w h east north s ↔
      ∃ T, ∀ t, T ≤ t → ∀ p, p ∈ occupiedPositions s →
        FullCanMove east north (BML.iterate (step east north) t s)
          (trace east north s t p) := by
  simp only [EventuallyFullSpeed, fullSpeed_at_time_iff_tags]

/-- Austin–Benjamini's sparse-square TRAIN theorem for the actual complete
east-then-north update.  The empty configuration is included. -/
theorem sparse_square_eventually_fullSpeed (n : Nat) (hn : 0 < n)
    (s : Config (Position n n)) (hsparse : 2 * population s < n) :
    EventuallyFullSpeed n n (eastRing n n hn) (northRing n n hn) s := by
  apply (eventuallyFullSpeed_iff_tags n n (eastRing n n hn) (northRing n n hn) s).mpr
  obtain ⟨T, hT⟩ := Diagonals.sparse_eventual_stable n hn
    (occupiedPositions s) (correctedTrace n hn s)
    (corrected_trace_step_cases n hn s)
    (corrected_trace_release n hn s)
    (by simpa only [population] using hsparse)
  refine ⟨T, ?_⟩
  intro t ht p hp
  have hpos : 0 < population s := List.length_pos_of_mem hp
  have hlarge : 1 < n := by omega
  exact (corrected_trace_stable_iff_move n hn hlarge s t p hp).mp (hT t ht p hp)

/-- The speed-one conclusion in the executable kernel's movement-counter
interface: eventually every complete update moves the initial number of cars. -/
theorem sparse_square_moves_equal_population (n : Nat) (hn : 0 < n)
    (s : Config (Position n n)) (hsparse : 2 * population s < n) :
    ∃ T, ∀ t, T ≤ t →
      totalMoveCount n n (eastRing n n hn) (northRing n n hn)
        (BML.iterate (torusStep n n hn hn) t s) = population s := by
  exact (eventuallyFullSpeed_iff_moves_equal_initial_population n n
    (eastRing n n hn) (northRing n n hn) s).mp
      (sparse_square_eventually_fullSpeed n hn s hsparse)

end BML.Train
