import BML.TrafficEvents

/-!
# A checked alternating vacancy with no tagged service

This is an all-time run of the finite event kernel. Tag 0 stays in cell 0;
tag 1 exits cell 1 on even half-steps and is admitted there on odd half-steps.
The only possible hop of tag 0 is horizontal. Consequently every vacancy
occurs on the wrong movement phase. The run leaves a vacant checkpoint
after every departure, satisfies a safe-cell rank certificate, and still
violates opportunity fairness and every finite R2 service cap.

The cell-1 menu includes its self-loop and EXIT, as in the production toy.
CLASSIC pre-step vacancy never licenses that self-hop. The production
correspondence script checks finite prefixes; this module does not prove a
JavaScript or pseudorandom-generator semantics.
-/
namespace BML.TrafficObstruction

open TrafficEvents

abbrev Cell := Fin 2
abbrev Tag := Fin 2

def routes : Routes 2 := fun _ c => if c.val = 0 then [some 1] else [some 1, none]
def entries : Cell → Bool := fun c => c.val == 1

private def evenPositions : Positions 2 2 := fun k => some k
private def oddPositions : Positions 2 2 := fun k => if k.val = 0 then some 0 else none
private def noPrevious : Positions 2 2 := fun _ => none

def evenState : State 2 2 := stateOfChecked evenPositions noPrevious (by decide)
def oddState : State 2 2 := stateOfChecked oddPositions noPrevious (by decide)

def evenEvents : Tag → Event Cell := fun k =>
  if k.val = 0 then .stay (some 0) else .exit 1

def oddEvents : Tag → Event Cell := fun k =>
  if k.val = 0 then .stay (some 0) else .admit 1

theorem even_accepted : checkBatch evenState routes entries evenEvents = true := by decide
theorem odd_accepted : checkBatch oddState routes entries oddEvents = true := by decide

private theorem state_ext {a b : State cells cars}
    (positions : ∀ k, a.pos k = b.pos k) (previous : ∀ k, a.prev k = b.prev k) : a = b := by
  cases a with
  | mk ap av ae =>
    cases b with
    | mk bp bv be =>
      have hp : ap = bp := funext positions
      have hv : av = bv := funext previous
      subst bp
      subst bv
      rfl

theorem even_step : applyBatch evenState routes entries evenEvents even_accepted = oddState := by
  apply state_ext <;> decide

theorem odd_step : applyBatch oddState routes entries oddEvents odd_accepted = evenState := by
  apply state_ext <;> decide

def state (t : Nat) : State 2 2 := if t % 2 = 0 then evenState else oddState
def events (t : Nat) : Tag → Event Cell := if t % 2 = 0 then evenEvents else oddEvents

theorem accepted (t : Nat) : checkBatch (state t) routes entries (events t) = true := by
  by_cases even : t % 2 = 0
  · simpa only [state, events, ite_eq_left even] using even_accepted
  · simpa only [state, events, ite_eq_right even] using odd_accepted

theorem evolves (t : Nat) :
    state (t + 1) = applyBatch (state t) routes entries (events t) (accepted t) := by
  by_cases even : t % 2 = 0
  · have odd : (t + 1) % 2 ≠ 0 := by omega
    simpa only [state, events, ite_eq_left even, ite_eq_right odd] using even_step.symm
  · have nextEven : (t + 1) % 2 = 0 := by omega
    simpa only [state, events, ite_eq_right even, ite_eq_left nextEven] using odd_step.symm

/-- Both event batches are checked and their computed next states are the
next states of the infinite orbit. -/
def run : Run 2 2 where
  routes := routes
  entries := entries
  state := state
  events := events
  accepted := accepted
  evolves := evolves

def batches (start : Nat) : Nat → List (Tag → Event Cell)
  | 0 => []
  | length + 1 => events start :: batches (start + 1) length

/-- Every finite prefix of the infinite orbit is accepted by the same
replay relation used by executable event correspondence. -/
theorem accepted_prefix (start length : Nat) :
    AcceptedHistory routes entries (state start) (batches start length) (state (start + length)) := by
  induction length generalizing start with
  | zero => simpa [batches] using AcceptedHistory.nil (state start)
  | succ length ih =>
    apply AcceptedHistory.cons (accepted start)
    rw [← evolves start]
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (start + 1)

theorem replay_prefix (start length : Nat) :
    replay? routes entries (state start) (batches start length) = some (state (start + length)) :=
  replay?_complete (accepted_prefix start length)

theorem focal_always_present (t : Nat) : (run.state t).pos 0 = some 0 := by
  by_cases even : t % 2 = 0 <;>
    simp [run, state, even, evenState, oddState, stateOfChecked, evenPositions, oddPositions]

theorem focal_never_moves (t : Nat) : (run.events t 0).moves = false := by
  by_cases even : t % 2 = 0 <;>
    simp [run, events, even, evenEvents, oddEvents, Event.moves]

theorem lower_exits_at_even (n : Nat) : run.events (2 * n) 1 = .exit 1 := by
  have even : (2 * n) % 2 = 0 := by omega
  simp [run, events, even, evenEvents]

theorem lower_admitted_at_odd (n : Nat) : run.events (2 * n + 1) 1 = .admit 1 := by
  simp [run, events, oddEvents]

private theorem even_lower_occupied : evenState.occ 1 = some 1 := by decide
private theorem odd_lower_vacant : oddState.occ 1 = none := by decide

theorem lower_vacant_iff_odd (t : Nat) : (run.state t).occ 1 = none ↔ t % 2 = 1 := by
  by_cases even : t % 2 = 0
  · simp only [run, state, ite_eq_left even, even_lower_occupied, Option.some_ne_none, false_iff]
    omega
  · simp only [run, state, ite_eq_right even, odd_lower_vacant, true_iff]
    omega

/-- Every two-checkpoint window contains an actual model vacancy. -/
theorem vacancy_every_two (t : Nat) : ∃ i < 2, (run.state (t + i)).occ 1 = none := by
  by_cases odd : t % 2 = 1
  · exact ⟨0, by decide, (lower_vacant_iff_odd _).mpr (by simpa using odd)⟩
  · exact ⟨1, by decide, (lower_vacant_iff_odd _).mpr (by omega)⟩

/-- The horizontal movement phase and vacancy never coincide. This uses
green duration one, where no additional signal gate excludes a phase. -/
theorem no_joint_vacancy_and_phase (t : Nat) :
    ¬ ((run.state t).occ 1 = none ∧ t % 2 = 0) := by
  rintro ⟨vacant, phase⟩
  have odd := (lower_vacant_iff_odd t).mp vacant
  omega

def plans (_t : Nat) (k : Tag) : LaneDeadlock.Plan Cell :=
  ⟨if k.val = 0 then some 1 else none, .east, []⟩

def trace : RouteProgress.Trace Cell Tag := run.toRouteTrace plans

/-- Source vacancy follows from accepted event batches, not an extra
promise attached to this counterexample. -/
theorem leaves_vacancy : trace.LeavesVacancy := run.toRouteTrace_leaves_vacancy plans

theorem trace_focal_never (t : Nat) : ¬ trace.moves t 0 := by
  change (run.events t 0).moves ≠ true
  rw [focal_never_moves]
  decide

theorem trace_clear_lower (t : Nat) : trace.ClearAt (some 1) t ↔ t % 2 = 1 :=
  lower_vacant_iff_odd t

def rank (c : Cell) : Option Nat := some (if c.val = 0 then 1 else 0)
def turns (c : Cell) : List (List (Option Cell)) := [routes none c]

theorem rank_certificate : RouteTrap.checkRanks (List.finRange 2) turns rank = true := by decide

theorem follows_arrivals : trace.FollowsArrivals (List.finRange 2) turns := by
  intro t k c pos
  constructor
  · exact List.mem_finRange c
  · change (run.state t).menu routes k ∈ turns c
    change (run.state t).pos k = some c at pos
    simp [State.menu, pos, turns, routes]

theorem focal_has_rank_one : rank 0 = some 1 := rfl
theorem lower_has_rank_zero : rank 1 = some 0 := rfl

def onStreet (t : Nat) : List Tag :=
  (List.finRange 2).filter fun k => ((run.state t).pos k).isSome

/-- The actual on-street tag set has an empty greatest structural trap at
every checkpoint, including checkpoints with the returning tag outside. -/
theorem empty_structural_trap (t : Nat) :
    RouteTrap.greatestTrap (onStreet t)
      (RouteTrap.blockerMenus (trace.state t) (fun k => (trace.menu t k).map Option.toList)) = [] := by
  apply RouteTrap.greatestTrap_empty_of_all_ranked
    (roads := List.finRange 2) (turns := turns) (rank := rank)
  · intro k member
    have present := (List.mem_filter.mp member).2
    cases pos : (run.state t).pos k with
    | none => simp [pos] at present
    | some c => exact ⟨c, pos⟩
  · intro k _ c pos
    obtain ⟨road, menu⟩ := follows_arrivals t k c pos
    refine ⟨road, trace.menu t k, menu, ?_⟩
    intro d offered
    exact List.mem_map.mpr ⟨d, offered, rfl⟩
  · exact rank_certificate
  · intro c _
    simp [RouteTrap.certified, rank]

/-- The safe-cell certificate and real checkpoint vacancies do not imply
the opportunity fairness used by the qualitative R2 theorem. -/
theorem not_opportunity_fair : ¬ trace.OpportunityFair := by
  intro fair
  have atStart : (trace.state 0).pos 0 = some 0 := focal_always_present 0
  have offered : some 1 ∈ trace.menu 0 0 := by decide
  have recurrent : ∀ start ≥ 0, ∃ u ≥ start, trace.ClearAt (some 1) u := by
    intro start _
    obtain ⟨i, _, vacant⟩ := vacancy_every_two start
    exact ⟨start + i, Nat.le_add_right _ _, vacant⟩
  obtain ⟨i, moved⟩ := fair 0 0 0 (some 1) atStart offered recurrent
  exact trace_focal_never i (by simpa using moved)

/-- For every finite cap K, the first 2K half-steps already contain K
distinct legal vacancies while the focal tag never moves. -/
theorem no_bounded_service (K : Nat) : ¬ trace.BoundedService (2 * K) K := by
  intro service
  let slots : Fin K → Fin (2 * K) := fun i => ⟨2 * i.val + 1, by omega⟩
  have ordered : ∀ i j, i < j → slots i < slots j := by
    intro i j before
    change 2 * i.val + 1 < 2 * j.val + 1
    omega
  refine service 0 (2 * K) 0 0 (some 1) (by omega) (focal_always_present 0) (by decide)
    (fun i _ => by simpa using trace_focal_never i) slots ordered ?_
  intro i
  apply (trace_clear_lower _).mpr
  dsimp [slots]
  omega

/-- Legacy priority counts unsuccessful requests, hence only the even
half-steps in this orbit. It is not elapsed stopped time. -/
def requestAge (t : Nat) : Nat := (t + 1) / 2

theorem requestAge_zero : requestAge 0 = 0 := rfl

theorem requestAge_step (t : Nat) :
    requestAge (t + 1) = requestAge t + if t % 2 = 0 then 1 else 0 := by
  unfold requestAge
  split <;> omega

end BML.TrafficObstruction
