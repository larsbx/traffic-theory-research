import BML.RouteProgress

/-!
# Finite traffic objects and checked event batches

This is an executable event model, not a parser for uncertain observations.
`none` in a model state means known outside the modeled road network. A
missing trajectory observation must not be imported as `none`.

One event record is supplied for each finite model tag. A recycled simulator
tag need not denote the same physical vehicle or trip after admission;
matching source-scoped observed identities requires an explicit lifecycle
mapping. The combined `exitAdmit` constructor records both stages of a
same-interval exit and readmission. Hops and admissions use pre-step vacant
cells; a departing source cannot be refilled within its event batch.
-/
namespace BML.TrafficEvents

inductive Event (Cell : Type) where
  | stay (claimed : Option Cell)
  | hop (source target : Cell)
  | exit (source : Cell)
  | admit (target : Cell)
  | exitAdmit (source target : Cell)
  deriving DecidableEq, Repr

variable {Cell : Type}

def Event.before : Event Cell → Option Cell
  | .stay p => p
  | .hop p _ | .exit p | .exitAdmit p _ => some p
  | .admit _ => none

def Event.after : Event Cell → Option Cell
  | .stay p => p
  | .hop _ q | .admit q | .exitAdmit _ q => some q
  | .exit _ => none

def Event.nextPrev (old : Option Cell) : Event Cell → Option Cell
  | .stay _ => old
  | .hop p _ => some p
  | .exit _ | .admit _ | .exitAdmit _ _ => none

def Event.moves : Event Cell → Bool
  | .hop _ _ | .exit _ | .exitAdmit _ _ => true
  | .stay _ | .admit _ => false

def Event.admitted : Event Cell → Bool
  | .admit _ | .exitAdmit _ _ => true
  | _ => false

def Event.departed : Event Cell → Bool
  | .exit _ | .exitAdmit _ _ => true
  | _ => false

def Event.moveCount (e : Event Cell) : Nat := if e.moves then 1 else 0
def Event.admissionCount (e : Event Cell) : Nat := if e.admitted then 1 else 0

/-- Only events that actually enter a cell need its pre-step vacancy. -/
def Event.arrivalTarget : Event Cell → Option Cell
  | .hop _ q | .admit q | .exitAdmit _ q => some q
  | .stay _ | .exit _ => none

def workAt (height : Cell → Nat) (p : Option Cell) : Nat := p.elim 0 height

/-- Work descent is an additional checked policy; it is not inferred from
the existence of one descending safe-cell option. -/
def Event.WorkAllowed (height : Cell → Nat) (D : Nat) : Event Cell → Prop
  | .stay _ => True
  | .hop p q => height q < height p
  | .exit p => 0 < height p
  | .admit q => height q ≤ D
  | .exitAdmit p q => 0 < height p ∧ height q ≤ D

theorem Event.work_inequality (height : Cell → Nat) (D : Nat) (e : Event Cell)
    (allowed : e.WorkAllowed height D) :
    workAt height e.after + e.moveCount ≤
      workAt height e.before + D * e.admissionCount := by
  cases e <;> simp_all [WorkAllowed, workAt, before, after, moveCount, admissionCount, moves, admitted]
  all_goals omega

theorem Event.exit_admit_counts (p q : Cell) :
    (Event.exitAdmit p q).moveCount = 1 ∧ (Event.exitAdmit p q).admissionCount = 1 := by
  simp [moveCount, admissionCount, moves, admitted]

/-- Position endpoints do not identify the event history. A hop and an
exit followed by admission share endpoints but have different boundary
admission counts. An observational adapter needs independent event evidence. -/
theorem endpoints_do_not_determine_admissions (p q : Cell) :
    (Event.hop p q).before = (Event.exitAdmit p q).before ∧
    (Event.hop p q).after = (Event.exitAdmit p q).after ∧
    (Event.hop p q).admissionCount ≠ (Event.exitAdmit p q).admissionCount := by
  simp [Event.before, Event.after, Event.admissionCount, Event.admitted]

abbrev Positions (cells cars : Nat) := Fin cars → Option (Fin cells)

def Exclusive (pos : Positions cells cars) : Prop :=
  ∀ k j c, pos k = some c → pos j = some c → k = j

/-- Check occupied-cell exclusivity over every pair of finite model tags. -/
def checkState (pos : Positions cells cars) : Bool :=
  (List.finRange cars).all fun k => (List.finRange cars).all fun j =>
    match pos k with
    | none => true
    | some c => if pos j = some c then decide (k = j) else true

theorem checkState_sound {pos : Positions cells cars} (accepted : checkState pos = true) :
    Exclusive pos := by
  intro k j c atK atJ
  have row := List.all_eq_true.mp accepted k (List.mem_finRange k)
  have entry := List.all_eq_true.mp row j (List.mem_finRange j)
  simpa [atK, atJ] using entry

theorem checkState_complete {pos : Positions cells cars} (exclusive : Exclusive pos) :
    checkState pos = true := by
  apply List.all_eq_true.mpr
  intro k _
  apply List.all_eq_true.mpr
  intro j _
  cases atK : pos k with
  | none => simp
  | some c =>
    by_cases atJ : pos j = some c
    · have same := exclusive k j c atK atJ
      simp [atJ, same]
    · simp [atJ]

structure State (cells cars : Nat) where
  pos : Positions cells cars
  prev : Positions cells cars
  exclusive : Exclusive pos

def stateOfChecked (pos prev : Positions cells cars) (accepted : checkState pos = true) :
    State cells cars := ⟨pos, prev, checkState_sound accepted⟩

def State.occ (s : State cells cars) (c : Fin cells) : Option (Fin cars) :=
  (List.finRange cars).find? (fun k => s.pos k == some c)

/-- Occupancy is computed from finite positions; its inverse relationship
is proved, rather than a second unchecked array supplied by an adapter. -/
theorem State.occ_iff_pos (s : State cells cars) (c : Fin cells) (k : Fin cars) :
    s.occ c = some k ↔ s.pos k = some c := by
  constructor
  · intro found
    simpa [State.occ] using List.find?_some found
  · intro atK
    cases found : s.occ c with
    | none =>
      have absent := List.find?_eq_none.mp found k (List.mem_finRange k)
      simp [atK] at absent
    | some j =>
      have atJ : s.pos j = some c := by simpa using List.find?_some found
      have same := s.exclusive j k c atJ atK
      simp [same]

def State.toSnapshot (s : State cells cars)
    (plan : Fin cars → LaneDeadlock.Plan (Fin cells)) : LaneDeadlock.Snapshot (Fin cells) (Fin cars) :=
  { pos := s.pos, occ := s.occ, plan := plan, occ_iff_pos := s.occ_iff_pos }

/-- Legal menus are indexed by arrival and current cell. A stationary car
therefore keeps the same menu, even if its committed route changes. -/
abbrev Routes (cells : Nat) := Option (Fin cells) → Fin cells → List (Option (Fin cells))

def State.menu (s : State cells cars) (routes : Routes cells) (k : Fin cars) : List (Option (Fin cells)) :=
  match s.pos k with
  | none => []
  | some c => routes (s.prev k) c

def Event.routeAllowed (menu : List (Option (Fin cells))) (entries : Fin cells → Bool) :
    Event (Fin cells) → Bool
  | .stay _ => true
  | .hop _ q => decide (some q ∈ menu)
  | .exit _ => decide (none ∈ menu)
  | .admit q => entries q
  | .exitAdmit _ q => decide (none ∈ menu) && entries q

def checkEvent (s : State cells cars) (routes : Routes cells) (entries : Fin cells → Bool)
    (k : Fin cars) (e : Event (Fin cells)) : Bool :=
  (e.before == s.pos k) && e.routeAllowed (s.menu routes k) entries &&
    (e.arrivalTarget.elim true fun q => (s.occ q).isNone)

def checkBatch (s : State cells cars) (routes : Routes cells) (entries : Fin cells → Bool)
    (events : Fin cars → Event (Fin cells)) : Bool :=
  checkState (fun k => (events k).after) &&
    (List.finRange cars).all (fun k => checkEvent s routes entries k (events k))

theorem checked_event {s : State cells cars} {routes : Routes cells} {entries : Fin cells → Bool}
    {events : Fin cars → Event (Fin cells)} (accepted : checkBatch s routes entries events = true)
    (k : Fin cars) : checkEvent s routes entries k (events k) = true := by
  have each := (Bool.and_eq_true_iff.mp accepted).2
  exact List.all_eq_true.mp each k (List.mem_finRange k)

theorem checkEvent_source {s : State cells cars} {routes : Routes cells} {entries : Fin cells → Bool}
    {k : Fin cars} {e : Event (Fin cells)} (accepted : checkEvent s routes entries k e = true) :
    e.before = s.pos k := by
  simpa only [beq_iff_eq] using (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp accepted).1).1

theorem checkEvent_route {s : State cells cars} {routes : Routes cells} {entries : Fin cells → Bool}
    {k : Fin cars} {e : Event (Fin cells)} (accepted : checkEvent s routes entries k e = true) :
    e.routeAllowed (s.menu routes k) entries = true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp accepted).1).2

theorem checkEvent_vacant {s : State cells cars} {routes : Routes cells} {entries : Fin cells → Bool}
    {k : Fin cars} {e : Event (Fin cells)} (accepted : checkEvent s routes entries k e = true)
    {q : Fin cells} (arrival : e.arrivalTarget = some q) : s.occ q = none := by
  have clear := (Bool.and_eq_true_iff.mp accepted).2
  simpa [arrival] using clear

def applyBatch (s : State cells cars) (routes : Routes cells) (entries : Fin cells → Bool)
    (events : Fin cars → Event (Fin cells)) (accepted : checkBatch s routes entries events = true) :
    State cells cars where
  pos k := (events k).after
  prev k := (events k).nextPrev (s.prev k)
  exclusive := checkState_sound (Bool.and_eq_true_iff.mp accepted).1

/-- Executable rejection is part of the transition, rather than an
unverified caller promise that a proposed event array is valid. -/
def step? (s : State cells cars) (routes : Routes cells) (entries : Fin cells → Bool)
    (events : Fin cars → Event (Fin cells)) : Option (State cells cars) :=
  if accepted : checkBatch s routes entries events = true then
    some (applyBatch s routes entries events accepted)
  else none

theorem step?_accepted {s next : State cells cars} {routes : Routes cells}
    {entries : Fin cells → Bool} {events : Fin cars → Event (Fin cells)}
    (result : step? s routes entries events = some next) :
    ∃ accepted : checkBatch s routes entries events = true,
      next = applyBatch s routes entries events accepted := by
  unfold step? at result
  split at result
  next accepted => exact ⟨accepted, (Option.some.inj result).symm⟩
  next rejected => contradiction

theorem rejects_false_source {s : State cells cars} {routes : Routes cells}
    {entries : Fin cells → Bool} {events : Fin cars → Event (Fin cells)}
    {k : Fin cars} (falseSource : (events k).before ≠ s.pos k) :
    step? s routes entries events = none := by
  unfold step?
  split
  next accepted => exact (falseSource (checkEvent_source (checked_event accepted k))).elim
  next rejected => rfl

/-- Even a cell whose occupant leaves in this batch is unavailable to
admission or a CLASSIC hop. This rejects same-step source refill. -/
theorem rejects_occupied_arrival {s : State cells cars} {routes : Routes cells}
    {entries : Fin cells → Bool} {events : Fin cars → Event (Fin cells)}
    {k j : Fin cars} {q : Fin cells} (arrival : (events k).arrivalTarget = some q)
    (occupied : s.pos j = some q) : step? s routes entries events = none := by
  unfold step?
  split
  next accepted =>
    have empty := checkEvent_vacant (checked_event accepted k) arrival
    have full := (s.occ_iff_pos q j).mpr occupied
    rw [full] at empty
    contradiction
  next rejected => rfl

theorem rejects_post_collision {s : State cells cars} {routes : Routes cells}
    {entries : Fin cells → Bool} {events : Fin cars → Event (Fin cells)}
    {k j : Fin cars} {q : Fin cells} (different : k ≠ j)
    (first : (events k).after = some q) (second : (events j).after = some q) :
    step? s routes entries events = none := by
  unfold step?
  split
  next accepted =>
    exact (different ((applyBatch s routes entries events accepted).exclusive k j q first second)).elim
  next rejected => rfl

def replay? (routes : Routes cells) (entries : Fin cells → Bool) :
    State cells cars → List (Fin cars → Event (Fin cells)) → Option (State cells cars)
  | initial, [] => some initial
  | initial, batch :: rest =>
    (step? initial routes entries batch).bind fun next => replay? routes entries next rest

/-- A finite accepted history includes exactly the event batches and
intermediate computed states; it makes no claim about unobserved future time. -/
inductive AcceptedHistory (routes : Routes cells) (entries : Fin cells → Bool) :
    State cells cars → List (Fin cars → Event (Fin cells)) → State cells cars → Prop where
  | nil (s : State cells cars) : AcceptedHistory routes entries s [] s
  | cons {s final : State cells cars} {batch : Fin cars → Event (Fin cells)}
      {rest : List (Fin cars → Event (Fin cells))}
      (accepted : checkBatch s routes entries batch = true)
      (tail : AcceptedHistory routes entries (applyBatch s routes entries batch accepted) rest final) :
      AcceptedHistory routes entries s (batch :: rest) final

theorem replay?_sound {routes : Routes cells} {entries : Fin cells → Bool}
    {initial final : State cells cars} {batches : List (Fin cars → Event (Fin cells))}
    (result : replay? routes entries initial batches = some final) :
    AcceptedHistory routes entries initial batches final := by
  induction batches generalizing initial with
  | nil =>
    have same : initial = final := by simpa [replay?] using result
    subst final
    exact .nil initial
  | cons batch rest ih =>
    cases step : step? initial routes entries batch with
    | none => simp [replay?, step] at result
    | some next =>
      obtain ⟨accepted, same⟩ := step?_accepted step
      have remaining : replay? routes entries next rest = some final := by
        simpa [replay?, step] using result
      have tail := ih remaining
      rw [same] at tail
      exact .cons accepted tail

theorem replay?_complete {routes : Routes cells} {entries : Fin cells → Bool}
    {initial final : State cells cars} {batches : List (Fin cars → Event (Fin cells))}
    (history : AcceptedHistory routes entries initial batches final) :
    replay? routes entries initial batches = some final := by
  induction history with
  | nil s => rfl
  | cons accepted tail ih => simpa [replay?, step?, accepted] using ih

theorem replay?_iff {routes : Routes cells} {entries : Fin cells → Bool}
    {initial final : State cells cars} {batches : List (Fin cars → Event (Fin cells))} :
    replay? routes entries initial batches = some final ↔
      AcceptedHistory routes entries initial batches final :=
  ⟨replay?_sound, replay?_complete⟩

/-- Every retained prefix is itself an accepted finite history. No records
after the requested prefix are needed to certify its state transitions. -/
theorem AcceptedHistory.prefix {routes : Routes cells} {entries : Fin cells → Bool}
    {initial final : State cells cars} {batches : List (Fin cars → Event (Fin cells))}
    (history : AcceptedHistory routes entries initial batches final) (count : Nat) :
    ∃ middle, AcceptedHistory routes entries initial (batches.take count) middle := by
  induction history generalizing count with
  | nil s => exact ⟨s, by simpa using AcceptedHistory.nil s⟩
  | @cons s final batch rest accepted tail ih =>
    cases count with
    | zero => exact ⟨s, by simpa using AcceptedHistory.nil s⟩
    | succ count =>
      obtain ⟨middle, part⟩ := ih count
      exact ⟨middle, by simpa using AcceptedHistory.cons accepted part⟩

theorem AcceptedHistory.append {routes : Routes cells} {entries : Fin cells → Bool}
    {initial middle final : State cells cars}
    {first second : List (Fin cars → Event (Fin cells))}
    (head : AcceptedHistory routes entries initial first middle)
    (tail : AcceptedHistory routes entries middle second final) :
    AcceptedHistory routes entries initial (first ++ second) final := by
  induction head with
  | nil s => exact tail
  | cons accepted rest ih => exact .cons accepted (ih tail)

/-- Checked movement events always begin with the named vehicle on street. -/
theorem movement_has_source {s : State cells cars} {routes : Routes cells} {entries : Fin cells → Bool}
    {k : Fin cars} {e : Event (Fin cells)} (accepted : checkEvent s routes entries k e = true)
    (moved : e.moves = true) : ∃ p, s.pos k = some p := by
  have source := checkEvent_source accepted
  cases e with
  | stay p => simp [Event.moves] at moved
  | hop p q => exact ⟨p, by simpa [Event.before] using source.symm⟩
  | exit p => exact ⟨p, by simpa [Event.before] using source.symm⟩
  | admit q => simp [Event.moves] at moved
  | exitAdmit p q => exact ⟨p, by simpa [Event.before] using source.symm⟩

/-- If an on-street tag has no hop/exit event, its checked event must be
an actual stay. An admission cannot masquerade as a waiting vehicle. -/
theorem nonmovement_is_stay {s : State cells cars} {routes : Routes cells} {entries : Fin cells → Bool}
    {k : Fin cars} {e : Event (Fin cells)} (accepted : checkEvent s routes entries k e = true)
    {p : Fin cells} (pos : s.pos k = some p) (notMoved : e.moves ≠ true) : e = .stay (some p) := by
  have source := checkEvent_source accepted
  cases e <;> simp_all [Event.moves, Event.before]

/-- Every post-step occupant either stayed without moving, or entered a
cell that was vacant before the batch. This includes combined exit/admit. -/
theorem post_occupant {s : State cells cars} {routes : Routes cells} {entries : Fin cells → Bool}
    {events : Fin cars → Event (Fin cells)} (accepted : checkBatch s routes entries events = true)
    {q : Fin cells} {k : Fin cars} (occupied : (applyBatch s routes entries events accepted).occ q = some k) :
    s.occ q = none ∨ (s.occ q = some k ∧ (events k).moves = false) := by
  have after := ((applyBatch s routes entries events accepted).occ_iff_pos q k).mp occupied
  change (events k).after = some q at after
  have event := checked_event accepted k
  have source := checkEvent_source event
  cases action : events k with
  | stay p =>
    have same : p = some q := by simpa [action, Event.after] using after
    right
    refine ⟨(s.occ_iff_pos q k).mpr ?_, by simp [Event.moves]⟩
    simpa [action, Event.before, same] using source.symm
  | hop p r =>
    have same : r = q := by simpa [action, Event.after] using after
    left
    exact checkEvent_vacant event (by simp [action, Event.arrivalTarget, same])
  | exit p => simp [action, Event.after] at after
  | admit r =>
    have same : r = q := by simpa [action, Event.after] using after
    left
    exact checkEvent_vacant event (by simp [action, Event.arrivalTarget, same])
  | exitAdmit p r =>
    have same : r = q := by simpa [action, Event.after] using after
    left
    exact checkEvent_vacant event (by simp [action, Event.arrivalTarget, same])

/-- The executable batch checker derives the source-vacancy premise used
by R2. This is not inferred from a reported departure or a respawn delay. -/
theorem departure_leaves_vacancy {s : State cells cars} {routes : Routes cells}
    {entries : Fin cells → Bool} {events : Fin cars → Event (Fin cells)}
    (accepted : checkBatch s routes entries events = true) {k : Fin cars} {p : Fin cells}
    (pos : s.pos k = some p) (moved : (events k).moves = true) :
    (applyBatch s routes entries events accepted).occ p = none := by
  have occupied := (s.occ_iff_pos p k).mpr pos
  cases after : (applyBatch s routes entries events accepted).occ p with
  | none => rfl
  | some j =>
    rcases post_occupant accepted after with wasEmpty | stayed
    · rw [occupied] at wasEmpty
      contradiction
    · have same : k = j := Option.some.inj (occupied.symm.trans stayed.1)
      subst j
      have impossible := stayed.2
      rw [moved] at impossible
      contradiction

/-- In this checked, fenced model, movement is exactly an on-street tag
changing its modeled position. Admission alone changes an outside tag's
position but is not counted as an on-street hop or exit. -/
theorem movement_iff_onstreet_change {s : State cells cars} {routes : Routes cells}
    {entries : Fin cells → Bool} {events : Fin cars → Event (Fin cells)}
    (accepted : checkBatch s routes entries events = true) (k : Fin cars) :
    (events k).moves = true ↔
      ∃ p, s.pos k = some p ∧ (applyBatch s routes entries events accepted).pos k ≠ some p := by
  constructor
  · intro moved
    obtain ⟨p, pos⟩ := movement_has_source (checked_event accepted k) moved
    refine ⟨p, pos, ?_⟩
    intro remains
    have vacant := departure_leaves_vacancy accepted pos moved
    have occupied := ((applyBatch s routes entries events accepted).occ_iff_pos p k).mpr remains
    rw [occupied] at vacant
    contradiction
  · rintro ⟨p, pos, changed⟩
    by_cases moved : (events k).moves = true
    · exact moved
    have stay := nonmovement_is_stay (checked_event accepted k) pos moved
    exact (changed (by simp [applyBatch, stay, Event.after])).elim

/-- A hop is licensed by the route table for its actual source and arrival,
not merely by a target ID falling in the finite cell range. -/
theorem checked_hop_route {s : State cells cars} {routes : Routes cells}
    {entries : Fin cells → Bool} {k : Fin cars} {p q : Fin cells}
    (accepted : checkEvent s routes entries k (.hop p q) = true) :
    s.pos k = some p ∧ some q ∈ routes (s.prev k) p := by
  have source : s.pos k = some p := (checkEvent_source accepted).symm
  have allowed := checkEvent_route accepted
  exact ⟨source, by simpa [Event.routeAllowed, State.menu, source] using allowed⟩

theorem checked_exit_route {s : State cells cars} {routes : Routes cells}
    {entries : Fin cells → Bool} {k : Fin cars} {p : Fin cells}
    (accepted : checkEvent s routes entries k (.exit p) = true) :
    s.pos k = some p ∧ none ∈ routes (s.prev k) p := by
  have source : s.pos k = some p := (checkEvent_source accepted).symm
  have allowed := checkEvent_route accepted
  exact ⟨source, by simpa [Event.routeAllowed, State.menu, source] using allowed⟩

/-- The transition runner contains only accepted, computed batches. The
adapter still has to establish that its source records describe these
events; acceptance alone does not establish observation completeness. -/
structure Run (cells cars : Nat) where
  routes : Routes cells
  entries : Fin cells → Bool
  state : Nat → State cells cars
  events : Nat → Fin cars → Event (Fin cells)
  accepted : ∀ t, checkBatch (state t) routes entries (events t) = true
  evolves : ∀ t, state (t + 1) = applyBatch (state t) routes entries (events t) (accepted t)

/-- Auxiliary plans are not used to infer events. R2 obtains its full legal
menu from the arrival-indexed route table and the checked state history. -/
def Run.toRouteTrace (run : Run cells cars)
    (plans : Nat → Fin cars → LaneDeadlock.Plan (Fin cells)) : RouteProgress.Trace (Fin cells) (Fin cars) where
  state t := (run.state t).toSnapshot (plans t)
  moves t k := (run.events t k).moves = true
  menu t k := (run.state t).menu run.routes k
  stays := by
    intro t k c pos noMove
    change (run.state t).pos k = some c at pos
    have stay := nonmovement_is_stay (checked_event (run.accepted t) k) pos noMove
    constructor
    · change (run.state (t + 1)).pos k = some c
      rw [run.evolves t]
      simp [applyBatch, stay, Event.after]
    · change (run.state (t + 1)).menu run.routes k = (run.state t).menu run.routes k
      rw [run.evolves t]
      simp [State.menu, applyBatch, stay, Event.after, Event.nextPrev, pos]

theorem Run.toRouteTrace_leaves_vacancy (run : Run cells cars)
    (plans : Nat → Fin cars → LaneDeadlock.Plan (Fin cells)) :
    (run.toRouteTrace plans).LeavesVacancy := by
  intro t k c pos moved
  change (run.state (t + 1)).occ c = none
  rw [run.evolves t]
  exact departure_leaves_vacancy (run.accepted t) pos moved

theorem Run.movement_correspondence (run : Run cells cars)
    (plans : Nat → Fin cars → LaneDeadlock.Plan (Fin cells)) (t : Nat) (k : Fin cars) :
    (run.toRouteTrace plans).moves t k ↔ (run.events t k).moveCount = 1 := by
  simp [Run.toRouteTrace, Event.moveCount]

end BML.TrafficEvents
