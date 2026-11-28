import Init.Data.List.Nat.Basic
import Lean.Elab.Tactic.Omega
import BML.TrafficEvents

/-!
# Work accounting for actual traffic events

`movements` counts completed hops and exits; `admissions` counts entries into
the certified region. Requests, intentions, changes of route, and samples
without a transition are not movements. The local accounting inequality is
the interface to an event/state kernel, not a waiting-time assumption.

The counting theorems below distinguish two independent requirements:
* work decreases on every actual non-admission movement in the region;
* a nonempty block contains an actual movement or admission.

The second requirement is stated explicitly as `BlockProgress`. A proof that
a particular controller enforces it, or a bounded observation check of it,
is separate from these event-accounting theorems. A retrospective observed
admission count is also distinct from the local token rule `AdmissionBudget`.

Finite tags name model objects. A simulator may recycle a tag at admission;
this does not establish continuity of a physical vehicle or trip. A source
observation ID is source-scoped and needs a separate lifecycle mapping into
these objects before measured records can instantiate the event trajectory.
-/
namespace BML.TrafficWork

/-- Number of recorded events in `[start, start + length)`. -/
def count (events : Nat → Nat) (start : Nat) : Nat → Nat
  | 0 => 0
  | length + 1 => count events start length + events (start + length)

@[simp] theorem count_zero (events : Nat → Nat) (start : Nat) :
    count events start 0 = 0 := rfl

@[simp] theorem count_succ (events : Nat → Nat) (start length : Nat) :
    count events start (length + 1) = count events start length + events (start + length) := rfl

theorem count_append (events : Nat → Nat) (start first second : Nat) :
    count events start (first + second) =
      count events start first + count events (start + first) second := by
  induction second with
  | zero => simp
  | succ second ih =>
    simp only [Nat.add_succ, count_succ, ih, Nat.add_assoc]

theorem count_add (first second : Nat → Nat) (start length : Nat) :
    count (fun t => first t + second t) start length =
      count first start length + count second start length := by
  induction length with
  | zero => rfl
  | succ length ih => simp only [count_succ, ih]; omega

theorem count_of_zero (events : Nat → Nat) (start length : Nat)
    (empty : ∀ i < length, events (start + i) = 0) : count events start length = 0 := by
  induction length with
  | zero => rfl
  | succ length ih =>
    rw [count_succ, ih (fun i hi => empty i (by omega)), empty length (by omega)]

theorem count_term_le (events : Nat → Nat) (start length i : Nat) (inside : i < length) :
    events (start + i) ≤ count events start length := by
  induction length with
  | zero => omega
  | succ length ih =>
    rw [count_succ]
    by_cases last : i = length
    · subst i; omega
    · have earlier := ih (by omega); omega

/-- Local model work accounting. A hop or exit costs at least one unit;
an admission injects at most `D`. Both may occur for one tag in one step. -/
structure Ledger (D : Nat) where
  potential : Nat → Nat
  movements : Nat → Nat
  admissions : Nat → Nat
  step : ∀ t, potential (t + 1) + movements t ≤ potential t + D * admissions t

def Ledger.events {D : Nat} (run : Ledger D) (t : Nat) : Nat :=
  run.movements t + run.admissions t

/-- Telescoping is derived from each transition's work inequality. -/
theorem Ledger.telescoping {D : Nat} (run : Ledger D) (start length : Nat) :
    run.potential (start + length) + count run.movements start length ≤
      run.potential start + D * count run.admissions start length := by
  induction length with
  | zero => simp
  | succ length ih =>
    have stepLaw := run.step (start + length)
    simp only [Nat.add_assoc] at stepLaw
    simp only [count_succ, Nat.mul_add]
    omega

/-- The advertised cumulative inequality `Phi(t) + M(t) ≤ Phi(0) + D*A(t)`. -/
theorem Ledger.prefix_accounting {D : Nat} (run : Ledger D) (t : Nat) :
    run.potential t + count run.movements 0 t ≤
      run.potential 0 + D * count run.admissions 0 t := by
  simpa using run.telescoping 0 t

theorem Ledger.event_budget_credit {D : Nat} (run : Ledger D)
    (start length credit quota : Nat)
    (retained : credit ≤ run.potential (start + length))
    (admitted : count run.admissions start length ≤ quota) :
    count run.events start length + credit ≤ run.potential start + (D + 1) * quota := by
  have accounting := run.telescoping start length
  have admissions := Nat.mul_le_mul_left D admitted
  change count (fun t => run.movements t + run.admissions t) start length + credit ≤ _
  rw [count_add]
  simp only [Nat.add_mul, Nat.one_mul]
  omega

/-- A stationary focal car's work cannot finance other cars' movements. -/
theorem Ledger.event_budget {D : Nat} (run : Ledger D)
    (start length credit quota : Nat)
    (initial : credit ≤ run.potential start)
    (retained : credit ≤ run.potential (start + length))
    (admitted : count run.admissions start length ≤ quota) :
    count run.events start length ≤ run.potential start - credit + (D + 1) * quota := by
  have bound := run.event_budget_credit start length credit quota retained admitted
  omega

/-- One positive recorded event per block gives at least one event per
block in the total count. Multiple simultaneous events are counted fully. -/
theorem block_event_count (events : Nat → Nat) (start Q blocks : Nat)
    (progress : ∀ j < blocks, ∃ i < Q, 0 < events (start + j * Q + i)) :
    blocks ≤ count events start (blocks * Q) := by
  induction blocks with
  | zero => simp
  | succ blocks ih =>
    have earlier := ih (fun j hj => progress j (by omega))
    obtain ⟨i, hi, event⟩ := progress blocks (by omega)
    have contained := count_term_le events (start + blocks * Q) Q i hi
    rw [Nat.succ_mul, count_append]
    omega

/-- A finite event budget cannot support one event in each of budget+1
disjoint blocks. This is a counting contradiction, not a service assumption. -/
theorem finite_event_contradiction (events : Nat → Nat) (start Q budget : Nat)
    (limited : count events start (Q * (budget + 1)) ≤ budget)
    (progress : ∀ j < budget + 1, ∃ i < Q, 0 < events (start + j * Q + i)) : False := by
  have lower := block_event_count events start Q (budget + 1) progress
  rw [Nat.mul_comm (budget + 1) Q] at lower
  omega

/-- The explicit remaining controller/observation premise: every complete
nonempty block in the accepted horizon has a real movement or admission.
It is not obtained from acyclic work accounting alone. -/
def BlockProgress (potential events : Nat → Nat) (horizon Q : Nat) : Prop :=
  ∀ start, start + Q ≤ horizon → (∀ i < Q, 0 < potential (start + i)) →
    ∃ i < Q, 0 < events (start + i)

/-- A separately enforced admission token rule. Tokens cannot be renewed
inside this trace; each actual admission must be charged to a remaining
token. A raw observed count does not supply this prospective invariant. -/
structure AdmissionBudget (admissions : Nat → Nat) where
  remaining : Nat → Nat
  debit : ∀ t, remaining (t + 1) + admissions t ≤ remaining t

theorem AdmissionBudget.accounting {admissions : Nat → Nat}
    (budget : AdmissionBudget admissions) (start length : Nat) :
    budget.remaining (start + length) + count admissions start length ≤ budget.remaining start := by
  induction length with
  | zero => simp
  | succ length ih =>
    have stepLaw := budget.debit (start + length)
    simp only [Nat.add_assoc] at stepLaw
    simp only [count_succ]
    omega

theorem AdmissionBudget.count_le {admissions : Nat → Nat}
    (budget : AdmissionBudget admissions) (start length : Nat) :
    count admissions start length ≤ budget.remaining start := by
  have bound := budget.accounting start length
  omega

/-- A focal model object's stationary-state and work contribution
interface. The concrete event kernel supplies these from its finite tag,
actual movement events, and positive cell heights. -/
structure Focal {D : Nat} (run : Ledger D) (Cell : Type) where
  position : Nat → Option Cell
  height : Cell → Nat
  moved : Nat → Prop
  recorded : ∀ t, moved t → 0 < run.movements t
  stays : ∀ t c, position t = some c → ¬ moved t → position (t + 1) = some c
  contributes : ∀ t c, position t = some c → height c ≤ run.potential t

theorem Focal.stays_window {D : Nat} {run : Ledger D} {Cell : Type}
    (focal : Focal run Cell) (start length : Nat) (c : Cell)
    (present : focal.position start = some c)
    (waiting : ∀ i < length, ¬ focal.moved (start + i)) :
    focal.position (start + length) = some c := by
  induction length with
  | zero => simpa using present
  | succ length ih =>
    exact focal.stays (start + length) c (ih fun i hi => waiting i (by omega))
      (waiting length (by omega))

theorem Focal.retained_credit {D : Nat} {run : Ledger D} {Cell : Type}
    (focal : Focal run Cell) (start length : Nat) (c : Cell)
    (present : focal.position start = some c)
    (waiting : ∀ i < length, ¬ focal.moved (start + i)) :
    focal.height c ≤ run.potential (start + length) :=
  focal.contributes _ c (focal.stays_window start length c present waiting)

def waitBound (Q initial credit D quota : Nat) : Nat :=
  Q * (initial - credit + (D + 1) * quota + 1)

/-- The focal deadline from an admission bound on this exact horizon.
Used with observed admissions it is a retrospective conditional result;
`quota_wait_of_budget` supplies the independent prospective quota rule. -/
theorem Focal.quota_wait {D : Nat} {run : Ledger D} {Cell : Type}
    (focal : Focal run Cell) (start Q horizon quota : Nat) (c : Cell)
    (present : focal.position start = some c) (positive : 0 < focal.height c)
    (progress : BlockProgress run.potential run.events horizon Q)
    (within : start + waitBound Q (run.potential start) (focal.height c) D quota ≤ horizon)
    (admitted : count run.admissions start
      (waitBound Q (run.potential start) (focal.height c) D quota) ≤ quota) :
    ∃ i < waitBound Q (run.potential start) (focal.height c) D quota,
      focal.moved (start + i) := by
  let budget := run.potential start - focal.height c + (D + 1) * quota
  let deadline := Q * (budget + 1)
  change ∃ i < deadline, focal.moved (start + i)
  by_cases moved : ∃ i < deadline, focal.moved (start + i)
  · exact moved
  exfalso
  have waiting (i : Nat) (hi : i < deadline) : ¬ focal.moved (start + i) :=
    fun event => moved ⟨i, hi, event⟩
  have initial := focal.contributes start c present
  have retained := focal.retained_credit start deadline c present waiting
  have limited : count run.events start deadline ≤ budget :=
    run.event_budget start deadline (focal.height c) quota initial retained admitted
  apply finite_event_contradiction run.events start Q budget limited
  intro j hj
  have blockEnd : (j + 1) * Q ≤ deadline := by
    dsimp [deadline]
    rw [Nat.mul_comm Q (budget + 1)]
    exact Nat.mul_le_mul_right Q (Nat.succ_le_of_lt hj)
  have fits : start + j * Q + Q ≤ horizon := by
    change start + deadline ≤ horizon at within
    rw [Nat.succ_mul] at blockEnd
    omega
  apply progress (start + j * Q) fits
  intro i hi
  have inside : j * Q + i < deadline := by rw [Nat.succ_mul] at blockEnd; omega
  have credit := focal.retained_credit start (j * Q + i) c present
    (fun earlier he => waiting earlier (Nat.lt_trans he inside))
  simpa only [Nat.add_assoc] using Nat.lt_of_lt_of_le positive credit

/-- A deadline using only the available token count at the start, together
with a future-enforced local debit rule. No future observed count is used
to select this bound. -/
theorem Focal.quota_wait_of_budget {D : Nat} {run : Ledger D} {Cell : Type}
    (focal : Focal run Cell) (budget : AdmissionBudget run.admissions)
    (start Q horizon : Nat) (c : Cell)
    (present : focal.position start = some c) (positive : 0 < focal.height c)
    (progress : BlockProgress run.potential run.events horizon Q)
    (within : start + waitBound Q (run.potential start) (focal.height c) D
      (budget.remaining start) ≤ horizon) :
    ∃ i < waitBound Q (run.potential start) (focal.height c) D (budget.remaining start),
      focal.moved (start + i) :=
  focal.quota_wait start Q horizon (budget.remaining start) c present positive progress within
    (budget.count_le start _)

/-- In a region with no admissions, complete work accounting and block
progress evacuate all positive work by `Q * Phi(start)` steps. A DAG's
strictly positive height certificate turns zero work into an empty region. -/
theorem Ledger.closed_evacuation {D : Nat} (run : Ledger D) (start Q horizon : Nat)
    (progress : BlockProgress run.potential run.events horizon Q)
    (within : start + Q * run.potential start ≤ horizon)
    (closed : ∀ i < Q * run.potential start, run.admissions (start + i) = 0) :
    run.potential (start + Q * run.potential start) = 0 := by
  let length := Q * run.potential start
  by_cases empty : run.potential (start + length) = 0
  · exact empty
  exfalso
  have positive : 0 < run.potential (start + length) := by omega
  have remains (i : Nat) (hi : i ≤ length) : 0 < run.potential (start + i) := by
    have account := run.telescoping (start + i) (length - i)
    have noAdmissions : count run.admissions (start + i) (length - i) = 0 :=
      count_of_zero _ _ _ fun j hj => by
        have inWindow : i + j < length := by omega
        simpa only [Nat.add_assoc] using closed (i + j) inWindow
    rw [show start + i + (length - i) = start + length by omega, noAdmissions] at account
    omega
  have enough := block_event_count run.events start Q (run.potential start) (by
    intro j hj
    have blockEnd : (j + 1) * Q ≤ length := by
      dsimp [length]
      rw [Nat.mul_comm Q (run.potential start)]
      exact Nat.mul_le_mul_right Q (Nat.succ_le_of_lt hj)
    apply progress (start + j * Q) (by rw [Nat.succ_mul] at blockEnd; omega)
    intro i hi
    have nonempty := remains (j * Q + i) (by rw [Nat.succ_mul] at blockEnd; omega)
    simpa only [Nat.add_assoc] using nonempty)
  rw [Nat.mul_comm (run.potential start) Q] at enough
  have noAdmissions := count_of_zero run.admissions start length closed
  have account := run.telescoping start length
  rw [noAdmissions] at account
  change run.potential start ≤ count (fun t => run.movements t + run.admissions t) start length at enough
  rw [count_add, noAdmissions, Nat.add_zero] at enough
  omega

section CheckedEvents

open TrafficEvents

/-- Sum once for each finite model tag, including tags currently off street. -/
def sumOn (cars : Nat) (quantity : Fin cars → Nat) : Nat :=
  ((List.finRange cars).map quantity).sum

private theorem term_le_sum {Tag : Type} (tags : List Tag) (quantity : Tag → Nat)
    {k : Tag} (member : k ∈ tags) : quantity k ≤ (tags.map quantity).sum := by
  induction tags with
  | nil => simp at member
  | cons j rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp member with rfl | inside
    · omega
    · have bound := ih inside; omega

theorem sumOn_term_le (quantity : Fin cars → Nat) (k : Fin cars) :
    quantity k ≤ sumOn cars quantity :=
  term_le_sum (List.finRange cars) quantity (List.mem_finRange k)

private theorem sum_inequality {Tag : Type} (tags : List Tag)
    (before after movements admissions : Tag → Nat) (D : Nat)
    (each : ∀ k ∈ tags, after k + movements k ≤ before k + D * admissions k) :
    (tags.map after).sum + (tags.map movements).sum ≤
      (tags.map before).sum + D * (tags.map admissions).sum := by
  induction tags with
  | nil => simp
  | cons k rest ih =>
    have stepLaw := each k (List.mem_cons_self ..)
    have restLaw := ih (fun j hj => each j (List.mem_cons_of_mem _ hj))
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    omega

def framePotential (height : Fin cells → Nat) (state : State cells cars) : Nat :=
  sumOn cars fun k => workAt height (state.pos k)

def movementCount (events : Fin cars → Event (Fin cells)) : Nat :=
  sumOn cars fun k => (events k).moveCount

def admissionCount (events : Fin cars → Event (Fin cells)) : Nat :=
  sumOn cars fun k => (events k).admissionCount

/-- Exhaust the finite arrival-indexed legal menus. Self options may be
listed but cannot be granted by the CLASSIC pre-vacancy checker. Every
other listed hop must descend; one decreasing rank witness is insufficient. -/
def checkDAG (routes : Routes cells) (height : Fin cells → Nat) (D : Nat) : Bool :=
  (List.finRange cells).all fun c =>
    decide (0 < height c) && decide (height c ≤ D) &&
      (none :: (List.finRange cells).map some).all fun prev =>
        (routes prev c).all fun target => target.elim true fun q =>
          q == c || decide (height q < height c)

theorem checkDAG_sound {routes : Routes cells} {height : Fin cells → Nat} {D : Nat}
    (accepted : checkDAG routes height D = true) :
    (∀ c, 0 < height c) ∧ (∀ c, height c ≤ D) ∧
      ∀ prev c q, q ≠ c → some q ∈ routes prev c → height q < height c := by
  have row (c : Fin cells) := List.all_eq_true.mp accepted c (List.mem_finRange c)
  refine ⟨?_, ?_, ?_⟩
  · intro c
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (row c)).1).1
  · intro c
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (row c)).1).2
  · intro prev c q different offered
    have arrival : prev ∈ none :: (List.finRange cells).map some := by
      cases prev with
      | none => exact List.mem_cons_self ..
      | some p => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p, List.mem_finRange p, rfl⟩)
    have arrivals := (Bool.and_eq_true_iff.mp (row c)).2
    have menu := List.all_eq_true.mp arrivals prev arrival
    have legal := List.all_eq_true.mp menu (some q) offered
    simpa [different] using legal

theorem frame_retains_credit (height : Fin cells → Nat) (state : State cells cars)
    (k : Fin cars) (c : Fin cells) (present : state.pos k = some c) :
    height c ≤ framePotential height state := by
  have included := sumOn_term_le (fun j => workAt height (state.pos j)) k
  simpa [framePotential, workAt, present] using included

/-- Sum local work inequalities for the actual checked event objects.
An `exitAdmit` record contributes one to each count, so its injected work
is never mistaken for an uncharged continuation or a stationary tag. -/
theorem checked_batch_accounting (height : Fin cells → Nat) (D : Nat)
    (state : State cells cars) (routes : Routes cells) (entries : Fin cells → Bool)
    (events : Fin cars → Event (Fin cells)) (accepted : checkBatch state routes entries events = true)
    (allowed : ∀ k, (events k).WorkAllowed height D) :
    framePotential height (applyBatch state routes entries events accepted) + movementCount events ≤
      framePotential height state + D * admissionCount events := by
  unfold framePotential movementCount admissionCount sumOn
  apply sum_inequality
  intro k _
  have source := checkEvent_source (checked_event accepted k)
  have accounting := Event.work_inequality height D (events k) (allowed k)
  simpa only [applyBatch, source] using accounting

/-- A checked sequence of finite states and named event objects supplies
the accounting ledger. The scalar inequality is now a proved consequence
of those objects, not an arbitrary imported assertion. -/
def checkedLedger (run : TrafficEvents.Run cells cars) (height : Fin cells → Nat) (D : Nat)
    (allowed : ∀ t k, (run.events t k).WorkAllowed height D) : Ledger D where
  potential t := framePotential height (run.state t)
  movements t := movementCount (run.events t)
  admissions t := admissionCount (run.events t)
  step t := by
    rw [run.evolves t]
    exact checked_batch_accounting height D (run.state t) run.routes run.entries (run.events t)
      (run.accepted t) (allowed t)

/-- The focal object is the same finite tag in the event kernel. Its
movement predicate is computed from the actual hop/exit constructor. -/
def checkedFocal (run : TrafficEvents.Run cells cars) (height : Fin cells → Nat) (D : Nat)
    (allowed : ∀ t k, (run.events t k).WorkAllowed height D) (k : Fin cars) :
    Focal (checkedLedger run height D allowed) (Fin cells) where
  position t := (run.state t).pos k
  height := height
  moved t := (run.events t k).moves = true
  recorded t moved := by
    have included := sumOn_term_le (fun j => (run.events t j).moveCount) k
    have one : (run.events t k).moveCount = 1 := by simp [Event.moveCount, moved]
    rw [one] at included
    exact included
  stays t c pos noMove := by
    have stay := nonmovement_is_stay (checked_event (run.accepted t) k) pos noMove
    rw [run.evolves t]
    simp only [applyBatch, stay, Event.after]
  contributes t c pos := frame_retains_credit height (run.state t) k c pos

/-- A certificate decreasing on every legal non-self hop establishes work
descent for every accepted event. CLASSIC vacancy excludes self-hop grants.
This does not follow from an existential safe-rank witness alone. -/
theorem checked_work_of_DAG (height : Fin cells → Nat) (D : Nat)
    (positive : ∀ c, 0 < height c) (bounded : ∀ c, height c ≤ D)
    (state : State cells cars) (routes : Routes cells) (entries : Fin cells → Bool)
    (descends : ∀ prev c q, q ≠ c → some q ∈ routes prev c → height q < height c)
    (events : Fin cars → Event (Fin cells)) (accepted : checkBatch state routes entries events = true)
    (k : Fin cars) : (events k).WorkAllowed height D := by
  have event := checked_event accepted k
  have source := checkEvent_source event
  have legal := checkEvent_route event
  cases action : events k with
  | stay p => trivial
  | hop p q =>
    have pos : state.pos k = some p := by simpa [action, Event.before] using source.symm
    have different : q ≠ p := by
      intro same
      have vacant := checkEvent_vacant event (q := p) (by simp [action, Event.arrivalTarget, same])
      have occupied := (state.occ_iff_pos p k).mpr pos
      rw [occupied] at vacant
      contradiction
    have offered : some q ∈ routes (state.prev k) p := by
      simpa [action, Event.routeAllowed, State.menu, pos] using legal
    exact descends _ _ _ different offered
  | exit p => exact positive p
  | admit q => exact bounded q
  | exitAdmit p q => exact ⟨positive p, bounded q⟩

theorem checked_run_work_allowed (run : TrafficEvents.Run cells cars)
    (height : Fin cells → Nat) (D : Nat)
    (positive : ∀ c, 0 < height c) (bounded : ∀ c, height c ≤ D)
    (descends : ∀ prev c q, q ≠ c → some q ∈ run.routes prev c → height q < height c)
    (t : Nat) (k : Fin cars) : (run.events t k).WorkAllowed height D :=
  checked_work_of_DAG height D positive bounded (run.state t) run.routes run.entries descends
    (run.events t) (run.accepted t) k

theorem empty_of_zero_work (height : Fin cells → Nat) (positive : ∀ c, 0 < height c)
    (state : State cells cars) (empty : framePotential height state = 0) :
    ∀ k, state.pos k = none := by
  intro k
  cases pos : state.pos k with
  | none => rfl
  | some c =>
    have credit := frame_retains_credit height state k c pos
    rw [empty] at credit
    have nonzero := positive c
    omega

/-- Closed-DAG evacuation for the concrete checked event/state trajectory.
All on-street objects have positive height; every granted non-self hop
descends, and no admission event occurs in the complete certified horizon.
Controller-level block progress remains an explicit independent premise. -/
theorem checked_closed_DAG_evacuation (run : TrafficEvents.Run cells cars)
    (height : Fin cells → Nat) (D : Nat)
    (positive : ∀ c, 0 < height c) (bounded : ∀ c, height c ≤ D)
    (descends : ∀ prev c q, q ≠ c → some q ∈ run.routes prev c → height q < height c)
    (start Q horizon : Nat)
    (progress : BlockProgress (fun t => framePotential height (run.state t))
      (fun t => movementCount (run.events t) + admissionCount (run.events t)) horizon Q)
    (within : start + Q * framePotential height (run.state start) ≤ horizon)
    (closed : ∀ i < Q * framePotential height (run.state start), admissionCount (run.events (start + i)) = 0) :
    ∀ k, (run.state (start + Q * framePotential height (run.state start))).pos k = none := by
  let ledger := checkedLedger run height D (checked_run_work_allowed run height D positive bounded descends)
  have drained := ledger.closed_evacuation start Q horizon progress within closed
  exact empty_of_zero_work height positive _ drained

end CheckedEvents

end BML.TrafficWork
