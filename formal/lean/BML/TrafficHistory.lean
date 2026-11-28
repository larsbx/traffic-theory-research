import BML.TrafficPolicy

/-!
# Finite accepted histories have an idle event extension

Finite JSON correspondence establishes a checked finite history, not an
assumption about all future event batches. Every such history embeds into
an infinite `TrafficEvents.Run` by keeping its final state and issuing only
stay events afterwards. This extension preserves every recorded prefix
state and event. It carries no controller-policy claim beyond the horizon.

Finite local controller checks can therefore construct `ProtectedPrefix`
on the extension without requiring an unobserved policy continuation.
-/
namespace BML.TrafficHistory

open TrafficEvents

def stayBatch (s : State cells cars) : Fin cars → Event (Fin cells) := fun k => .stay (s.pos k)

theorem stay_accepted (s : State cells cars) (routes : Routes cells) (entries : Fin cells → Bool) :
    checkBatch s routes entries (stayBatch s) = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · simpa only [stayBatch, Event.after] using checkState_complete s.exclusive
  · apply List.all_eq_true.mpr
    intro k _
    simp [checkEvent, stayBatch, Event.before, Event.routeAllowed, Event.arrivalTarget]

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

theorem stay_preserves (s : State cells cars) (routes : Routes cells) (entries : Fin cells → Bool) :
    applyBatch s routes entries (stayBatch s) (stay_accepted s routes entries) = s := by
  apply state_ext <;> intro k <;> rfl

def idleRun (routes : Routes cells) (entries : Fin cells → Bool) (s : State cells cars) : Run cells cars where
  routes := routes
  entries := entries
  state _ := s
  events _ := stayBatch s
  accepted _ := stay_accepted s routes entries
  evolves _ := (stay_preserves s routes entries).symm

/-- Prepend one accepted batch to a compatible event run. -/
def prepend (tail : Run cells cars) (s : State cells cars)
    (batch : Fin cars → Event (Fin cells))
    (accepted : checkBatch s tail.routes tail.entries batch = true)
    (next : tail.state 0 = applyBatch s tail.routes tail.entries batch accepted) : Run cells cars where
  routes := tail.routes
  entries := tail.entries
  state
    | 0 => s
    | n + 1 => tail.state n
  events
    | 0 => batch
    | n + 1 => tail.events n
  accepted
    | 0 => accepted
    | n + 1 => tail.accepted n
  evolves
    | 0 => next
    | n + 1 => tail.evolves n

/-- Exact finite-prefix agreement together with an explicitly idle suffix.
The suffix is a device for using a total-time event interface, not evidence
of the controller or traffic after the supplied observations. -/
structure Extends (run : Run cells cars) (routes : Routes cells) (entries : Fin cells → Bool)
    (initial : State cells cars) (batches : List (Fin cars → Event (Fin cells)))
    (final : State cells cars) : Prop where
  routes_eq : run.routes = routes
  entries_eq : run.entries = entries
  initial_eq : run.state 0 = initial
  events_eq : ∀ i (inside : i < batches.length), run.events i = batches[i]
  final_eq : run.state batches.length = final
  replay_prefix : ∀ i, i ≤ batches.length →
    replay? routes entries initial (batches.take i) = some (run.state i)
  idle_suffix : ∀ i, run.events (batches.length + i) = stayBatch final
  state_suffix : ∀ i, run.state (batches.length + i) = final

/-- Induction is into an existence proposition. No data are extracted from
`AcceptedHistory` by an illicit Prop-to-Type recursion. -/
theorem extend_accepted {routes : Routes cells} {entries : Fin cells → Bool}
    {initial final : State cells cars} {batches : List (Fin cars → Event (Fin cells))}
    (history : AcceptedHistory routes entries initial batches final) :
    ∃ run : Run cells cars, Extends run routes entries initial batches final := by
  induction history with
  | nil s =>
    refine ⟨idleRun routes entries s, rfl, rfl, rfl, ?_, rfl, ?_, ?_, ?_⟩
    · intro i inside
      simp at inside
    · intro i inside
      have zero : i = 0 := by simpa using inside
      subst i
      rfl
    · intro i
      rfl
    · intro i
      rfl
  | @cons s final batch rest accepted history ih =>
    obtain ⟨tail, extension⟩ := ih
    have accepted' : checkBatch s tail.routes tail.entries batch = true := by
      simpa only [extension.routes_eq, extension.entries_eq] using accepted
    have next : tail.state 0 = applyBatch s tail.routes tail.entries batch accepted' := by
      simpa only [extension.routes_eq, extension.entries_eq] using extension.initial_eq
    let whole := prepend tail s batch accepted' next
    refine ⟨whole, extension.routes_eq, extension.entries_eq, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro i inside
      cases i with
      | zero => rfl
      | succ i =>
        exact extension.events_eq i (by simpa using inside)
    · exact extension.final_eq
    · intro i inside
      cases i with
      | zero => rfl
      | succ i =>
        have step : step? s routes entries batch = some (applyBatch s routes entries batch accepted) := by
          simp [step?, accepted]
        simpa only [List.take_succ_cons, replay?, step, Option.bind_some, whole, prepend] using
          extension.replay_prefix i (by simpa using inside)
    · intro i
      have index : (batch :: rest).length + i = (rest.length + i) + 1 := by simp; omega
      rw [index]
      exact extension.idle_suffix i
    · intro i
      have index : (batch :: rest).length + i = (rest.length + i) + 1 := by simp; omega
      rw [index]
      exact extension.state_suffix i

/-- The executable replay result directly supplies an infinite event
extension whose every finite prefix agrees with the accepted input. -/
theorem extend_replay {routes : Routes cells} {entries : Fin cells → Bool}
    {initial final : State cells cars} {batches : List (Fin cars → Event (Fin cells))}
    (accepted : replay? routes entries initial batches = some final) :
    ∃ run : Run cells cars, Extends run routes entries initial batches final :=
  extend_accepted (replay?_sound accepted)

theorem Extends.state_eq_frame {run : Run cells cars} {routes : Routes cells}
    {entries : Fin cells → Bool} {initial final : State cells cars}
    {batches : List (Fin cars → Event (Fin cells))}
    (extension : Extends run routes entries initial batches final)
    (frames : Nat → State cells cars)
    (matched : ∀ i, i ≤ batches.length →
      replay? routes entries initial (batches.take i) = some (frames i))
    (i : Nat) (inside : i ≤ batches.length) : run.state i = frames i :=
  Option.some.inj ((extension.replay_prefix i inside).symm.trans (matched i inside))

/-- Any local assertion about consecutive prefix states and its actual
event batch transfers to the extension. No assertion after the finite
history is requested or inferred. -/
theorem Extends.transfer_local_checks {run : Run cells cars} {routes : Routes cells}
    {entries : Fin cells → Bool} {initial final : State cells cars}
    {batches : List (Fin cars → Event (Fin cells))}
    (extension : Extends run routes entries initial batches final)
    (frames : Nat → State cells cars)
    (matched : ∀ i, i ≤ batches.length →
      replay? routes entries initial (batches.take i) = some (frames i))
    (check : Nat → State cells cars → State cells cars → (Fin cars → Event (Fin cells)) → Prop)
    (checked : ∀ i (inside : i < batches.length),
      check i (frames i) (frames (i + 1)) batches[i]) :
    ∀ i, i < batches.length → check i (run.state i) (run.state (i + 1)) (run.events i) := by
  intro i inside
  rw [extension.state_eq_frame frames matched i (by omega),
    extension.state_eq_frame frames matched (i + 1) (by omega), extension.events_eq i inside]
  exact checked i inside

/-- Finite checked controller rows instantiate the finite policy theorem
on a replay extension. Idle suffix events need not satisfy this policy. -/
theorem extend_checked_policy {routes : Routes cells} {entries : Fin cells → Bool}
    {initial final : State cells cars} {batches : List (Fin cars → Event (Fin cells))}
    (history : AcceptedHistory routes entries initial batches final)
    (frames : Nat → State cells cars)
    (matched : ∀ i, i ≤ batches.length →
      replay? routes entries initial (batches.take i) = some (frames i))
    (L green : Nat) (age : Nat → Fin cars → Nat)
    (axis : TrafficPolicy.AxisMap cells) (junction : Fin cells → Bool)
    (owners : Nat → Fin cells → Option (Fin cars))
    (checked : ∀ i (inside : i < batches.length),
      TrafficPolicy.checkStoppedAge (frames i) batches[i] (age i) (age (i + 1)) = true ∧
      TrafficPolicy.checkOwnerTable (frames i) routes (age i) L (owners i) = true ∧
      TrafficPolicy.checkSignalPermission (frames i) batches[i] green i axis junction = true ∧
      TrafficPolicy.checkOwnerConservingFrame (frames i) routes batches[i]
        (age i) L green i axis junction (owners i) = true) :
    ∃ run : Run cells cars, Extends run routes entries initial batches final ∧
      _root_.Nonempty (TrafficPolicy.ProtectedPrefix run L green batches.length) := by
  obtain ⟨run, extension⟩ := extend_accepted history
  have accepted : TrafficPolicy.checkProtectedPrefix run L green batches.length age axis junction owners = true := by
    apply List.all_eq_true.mpr
    intro i member
    have inside : i < batches.length := List.mem_range.mp member
    have localChecks := checked i inside
    simpa only [extension.state_eq_frame frames matched i (by omega), extension.events_eq i inside,
      extension.routes_eq, Bool.and_eq_true_iff, and_assoc] using localChecks
  exact ⟨run, extension, ⟨TrafficPolicy.ProtectedPrefix.ofChecked run L green batches.length
    age axis junction owners accepted⟩⟩

end BML.TrafficHistory
