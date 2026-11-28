import BML.TrafficWork
import BML.RouteService
import Init.Data.List.MinMax

/-!
# Local controller rules imply block progress

This formalizes the protected reference policy, not Gridlock City's legacy
pre-phase random re-routing. The local controller assigns oldest-tag
ownership of clear street targets before phase eligibility. If a protected
owner or an EXIT claimant is eligible, at least one actual movement must
occur in that batch. Full stopped-half-step age is separate from the legacy
unsuccessful-request counter.

On an acyclic-height network with productive menus, a silent block freezes
positions, arrival contexts and vacancies. A minimum-height occupied cell
then supplies a permanently clear option during that block. Its age reaches
`L`, and the exact phase/signal clock supplies eligibility within `2G` more
half-steps. Hence `Q = L + 2G` block progress is a proved consequence of
local executable checks, not an assumed future service guarantee.
-/
namespace BML.TrafficPolicy

open TrafficEvents TrafficWork

def clearOption (s : State cells cars) (d : Option (Fin cells)) : Bool :=
  d.elim true (fun q => (s.occ q).isNone)

def checkProductive (routes : Routes cells) : Bool :=
  (List.finRange cells).all fun c =>
    (none :: (List.finRange cells).map some).all fun prev =>
      (routes prev c).any (fun d => d != some c)

theorem checkProductive_sound {routes : Routes cells} (accepted : checkProductive routes = true) :
    ∀ prev c, ∃ d ∈ routes prev c, d ≠ some c := by
  intro prev c
  have row := List.all_eq_true.mp accepted c (List.mem_finRange c)
  have arrival : prev ∈ none :: (List.finRange cells).map some := by
    cases prev with
    | none => exact List.mem_cons_self ..
    | some p => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p, List.mem_finRange p, rfl⟩)
  have ready := List.all_eq_true.mp row prev arrival
  simpa using List.any_eq_true.mp ready

private theorem occupied_of_positive (height : Fin cells → Nat) (s : State cells cars)
    (positive : 0 < framePotential height s) : ∃ k c, s.pos k = some c := by
  by_cases present : ∃ k c, s.pos k = some c
  · exact present
  have outside (k : Fin cars) : s.pos k = none := by
    cases pos : s.pos k with
    | none => rfl
    | some c => exact (present ⟨k, c, pos⟩).elim
  have zero : ((List.finRange cars).map (fun _ => (0 : Nat))).sum = 0 := by
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro n member
    obtain ⟨_, _, same⟩ := List.mem_map.mp member
    exact same.symm
  simp [framePotential, sumOn, workAt, outside, zero] at positive

/-- A minimum occupied height has a clear legal exit or lower-height
target. Self options do not supply this witness. -/
theorem clear_route_of_positive_work (height : Fin cells → Nat) (s : State cells cars)
    (routes : Routes cells)
    (productive : ∀ prev c, ∃ d ∈ routes prev c, d ≠ some c)
    (descends : ∀ prev c q, q ≠ c → some q ∈ routes prev c → height q < height c)
    (positive : 0 < framePotential height s) :
    ∃ k c d, s.pos k = some c ∧ d ∈ s.menu routes k ∧ d ≠ some c ∧ clearOption s d = true := by
  obtain ⟨initialTag, initialCell, initialPos⟩ := occupied_of_positive height s positive
  let occupied := (List.finRange cars).filterMap s.pos
  let heights := occupied.map height
  have firstMember : initialCell ∈ occupied :=
    List.mem_filterMap.mpr ⟨initialTag, List.mem_finRange initialTag, initialPos⟩
  have nonempty : heights ≠ [] := List.ne_nil_of_mem (List.mem_map.mpr ⟨_, firstMember, rfl⟩)
  obtain ⟨c, occupiedC, minimum⟩ := List.mem_map.mp (List.min_mem (l := heights) nonempty)
  obtain ⟨k, _, pos⟩ := List.mem_filterMap.mp occupiedC
  obtain ⟨d, offered, notSelf⟩ := productive (s.prev k) c
  refine ⟨k, c, d, pos, by simpa [State.menu, pos] using offered, notSelf, ?_⟩
  cases d with
  | none => rfl
  | some q =>
    have different : q ≠ c := by simpa using notSelf
    have lower := descends (s.prev k) c q different offered
    cases occupant : s.occ q with
    | none => simp [clearOption, occupant]
    | some j =>
      have atQ := (s.occ_iff_pos q j).mp occupant
      have inside : q ∈ occupied := List.mem_filterMap.mpr ⟨j, List.mem_finRange j, atQ⟩
      have higher : heights.min nonempty ≤ height q := List.min_le_of_mem (List.mem_map.mpr ⟨q, inside, rfl⟩)
      rw [← minimum] at higher
      omega

abbrev AxisMap (cells : Nat) := Option (Fin cells) → Fin cells → Option (Fin cells) → Fin 2

def eligible (axis : AxisMap cells) (junction : Fin cells → Bool) (green time : Nat)
    (prev : Option (Fin cells)) (cell : Fin cells) (target : Option (Fin cells)) : Bool :=
  RouteService.clockAllows green time (axis prev cell target).val (target.elim false junction)

/-- The movement stage of exit/admission is EXIT, not a hop to the newly
admitted cell. Admission itself is a separate boundary event. -/
def movementTarget : Event (Fin cells) → Option (Fin cells)
  | .hop _ q => some q
  | .exit _ | .exitAdmit _ _ | .stay _ | .admit _ => none

/-- Safety is separate from work conservation: every actual movement must
respect its phase and junction signal. No permission is inferred merely
from the fact that a movement was reported. -/
def checkSignalPermission (s : State cells cars) (events : Fin cars → Event (Fin cells))
    (green time : Nat) (axis : AxisMap cells) (junction : Fin cells → Bool) : Bool :=
  (List.finRange cars).all fun k => !(events k).moves ||
    match s.pos k with
    | none => false
    | some c => eligible axis junction green time (s.prev k) c (movementTarget (events k))

theorem checkSignalPermission_sound {s : State cells cars} {events : Fin cars → Event (Fin cells)}
    {green time : Nat} {axis : AxisMap cells} {junction : Fin cells → Bool}
    (accepted : checkSignalPermission s events green time axis junction = true)
    {k : Fin cars} {c : Fin cells} (pos : s.pos k = some c) (moved : (events k).moves = true) :
    eligible axis junction green time (s.prev k) c (movementTarget (events k)) = true := by
  have row := List.all_eq_true.mp accepted k (List.mem_finRange k)
  simpa [pos, moved] using row

/-- This strictly stronger alternative checks every eligible claimant,
including one that loses pre-phase ownership. It is retained as a negative
boundary control; `ProtectedPolicy` uses the owner-aware checker below.
It requires an
actual hop/exit somewhere when any protected tag has a jointly clear,
eligible legal option; it does not promise a particular tag service. -/
def checkWorkConservingFrame (s : State cells cars) (routes : Routes cells)
    (events : Fin cars → Event (Fin cells)) (age : Fin cars → Nat)
    (L green time : Nat) (axis : AxisMap cells) (junction : Fin cells → Bool) : Bool :=
  let opportunity := (List.finRange cars).any fun k =>
    match s.pos k with
    | none => false
    | some c => decide (L ≤ age k) && (s.menu routes k).any fun d =>
      d != some c && clearOption s d && eligible axis junction green time (s.prev k) c d
  !opportunity || (List.finRange cars).any (fun j => (events j).moves)

theorem checkWorkConservingFrame_sound {s : State cells cars} {routes : Routes cells}
    {events : Fin cars → Event (Fin cells)} {age : Fin cars → Nat}
    {L green time : Nat} {axis : AxisMap cells} {junction : Fin cells → Bool}
    (accepted : checkWorkConservingFrame s routes events age L green time axis junction = true)
    {k : Fin cars} {c : Fin cells} {d : Option (Fin cells)}
    (pos : s.pos k = some c) (oldEnough : L ≤ age k) (offered : d ∈ s.menu routes k)
    (notSelf : d ≠ some c) (clear : clearOption s d = true)
    (allowed : eligible axis junction green time (s.prev k) c d = true) :
    ∃ j, (events j).moves = true := by
  have candidate : (s.menu routes k).any (fun q => q != some c && clearOption s q &&
      eligible axis junction green time (s.prev k) c q) = true :=
    List.any_eq_true.mpr ⟨d, offered, by simp [notSelf, clear, allowed]⟩
  have opportunity : (List.finRange cars).any (fun j => match s.pos j with
    | none => false
    | some c => decide (L ≤ age j) && (s.menu routes j).any fun d =>
      d != some c && clearOption s d && eligible axis junction green time (s.prev j) c d) = true :=
    List.any_eq_true.mpr ⟨k, List.mem_finRange k, by simp [pos, oldEnough, candidate]⟩
  have movement : (List.finRange cars).any (fun j => (events j).moves) = true := by
    simpa [checkWorkConservingFrame, opportunity] using accepted
  obtain ⟨j, _, go⟩ := List.any_eq_true.mp movement
  exact ⟨j, go⟩

def priority (age : Fin cars → Nat) (owner rival : Fin cars) : Prop :=
  age rival < age owner ∨ (age rival = age owner ∧ owner.val ≤ rival.val)

instance (age : Fin cars → Nat) (owner rival : Fin cars) : Decidable (priority age owner rival) :=
  inferInstanceAs (Decidable (_ ∨ (_ ∧ _)))

def claimant (s : State cells cars) (routes : Routes cells) (age : Fin cars → Nat)
    (L : Nat) (q : Fin cells) (k : Fin cars) : Bool :=
  clearOption s (some q) && match s.pos k with
  | none => false
  | some c => decide (L ≤ age k) && decide (some q ∈ s.menu routes k) && q != c

theorem claimant_sound {s : State cells cars} {routes : Routes cells} {age : Fin cars → Nat}
    {L : Nat} {q : Fin cells} {k : Fin cars} (claims : claimant s routes age L q k = true) :
    ∃ c, s.pos k = some c ∧ L ≤ age k ∧ some q ∈ s.menu routes k ∧ q ≠ c ∧
      clearOption s (some q) = true := by
  cases pos : s.pos k with
  | none => simp [claimant, pos] at claims
  | some c =>
    have facts : clearOption s (some q) = true ∧ (L ≤ age k ∧ some q ∈ s.menu routes k) ∧ q ≠ c := by
      simpa [claimant, pos] using claims
    exact ⟨c, rfl, facts.2.1.1, facts.2.1.2, facts.2.2, facts.1⟩

theorem claimant_complete {s : State cells cars} {routes : Routes cells} {age : Fin cars → Nat}
    {L : Nat} {q c : Fin cells} {k : Fin cars} (pos : s.pos k = some c)
    (oldEnough : L ≤ age k) (offered : some q ∈ s.menu routes k) (different : q ≠ c)
    (clear : clearOption s (some q) = true) : claimant s routes age L q k = true := by
  simp [claimant, pos, oldEnough, offered, different, clear]

/-- A local owner certificate covers exactly the vacant targets with
protected legal claimants and uses maximum age, ties to the lower tag.
There is no assumption about how long the owner will remain selected. -/
def checkOwnerTable (s : State cells cars) (routes : Routes cells) (age : Fin cars → Nat)
    (L : Nat) (owners : Fin cells → Option (Fin cars)) : Bool :=
  (List.finRange cells).all fun q => match owners q with
  | none => !((List.finRange cars).any (claimant s routes age L q))
  | some k => claimant s routes age L q k && (List.finRange cars).all fun j =>
      !(claimant s routes age L q j) || decide (priority age k j)

theorem checkOwnerTable_owner {s : State cells cars} {routes : Routes cells} {age : Fin cars → Nat}
    {L : Nat} {owners : Fin cells → Option (Fin cars)}
    (accepted : checkOwnerTable s routes age L owners = true) {q : Fin cells} {k : Fin cars}
    (owned : owners q = some k) :
    claimant s routes age L q k = true ∧
      ∀ j, claimant s routes age L q j = true → priority age k j := by
  have row := List.all_eq_true.mp accepted q (List.mem_finRange q)
  rw [owned] at row
  obtain ⟨ownClaim, maximal⟩ := Bool.and_eq_true_iff.mp row
  refine ⟨ownClaim, ?_⟩
  intro j claims
  have compared := List.all_eq_true.mp maximal j (List.mem_finRange j)
  simpa [claims] using compared

theorem checkOwnerTable_exists {s : State cells cars} {routes : Routes cells} {age : Fin cars → Nat}
    {L : Nat} {owners : Fin cells → Option (Fin cars)}
    (accepted : checkOwnerTable s routes age L owners = true) {q : Fin cells} {k : Fin cars}
    (claims : claimant s routes age L q k = true) : ∃ owner, owners q = some owner := by
  have row := List.all_eq_true.mp accepted q (List.mem_finRange q)
  cases assigned : owners q with
  | some owner => exact ⟨owner, rfl⟩
  | none =>
    have nonempty : (List.finRange cars).any (claimant s routes age L q) = true :=
      List.any_eq_true.mpr ⟨k, List.mem_finRange k, claims⟩
    simp [assigned, nonempty] at row

def owns (owners : Fin cells → Option (Fin cars)) (k : Fin cars) : Option (Fin cells) → Bool
  | none => true
  | some q => owners q == some k

/-- The PR #46 ownership order precedes phase eligibility. Only the
selected protected owner of a vacant street target triggers conservation;
an EXIT has no competing destination and needs no owner certificate. -/
def checkOwnerConservingFrame (s : State cells cars) (routes : Routes cells)
    (events : Fin cars → Event (Fin cells)) (age : Fin cars → Nat)
    (L green time : Nat) (axis : AxisMap cells) (junction : Fin cells → Bool)
    (owners : Fin cells → Option (Fin cars)) : Bool :=
  let opportunity := (List.finRange cars).any fun k =>
    match s.pos k with
    | none => false
    | some c => decide (L ≤ age k) && (s.menu routes k).any fun d =>
      d != some c && clearOption s d && owns owners k d &&
        eligible axis junction green time (s.prev k) c d
  !opportunity || (List.finRange cars).any (fun j => (events j).moves)

theorem checkOwnerConservingFrame_sound {s : State cells cars} {routes : Routes cells}
    {events : Fin cars → Event (Fin cells)} {age : Fin cars → Nat}
    {L green time : Nat} {axis : AxisMap cells} {junction : Fin cells → Bool}
    {owners : Fin cells → Option (Fin cars)}
    (accepted : checkOwnerConservingFrame s routes events age L green time axis junction owners = true)
    {k : Fin cars} {c : Fin cells} {d : Option (Fin cells)}
    (pos : s.pos k = some c) (oldEnough : L ≤ age k) (offered : d ∈ s.menu routes k)
    (notSelf : d ≠ some c) (clear : clearOption s d = true) (owned : owns owners k d = true)
    (allowed : eligible axis junction green time (s.prev k) c d = true) :
    ∃ j, (events j).moves = true := by
  have candidate : (s.menu routes k).any (fun q => q != some c && clearOption s q && owns owners k q &&
      eligible axis junction green time (s.prev k) c q) = true :=
    List.any_eq_true.mpr ⟨d, offered, by simp [notSelf, clear, owned, allowed]⟩
  have opportunity : (List.finRange cars).any (fun j => match s.pos j with
    | none => false
    | some c => decide (L ≤ age j) && (s.menu routes j).any fun d =>
      d != some c && clearOption s d && owns owners j d &&
        eligible axis junction green time (s.prev j) c d) = true :=
    List.any_eq_true.mpr ⟨k, List.mem_finRange k, by simp [pos, oldEnough, candidate]⟩
  have movement : (List.finRange cars).any (fun j => (events j).moves) = true := by
    simpa [checkOwnerConservingFrame, opportunity] using accepted
  obtain ⟨j, _, go⟩ := List.any_eq_true.mp movement
  exact ⟨j, go⟩

def checkStoppedAge (s : State cells cars) (events : Fin cars → Event (Fin cells))
    (age nextAge : Fin cars → Nat) : Bool :=
  (List.finRange cars).all fun k => match s.pos k with
    | none => true
    | some _ => (events k).moves || decide (nextAge k = age k + 1)

theorem checkStoppedAge_sound {s : State cells cars} {events : Fin cars → Event (Fin cells)}
    {age nextAge : Fin cars → Nat} (accepted : checkStoppedAge s events age nextAge = true)
    {k : Fin cars} {c : Fin cells} (pos : s.pos k = some c) (still : (events k).moves = false) :
    nextAge k = age k + 1 := by
  have row := List.all_eq_true.mp accepted k (List.mem_finRange k)
  simpa [pos, still] using row

def frameEvents (events : Fin cars → Event (Fin cells)) : Nat :=
  movementCount events + admissionCount events

private theorem no_events_are_stays (run : TrafficEvents.Run cells cars) (t : Nat)
    (quiet : frameEvents (run.events t) = 0) (k : Fin cars) :
    run.events t k = .stay ((run.state t).pos k) := by
  have movement := sumOn_term_le (fun j => (run.events t j).moveCount) k
  have admission := sumOn_term_le (fun j => (run.events t j).admissionCount) k
  change (run.events t k).moveCount ≤ movementCount (run.events t) at movement
  change (run.events t k).admissionCount ≤ admissionCount (run.events t) at admission
  change movementCount (run.events t) + admissionCount (run.events t) = 0 at quiet
  have source := checkEvent_source (checked_event (run.accepted t) k)
  cases action : run.events t k <;>
    simp_all [Event.moveCount, Event.admissionCount, Event.moves, Event.admitted, Event.before]
  all_goals omega

private theorem state_ext {s u : State cells cars} (pos : s.pos = u.pos) (prev : s.prev = u.prev) : s = u := by
  cases s
  cases u
  cases pos
  cases prev
  rfl

theorem quiet_state_step (run : TrafficEvents.Run cells cars) (t : Nat)
    (quiet : frameEvents (run.events t) = 0) : run.state (t + 1) = run.state t := by
  rw [run.evolves t]
  apply state_ext
  · funext k
    simp [applyBatch, no_events_are_stays run t quiet k, Event.after]
  · funext k
    simp [applyBatch, no_events_are_stays run t quiet k, Event.nextPrev]

theorem quiet_state_window (run : TrafficEvents.Run cells cars) (start length : Nat)
    (quiet : ∀ i < length, frameEvents (run.events (start + i)) = 0) :
    run.state (start + length) = run.state start := by
  induction length with
  | zero => simp
  | succ length ih =>
    rw [show start + (length + 1) = start + length + 1 by omega,
      quiet_state_step run (start + length) (quiet length (by omega))]
    exact ih (fun i hi => quiet i (by omega))

/-- The hypotheses are per-step executable rules on concrete state/event
objects. No bounded waiting, future grant, or block-progress premise occurs. -/
structure ProtectedPolicy (run : TrafficEvents.Run cells cars) (L green : Nat) where
  age : Nat → Fin cars → Nat
  axis : AxisMap cells
  junction : Fin cells → Bool
  owners : Nat → Fin cells → Option (Fin cars)
  ages : ∀ t, checkStoppedAge (run.state t) (run.events t) (age t) (age (t + 1)) = true
  ownership : ∀ t, checkOwnerTable (run.state t) run.routes (age t) L (owners t) = true
  permissions : ∀ t, checkSignalPermission (run.state t) (run.events t) green t axis junction = true
  conservation : ∀ t, checkOwnerConservingFrame (run.state t) run.routes (run.events t)
    (age t) L green t axis junction (owners t) = true

theorem ProtectedPolicy.quiet_age_window {run : TrafficEvents.Run cells cars} {L green : Nat}
    (policy : ProtectedPolicy run L green) (start length : Nat)
    (quiet : ∀ i < length, frameEvents (run.events (start + i)) = 0)
    (k : Fin cars) (c : Fin cells) (pos : (run.state start).pos k = some c) :
    policy.age (start + length) k = policy.age start k + length := by
  induction length with
  | zero => simp
  | succ length ih =>
    have quietPrefix := fun i (hi : i < length) => quiet i (by omega)
    have same := quiet_state_window run start length quietPrefix
    have atC : (run.state (start + length)).pos k = some c := by rw [same]; exact pos
    have stay : (run.events (start + length) k).moves = false := by
      rw [no_events_are_stays run _ (quiet length (by omega)) k]
      rfl
    have ticks := checkStoppedAge_sound (policy.ages (start + length)) atC stay
    rw [show start + (length + 1) = start + length + 1 by omega, ticks, ih quietPrefix]
    omega

/-- Once all present tags are protected, a quiet interval preserves the
certified oldest owner. Both candidate sets and all age differences are
derived to be constant; owner stability is not a premise of the policy. -/
theorem ProtectedPolicy.quiet_owner_stable {run : TrafficEvents.Run cells cars} {L green : Nat}
    (policy : ProtectedPolicy run L green) (start length : Nat)
    (quiet : ∀ i < length, frameEvents (run.events (start + i)) = 0)
    (mature : ∀ k c, (run.state start).pos k = some c → L ≤ policy.age start k)
    {q : Fin cells} {k : Fin cars} (owned : policy.owners start q = some k) :
    policy.owners (start + length) q = some k := by
  have same := quiet_state_window run start length quiet
  obtain ⟨oldClaim, oldMaximum⟩ := checkOwnerTable_owner (policy.ownership start) owned
  obtain ⟨c, pos, oldEnough, offered, different, clear⟩ := claimant_sound oldClaim
  have ageK := policy.quiet_age_window start length quiet k c pos
  have stillClaims : claimant (run.state (start + length)) run.routes
      (policy.age (start + length)) L q k = true :=
    claimant_complete (by rw [same]; exact pos) (by omega)
      (by rw [same]; exact offered) different (by rw [same]; exact clear)
  obtain ⟨j, assigned⟩ := checkOwnerTable_exists (policy.ownership (start + length)) stillClaims
  obtain ⟨newClaim, newMaximum⟩ := checkOwnerTable_owner (policy.ownership (start + length)) assigned
  obtain ⟨cj, posJ, _, offeredJ, differentJ, _⟩ := claimant_sound newClaim
  have oldPosJ : (run.state start).pos j = some cj := by rwa [same] at posJ
  have wasClaimant : claimant (run.state start) run.routes (policy.age start) L q j = true :=
    claimant_complete oldPosJ (mature j cj oldPosJ) (by rwa [same] at offeredJ) differentJ clear
  have firstPriority := oldMaximum j wasClaimant
  have secondPriority := newMaximum k stillClaims
  have ageJ := policy.quiet_age_window start length quiet j cj oldPosJ
  have equal : k = j := by
    apply Fin.ext
    dsimp [priority] at firstPriority secondPriority
    rw [ageK, ageJ] at secondPriority
    omega
  simpa [equal] using assigned

def blockLength (L green : Nat) : Nat := L + 2 * green

/-- On a productive DAG, the protected full-menu local rule forces a real
event in each nonempty `L + 2G` block. Admissions also count as real events,
so no assumption of unchanged occupancy is made across such an admission. -/
theorem ProtectedPolicy.block_progress {run : TrafficEvents.Run cells cars} {L green : Nat}
    (policy : ProtectedPolicy run L green) (greenPositive : 0 < green)
    (height : Fin cells → Nat)
    (productive : ∀ prev c, ∃ d ∈ run.routes prev c, d ≠ some c)
    (descends : ∀ prev c q, q ≠ c → some q ∈ run.routes prev c → height q < height c)
    (horizon : Nat) :
    BlockProgress (fun t => framePotential height (run.state t))
      (fun t => frameEvents (run.events t)) horizon (blockLength L green) := by
  intro start _ nonempty
  by_cases progress : ∃ i < blockLength L green, 0 < frameEvents (run.events (start + i))
  · exact progress
  have quiet (i : Nat) (hi : i < blockLength L green) : frameEvents (run.events (start + i)) = 0 := by
    have no : ¬ 0 < frameEvents (run.events (start + i)) := fun h => progress ⟨i, hi, h⟩
    omega
  have atStart : 0 < framePotential height (run.state start) := by
    simpa using nonempty 0 (by simp [blockLength]; omega)
  let base := start + L
  have warmQuiet : ∀ i < L, frameEvents (run.events (start + i)) = 0 :=
    fun i hi => quiet i (by dsimp [blockLength]; omega)
  have sameBase : run.state base = run.state start := quiet_state_window run start L warmQuiet
  have mature (k : Fin cars) (c : Fin cells) (pos : (run.state base).pos k = some c) :
      L ≤ policy.age base k := by
    have earlier : (run.state start).pos k = some c := by rwa [sameBase] at pos
    have age := policy.quiet_age_window start L warmQuiet k c earlier
    dsimp [base]
    omega
  have chosen : ∃ k c d, (run.state base).pos k = some c ∧ L ≤ policy.age base k ∧
      d ∈ (run.state base).menu run.routes k ∧ d ≠ some c ∧
      clearOption (run.state base) d = true ∧ owns (policy.owners base) k d = true := by
    obtain ⟨w, c, d, pos, offered, notSelf, clear⟩ :=
      clear_route_of_positive_work height (run.state base) run.routes productive descends (by rwa [sameBase])
    cases d with
    | none => exact ⟨w, c, none, pos, mature w c pos, offered, notSelf, clear, rfl⟩
    | some q =>
      have claims := claimant_complete pos (mature w c pos) offered
        (show q ≠ c by simpa using notSelf) clear
      obtain ⟨k, owned⟩ := checkOwnerTable_exists (policy.ownership base) claims
      obtain ⟨ownClaim, _⟩ := checkOwnerTable_owner (policy.ownership base) owned
      obtain ⟨ck, posK, ageK, offeredK, differentK, clearK⟩ := claimant_sound ownClaim
      exact ⟨k, ck, some q, posK, ageK, offeredK, by simpa using differentK, clearK,
        by simp [owns, owned]⟩
  obtain ⟨k, c, d, pos, oldEnough, offered, notSelf, clear, owned⟩ := chosen
  let routeAxis := policy.axis ((run.state base).prev k) c d
  obtain ⟨i, slot, allowed⟩ := RouteService.clock_service_window greenPositive routeAxis.isLt
    base (d.elim false policy.junction)
  have inside : L + i < blockLength L green := by dsimp [blockLength]; omega
  have quietSuffix : ∀ j < i, frameEvents (run.events (base + j)) = 0 := by
    intro j hj
    have before : L + j < blockLength L green := by omega
    simpa only [base, Nat.add_assoc] using quiet (L + j) before
  have same := quiet_state_window run base i quietSuffix
  have age := policy.quiet_age_window base i quietSuffix k c pos
  have stillOwned : owns (policy.owners (base + i)) k d = true := by
    cases d with
    | none => rfl
    | some q =>
      have ownerAtBase : policy.owners base q = some k := by simpa [owns] using owned
      have stable := policy.quiet_owner_stable base i quietSuffix mature ownerAtBase
      simp [owns, stable]
  have ready : eligible policy.axis policy.junction green (base + i)
      ((run.state (base + i)).prev k) c d = true := by
    rw [same]
    simpa only [eligible, routeAxis] using allowed
  obtain ⟨j, movement⟩ := checkOwnerConservingFrame_sound (policy.conservation (base + i))
    (k := k) (c := c) (d := d) (by rw [same]; exact pos) (by omega)
    (by rw [same]; exact offered) notSelf (by rw [same]; exact clear) stillOwned ready
  have recorded := sumOn_term_le (fun b => (run.events (base + i) b).moveCount) j
  have one : (run.events (base + i) j).moveCount = 1 := by simp [Event.moveCount, movement]
  rw [one] at recorded
  have silent : frameEvents (run.events (base + i)) = 0 := by
    simpa only [base, Nat.add_assoc] using quiet (L + i) inside
  change movementCount (run.events (base + i)) + admissionCount (run.events (base + i)) = 0 at silent
  change 1 ≤ movementCount (run.events (base + i)) at recorded
  omega

/-- The controller's local rules now discharge the formerly independent
block-progress premise in the concrete closed-DAG evacuation theorem. -/
theorem ProtectedPolicy.closed_DAG_evacuation {run : TrafficEvents.Run cells cars} {L green : Nat}
    (policy : ProtectedPolicy run L green) (greenPositive : 0 < green)
    (height : Fin cells → Nat) (D : Nat)
    (positive : ∀ c, 0 < height c) (bounded : ∀ c, height c ≤ D)
    (productive : ∀ prev c, ∃ d ∈ run.routes prev c, d ≠ some c)
    (descends : ∀ prev c q, q ≠ c → some q ∈ run.routes prev c → height q < height c)
    (start horizon : Nat)
    (within : start + blockLength L green * framePotential height (run.state start) ≤ horizon)
    (closed : ∀ i < blockLength L green * framePotential height (run.state start),
      admissionCount (run.events (start + i)) = 0) :
    ∀ k, (run.state (start + blockLength L green * framePotential height (run.state start))).pos k = none :=
  checked_closed_DAG_evacuation run height D positive bounded descends start (blockLength L green)
    horizon (policy.block_progress greenPositive height productive descends horizon) within closed

/-- An independently debited admission budget and the proved local-policy
progress rule give a prospective tagged deadline. No observed future count
is used to choose the quota, and no FIFO/merge-fairness premise is needed. -/
theorem ProtectedPolicy.quota_wait_of_budget {run : TrafficEvents.Run cells cars} {L green : Nat}
    (policy : ProtectedPolicy run L green) (greenPositive : 0 < green)
    (height : Fin cells → Nat) (D : Nat)
    (positive : ∀ c, 0 < height c) (bounded : ∀ c, height c ≤ D)
    (productive : ∀ prev c, ∃ d ∈ run.routes prev c, d ≠ some c)
    (descends : ∀ prev c q, q ≠ c → some q ∈ run.routes prev c → height q < height c)
    (budget : AdmissionBudget (fun t => admissionCount (run.events t)))
    (start horizon : Nat) (k : Fin cars) (c : Fin cells)
    (present : (run.state start).pos k = some c)
    (within : start + TrafficWork.waitBound (blockLength L green)
      (framePotential height (run.state start)) (height c) D (budget.remaining start) ≤ horizon) :
    ∃ i < TrafficWork.waitBound (blockLength L green) (framePotential height (run.state start))
      (height c) D (budget.remaining start), (run.events (start + i) k).moves = true := by
  let allowed := checked_run_work_allowed run height D positive bounded descends
  let focal := checkedFocal run height D allowed k
  exact focal.quota_wait_of_budget budget start (blockLength L green) horizon c present (positive c)
    (policy.block_progress greenPositive height productive descends horizon) within

/-- A finite controller certificate. Every controller rule is required only
for transitions strictly before `horizon`; no continuation of the policy is
assumed. The event run is still the checked state/event object supplied to
the work layer, whose finite-history checker is separate. -/
structure ProtectedPrefix (run : TrafficEvents.Run cells cars) (L green horizon : Nat) where
  age : Nat → Fin cars → Nat
  axis : AxisMap cells
  junction : Fin cells → Bool
  owners : Nat → Fin cells → Option (Fin cars)
  ages : ∀ t, t < horizon →
    checkStoppedAge (run.state t) (run.events t) (age t) (age (t + 1)) = true
  ownership : ∀ t, t < horizon →
    checkOwnerTable (run.state t) run.routes (age t) L (owners t) = true
  permissions : ∀ t, t < horizon →
    checkSignalPermission (run.state t) (run.events t) green t axis junction = true
  conservation : ∀ t, t < horizon →
    checkOwnerConservingFrame (run.state t) run.routes (run.events t)
      (age t) L green t axis junction (owners t) = true

/-- This finite executable predicate reads ages through `horizon` and
state/event/owner records strictly before it. Values beyond that prefix
cannot affect acceptance. -/
def checkProtectedPrefix (run : TrafficEvents.Run cells cars) (L green horizon : Nat)
    (age : Nat → Fin cars → Nat) (axis : AxisMap cells) (junction : Fin cells → Bool)
    (owners : Nat → Fin cells → Option (Fin cars)) : Bool :=
  (List.range horizon).all fun t =>
    checkStoppedAge (run.state t) (run.events t) (age t) (age (t + 1)) &&
    checkOwnerTable (run.state t) run.routes (age t) L (owners t) &&
    checkSignalPermission (run.state t) (run.events t) green t axis junction &&
    checkOwnerConservingFrame (run.state t) run.routes (run.events t)
      (age t) L green t axis junction (owners t)

theorem checkProtectedPrefix_sound {run : TrafficEvents.Run cells cars} {L green horizon : Nat}
    {age : Nat → Fin cars → Nat} {axis : AxisMap cells} {junction : Fin cells → Bool}
    {owners : Nat → Fin cells → Option (Fin cars)}
    (accepted : checkProtectedPrefix run L green horizon age axis junction owners = true)
    (t : Nat) (inside : t < horizon) :
    checkStoppedAge (run.state t) (run.events t) (age t) (age (t + 1)) = true ∧
    checkOwnerTable (run.state t) run.routes (age t) L (owners t) = true ∧
    checkSignalPermission (run.state t) (run.events t) green t axis junction = true ∧
    checkOwnerConservingFrame (run.state t) run.routes (run.events t)
      (age t) L green t axis junction (owners t) = true := by
  have row := List.all_eq_true.mp accepted t (List.mem_range.mpr inside)
  simpa only [Bool.and_eq_true_iff, and_assoc] using row

def ProtectedPrefix.ofChecked (run : TrafficEvents.Run cells cars) (L green horizon : Nat)
    (age : Nat → Fin cars → Nat) (axis : AxisMap cells) (junction : Fin cells → Bool)
    (owners : Nat → Fin cells → Option (Fin cars))
    (accepted : checkProtectedPrefix run L green horizon age axis junction owners = true) :
    ProtectedPrefix run L green horizon where
  age := age
  axis := axis
  junction := junction
  owners := owners
  ages t ht := (checkProtectedPrefix_sound accepted t ht).1
  ownership t ht := (checkProtectedPrefix_sound accepted t ht).2.1
  permissions t ht := (checkProtectedPrefix_sound accepted t ht).2.2.1
  conservation t ht := (checkProtectedPrefix_sound accepted t ht).2.2.2

def ProtectedPolicy.prefix {run : TrafficEvents.Run cells cars} {L green : Nat}
    (policy : ProtectedPolicy run L green) (horizon : Nat) : ProtectedPrefix run L green horizon where
  age := policy.age
  axis := policy.axis
  junction := policy.junction
  owners := policy.owners
  ages t _ := policy.ages t
  ownership t _ := policy.ownership t
  permissions t _ := policy.permissions t
  conservation t _ := policy.conservation t

theorem ProtectedPrefix.quiet_age_window {run : TrafficEvents.Run cells cars} {L green horizon : Nat}
    (policy : ProtectedPrefix run L green horizon) (start length : Nat)
    (within : start + length ≤ horizon)
    (quiet : ∀ i < length, frameEvents (run.events (start + i)) = 0)
    (k : Fin cars) (c : Fin cells) (pos : (run.state start).pos k = some c) :
    policy.age (start + length) k = policy.age start k + length := by
  induction length with
  | zero => simp
  | succ length ih =>
    have quietPrefix := fun i (hi : i < length) => quiet i (by omega)
    have same := quiet_state_window run start length quietPrefix
    have atC : (run.state (start + length)).pos k = some c := by rw [same]; exact pos
    have stay : (run.events (start + length) k).moves = false := by
      rw [no_events_are_stays run _ (quiet length (by omega)) k]
      rfl
    have ticks := checkStoppedAge_sound (policy.ages (start + length) (by omega)) atC stay
    rw [show start + (length + 1) = start + length + 1 by omega,
      ticks, ih (by omega) quietPrefix]
    omega

theorem ProtectedPrefix.quiet_owner_stable {run : TrafficEvents.Run cells cars} {L green horizon : Nat}
    (policy : ProtectedPrefix run L green horizon) (start length : Nat)
    (within : start + length < horizon)
    (quiet : ∀ i < length, frameEvents (run.events (start + i)) = 0)
    (mature : ∀ k c, (run.state start).pos k = some c → L ≤ policy.age start k)
    {q : Fin cells} {k : Fin cars} (owned : policy.owners start q = some k) :
    policy.owners (start + length) q = some k := by
  have same := quiet_state_window run start length quiet
  obtain ⟨oldClaim, oldMaximum⟩ :=
    checkOwnerTable_owner (policy.ownership start (by omega)) owned
  obtain ⟨c, pos, oldEnough, offered, different, clear⟩ := claimant_sound oldClaim
  have ageK := policy.quiet_age_window start length (by omega) quiet k c pos
  have stillClaims : claimant (run.state (start + length)) run.routes
      (policy.age (start + length)) L q k = true :=
    claimant_complete (by rw [same]; exact pos) (by omega)
      (by rw [same]; exact offered) different (by rw [same]; exact clear)
  obtain ⟨j, assigned⟩ :=
    checkOwnerTable_exists (policy.ownership (start + length) within) stillClaims
  obtain ⟨newClaim, newMaximum⟩ :=
    checkOwnerTable_owner (policy.ownership (start + length) within) assigned
  obtain ⟨cj, posJ, _, offeredJ, differentJ, _⟩ := claimant_sound newClaim
  have oldPosJ : (run.state start).pos j = some cj := by rwa [same] at posJ
  have wasClaimant : claimant (run.state start) run.routes (policy.age start) L q j = true :=
    claimant_complete oldPosJ (mature j cj oldPosJ) (by rwa [same] at offeredJ) differentJ clear
  have firstPriority := oldMaximum j wasClaimant
  have secondPriority := newMaximum k stillClaims
  have ageJ := policy.quiet_age_window start length (by omega) quiet j cj oldPosJ
  have equal : k = j := by
    apply Fin.ext
    dsimp [priority] at firstPriority secondPriority
    rw [ageK, ageJ] at secondPriority
    omega
  simpa [equal] using assigned

/-- The finite counterpart needs controller checks only inside the tested
horizon. In particular, a quiet block never invokes an owner or service
certificate at its right endpoint or beyond the supplied prefix. -/
theorem ProtectedPrefix.block_progress {run : TrafficEvents.Run cells cars} {L green horizon : Nat}
    (policy : ProtectedPrefix run L green horizon) (greenPositive : 0 < green)
    (height : Fin cells → Nat)
    (productive : ∀ prev c, ∃ d ∈ run.routes prev c, d ≠ some c)
    (descends : ∀ prev c q, q ≠ c → some q ∈ run.routes prev c → height q < height c) :
    BlockProgress (fun t => framePotential height (run.state t))
      (fun t => frameEvents (run.events t)) horizon (blockLength L green) := by
  intro start within nonempty
  by_cases progress : ∃ i < blockLength L green, 0 < frameEvents (run.events (start + i))
  · exact progress
  have quiet (i : Nat) (hi : i < blockLength L green) : frameEvents (run.events (start + i)) = 0 := by
    have no : ¬ 0 < frameEvents (run.events (start + i)) := fun h => progress ⟨i, hi, h⟩
    omega
  have atStart : 0 < framePotential height (run.state start) := by
    simpa using nonempty 0 (by simp [blockLength]; omega)
  let base := start + L
  have baseWithin : base < horizon := by dsimp [base, blockLength] at *; omega
  have warmQuiet : ∀ i < L, frameEvents (run.events (start + i)) = 0 :=
    fun i hi => quiet i (by dsimp [blockLength]; omega)
  have sameBase : run.state base = run.state start := quiet_state_window run start L warmQuiet
  have mature (k : Fin cars) (c : Fin cells) (pos : (run.state base).pos k = some c) :
      L ≤ policy.age base k := by
    have earlier : (run.state start).pos k = some c := by rwa [sameBase] at pos
    have age := policy.quiet_age_window start L (by dsimp [base] at baseWithin; omega)
      warmQuiet k c earlier
    dsimp [base]
    omega
  have chosen : ∃ k c d, (run.state base).pos k = some c ∧ L ≤ policy.age base k ∧
      d ∈ (run.state base).menu run.routes k ∧ d ≠ some c ∧
      clearOption (run.state base) d = true ∧ owns (policy.owners base) k d = true := by
    obtain ⟨w, c, d, pos, offered, notSelf, clear⟩ :=
      clear_route_of_positive_work height (run.state base) run.routes productive descends (by rwa [sameBase])
    cases d with
    | none => exact ⟨w, c, none, pos, mature w c pos, offered, notSelf, clear, rfl⟩
    | some q =>
      have claims := claimant_complete pos (mature w c pos) offered
        (show q ≠ c by simpa using notSelf) clear
      obtain ⟨k, owned⟩ := checkOwnerTable_exists (policy.ownership base baseWithin) claims
      obtain ⟨ownClaim, _⟩ := checkOwnerTable_owner (policy.ownership base baseWithin) owned
      obtain ⟨ck, posK, ageK, offeredK, differentK, clearK⟩ := claimant_sound ownClaim
      exact ⟨k, ck, some q, posK, ageK, offeredK, by simpa using differentK, clearK,
        by simp [owns, owned]⟩
  obtain ⟨k, c, d, pos, oldEnough, offered, notSelf, clear, owned⟩ := chosen
  let routeAxis := policy.axis ((run.state base).prev k) c d
  obtain ⟨i, slot, allowed⟩ := RouteService.clock_service_window greenPositive routeAxis.isLt
    base (d.elim false policy.junction)
  have inside : L + i < blockLength L green := by dsimp [blockLength]; omega
  have stepWithin : base + i < horizon := by dsimp [base, blockLength] at *; omega
  have quietSuffix : ∀ j < i, frameEvents (run.events (base + j)) = 0 := by
    intro j hj
    have before : L + j < blockLength L green := by omega
    simpa only [base, Nat.add_assoc] using quiet (L + j) before
  have same := quiet_state_window run base i quietSuffix
  have age := policy.quiet_age_window base i (by omega) quietSuffix k c pos
  have stillOwned : owns (policy.owners (base + i)) k d = true := by
    cases d with
    | none => rfl
    | some q =>
      have ownerAtBase : policy.owners base q = some k := by simpa [owns] using owned
      have stable := policy.quiet_owner_stable base i stepWithin quietSuffix mature ownerAtBase
      simp [owns, stable]
  have ready : eligible policy.axis policy.junction green (base + i)
      ((run.state (base + i)).prev k) c d = true := by
    rw [same]
    simpa only [eligible, routeAxis] using allowed
  obtain ⟨j, movement⟩ :=
    checkOwnerConservingFrame_sound (policy.conservation (base + i) stepWithin)
      (k := k) (c := c) (d := d) (by rw [same]; exact pos) (by omega)
      (by rw [same]; exact offered) notSelf (by rw [same]; exact clear) stillOwned ready
  have recorded := sumOn_term_le (fun b => (run.events (base + i) b).moveCount) j
  have one : (run.events (base + i) j).moveCount = 1 := by simp [Event.moveCount, movement]
  rw [one] at recorded
  have silent : frameEvents (run.events (base + i)) = 0 := by
    simpa only [base, Nat.add_assoc] using quiet (L + i) inside
  change movementCount (run.events (base + i)) + admissionCount (run.events (base + i)) = 0 at silent
  change 1 ≤ movementCount (run.events (base + i)) at recorded
  omega

theorem ProtectedPrefix.closed_DAG_evacuation {run : TrafficEvents.Run cells cars}
    {L green horizon : Nat} (policy : ProtectedPrefix run L green horizon) (greenPositive : 0 < green)
    (height : Fin cells → Nat) (D : Nat)
    (positive : ∀ c, 0 < height c) (bounded : ∀ c, height c ≤ D)
    (productive : ∀ prev c, ∃ d ∈ run.routes prev c, d ≠ some c)
    (descends : ∀ prev c q, q ≠ c → some q ∈ run.routes prev c → height q < height c)
    (start : Nat)
    (within : start + blockLength L green * framePotential height (run.state start) ≤ horizon)
    (closed : ∀ i < blockLength L green * framePotential height (run.state start),
      admissionCount (run.events (start + i)) = 0) :
    ∀ k, (run.state (start + blockLength L green * framePotential height (run.state start))).pos k = none :=
  checked_closed_DAG_evacuation run height D positive bounded descends start (blockLength L green)
    horizon (policy.block_progress greenPositive height productive descends) within closed

theorem ProtectedPrefix.quota_wait_of_budget {run : TrafficEvents.Run cells cars}
    {L green horizon : Nat} (policy : ProtectedPrefix run L green horizon) (greenPositive : 0 < green)
    (height : Fin cells → Nat) (D : Nat)
    (positive : ∀ c, 0 < height c) (bounded : ∀ c, height c ≤ D)
    (productive : ∀ prev c, ∃ d ∈ run.routes prev c, d ≠ some c)
    (descends : ∀ prev c q, q ≠ c → some q ∈ run.routes prev c → height q < height c)
    (budget : AdmissionBudget (fun t => admissionCount (run.events t)))
    (start : Nat) (k : Fin cars) (c : Fin cells)
    (present : (run.state start).pos k = some c)
    (within : start + TrafficWork.waitBound (blockLength L green)
      (framePotential height (run.state start)) (height c) D (budget.remaining start) ≤ horizon) :
    ∃ i < TrafficWork.waitBound (blockLength L green) (framePotential height (run.state start))
      (height c) D (budget.remaining start), (run.events (start + i) k).moves = true := by
  let allowed := checked_run_work_allowed run height D positive bounded descends
  let focal := checkedFocal run height D allowed k
  exact focal.quota_wait_of_budget budget start (blockLength L green) horizon c present (positive c)
    (policy.block_progress greenPositive height productive descends) within

/-! A complete, nonvacuous instance of the local policy. It exits its one
on-street tag immediately and stays outside thereafter. These are synthetic
model events, not a reconstruction of a field trajectory. -/
namespace Example

def state (occupied : Bool) : State 1 1 where
  pos _ := if occupied then some 0 else none
  prev _ := none
  exclusive _ _ _ _ _ := Subsingleton.elim _ _

def event (t : Nat) : Event (Fin 1) := if t = 0 then .exit 0 else .stay none

def run : TrafficEvents.Run 1 1 where
  routes _ _ := [none]
  entries _ := false
  state t := state (t == 0)
  events t _ := event t
  accepted t := by
    cases t with
    | zero => decide
    | succ t => simp [checkBatch, checkState, checkEvent, state, event,
        Event.before, Event.after, Event.routeAllowed, Event.arrivalTarget, List.finRange_succ]
  evolves t := by
    apply state_ext
    · funext k
      cases t with
      | zero => rfl
      | succ t => simp [applyBatch, state, event, Event.after]
    · funext k
      cases t with
      | zero => rfl
      | succ t => simp [applyBatch, state, event, Event.nextPrev]

def policy : ProtectedPolicy run 0 1 where
  age _ _ := 0
  axis _ _ _ := 0
  junction _ := false
  owners _ _ := none
  ages t := by
    cases t with
    | zero => decide
    | succ t => simp [checkStoppedAge, run, state, List.finRange_succ]
  permissions t := by
    cases t with
    | zero => decide
    | succ t => simp [checkSignalPermission, run, state, List.finRange_succ, event, Event.moves]
  ownership t := by
    cases t with
    | zero => decide
    | succ t => simp [checkOwnerTable, claimant, clearOption, run, state, State.occ, List.finRange_succ]
  conservation t := by
    cases t with
    | zero => decide
    | succ t => simp [checkOwnerConservingFrame, run, state, List.finRange_succ]

theorem proved_block_progress (horizon : Nat) :
    BlockProgress (fun t => framePotential (fun _ => 1) (run.state t))
      (fun t => frameEvents (run.events t)) horizon 2 := by
  apply policy.block_progress (by decide) (fun _ => 1)
  · intro prev c
    exact ⟨none, by simp [run], by simp⟩
  · intro prev c q _ offered
    simp [run] at offered

end Example

end BML.TrafficPolicy
