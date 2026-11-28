import BML.TrafficPolicy

/-!
# The protected event model supplies the original R2 service interface

The joint vacancy/service premises of `RouteProgress` are derived here for
the checked protected model on a productive DAG with nonrenewing admission
tokens. This is a uniform, deliberately conservative conversion of the
stronger elapsed-time work bound. It does not assert service for the legacy
random-routing policy or for an unrestricted stream of admissions.

Controller checks are needed only inside the finite certified horizon.
The separate token-debit invariant is the `TrafficWork.AdmissionBudget`
contract. Initial token count is fixed before the waiting window.
-/
namespace BML.TrafficServiceBridge

open TrafficEvents TrafficWork TrafficPolicy

/-- A single cap valid for every starting state and focal tag in the
certified horizon. `quota` is the initial admission token count. -/
def serviceCap (cars D L green quota : Nat) : Nat :=
  blockLength L green * (cars * D + (D + 1) * quota + 1)

theorem serviceCap_pos (cars D L quota : Nat) {green : Nat} (positive : 0 < green) :
    0 < serviceCap cars D L green quota := by
  apply Nat.mul_pos
  · dsimp [blockLength]
    omega
  · omega

private theorem sum_le_length_mul {Tag : Type} (tags : List Tag) (quantity : Tag → Nat) (D : Nat)
    (bounded : ∀ k ∈ tags, quantity k ≤ D) : (tags.map quantity).sum ≤ tags.length * D := by
  induction tags with
  | nil => simp
  | cons k rest ih =>
    have head := bounded k (List.mem_cons_self ..)
    have tail := ih (fun j hj => bounded j (List.mem_cons_of_mem _ hj))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- At most one bounded-height contribution occurs per finite model tag,
including tags currently outside the modeled network. -/
theorem framePotential_le (height : Fin cells → Nat) (D : Nat)
    (bounded : ∀ c, height c ≤ D) (state : State cells cars) :
    framePotential height state ≤ cars * D := by
  have perTag (k : Fin cars) : workAt height (state.pos k) ≤ D := by
    cases pos : state.pos k with
    | none => simp [workAt]
    | some c => simpa [workAt, pos] using bounded c
  have total := sum_le_length_mul (List.finRange cars)
    (fun k => workAt height (state.pos k)) D (fun k _ => perTag k)
  simpa [framePotential, sumOn] using total

theorem remaining_le_initial {admissions : Nat → Nat}
    (budget : AdmissionBudget admissions) (start : Nat) :
    budget.remaining start ≤ budget.remaining 0 := by
  have accounted := budget.accounting 0 start
  simp only [Nat.zero_add] at accounted
  omega

/-- The sharper per-tag elapsed-time bound is uniformly dominated by the
cap, independently of its starting time or occupied cell. -/
theorem focal_wait_le_cap (run : TrafficEvents.Run cells cars) (height : Fin cells → Nat)
    (D L green : Nat) (bounded : ∀ c, height c ≤ D)
    (budget : AdmissionBudget (fun t => admissionCount (run.events t)))
    (start : Nat) (c : Fin cells) :
    TrafficWork.waitBound (blockLength L green) (framePotential height (run.state start))
      (height c) D (budget.remaining start) ≤ serviceCap cars D L green (budget.remaining 0) := by
  have potential := framePotential_le height D bounded (run.state start)
  have tokens := remaining_le_initial budget start
  have tokenWork := Nat.mul_le_mul_left (D + 1) tokens
  apply Nat.mul_le_mul_left
  omega

/-- The ordered checkpoints in the original service definition cannot
outnumber the halfsteps of their containing window. -/
theorem ordered_slots_cardinality {K length : Nat} (slots : Fin K → Fin length)
    (ordered : ∀ i j, i < j → slots i < slots j) : K ≤ length := by
  have lower : ∀ n (hn : n < K), n ≤ (slots ⟨n, hn⟩).val := by
    intro n
    induction n with
    | zero => intro hn; omega
    | succ n ih =>
      intro hn
      have previous : n < K := by omega
      have below := ih previous
      have increasing := ordered ⟨n, previous⟩ ⟨n + 1, hn⟩ (by change n < n + 1; omega)
      change (slots ⟨n, previous⟩).val < (slots ⟨n + 1, hn⟩).val at increasing
      omega
  cases K with
  | zero => omega
  | succ K =>
    have below := lower K (by omega)
    have above := (slots ⟨K, by omega⟩).isLt
    omega

/-- This is PR #44's actual `Trace.BoundedService`, not a parallel waiting
predicate. The elapsed-time quota theorem is stronger than required: once
the ordered slots force a long enough window, the focal tag must move,
regardless of which destination supplied those clear checkpoints. -/
theorem protected_bounded_service {run : TrafficEvents.Run cells cars} {L green horizon : Nat}
    (policy : ProtectedPrefix run L green horizon) (greenPositive : 0 < green)
    (height : Fin cells → Nat) (D : Nat)
    (positive : ∀ c, 0 < height c) (bounded : ∀ c, height c ≤ D)
    (productive : ∀ prev c, ∃ d ∈ run.routes prev c, d ≠ some c)
    (descends : ∀ prev c q, q ≠ c → some q ∈ run.routes prev c → height q < height c)
    (budget : AdmissionBudget (fun t => admissionCount (run.events t)))
    (plans : Nat → Fin cars → LaneDeadlock.Plan (Fin cells)) :
    (run.toRouteTrace plans).BoundedService horizon
      (serviceCap cars D L green (budget.remaining 0)) := by
  intro start length k c _ within present _ waiting slots ordered _
  have slotsFit := ordered_slots_cardinality slots ordered
  have cap := focal_wait_le_cap run height D L green bounded budget start c
  have deadline : start + TrafficWork.waitBound (blockLength L green)
      (framePotential height (run.state start)) (height c) D (budget.remaining start) ≤ horizon := by
    omega
  change (run.state start).pos k = some c at present
  obtain ⟨i, before, moved⟩ := policy.quota_wait_of_budget greenPositive height D
    positive bounded productive descends budget start k c present deadline
  exact waiting i (by omega) moved

/-- The two dynamic premises used together by the R2 rank recurrence are
both consequences of the explicit checked-event and protected-policy
rules, under the stated DAG and admission-budget scope. -/
theorem protected_joint_guarantee {run : TrafficEvents.Run cells cars} {L green horizon : Nat}
    (policy : ProtectedPrefix run L green horizon) (greenPositive : 0 < green)
    (height : Fin cells → Nat) (D : Nat)
    (positive : ∀ c, 0 < height c) (bounded : ∀ c, height c ≤ D)
    (productive : ∀ prev c, ∃ d ∈ run.routes prev c, d ≠ some c)
    (descends : ∀ prev c q, q ≠ c → some q ∈ run.routes prev c → height q < height c)
    (budget : AdmissionBudget (fun t => admissionCount (run.events t)))
    (plans : Nat → Fin cars → LaneDeadlock.Plan (Fin cells)) :
    (run.toRouteTrace plans).LeavesVacancy ∧
      (run.toRouteTrace plans).BoundedService horizon
        (serviceCap cars D L green (budget.remaining 0)) :=
  ⟨run.toRouteTrace_leaves_vacancy plans,
    protected_bounded_service policy greenPositive height D positive bounded productive descends budget plans⟩

/-- The existing rank recurrence can now be applied directly. Its structural
rank certificate and arrival-menu correspondence remain explicit,
independent inputs; the dynamic service/vacancy premises are derived. -/
theorem protected_moves_before_rank_bound {run : TrafficEvents.Run cells cars} {L green horizon : Nat}
    (policy : ProtectedPrefix run L green horizon) (greenPositive : 0 < green)
    (height : Fin cells → Nat) (D : Nat)
    (positive : ∀ c, 0 < height c) (bounded : ∀ c, height c ≤ D)
    (productive : ∀ prev c, ∃ d ∈ run.routes prev c, d ≠ some c)
    (descends : ∀ prev c q, q ≠ c → some q ∈ run.routes prev c → height q < height c)
    (budget : AdmissionBudget (fun t => admissionCount (run.events t)))
    (plans : Nat → Fin cars → LaneDeadlock.Plan (Fin cells))
    {roads : List (Fin cells)} {turns : RouteTrap.Turns (Fin cells)}
    {rank : Fin cells → Option Nat}
    (checked : RouteTrap.checkRanks roads turns rank = true)
    (arrivals : (run.toRouteTrace plans).FollowsArrivals roads turns) (n : Nat) :
    ∀ t k c, ((run.toRouteTrace plans).state t).pos k = some c → rank c = some n →
      t + RouteProgress.waitBound (serviceCap cars D L green (budget.remaining 0)) n ≤ horizon →
      ∃ i < RouteProgress.waitBound (serviceCap cars D L green (budget.remaining 0)) n,
        (run.toRouteTrace plans).moves (t + i) k := by
  obtain ⟨vacancy, service⟩ := protected_joint_guarantee policy greenPositive height D
    positive bounded productive descends budget plans
  exact (run.toRouteTrace plans).moves_before_rank_bound checked arrivals vacancy
    (serviceCap_pos cars D L (budget.remaining 0) greenPositive) service n

end BML.TrafficServiceBridge
