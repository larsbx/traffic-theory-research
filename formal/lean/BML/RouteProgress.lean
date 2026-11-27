import BML.RouteTrap

/-! # R2 progress from vacancy and service

Ranks come from the structural safe-cell checker. Service is a separate
property of a trace. The vacancy premise holds when a departing vehicle's
cell stays empty until the next checkpoint, as with CLASSIC and no same-step
refill. Movement records hop and exit events even when a tag re-enters.
-/
namespace BML.RouteProgress

open LaneDeadlock (Snapshot)
open RouteTrap (Turns checkRanks rank_witness descends)

variable {Cell Car : Type}

structure Trace (Cell Car : Type) where
  state : Nat → Snapshot Cell Car
  moves : Nat → Car → Prop
  menu : Nat → Car → List (Option Cell)
  stays : ∀ t k c, (state t).pos k = some c → ¬ moves t k →
    (state (t + 1)).pos k = some c ∧ menu (t + 1) k = menu t k

def Trace.LeavesVacancy (run : Trace Cell Car) : Prop :=
  ∀ t k c, (run.state t).pos k = some c → run.moves t k →
    (run.state (t + 1)).occ c = none

def Trace.FollowsArrivals (run : Trace Cell Car) (roads : List Cell) (turns : Turns Cell) : Prop :=
  ∀ t k c, (run.state t).pos k = some c → c ∈ roads ∧ run.menu t k ∈ turns c

/-- An exit is always clear of occupying vehicles. Signals, contention,
breakdowns and route choice are accounted for in the service hypothesis. -/
def Trace.ClearAt (run : Trace Cell Car) (dest : Option Cell) (t : Nat) : Prop :=
  dest.elim True (fun c => (run.state t).occ c = none)

/-- A car waiting throughout a window cannot see one legal option clear at
`K` distinct start-of-half-step checkpoints. The law of turns is fixed for
the waiting car's arrival until it records a hop or exit. -/
def Trace.BoundedService (run : Trace Cell Car) (horizon K : Nat) : Prop :=
  ∀ t len k c d, t + len ≤ horizon → (run.state t).pos k = some c → d ∈ run.menu t k →
    (∀ i < len, ¬ run.moves (t + i) k) →
    ∀ slots : Fin K → Fin len, (∀ i j, i < j → slots i < slots j) →
      (∀ i, run.ClearAt d (t + (slots i).val)) → False

/-- Recurring vacancy of an arrival option is enough for eventual service.
The requirement applies even when the vacancy windows are intermittent. -/
def Trace.OpportunityFair (run : Trace Cell Car) : Prop :=
  ∀ t k c d, (run.state t).pos k = some c → d ∈ run.menu t k →
    (∀ start ≥ t, ∃ u ≥ start, run.ClearAt d u) →
    ∃ i, run.moves (t + i) k

theorem Trace.vacancy_by_move (run : Trace Cell Car) {k : Car} {c : Cell} {t i : Nat}
    (vacates : run.LeavesVacancy) (pos : (run.state t).pos k = some c)
    (moved : run.moves (t + i) k) :
    ∃ j ≤ i + 1, (run.state (t + j)).occ c = none := by
  induction i generalizing t with
  | zero =>
    exact ⟨1, Nat.le_refl _, vacates t k c pos (by simpa using moved)⟩
  | succ i ih =>
    by_cases now : run.moves t k
    · exact ⟨1, by omega, vacates t k c pos now⟩
    · have same : t + 1 + i = t + (i + 1) := by omega
      obtain ⟨j, hj, vacant⟩ := ih (run.stays t k c pos now).1 (same.symm ▸ moved)
      have next : t + (j + 1) = t + 1 + j := by omega
      exact ⟨j + 1, by omega, next ▸ vacant⟩

private theorem lower_rank {rank : Cell → Option Nat} {q : Cell} {n : Nat}
    (lower : descends rank n (some q) = true) : ∃ m < n, rank q = some m := by
  cases r : rank q with
  | none => simp [descends, r] at lower
  | some m => exact ⟨m, by simpa [descends, r] using lower, rfl⟩

/-- Every ranked vehicle eventually records a move under opportunity
fairness, including vehicles below the highest rank on a partially ranked map. -/
theorem Trace.eventually_moves_of_rank (run : Trace Cell Car)
    {roads : List Cell} {turns : Turns Cell} {rank : Cell → Option Nat}
    (checked : checkRanks roads turns rank = true) (arrivals : run.FollowsArrivals roads turns)
    (vacates : run.LeavesVacancy) (fair : run.OpportunityFair) (n : Nat) :
    ∀ t k c, (run.state t).pos k = some c → rank c = some n →
      ∃ i, run.moves (t + i) k := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro t k c pos atRank
    obtain ⟨road, menu⟩ := arrivals t k c pos
    obtain ⟨d, offered, lower⟩ := rank_witness checked road atRank menu
    apply fair t k c d pos offered
    intro start ht
    cases d with
    | none => exact ⟨start, Nat.le_refl _, trivial⟩
    | some q =>
      obtain ⟨m, hm, rq⟩ := lower_rank lower
      cases occ : (run.state start).occ q with
      | none => exact ⟨start, Nat.le_refl _, occ⟩
      | some b =>
        have bp := ((run.state start).occ_iff_pos q b).mp occ
        obtain ⟨i, moved⟩ := ih m hm start b q bp rq
        obtain ⟨j, _, vacant⟩ := run.vacancy_by_move vacates bp moved
        exact ⟨start + j, Nat.le_add_right _ _, vacant⟩

/-- Block length for finding a clear option at rank `n`. -/
def stride (K : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => K * stride K n + 1

def waitBound (K n : Nat) : Nat := K * stride K n

private theorem stride_pos (K n : Nat) : 0 < stride K n := by
  cases n <;> simp [stride]

private theorem stride_mono {K : Nat} (positive : 0 < K) {m n : Nat} (h : m ≤ n) :
    stride K m ≤ stride K n := by
  induction n with
  | zero =>
    have zero : m = 0 := by omega
    simp [zero]
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le h with lt | eq
    · have le := Nat.le_mul_of_pos_left (stride K n) positive
      apply Nat.le_trans (ih (Nat.le_of_lt_succ lt))
      simp only [stride]
      omega
    · simp [eq]

private theorem lower_wait {K m n : Nat} (positive : 0 < K) (h : m < n) :
    waitBound K m < stride K n :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self (K * stride K m))
    (stride_mono positive (Nat.succ_le_of_lt h))

/-- The half-step offset of the next movement is less than the rank budget.
The bound depends on the service cap and rank, without restricting which
legal move is actually served. -/
theorem Trace.moves_before_rank_bound (run : Trace Cell Car)
    {roads : List Cell} {turns : Turns Cell} {rank : Cell → Option Nat}
    (checked : checkRanks roads turns rank = true) (arrivals : run.FollowsArrivals roads turns)
    (vacates : run.LeavesVacancy)
    {K horizon : Nat} (positive : 0 < K) (service : run.BoundedService horizon K) (n : Nat) :
    ∀ t k c, (run.state t).pos k = some c → rank c = some n → t + waitBound K n ≤ horizon →
      ∃ i < waitBound K n, run.moves (t + i) k := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro t k c pos atRank within
    by_cases moved : ∃ i < waitBound K n, run.moves (t + i) k
    · exact moved
    exfalso
    obtain ⟨road, menu⟩ := arrivals t k c pos
    obtain ⟨d, offered, lower⟩ := rank_witness checked road atRank menu
    have block_end (i : Fin K) :
        t + (i.val + 1) * stride K n ≤ horizon := by
      exact Nat.le_trans (Nat.add_le_add_left
        (Nat.mul_le_mul_right (stride K n) (Nat.succ_le_of_lt i.isLt)) t) within
    have clear (i : Fin K) : ∃ j < stride K n, run.ClearAt d (t + i.val * stride K n + j) := by
      let start := t + i.val * stride K n
      cases d with
      | none => exact ⟨0, stride_pos K n, trivial⟩
      | some q =>
        obtain ⟨m, hm, rq⟩ := lower_rank lower
        have short := lower_wait positive hm
        cases occ : (run.state start).occ q with
        | none => exact ⟨0, stride_pos K n, by simpa [start, Trace.ClearAt] using occ⟩
        | some b =>
          have bp := ((run.state start).occ_iff_pos q b).mp occ
          have block : start + waitBound K m ≤ horizon := by
            have endOfBlock := block_end i
            rw [Nat.succ_mul] at endOfBlock
            dsimp [start]
            omega
          obtain ⟨off, hoff, go⟩ := ih m hm start b q bp rq block
          obtain ⟨j, hj, vacant⟩ := run.vacancy_by_move vacates bp go
          exact ⟨j, by omega, vacant⟩
    let offset (i : Fin K) := i.val * stride K n + Classical.choose (clear i)
    have offset_lt (i : Fin K) : offset i < (i.val + 1) * stride K n := by
      rw [Nat.succ_mul]
      exact Nat.add_lt_add_left (Classical.choose_spec (clear i)).1 _
    let slots (i : Fin K) : Fin (waitBound K n) :=
      ⟨offset i, Nat.lt_of_lt_of_le (offset_lt i)
        (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt i.isLt))⟩
    have ordered (i j : Fin K) (before : i < j) : slots i < slots j := by
      exact Nat.lt_of_lt_of_le (offset_lt i)
        (Nat.le_trans (Nat.mul_le_mul_right (stride K n) (Nat.succ_le_of_lt before))
          (Nat.le_add_right _ _))
    refine service t (waitBound K n) k c d within pos offered (fun i hi h => moved ⟨i, hi, h⟩)
      slots ordered ?_
    intro i
    simpa only [slots, offset, Nat.add_assoc] using (Classical.choose_spec (clear i)).2

@[simp] theorem waitBound_zero (K : Nat) : waitBound K 0 = K := by
  simp [waitBound, stride]

theorem waitBound_succ (K n : Nat) : waitBound K (n + 1) = K * (waitBound K n + 1) := rfl

theorem waitBound_one (n : Nat) : waitBound 1 n = n + 1 := by
  induction n with
  | zero => simp
  | succ n ih => simp [waitBound_succ, ih]

private def idleSnapshot : Snapshot Unit Unit where
  pos _ := some ()
  occ _ := some ()
  plan _ := ⟨none, .east, []⟩
  occ_iff_pos c k := by
    cases c
    cases k
    simp

private def idleTrace : Trace Unit Unit where
  state _ := idleSnapshot
  moves _ _ := False
  menu _ _ := [none]
  stays _ _ _ pos _ := ⟨pos, rfl⟩

/-- All-road rank coverage and an empty greatest trap can coexist with
an arbitrarily long wait. The example has one car and an offered exit. -/
theorem trap_free_can_wait_forever :
    ∃ run : Trace Unit Unit,
      run.LeavesVacancy ∧ run.FollowsArrivals [()] (fun _ => [[none]]) ∧
      checkRanks ([()] : List Unit) (fun _ => [[none]]) (fun _ => some 0) = true ∧
      ∀ t, (run.state t).pos () = some () ∧
        RouteTrap.greatestTrap [()] (RouteTrap.blockerMenus (run.state t) (fun _ => [[]])) = [] ∧
        ¬ run.moves t () := by
  refine ⟨idleTrace, fun _ _ _ _ moved => moved.elim, ?_, by decide, ?_⟩
  · intro _ _ c _
    cases c
    simp [idleTrace]
  · intro _
    exact ⟨rfl, rfl, id⟩

private def refillSnapshot : Snapshot Bool Bool where
  pos k := some k
  occ c := some c
  plan k := ⟨if k then none else some true, .east, []⟩
  occ_iff_pos _ _ := by simp [eq_comm]

private def refillMenu (k : Bool) : List (Option Bool) :=
  if k then [none] else [some true]

private def refillTrace : Trace Bool Bool where
  state _ := refillSnapshot
  moves t k := k = true ∧ t % 2 = 0
  menu _ k := refillMenu k
  stays _ _ _ pos _ := ⟨pos, rfl⟩

private theorem refill_service (horizon : Nat) : refillTrace.BoundedService horizon 2 := by
  intro t len k c d _ _ member waiting slots ordered clear
  cases k with
  | false =>
    have same : d = some true := by simpa [refillTrace, refillMenu] using member
    subst d
    have vacant := clear 0
    simp [Trace.ClearAt, refillTrace, refillSnapshot] at vacant
  | true =>
    let i := (slots 0).val
    have separate : i < (slots 1).val := ordered 0 1 (by decide)
    have next : i + 1 < len := Nat.lt_of_le_of_lt (Nat.succ_le_of_lt separate) (slots 1).isLt
    have odd : (t + i) % 2 ≠ 0 := by
      simpa [refillTrace] using waiting i (by omega)
    apply waiting (i + 1) next
    exact ⟨rfl, by omega⟩

/-- A rank-zero vehicle can exit and immediately refill its cell at every
even step. The rank-one follower keeps waiting, although service cap two
holds in every window and the structural trap is empty at every snapshot. -/
theorem immediate_refill_can_keep_ranked_car_stopped :
    ∃ (run : Trace Bool Bool) (turns : Turns Bool) (rank : Bool → Option Nat),
      run.FollowsArrivals [false, true] turns ∧ checkRanks [false, true] turns rank = true ∧
      rank false = some 1 ∧ rank true = some 0 ∧
      (∀ horizon, run.BoundedService horizon 2) ∧ ¬ run.LeavesVacancy ∧
      ∀ t, (run.state t).pos false = some false ∧ ¬ run.moves t false ∧
        RouteTrap.greatestTrap [false, true]
          (RouteTrap.blockerMenus (run.state t) (fun k => (run.menu t k).map Option.toList)) = [] := by
  refine ⟨refillTrace, fun c => [refillMenu c], fun c => if c then some 0 else some 1, ?_,
    by decide, rfl, rfl, refill_service, ?_, ?_⟩
  · intro t k c pos
    have same : k = c := by simpa [refillTrace, refillSnapshot] using pos
    subst c
    cases k <;> simp [refillTrace, refillMenu]
  · intro vacates
    have cleared := vacates 0 true true rfl ⟨rfl, rfl⟩
    simp [refillTrace, refillSnapshot] at cleared
  · intro _
    exact ⟨rfl, fun moved => Bool.noConfusion moved.1, rfl⟩

end BML.RouteProgress
