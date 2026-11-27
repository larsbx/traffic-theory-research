import BML.RouteProgress
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm

/-! # R2 signal and merge service -/
namespace BML.RouteService

/-- Gridlock City's phase gate, with a signal gate only at junction targets. -/
def clockAllows (green t axis : Nat) (junction : Bool) : Bool :=
  t % 2 == axis && (!junction || (t / green) % 2 == axis)

private theorem clock_periods {green : Nat} (positive : 0 < green)
    (r n axis : Nat) (junction : Bool) :
    clockAllows green (r + (2 * green) * n) axis junction =
      clockAllows green r axis junction := by
  have phase : (r + (2 * green) * n) % 2 = r % 2 := by
    rw [Nat.mul_assoc, Nat.add_mul_mod_self_left]
  have signal : ((r + (2 * green) * n) / green) % 2 = (r / green) % 2 := by
    rw [show (2 * green) * n = green * (2 * n) by ac_rfl,
      Nat.add_mul_div_left _ _ positive, Nat.add_mul_mod_self_left]
  simp only [clockAllows, phase, signal]

private theorem clock_in_period {green axis : Nat} (positive : 0 < green) (axisBound : axis < 2) :
    ∃ r < 2 * green, clockAllows green r axis true = true := by
  rcases Nat.eq_zero_or_pos axis with zero | one
  · exact ⟨0, by omega, by simp [clockAllows, zero]⟩
  have axisOne : axis = 1 := by omega
  by_cases even : green % 2 = 0
  · have oneLt : 1 < green := by omega
    have parity : (green + 1) % 2 = 1 := by omega
    have div : (green + 1) / green = 1 := by
      rw [show green + 1 = 1 + green * 1 by omega, Nat.add_mul_div_left _ _ positive,
        Nat.div_eq_of_lt oneLt]
    exact ⟨green + 1, by omega, by simp [clockAllows, axisOne, parity, div]⟩
  · have parity : green % 2 = 1 := by omega
    exact ⟨green, by omega, by simp [clockAllows, axisOne, parity, Nat.div_self positive]⟩

/-- Every full two-green window contains a half-step with both the matching
movement phase and junction green, including for odd green durations. -/
theorem clock_service_window {green axis : Nat} (positive : 0 < green) (axisBound : axis < 2)
    (start : Nat) (junction : Bool) :
    ∃ i < 2 * green, clockAllows green (start + i) axis junction = true := by
  obtain ⟨r, hr, allowed⟩ := clock_in_period positive axisBound
  have rAllowed : clockAllows green r axis junction = true := by
    cases junction
    · simp [clockAllows] at allowed ⊢
      exact allowed.1
    · exact allowed
  let period := 2 * green
  let remainder := start % period
  let cycle := start / period
  have decomposition : start = remainder + period * cycle := (Nat.mod_add_div start period).symm
  have remBound : remainder < period := Nat.mod_lt _ (by dsimp [period]; omega)
  change r < period at hr
  change ∃ i < period, clockAllows green (start + i) axis junction = true
  by_cases same : remainder ≤ r
  · have time : start + (r - remainder) = r + period * cycle := by omega
    exact ⟨r - remainder, by omega, by rw [time, clock_periods positive, rAllowed]⟩
  · have time : start + (period - remainder + r) = r + period * (cycle + 1) := by
      rw [Nat.mul_succ]
      omega
    exact ⟨period - remainder + r, by omega, by rw [time, clock_periods positive, rAllowed]⟩

open LaneDeadlock (Snapshot)
open RouteTrap (blockerMenus greatestTrap greatestTrap_greatest snapshotTrap_iff)

/-- The full on-street universe cannot be nonempty and entirely blocked
when its greatest structural trap is empty. -/
theorem free_route_of_empty_trap {Cell Car : Type} [DecidableEq Car]
    (s : Snapshot Cell Car) (cars : List Car) (menu : Car → List (Option Cell))
    (someCar : cars ≠ []) (onRoad : ∀ k ∈ cars, ∃ c, s.pos k = some c)
    (covers : ∀ c k, s.occ c = some k → k ∈ cars)
    (trapFree : greatestTrap cars (blockerMenus s (fun k => (menu k).map Option.toList)) = []) :
    ∃ k ∈ cars, ∃ d ∈ menu k, d.elim True (fun q => s.occ q = none) := by
  by_cases noRoute : ∃ k ∈ cars, ∃ d ∈ menu k, d.elim True (fun q => s.occ q = none)
  · exact noRoute
  exfalso
  have closed : RouteTrap.SnapshotTrap s (fun k => (menu k).map Option.toList) cars := by
    refine ⟨onRoad, ?_⟩
    intro k hk req hreq
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hreq
    cases d with
    | none => exact (noRoute ⟨k, hk, none, hd, trivial⟩).elim
    | some q =>
      cases occ : s.occ q with
      | none => exact (noRoute ⟨k, hk, some q, hd, occ⟩).elim
      | some b => exact ⟨q, by simp, b, covers q b occ, occ⟩
  have inside := greatestTrap_greatest (List.Subset.refl cars)
    ((snapshotTrap_iff ..).mp closed).2
  rw [trapFree] at inside
  exact someCar (List.eq_nil_iff_forall_not_mem.mpr fun _ hk => by simpa using inside hk)

/-- Priority on one vacant target is maximum age, with ties to the lower tag. -/
def chooseWinner (age : Nat → Nat) : List Nat → Option Nat
  | [] => none
  | k :: rest =>
    match chooseWinner age rest with
    | none => some k
    | some j => some (if age j < age k ∨ (age j = age k ∧ k < j) then k else j)

theorem chooseWinner_spec (age : Nat → Nat) (contenders : List Nat) :
    match chooseWinner age contenders with
    | none => contenders = []
    | some j => j ∈ contenders ∧
        ∀ k ∈ contenders, age k < age j ∨ (age k = age j ∧ j ≤ k) := by
  induction contenders with
  | nil => rfl
  | cons k rest ih =>
    cases picked : chooseWinner age rest with
    | none =>
      have empty : rest = [] := by simpa only [picked] using ih
      subst rest
      simp [chooseWinner]
    | some j =>
      have old : j ∈ rest ∧ ∀ b ∈ rest, age b < age j ∨ (age b = age j ∧ j ≤ b) := by
        simpa only [picked] using ih
      simp only [chooseWinner, picked]
      split
      next better =>
        refine ⟨List.mem_cons_self .., ?_⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact Or.inr ⟨rfl, Nat.le_refl _⟩
        · have priority := old.2 b hb
          omega
      next noBetter =>
        refine ⟨List.mem_cons_of_mem _ old.1, ?_⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · omega
        · exact old.2 b hb

/-- The CLASSIC merge contract. An attempt has passed all request gates and
targets a pre-step vacancy or EXIT. A lost attempt has a real winner at the
same vacancy, of at least the loser's priority age. Entry into that cell
resets the winner's age. Other updates increase age by at most one. The
age of an off-street tag is taken to be zero. -/
structure Arbitration (N : Nat) where
  age : Nat → Fin N → Nat
  moved : Nat → Fin N → Prop
  attempt : Nat → Fin N → Prop
  growth : ∀ t k, age (t + 1) k ≤ age t k + 1
  preserves : ∀ t k, ¬ moved t k → age t k ≤ age (t + 1) k
  counts : ∀ t k, attempt t k → ¬ moved t k → age t k + 1 ≤ age (t + 1) k
  winner : ∀ t k, attempt t k → ¬ moved t k →
    ∃ j ≠ k, moved t j ∧ age t k ≤ age t j ∧ age (t + 1) j = 0

variable {N : Nat}

theorem Arbitration.some_move_of_attempt (run : Arbitration N) {t : Nat} {k : Fin N}
    (attempt : run.attempt t k) : ∃ j, run.moved t j := by
  by_cases own : run.moved t k
  · exact ⟨k, own⟩
  · obtain ⟨j, _, go, _, _⟩ := run.winner t k attempt own
    exact ⟨j, go⟩

/-- A held vacancy with a ready vehicle forces network activity within a
signal cycle. The route only needs to be held while the network is still. -/
theorem Arbitration.some_move_of_held_route (run : Arbitration N) (k : Fin N)
    {green axis : Nat} (positive : 0 < green) (axisBound : axis < 2)
    (start : Nat) (junction : Bool)
    (held : ∀ i < 2 * green, (∀ before < i, ∀ j, ¬ run.moved (start + before) j) →
      clockAllows green (start + i) axis junction = true → run.attempt (start + i) k) :
    ∃ i < 2 * green, ∃ j, run.moved (start + i) j := by
  by_cases go : ∃ i < 2 * green, ∃ j, run.moved (start + i) j
  · exact go
  obtain ⟨i, hi, greenNow⟩ := clock_service_window positive axisBound start junction
  have waits (before : Nat) (hb : before < i) (j : Fin N) (moved : run.moved (start + before) j) :
      False := go ⟨before, Nat.lt_trans hb hi, j, moved⟩
  exact ⟨i, hi, run.some_move_of_attempt (held i hi waits greenNow)⟩

/-- If each silent cycle admits a new tag and at most `budget` tags can
enter during a pause, a hop or exit occurs within `budget + 1` cycles. -/
theorem move_with_admission_budget (moved : Nat → Prop) (admissions : Nat → Nat)
    (start cycle budget : Nat)
    (cycleAdmission : ∀ j < budget + 1,
      (∀ i < cycle, ¬ moved (start + j * cycle + i)) →
      admissions (start + j * cycle) < admissions (start + (j + 1) * cycle))
    (capacity : (∀ i < (budget + 1) * cycle, ¬ moved (start + i)) →
      admissions (start + (budget + 1) * cycle) ≤ admissions start + budget) :
    ∃ i < (budget + 1) * cycle, moved (start + i) := by
  by_cases go : ∃ i < (budget + 1) * cycle, moved (start + i)
  · exact go
  exfalso
  have silent (i : Nat) (hi : i < (budget + 1) * cycle) : ¬ moved (start + i) :=
    fun movement => go ⟨i, hi, movement⟩
  have count (j : Nat) (hj : j ≤ budget + 1) :
      admissions start + j ≤ admissions (start + j * cycle) := by
    induction j with
    | zero => simp
    | succ j ih =>
      have finish := Nat.mul_le_mul_right cycle hj
      have gain := cycleAdmission j (by omega) fun i hi => by
        have beforeEnd : j * cycle + i < (j + 1) * cycle := by rw [Nat.succ_mul]; omega
        simpa only [Nat.add_assoc] using silent (j * cycle + i) (Nat.lt_of_lt_of_le beforeEnd finish)
      have prior := ih (by omega)
      omega
  have maximum := capacity silent
  have minimum := count (budget + 1) (Nat.le_refl _)
  omega

private theorem Arbitration.growth_window (run : Arbitration N) (t : Nat) (k : Fin N) (i : Nat) :
    run.age (t + i) k ≤ run.age t k + i := by
  induction i with
  | zero => simp
  | succ i ih =>
    exact Nat.le_trans (run.growth (t + i) k) (Nat.succ_le_succ ih)

private theorem Arbitration.age_monotone_while_waiting (run : Arbitration N)
    (t : Nat) (k : Fin N) {a b : Nat} (ordered : a ≤ b)
    (patient : ∀ i < b, ¬ run.moved (t + i) k) : run.age (t + a) k ≤ run.age (t + b) k := by
  induction b with
  | zero =>
    have zero : a = 0 := by omega
    simp [zero]
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le ordered with lt | eq
    · exact Nat.le_trans (ih (Nat.le_of_lt_succ lt) (fun i hi => patient i (by omega)))
        (run.preserves (t + b) k (patient b (by omega)))
    · simp [eq]

/-- If the waiting car is at least as old as the window length, every
opportunity lost in that window has a distinct winner, even if routes change. -/
theorem Arbitration.move_of_old_age (run : Arbitration N) (start len : Nat) (k : Fin N)
    (old : len ≤ run.age start k)
    (slots : Fin N → Fin len) (ordered : ∀ i j, i < j → slots i < slots j)
    (opportunities : ∀ i, run.attempt (start + (slots i).val) k) :
    ∃ i < len, run.moved (start + i) k := by
  by_cases moved : ∃ i < len, run.moved (start + i) k
  · exact moved
  exfalso
  have patient (i : Nat) (h : i < len) : ¬run.moved (start + i) k :=
    fun go => moved ⟨i, h, go⟩
  let time (i : Fin N) := start + (slots i).val
  have loses (i : Fin N) : ∃ j ≠ k, run.moved (time i) j ∧
      run.age (time i) k ≤ run.age (time i) j ∧ run.age (time i + 1) j = 0 :=
    run.winner (time i) k (opportunities i) (patient _ (slots i).isLt)
  let winner (i : Fin N) := Classical.choose (loses i)
  have noRepeat (i j : Fin N) (earlier : i < j) : winner i ≠ winner j := by
    intro same
    have order := ordered i j earlier
    change (slots i).val < (slots j).val at order
    let elapsed := (slots j).val - ((slots i).val + 1)
    have total : time i + 1 + elapsed = time j := by dsimp [time, elapsed]; omega
    have grows := run.growth_window (time i + 1) (winner i) elapsed
    rw [total, (Classical.choose_spec (loses i)).2.2.2, same] at grows
    have priority : run.age (time j) k ≤ run.age (time j) (winner j) :=
      (Classical.choose_spec (loses j)).2.2.1
    have remains := run.age_monotone_while_waiting start k (a := 0)
      (b := (slots j).val) (Nat.zero_le _) (fun i hi => patient i (Nat.lt_trans hi (slots j).isLt))
    have oldNow : len ≤ run.age (time j) k := Nat.le_trans old (by simpa [time] using remains)
    have elapsedLt : elapsed < len := by have bound := (slots j).isLt; dsimp [elapsed]; omega
    omega
  have injective (i j : Fin N) (same : winner i = winner j) : i = j := by
    by_cases eq : i = j
    · exact eq
    by_cases earlier : i < j
    · exact (noRepeat i j earlier same).elim
    · have later : j < i := by
        have distinct : i.val ≠ j.val := fun h => eq (Fin.ext h)
        change ¬ i.val < j.val at earlier
        change j.val < i.val
        omega
      exact (noRepeat j i later same.symm).elim
  let winners := (List.finRange N).map winner
  have distinct : winners.Nodup := by
    apply List.pairwise_map.mpr
    exact (List.nodup_finRange N).imp fun different same => different (injective _ _ same)
  have absent : k ∉ winners := by
    intro h
    obtain ⟨i, _, same⟩ := List.mem_map.mp h
    exact (Classical.choose_spec (loses i)).1 same
  have count := (List.nodup_cons.mpr ⟨absent, distinct⟩).length_le_of_subset
    (l₂ := List.finRange N) (fun tag _ => List.mem_finRange tag)
  simp [winners] at count
  omega

def mergeDeadline (N gap : Nat) : Nat := (N * gap + N) * gap

/-- If a waiting tag gets an attempt in each block of `gap` half-steps,
it moves within `N * gap * (gap + 1)` steps. The first `N * gap` blocks
build priority age. The last `N` blocks supply distinct contests. -/
theorem Arbitration.move_of_bounded_attempt_gaps (run : Arbitration N) {gap : Nat}
    (start : Nat) (k : Fin N)
    (recurs : ∀ kBlock < N * gap + N,
      (∀ i < (kBlock + 1) * gap, ¬ run.moved (start + i) k) →
      ∃ off < gap, run.attempt (start + kBlock * gap + off) k) :
    ∃ i < mergeDeadline N gap, run.moved (start + i) k := by
  by_cases go : ∃ i < mergeDeadline N gap, run.moved (start + i) k
  · exact go
  exfalso
  let warm := N * gap
  have patient (i : Nat) (hi : i < mergeDeadline N gap) : ¬run.moved (start + i) k :=
    fun moved => go ⟨i, hi, moved⟩
  have within (j : Nat) (hj : j < warm + N) :
      (j + 1) * gap ≤ mergeDeadline N gap :=
    Nat.mul_le_mul_right gap (Nat.succ_le_of_lt hj)
  have block (j : Nat) (hj : j < warm + N) :
      ∃ off < gap, run.attempt (start + j * gap + off) k :=
    recurs j hj fun i hi => patient i (Nat.lt_of_lt_of_le hi (within j hj))
  have stage (j : Nat) (enough : j ≤ warm) : j ≤ run.age (start + j * gap) k := by
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      have hj : j < warm + N := by omega
      obtain ⟨off, ho, tries⟩ := block j hj
      have hi : j * gap + off < (j + 1) * gap := by rw [Nat.succ_mul]; omega
      have last := within j hj
      have before := run.age_monotone_while_waiting start k
        (a := j * gap) (b := j * gap + off) (by omega)
        (fun i h => patient i (by omega))
      have gained := run.counts (start + j * gap + off) k tries
        (by simpa only [Nat.add_assoc] using patient (j * gap + off) (by omega))
      have after := run.age_monotone_while_waiting start k
        (a := j * gap + off + 1) (b := (j + 1) * gap) (by omega)
        (fun i h => patient i (by omega))
      simp only [← Nat.add_assoc] at before after
      have lower := ih (by omega)
      omega
  let suffix := start + warm * gap
  have late (i : Fin N) : ∃ off < gap, run.attempt (suffix + i.val * gap + off) k := by
    obtain ⟨off, ho, hit⟩ := block (warm + i.val) (by have := i.isLt; omega)
    exact ⟨off, ho, by simpa only [suffix, Nat.add_mul, ← Nat.add_assoc] using hit⟩
  let offset (i : Fin N) := i.val * gap + Classical.choose (late i)
  have ends (i : Fin N) : offset i < (i.val + 1) * gap := by
    rw [Nat.succ_mul]
    exact Nat.add_lt_add_left (Classical.choose_spec (late i)).1 _
  let slots (i : Fin N) : Fin warm :=
    ⟨offset i, Nat.lt_of_lt_of_le (ends i) (Nat.mul_le_mul_right gap (Nat.succ_le_of_lt i.isLt))⟩
  obtain ⟨i, hi, moved⟩ := run.move_of_old_age suffix warm k (stage warm (Nat.le_refl _)) slots
    (fun i j ord => Nat.lt_of_lt_of_le (ends i)
      (Nat.le_trans (Nat.mul_le_mul_right gap (Nat.succ_le_of_lt ord)) (Nat.le_add_right _ _)))
    (fun i => by simpa only [slots, offset, Nat.add_assoc] using (Classical.choose_spec (late i)).2)
  apply patient (warm * gap + i) ?_ (by simpa only [suffix, Nat.add_assoc] using moved)
  rw [mergeDeadline, Nat.add_mul]
  change warm * gap + i < warm * gap + warm
  omega

open RouteProgress (Trace)
open RouteTrap (Turns checkRanks rank_witness descends)

def rankAttemptGap (N delay : Nat) : Nat → Nat
  | 0 => delay
  | r + 1 => mergeDeadline N (rankAttemptGap N delay r) + delay

def rankDeadline (N delay rank : Nat) : Nat := mergeDeadline N (rankAttemptGap N delay rank)

/-- Clearance triggers an actual request at a vacancy within the delay if
the tag stays parked. This is the remaining route-choice and timing premise. -/
def ClearanceResponse {Cell : Type} (run : Trace Cell (Fin N)) (arb : Arbitration N)
    (horizon delay : Nat) : Prop :=
  ∀ t k c d, (run.state t).pos k = some c → d ∈ run.menu t k → run.ClearAt d t →
    t + delay ≤ horizon → (∀ i < delay, ¬ run.moves (t + i) k) →
    ∃ i < delay, arb.attempt (t + i) k

private theorem rankAttemptGap_mono {delay : Nat} (nonempty : 0 < N) {m n : Nat} (le : m ≤ n) :
    rankAttemptGap N delay m ≤ rankAttemptGap N delay n := by
  induction n with
  | zero =>
    have zero : m = 0 := by omega
    simp [zero]
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le le with lt | eq
    · apply Nat.le_trans (ih (Nat.le_of_lt_succ lt))
      simp only [rankAttemptGap, mergeDeadline]
      have stages : 0 < N * rankAttemptGap N delay n + N := by omega
      exact Nat.le_trans (Nat.le_mul_of_pos_left _ stages) (Nat.le_add_right _ _)
    · simp [eq]

private theorem held_arrival {Cell : Type} (run : Trace Cell (Fin N)) (t i : Nat)
    (k : Fin N) (c : Cell) (pos : (run.state t).pos k = some c)
    (held : ∀ j < i, ¬run.moves (t + j) k) :
    (run.state (t + i)).pos k = some c ∧ run.menu (t + i) k = run.menu t k := by
  induction i with
  | zero => simpa using And.intro pos (rfl : run.menu t k = run.menu t k)
  | succ i ih =>
    obtain ⟨atI, menu⟩ := ih fun j hj => held j (by omega)
    have next := run.stays (t + i) k c atI (held i (by omega))
    exact ⟨next.1, next.2.trans menu⟩

/-- Rank descent supplies a bounded gap between attempts when clearance
has a bounded response. The merge theorem supplies service of the tag. -/
theorem moves_before_rank_deadline {Cell : Type} (run : Trace Cell (Fin N))
    (arb : Arbitration N) (events : ∀ t k, arb.moved t k ↔ run.moves t k)
    {roads : List Cell} {turns : Turns Cell} {rank : Cell → Option Nat}
    (checked : checkRanks roads turns rank = true) (arrivals : run.FollowsArrivals roads turns)
    (vacates : run.LeavesVacancy) {horizon delay : Nat}
    (responds : ClearanceResponse run arb horizon delay) (r : Nat) :
    ∀ t k c, (run.state t).pos k = some c → rank c = some r →
      t + rankDeadline N delay r ≤ horizon →
      ∃ i < rankDeadline N delay r, run.moves (t + i) k := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro t k c pos atRank within
    have nonempty : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) k.isLt
    obtain ⟨road, menu⟩ := arrivals t k c pos
    obtain ⟨d, offered, descendsAt⟩ := rank_witness checked road atRank menu
    let gap := rankAttemptGap N delay r
    have delayFits : delay ≤ gap := rankAttemptGap_mono nonempty (Nat.zero_le r)
    have ready : ∃ i < mergeDeadline N gap, arb.moved (t + i) k := by
      apply arb.move_of_bounded_attempt_gaps t k
      intro j hj waiting
      let start := t + j * gap
      have blockEnd : (j + 1) * gap = j * gap + gap := Nat.succ_mul j gap
      have endTime : start + gap ≤ horizon := by
        have limit : t + (j + 1) * gap ≤ horizon :=
          Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right gap (Nat.succ_le_of_lt hj)) t) within
        simpa [start, blockEnd, Nat.add_assoc] using limit
      have clear : ∃ off, off + delay ≤ gap ∧ run.ClearAt d (start + off) := by
        cases d with
        | none => exact ⟨0, by simpa using delayFits, trivial⟩
        | some q =>
          cases rq : rank q with
          | none => simp [descends, rq] at descendsAt
          | some m =>
            have lower : m < r := by simpa [descends, rq] using descendsAt
            have budgetFits : rankDeadline N delay m + delay ≤ gap :=
              rankAttemptGap_mono nonempty (Nat.succ_le_of_lt lower)
            cases occ : (run.state start).occ q with
            | none =>
              exact ⟨0, by simpa using delayFits, by simpa [Trace.ClearAt] using occ⟩
            | some b =>
              have holds := ((run.state start).occ_iff_pos q b).mp occ
              obtain ⟨i, hi, goes⟩ := ih m lower start b q holds rq (by omega)
              obtain ⟨off, opened, vacant⟩ := run.vacancy_by_move vacates holds goes
              exact ⟨off, by omega, vacant⟩
      obtain ⟨off, room, vacant⟩ := clear
      have waits (i : Nat) (hi : i < (j + 1) * gap) : ¬run.moves (t + i) k :=
        fun m => waiting i hi ((events _ _).mpr m)
      have sameTime : start + off = t + (j * gap + off) := by simp [start, Nat.add_assoc]
      have limit : (t + (j * gap + off)) + delay ≤ horizon := by
        rw [← sameTime]
        omega
      obtain ⟨parked, stillOffered⟩ := held_arrival run t (j * gap + off) k c pos
        (fun i hi => waits i (by omega))
      have allowed : d ∈ run.menu (t + (j * gap + off)) k := by
        rw [stillOffered]
        exact offered
      have unserved (i : Nat) (hi : i < delay) : ¬run.moves (t + (j * gap + off) + i) k := by
        have no := waits (j * gap + off + i) (by omega)
        simpa only [Nat.add_assoc] using no
      obtain ⟨i, hi, contends⟩ :=
        responds _ k c d parked allowed (sameTime ▸ vacant) limit unserved
      exact ⟨off + i, by omega, by simpa only [Nat.add_assoc] using contends⟩
    obtain ⟨i, hi, moved⟩ := ready
    exact ⟨i, hi, (events _ _).mp moved⟩

end BML.RouteService
