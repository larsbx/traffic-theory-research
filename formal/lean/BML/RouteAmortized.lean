import BML.RouteService

/-! Shared-work service for a protected, healthy acyclic reference policy.
The accounting is derived from tag changes; operational hypotheses remain
explicit and are not asserted of the production JavaScript. -/
namespace BML.RouteAmortized

/-- One tag's contribution to a simultaneous frame. Exit and re-admission
may occur in the same half-step, and must both be counted. -/
inductive TagChange (D : Nat) where
  | idle (h : Nat)
  | hop (old new : Nat) (decrease : new < old)
  | exit (old : Nat) (positive : 0 < old)
  | admit (new : Nat) (bounded : new ≤ D)
  | exitAdmit (old new : Nat) (positive : 0 < old) (bounded : new ≤ D)

namespace TagChange
variable {D : Nat}

def before : TagChange D → Nat
  | .idle h => h
  | .hop h _ _ => h
  | .exit h _ => h
  | .admit _ _ => 0
  | .exitAdmit h _ _ _ => h

def after : TagChange D → Nat
  | .idle h => h
  | .hop _ h _ => h
  | .exit _ _ => 0
  | .admit h _ => h
  | .exitAdmit _ h _ _ => h

def moved : TagChange D → Nat
  | .hop .. | .exit .. | .exitAdmit .. => 1
  | _ => 0

def admitted : TagChange D → Nat
  | .admit .. | .exitAdmit .. => 1
  | _ => 0

theorem budget (u : TagChange D) :
    u.after + u.moved ≤ u.before + D*u.admitted := by
  cases u <;> simp [after, before, moved, admitted] <;> omega

end TagChange

def total {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | a::as => f a + total f as

theorem frame_budget {D : Nat} (frame : List (TagChange D)) :
    total TagChange.after frame + total TagChange.moved frame ≤
      total TagChange.before frame + D*total TagChange.admitted frame := by
  induction frame with
  | nil => simp [total]
  | cons a as ih =>
    have h := a.budget
    simp only [total, Nat.mul_add]
    omega

/-- Frame completeness and tag identity are refinement obligations: the
two work totals must describe the actual same fleet/region. -/
structure WorkTrace (D : Nat) where
  work : Nat → Nat
  frame : Nat → List (TagChange D)
  before_eq : ∀ t, work t = total TagChange.before (frame t)
  after_eq : ∀ t, work (t+1) = total TagChange.after (frame t)

namespace WorkTrace
variable {D : Nat}

def movesAt (w : WorkTrace D) (t : Nat) : Nat :=
  total TagChange.moved (w.frame t)

def admitsAt (w : WorkTrace D) (t : Nat) : Nat :=
  total TagChange.admitted (w.frame t)

def eventsAt (w : WorkTrace D) (t : Nat) : Nat := w.movesAt t + w.admitsAt t

theorem step_budget (w : WorkTrace D) (t : Nat) :
    w.work (t+1) + w.movesAt t ≤ w.work t + D*w.admitsAt t := by
  rw [w.after_eq t, w.before_eq t]
  exact frame_budget (w.frame t)

end WorkTrace

def count (f : Nat → Nat) (t : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => count f t n + f (t+n)

theorem count_append (f : Nat → Nat) (t a b : Nat) :
    count f t (a+b) = count f t a + count f (t+a) b := by
  induction b with
  | zero => simp [count]
  | succ b ih =>
    simp only [Nat.add_succ, count, ih, Nat.add_assoc]

theorem count_add (f g : Nat → Nat) (t n : Nat) :
    count (fun u => f u + g u) t n = count f t n + count g t n := by
  induction n with
  | zero => simp [count]
  | succ n ih => simp only [count, ih]; omega

theorem count_positive (f : Nat → Nat) (t n : Nat) :
    ∀ i < n, 0 < f (t+i) → 0 < count f t n := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi hit
    by_cases eq : i = n
    · subst i
      simp only [count]
      omega
    · have old := ih i (by omega) hit
      simp only [count]
      omega

theorem cumulative_work {D : Nat} (w : WorkTrace D) (t n : Nat) :
    w.work (t+n) + count w.movesAt t n ≤ w.work t + D*count w.admitsAt t n := by
  induction n with
  | zero => simp [count]
  | succ n ih =>
    have h := w.step_budget (t+n)
    simp only [Nat.add_succ, count, Nat.mul_add]
    omega

theorem event_cap {D : Nat} (w : WorkTrace D) (t n A floor : Nat)
    (initial : floor ≤ w.work t) (final : floor ≤ w.work (t+n))
    (quota : count w.admitsAt t n ≤ A) :
    count w.eventsAt t n ≤ w.work t-floor+(D+1)*A := by
  have account := cumulative_work w t n
  have mul := Nat.mul_le_mul_left D quota
  unfold WorkTrace.eventsAt
  rw [count_add, Nat.add_mul, Nat.one_mul]
  omega

theorem count_of_blocks (f : Nat → Nat) (t Q K : Nat)
    (progress : ∀ b < K, ∃ i < Q, 0 < f (t+b*Q+i)) :
    ∀ b ≤ K, b ≤ count f t (b*Q) := by
  intro b
  induction b with
  | zero => intro _; simp [count]
  | succ b ih =>
    intro hb
    obtain ⟨i, hi, hit⟩ := progress b (by omega)
    have block := count_positive f (t+b*Q) Q i hi hit
    have prev := ih (by omega)
    rw [Nat.succ_mul, count_append]
    omega

private theorem least_height {Cell : Type} (height : Cell → Nat)
    (xs : List Cell) (nonempty : xs ≠ []) :
    ∃ c ∈ xs, ∀ q ∈ xs, height c ≤ height q := by
  induction xs with
  | nil => exact (nonempty rfl).elim
  | cons c xs ih =>
    by_cases empty : xs = []
    · subst xs
      refine ⟨c, by simp, ?_⟩
      intro q h
      have eq : q = c := by simpa using h
      subst q
      exact Nat.le_refl _
    obtain ⟨d, hd, minimum⟩ := ih empty
    by_cases le : height c ≤ height d
    · refine ⟨c, by simp, ?_⟩
      intro q h
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_refl _
      · exact Nat.le_trans le (minimum q h)
    · refine ⟨d, List.mem_cons_of_mem _ hd, ?_⟩
      intro q h
      rcases List.mem_cons.mp h with rfl | h
      · omega
      · exact minimum q h

/-- An exit or a strict lower-height target of a minimum occupied cell is clear. -/
theorem free_lower_route {Cell : Type} (height : Cell → Nat) (cells : List Cell)
    (menu : Cell → List (Option Cell)) (nonempty : cells ≠ [])
    (escape : ∀ c ∈ cells, ∃ d ∈ menu c, d.elim True (fun q => height q < height c)) :
    ∃ c ∈ cells, ∃ d ∈ menu c, d.elim True (fun q => q ∉ cells) := by
  obtain ⟨c, hc, least⟩ := least_height height cells nonempty
  obtain ⟨d, hd, lower⟩ := escape c hc
  refine ⟨c,hc,d,hd,?_⟩
  cases d with
  | none => trivial
  | some q =>
    intro occupied
    have h := least q occupied
    change height q < height c at lower
    omega

/-- The held-owner contract is the remaining scheduler refinement.
After a quiet warm-up, an available route has a protected owner with a
fixed clock gate while events remain absent. The gate forces an actual
event (not just an attempted request). All region events must be counted. -/
structure QuietRegion {Cell : Type} {D : Nat} (w : WorkTrace D) (L G : Nat) where
  cells : Nat → List Cell
  height : Cell → Nat
  menu : Nat → Cell → List (Option Cell)
  present : ∀ t, 0 < w.work t → cells t ≠ []
  stable : ∀ t n, (∀ i < n, w.eventsAt (t+i) = 0) → cells (t+n) = cells t
  escape : ∀ t c, c ∈ cells t → ∃ d ∈ menu t c, d.elim True (fun q => height q < height c)
  held : ∀ t c d, (∀ i < L, w.eventsAt (t+i) = 0) →
    c ∈ cells (t+L) → d ∈ menu (t+L) c → d.elim True (fun q => q ∉ cells (t+L)) →
    ∃ axis < 2, ∃ junction : Bool, ∀ i < 2*G,
      (∀ j < i, w.eventsAt (t+L+j) = 0) →
      RouteService.clockAllows G (t+L+i) axis junction = true →
      0 < w.eventsAt (t+L+i)

theorem QuietRegion.block_event {Cell : Type} {D L G : Nat} {w : WorkTrace D}
    (r : QuietRegion (Cell := Cell) w L G) (green : 0 < G) (t : Nat)
    (positive : 0 < w.work t) : ∃ i < L+2*G, 0 < w.eventsAt (t+i) := by
  by_cases hit : ∃ i < L+2*G, 0 < w.eventsAt (t+i)
  · exact hit
  exfalso
  have silent (i : Nat) (hi : i < L+2*G) : w.eventsAt (t+i) = 0 := by
    by_contra h
    exact hit ⟨i,hi,by omega⟩
  have warm : ∀ i < L, w.eventsAt (t+i) = 0 := fun i hi => silent i (by omega)
  have nonempty : r.cells (t+L) ≠ [] := by
    rw [r.stable t L warm]
    exact r.present t positive
  obtain ⟨c,hc,d,hd,clear⟩ := free_lower_route r.height (r.cells (t+L))
    (r.menu (t+L)) nonempty (r.escape (t+L))
  obtain ⟨axis,ha,junction,held⟩ := r.held t c d warm hc hd clear
  obtain ⟨i,hi,gate⟩ := RouteService.clock_service_window green ha (t+L) junction
  have prior (j : Nat) (hj : j < i) : w.eventsAt (t+L+j) = 0 := by
    simpa only [Nat.add_assoc] using silent (L+j) (by omega)
  have e := held i hi prior gate
  exact hit ⟨L+i,by omega,by simpa only [Nat.add_assoc] using e⟩

def deadline (work floor D A L G : Nat) : Nat :=
  (work-floor+(D+1)*A+1)*(L+2*G)

/-- A reserved, positive focal contribution cannot be spent before that
tag's first movement. A quota is prospective only if enforced. -/
theorem moves_before_work_deadline {Cell : Type} {D L G : Nat} (w : WorkTrace D)
    (r : QuietRegion (Cell := Cell) w L G) (green : 0 < G)
    (focal : Nat → Prop) (t floor A : Nat) (positive : 0 < floor)
    (initial : floor ≤ w.work t)
    (quota : count w.admitsAt t (deadline (w.work t) floor D A L G) ≤ A)
    (unspent : ∀ n ≤ deadline (w.work t) floor D A L G,
      (∀ i < n, ¬ focal (t+i)) → floor ≤ w.work (t+n)) :
    ∃ i < deadline (w.work t) floor D A L G, focal (t+i) := by
  let K := w.work t-floor+(D+1)*A+1
  let Q := L+2*G
  change count w.admitsAt t (K*Q) ≤ A at quota
  change ∃ i < K*Q, focal (t+i)
  by_cases go : ∃ i < K*Q, focal (t+i)
  · exact go
  exfalso
  have patient (n : Nat) (hn : n ≤ K*Q) : ∀ i < n, ¬ focal (t+i) :=
    fun i hi h => go ⟨i, Nat.lt_of_lt_of_le hi hn,h⟩
  have final := unspent (K*Q) (Nat.le_refl _) (patient _ (Nat.le_refl _))
  have progress (b : Nat) (hb : b < K) : ∃ i < Q, 0 < w.eventsAt (t+b*Q+i) := by
    have within := Nat.mul_le_mul_right Q (Nat.le_of_lt hb)
    have low := unspent (b*Q) within (patient _ within)
    exact r.block_event green (t+b*Q) (by omega)
  have spent := count_of_blocks w.eventsAt t Q K progress K (Nat.le_refl _)
  have cap := event_cap w t (K*Q) A floor initial final quota
  dsimp [K] at spent
  omega

/-- No-admission evacuation: positive final work would force an event in
every block and leave insufficient work for those events. -/
theorem drains_before_work_deadline {Cell : Type} {D L G : Nat} (w : WorkTrace D)
    (r : QuietRegion (Cell := Cell) w L G) (green : 0 < G) (t : Nat)
    (quota : count w.admitsAt t (w.work t*(L+2*G)) = 0) :
    w.work (t+w.work t*(L+2*G)) = 0 := by
  let K := w.work t
  let Q := L+2*G
  change count w.admitsAt t (K*Q) = 0 at quota
  change w.work (t+K*Q) = 0
  by_contra nonzero
  have progress (b : Nat) (hb : b < K) : ∃ i < Q, 0 < w.eventsAt (t+b*Q+i) := by
    have le := Nat.mul_le_mul_right Q (Nat.le_of_lt hb)
    let rest := K*Q-b*Q
    have partition : b*Q+rest = K*Q := by dsimp [rest]; omega
    have zero := count_append w.admitsAt t (b*Q) rest
    rw [partition, quota] at zero
    have none : count w.admitsAt (t+b*Q) rest = 0 := by omega
    have account := cumulative_work w (t+b*Q) rest
    rw [none, Nat.mul_zero, Nat.add_zero] at account
    rw [Nat.add_assoc, partition] at account
    exact r.block_event green (t+b*Q) (by omega)
  have spent := count_of_blocks w.eventsAt t Q K progress K (Nat.le_refl _)
  have account := cumulative_work w t (K*Q)
  rw [quota, Nat.mul_zero, Nat.add_zero] at account
  unfold WorkTrace.eventsAt at spent
  rw [count_add, quota, Nat.add_zero] at spent
  dsimp [K] at spent
  omega

/-- An outside hop cannot enter a sealed region through its occupied root. -/
theorem sealed_hop_impossible {Cell : Type} (inside vacant : Cell → Prop)
    (legal : Cell → Cell → Prop) (root a b : Cell)
    (boundary : ∀ x y, legal x y → ¬ inside x → inside y → y = root)
    (occupied : ¬ vacant root) (edge : legal a b) (outside : ¬ inside a)
    (dest : inside b) (classic : vacant b) : False := by
  have eq := boundary a b edge outside dest
  exact occupied (eq ▸ classic)

/-- Likewise an allowed admission at the root cannot enter while it is occupied. -/
theorem sealed_admit_impossible {Cell : Type} (inside vacant allowed : Cell → Prop)
    (root b : Cell) (boundary : ∀ x, allowed x → inside x → x = root)
    (occupied : ¬ vacant root) (entry : allowed b) (dest : inside b)
    (classic : vacant b) : False := by
  exact occupied (boundary b entry dest ▸ classic)

/-! Saturated merge calendars. Local alternating contests are proved
from ages; global schedule realization in the simulator is separate. -/
def pairStep (gap : Nat) (ages : Nat × Nat) : Nat × Nat :=
  if ages.2 ≤ ages.1 then (gap-2, ages.2+gap)
  else (ages.1+gap, gap-2)

def pairAt (gap : Nat) : Nat → Nat × Nat
  | 0 => (0,0)
  | n+1 => pairStep gap (pairAt gap n)

/-- Loser stays; winner is replaced no earlier than two checkpoints later.
This canonical recurrence uses replacement exactly two later. -/
theorem alternating_priority (gap : Nat) (enough : 2 ≤ gap) (n : Nat) :
    (pairAt gap n).2 ≤ (pairAt gap n).1 ↔ n % 2 = 0 := by
  induction n with
  | zero => simp [pairAt]
  | succ n ih =>
    by_cases win : (pairAt gap n).2 ≤ (pairAt gap n).1
    · have even := ih.mp win
      simp only [pairAt, pairStep, if_pos win]
      omega
    · have odd : n % 2 ≠ 0 := fun h => win (ih.mpr h)
      simp only [pairAt, pairStep, if_neg win]
      omega

/-- The local pair recurrence is the actual oldest-first two-tag selector
when the side tag wins the initial equal-age tie. -/
theorem choose_pair (age : Nat → Nat) (side trunk : Nat) (order : side < trunk) :
    RouteService.chooseWinner age [side,trunk] =
      some (if age trunk ≤ age side then side else trunk) := by
  have cmp : (age trunk < age side ∨ (age trunk = age side ∧ side < trunk)) ↔
      age trunk ≤ age side := by omega
  simp only [RouteService.chooseWinner, cmp]

theorem alternating_winner (gap n side trunk : Nat) (enough : 2 ≤ gap)
    (order : side < trunk) (age : Nat → Nat)
    (sideAge : age side = (pairAt gap n).1)
    (trunkAge : age trunk = (pairAt gap n).2) :
    RouteService.chooseWinner age [side,trunk] =
      some (if n % 2 = 0 then side else trunk) := by
  rw [choose_pair age side trunk order, sideAge, trunkAge, alternating_priority gap enough n]

theorem replacement_loses (gap loserAge refill : Nat) (positive : 0 < refill)
    (within : refill ≤ gap) : gap-refill < loserAge+gap := by omega

/-- With one tag per road cell initially, enough off-street tags exist
to refill all eligible empty feeders; distinct assignments are possible. -/
theorem admission_capacity (cells tags onStreet vacant offStreet feeders : Nat)
    (equal : tags = cells) (cellCount : onStreet+vacant = cells)
    (tagCount : onStreet+offStreet = tags) (eligible : feeders ≤ vacant) :
    ∃ assign : Fin feeders → Fin offStreet, ∀ i j, assign i = assign j → i = j := by
  have capacity : feeders ≤ offStreet := by omega
  refine ⟨fun i => ⟨i.val,Nat.lt_of_lt_of_le i.isLt capacity⟩,?_⟩
  intro i j h
  exact Fin.ext (congrArg Fin.val h)

def mergePeriod (base : Nat) : Nat → Nat
  | 0 => base
  | n+1 => 2*mergePeriod base n

def mergeStart (first base : Nat) : Nat → Nat
  | 0 => first
  | n+1 => mergeStart first base n+mergePeriod base n+2

def departure (first base level slot : Nat) : Nat :=
  mergeStart first base level + mergePeriod base level * slot

/-- Odd downstream contests are trunk fills. The upstream departure
calendar is exactly those fills two half-steps after downstream departure. -/
theorem upstream_calendar (first base level slot : Nat) :
    departure first base (level+1) slot =
      departure first base level (2*slot+1)+2 := by
  simp only [departure, mergeStart, mergePeriod, Nat.mul_add, Nat.mul_one]
  rw [show 2*mergePeriod base level = mergePeriod base level*2 by omega, Nat.mul_assoc]
  omega

theorem merge_period_formula (base n : Nat) : mergePeriod base n = base*2^n := by
  induction n with
  | zero => simp [mergePeriod]
  | succ n ih =>
    rw [mergePeriod,ih,Nat.pow_succ]
    ac_rfl

theorem merge_start_formula (first base n : Nat) :
    mergeStart first base n+base = first+base*2^n+2*n := by
  induction n with
  | zero => simp [mergeStart]
  | succ n ih =>
    rw [mergeStart,merge_period_formula,Nat.pow_succ,← Nat.mul_assoc]
    have e : base*2^n*2 = base*2^n + base*2^n := by omega
    rw [e]
    omega

/-- Horizontal calendar includes the sink as depth zero. -/
theorem horizontal_first (m : Nat) :
    mergeStart 0 4 m+4 = 4*2^m+2*m := by
  simpa using merge_start_formula 0 4 m

/-- Mixed-axis calendar starts at the first upstream trunk departure. -/
theorem grid_first (n : Nat) :
    mergeStart 4 6 n+4 = 3*2^(n+1)+2*(n+1) := by
  have h := merge_start_formula 4 6 n
  rw [Nat.pow_succ]
  omega

/-- Refill is strictly before the next contest at every saturated merge. -/
theorem refill_before_next (first base level slot : Nat) (gap : 4 ≤ base) :
    departure first base level slot+2 < departure first base level (slot+1) := by
  have period : 4 ≤ mergePeriod base level := by
    induction level with
    | zero => exact gap
    | succ level ih => simp only [mergePeriod]; omega
  simp only [departure, Nat.mul_add, Nat.mul_one]
  omega

/-! Derive the held-owner interface from local claimant invariants. -/

/-- Uniform ticking preserves oldest-first priority, including ties.
Only the ages of actual contenders need to tick. -/
theorem winner_uniform_tick (age next : Nat → Nat) (tags : List Nat) (dt : Nat)
    (tick : ∀ k ∈ tags, next k = age k+dt) :
    RouteService.chooseWinner next tags = RouteService.chooseWinner age tags := by
  induction tags with
  | nil => rfl
  | cons k rest ih =>
    have tail := ih (fun j hj => tick j (List.mem_cons_of_mem _ hj))
    simp only [RouteService.chooseWinner, tail]
    cases picked : RouteService.chooseWinner age rest with
    | none => rfl
    | some j =>
      have spec : j ∈ rest ∧ ∀ b ∈ rest, age b < age j ∨ (age b = age j ∧ j ≤ b) := by
        simpa only [picked] using RouteService.chooseWinner_spec age rest
      have ak := tick k (List.mem_cons_self ..)
      have aj := tick j (List.mem_cons_of_mem _ spec.1)
      have cmp :
          (next j < next k ∨ (next j = next k ∧ k < j)) ↔
          (age j < age k ∨ (age j = age k ∧ k < j)) := by
        rw [ak,aj]
        omega
      simp only [cmp]

private theorem mature_filter (age : Nat → Nat) (L : Nat) (tags : List Nat)
    (old : ∀ k ∈ tags, L ≤ age k) :
    tags.filter (fun k => decide (L ≤ age k)) = tags := by
  induction tags with
  | nil => rfl
  | cons k rest ih =>
    have hk := old k (List.mem_cons_self ..)
    have tail := ih (fun j hj => old j (List.mem_cons_of_mem _ hj))
    simp [List.filter, hk, tail]

/-- These are local operational invariants, not the desired deadline.
A claimant list enumerates legal clear requests before phase filtering;
for EXIT it may be the singleton focal tag. Mandatory means a real move
when a protected owner has an eligible option, possibly a different one. -/
structure Claimants {Cell : Type} {D : Nat} (w : WorkTrace D) (L G : Nat) where
  tags : Nat → Cell → Option Cell → List Nat
  age : Nat → Nat → Nat
  axis : Nat → Cell → Option Cell → Nat → Nat
  junction : Cell → Option Cell → Bool
  quiet_tags : ∀ t n c d, (∀ i < n, w.eventsAt (t+i) = 0) →
    tags (t+n) c d = tags t c d
  quiet_age : ∀ t n c d k, (∀ i < n, w.eventsAt (t+i) = 0) →
    k ∈ tags t c d → age (t+n) k = age t k+n
  quiet_axis : ∀ t n c d k, (∀ i < n, w.eventsAt (t+i) = 0) →
    k ∈ tags t c d → axis (t+n) c d k = axis t c d k
  axis_bound : ∀ t c d k, k ∈ tags t c d → axis t c d k < 2
  mandatory : ∀ t c d k,
    RouteService.chooseWinner (age t)
      ((tags t c d).filter fun j => decide (L ≤ age t j)) = some k →
    RouteService.clockAllows G t (axis t c d k) (junction c d) = true →
    0 < w.movesAt t

theorem Claimants.held_owner {Cell : Type} {D L G : Nat} {w : WorkTrace D}
    (p : Claimants (Cell := Cell) w L G) (t : Nat) (c : Cell) (d : Option Cell)
    (warm : ∀ i < L, w.eventsAt (t+i) = 0)
    (nonempty : p.tags (t+L) c d ≠ []) :
    ∃ a < 2, ∃ junction : Bool, ∀ i < 2*G,
      (∀ j < i, w.eventsAt (t+L+j) = 0) →
      RouteService.clockAllows G (t+L+i) a junction = true →
      0 < w.eventsAt (t+L+i) := by
  let u := t+L
  let xs := p.tags u c d
  have mature : ∀ k ∈ xs, L ≤ p.age u k := by
    intro k hk
    have same := p.quiet_tags t L c d warm
    have old : k ∈ p.tags t c d := by
      change k ∈ p.tags (t+L) c d at hk
      rw [same] at hk
      exact hk
    have grows := p.quiet_age t L c d k warm old
    change L ≤ p.age (t+L) k
    omega
  cases picked : RouteService.chooseWinner (p.age u) xs with
  | none =>
    have empty : xs = [] := by
      simpa only [picked] using RouteService.chooseWinner_spec (p.age u) xs
    exact (nonempty empty).elim
  | some k =>
    have spec : k ∈ xs ∧ ∀ b ∈ xs, p.age u b < p.age u k ∨
        (p.age u b = p.age u k ∧ k ≤ b) := by
      simpa only [picked] using RouteService.chooseWinner_spec (p.age u) xs
    refine ⟨p.axis u c d k, p.axis_bound u c d k spec.1, p.junction c d, ?_⟩
    intro i _ prior gate
    have same := p.quiet_tags u i c d prior
    have ticks (j : Nat) (hj : j ∈ xs) : p.age (u+i) j = p.age u j+i :=
      p.quiet_age u i c d j prior hj
    have old : ∀ j ∈ p.tags (u+i) c d, L ≤ p.age (u+i) j := by
      intro j hj
      rw [same] at hj
      have tick := ticks j hj
      have priorAge := mature j hj
      omega
    have grant : RouteService.chooseWinner (p.age (u+i))
        ((p.tags (u+i) c d).filter fun j => decide (L ≤ p.age (u+i) j)) = some k := by
      rw [mature_filter _ _ _ old, same]
      change RouteService.chooseWinner (p.age (u+i)) xs = some k
      rw [winner_uniform_tick (p.age u) (p.age (u+i)) xs i ticks, picked]
    have stable := p.quiet_axis u i c d k prior spec.1
    have clock : RouteService.clockAllows G (u+i) (p.axis (u+i) c d k) (p.junction c d) = true := by
      rw [stable]
      exact gate
    have moved := p.mandatory (u+i) c d k grant clock
    change 0 < w.movesAt (u+i) + w.admitsAt (u+i)
    omega

/-- A member's height is part of the total work, without double-counting
a tag's first exit and subsequent re-admission as a single event. -/
theorem member_work {Cell : Type} (height : Cell → Nat) (cells : List Cell)
    (c : Cell) (member : c ∈ cells) : height c ≤ total height cells := by
  induction cells with
  | nil => simp at member
  | cons d rest ih =>
    simp only [total]
    rcases List.mem_cons.mp member with eq | tail
    · subst d
      omega
    · have lower := ih tail
      omega

/-- A focal car which stays at its root reserves that root's work.
The general deadline now uses the occupied-cell total directly. -/
theorem moves_before_focal_deadline {Cell : Type} {D L G : Nat} (w : WorkTrace D)
    (r : QuietRegion (Cell := Cell) w L G) (green : 0 < G)
    (work_eq : ∀ t, w.work t = total r.height (r.cells t))
    (focal : Nat → Prop) (t A : Nat) (root : Cell)
    (positive : 0 < r.height root) (atRoot : root ∈ r.cells t)
    (stays : ∀ u, root ∈ r.cells u → ¬ focal u → root ∈ r.cells (u+1))
    (quota : count w.admitsAt t (deadline (w.work t) (r.height root) D A L G) ≤ A) :
    ∃ i < deadline (w.work t) (r.height root) D A L G, focal (t+i) := by
  apply moves_before_work_deadline w r green focal t (r.height root) A positive
  · rw [work_eq]
    exact member_work r.height (r.cells t) root atRoot
  · exact quota
  · intro n _ waiting
    have held (m : Nat) : (∀ i < m, ¬ focal (t+i)) → root ∈ r.cells (t+m) := by
      induction m with
      | zero =>
        intro _
        simpa using atRoot
      | succ m ih =>
        intro waits
        have prev := ih (fun i hi => waits i (by omega))
        exact stays (t+m) prev (waits m (by omega))
    rw [work_eq]
    exact member_work r.height (r.cells (t+n)) root (held n waiting)

/-- The zero-work result is actual evacuation when every occupied cell
contributes positive height and the regional work inventory is complete. -/
theorem empty_before_work_deadline {Cell : Type} {D L G : Nat} (w : WorkTrace D)
    (r : QuietRegion (Cell := Cell) w L G) (green : 0 < G) (t : Nat)
    (work_eq : ∀ t, w.work t = total r.height (r.cells t))
    (positive : ∀ c, 0 < r.height c)
    (quota : count w.admitsAt t (w.work t*(L+2*G)) = 0) :
    r.cells (t+w.work t*(L+2*G)) = [] := by
  have zero := drains_before_work_deadline w r green t quota
  let finish := t+w.work t*(L+2*G)
  change w.work finish = 0 at zero
  change r.cells finish = []
  cases cells : r.cells finish with
  | nil => rfl
  | cons c rest =>
    rw [work_eq, cells] at zero
    simp only [total] at zero
    have h := positive c
    omega

/-- Construct the quiet-region interface from the local claimant
invariants, rather than supplying a network-event conclusion. -/
def QuietRegion.ofClaimants {Cell : Type} {D L G : Nat} (w : WorkTrace D)
    (p : Claimants (Cell := Cell) w L G)
    (cells : Nat → List Cell) (height : Cell → Nat)
    (menu : Nat → Cell → List (Option Cell))
    (present : ∀ t, 0 < w.work t → cells t ≠ [])
    (stable : ∀ t n, (∀ i < n, w.eventsAt (t+i) = 0) → cells (t+n) = cells t)
    (escape : ∀ t c, c ∈ cells t → ∃ d ∈ menu t c, d.elim True (fun q => height q < height c))
    (covers : ∀ t c d, c ∈ cells t → d ∈ menu t c →
      d.elim True (fun q => q ∉ cells t) → p.tags t c d ≠ []) :
    QuietRegion (Cell := Cell) w L G where
  cells := cells
  height := height
  menu := menu
  present := present
  stable := stable
  escape := escape
  held := fun t c d warm hc hd clear =>
    p.held_owner t c d warm (covers (t+L) c d hc hd clear)

end BML.RouteAmortized
