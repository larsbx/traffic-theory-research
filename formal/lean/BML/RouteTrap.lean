import BML.LaneDeadlock
import Init.Data.List.Nat.Basic

/-! # R2: finite structural traps and arrival-indexed safe cells -/
namespace BML.RouteTrap

section Peeling

variable {α : Type}

/-- At most one pass per initial candidate. Every nonterminal pass strictly
decreases the number of candidates. -/
def peel (keep : List α → α → Bool) : Nat → List α → List α
  | 0, candidates => candidates
  | fuel + 1, candidates =>
    let next := candidates.filter (keep candidates)
    if next.length = candidates.length then candidates else peel keep fuel next

theorem peel_subset (keep : List α → α → Bool) (fuel : Nat) (candidates : List α) :
    peel keep fuel candidates ⊆ candidates := by
  induction fuel generalizing candidates with
  | zero => exact fun _ h => h
  | succ fuel ih =>
    simp only [peel]
    split
    · exact fun _ h => h
    · exact fun _ h => (List.mem_filter.mp (ih _ h)).1

theorem peel_fixed (keep : List α → α → Bool) (fuel : Nat) (candidates : List α)
    (budget : candidates.length ≤ fuel) :
    let result := peel keep fuel candidates
    result.filter (keep result) = result := by
  induction fuel generalizing candidates with
  | zero =>
    have h : candidates = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero budget)
    subst candidates
    rfl
  | succ fuel ih =>
    simp only [peel]
    split
    next h => exact (List.filter_sublist).eq_of_length h
    next h =>
      have le := List.length_filter_le (keep candidates) candidates
      have enough : (candidates.filter (keep candidates)).length ≤ fuel := by omega
      exact ih _ enough

theorem subset_peel (keep : List α → α → Bool)
    (mono : ∀ {xs ys}, xs ⊆ ys → ∀ x, keep xs x = true → keep ys x = true)
    (fuel : Nat) {closed candidates : List α} (inside : closed ⊆ candidates)
    (closedKeep : ∀ x ∈ closed, keep closed x = true) :
    closed ⊆ peel keep fuel candidates := by
  induction fuel generalizing candidates with
  | zero => exact inside
  | succ fuel ih =>
    simp only [peel]
    split
    · exact inside
    · exact ih fun x hx => List.mem_filter.mpr ⟨inside hx, mono inside x (closedKeep x hx)⟩

end Peeling

section Traps

variable {Car Cell : Type}

/-- Each member's every option must have a blocker in the set. An empty menu
is blocked vacuously. An option with zero blockers always defeats closure. -/
def Closed (menus : Car → List (List Car)) (members : List Car) : Prop :=
  ∀ k ∈ members, ∀ option ∈ menus k, ∃ j ∈ option, j ∈ members

def blocked [DecidableEq Car] (menus : Car → List (List Car)) (members : List Car)
    (k : Car) : Bool :=
  (menus k).all fun option => option.any members.contains

theorem blocked_iff [DecidableEq Car] (menus : Car → List (List Car))
    (members : List Car) (k : Car) :
    blocked menus members k = true ↔ ∀ option ∈ menus k, ∃ j ∈ option, j ∈ members := by
  simp [blocked]

def greatestTrap [DecidableEq Car] (cars : List Car) (menus : Car → List (List Car)) : List Car :=
  peel (blocked menus) cars.length cars

theorem greatestTrap_closed [DecidableEq Car] (cars : List Car) (menus : Car → List (List Car)) :
    Closed menus (greatestTrap cars menus) := by
  have fixed : (greatestTrap cars menus).filter (blocked menus (greatestTrap cars menus)) =
      greatestTrap cars menus := peel_fixed (blocked menus) cars.length cars (Nat.le_refl _)
  intro k hk
  have hm : k ∈ (greatestTrap cars menus).filter (blocked menus (greatestTrap cars menus)) := by
    rw [fixed]
    exact hk
  exact (blocked_iff ..).mp (List.mem_filter.mp hm).2

theorem greatestTrap_greatest [DecidableEq Car] {cars members : List Car}
    {menus : Car → List (List Car)} (inside : members ⊆ cars) (h : Closed menus members) :
    members ⊆ greatestTrap cars menus := by
  refine subset_peel (blocked menus) ?_ cars.length inside ?_
  · intro xs ys sub k hk
    apply (blocked_iff ..).mpr
    intro option hm
    obtain ⟨j, hj, hin⟩ := (blocked_iff ..).mp hk option hm
    exact ⟨j, hj, sub hin⟩
  · exact fun k hk => (blocked_iff ..).mpr (h k hk)

theorem greatestTrap_subset [DecidableEq Car] (cars : List Car) (menus : Car → List (List Car)) :
    greatestTrap cars menus ⊆ cars :=
  peel_subset (blocked menus) cars.length cars

/-- Fixed point of the operator on the original on-street universe. -/
theorem greatestTrap_fixed [DecidableEq Car] (cars : List Car) (menus : Car → List (List Car))
    (k : Car) :
    k ∈ greatestTrap cars menus ↔ k ∈ cars ∧ blocked menus (greatestTrap cars menus) k = true := by
  constructor
  · intro hk
    exact ⟨greatestTrap_subset cars menus hk, (blocked_iff ..).mpr (greatestTrap_closed cars menus k hk)⟩
  · intro ⟨hk, hb⟩
    have inside : k :: greatestTrap cars menus ⊆ cars := by
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hk
      · exact greatestTrap_subset cars menus hj
    have closed : Closed menus (k :: greatestTrap cars menus) := by
      intro j hj option ho
      have h : ∃ b ∈ option, b ∈ greatestTrap cars menus := by
        rcases List.mem_cons.mp hj with rfl | hj
        · exact (blocked_iff ..).mp hb option ho
        · exact greatestTrap_closed cars menus j hj option ho
      obtain ⟨b, hbo, hbg⟩ := h
      exact ⟨b, hbo, List.mem_cons_of_mem _ hbg⟩
    exact greatestTrap_greatest inside closed (List.mem_cons_self ..)

theorem greatestTrap_shrinks [DecidableEq Car] (cars : List Car)
    {old new : Car → List (List Car)} (added : ∀ k, old k ⊆ new k) :
    greatestTrap cars new ⊆ greatestTrap cars old :=
  greatestTrap_greatest (greatestTrap_subset cars new) fun k hk opt ho =>
    greatestTrap_closed cars new k hk opt (added k ho)

theorem empty_menu_mem [DecidableEq Car] {cars : List Car} {menus : Car → List (List Car)}
    {k : Car} (onStreet : k ∈ cars) (noMoves : menus k = []) :
    k ∈ greatestTrap cars menus :=
  (greatestTrap_fixed cars menus k).mpr ⟨onStreet, by simp [blocked, noMoves]⟩

theorem unblocked_option_excludes [DecidableEq Car] {cars : List Car}
    {menus : Car → List (List Car)} {k : Car} (escape : [] ∈ menus k) :
    k ∉ greatestTrap cars menus := by
  intro hk
  obtain ⟨j, hj, _⟩ := greatestTrap_closed cars menus k hk [] escape
  simp at hj

end Traps

section Snapshot

open LaneDeadlock (Snapshot)
variable {Cell Car : Type}

/-- Filter-map drops vacant cells. An exit is represented by an empty list
of required cells, not by an empty list of options. -/
def blockerMenus (s : Snapshot Cell Car) (required : Car → List (List Cell)) (k : Car) :
    List (List Car) :=
  (required k).map (fun needs => needs.filterMap s.occ)

def SnapshotTrap (s : Snapshot Cell Car) (required : Car → List (List Cell))
    (members : List Car) : Prop :=
  (∀ k ∈ members, ∃ c, s.pos k = some c) ∧
    ∀ k ∈ members, ∀ need ∈ required k, ∃ c ∈ need, ∃ j ∈ members, s.occ c = some j

theorem snapshotTrap_iff (s : Snapshot Cell Car) (required : Car → List (List Cell))
    (members : List Car) :
    SnapshotTrap s required members ↔
      (∀ k ∈ members, ∃ c, s.pos k = some c) ∧ Closed (blockerMenus s required) members := by
  unfold SnapshotTrap Closed blockerMenus
  simp only [List.mem_map]
  constructor
  · rintro ⟨onRoad, blocked⟩
    refine ⟨onRoad, ?_⟩
    rintro k hk _ ⟨need, hneed, rfl⟩
    obtain ⟨c, hc, j, hj, ho⟩ := blocked k hk need hneed
    exact ⟨j, List.mem_filterMap.mpr ⟨c, hc, ho⟩, hj⟩
  · rintro ⟨onRoad, closed⟩
    refine ⟨onRoad, ?_⟩
    intro k hk need hneed
    obtain ⟨j, hmap, hj⟩ := closed k hk _ ⟨need, hneed, rfl⟩
    obtain ⟨c, hc, ho⟩ := List.mem_filterMap.mp hmap
    exact ⟨c, hc, j, hj, ho⟩

theorem greatestTrap_snapshot [DecidableEq Car] (s : Snapshot Cell Car)
    (required : Car → List (List Cell)) (cars : List Car)
    (onStreet : ∀ k ∈ cars, ∃ c, s.pos k = some c) :
    SnapshotTrap s required (greatestTrap cars (blockerMenus s required)) :=
  (snapshotTrap_iff ..).mpr ⟨fun k hk => onStreet k (greatestTrap_subset cars _ hk),
    greatestTrap_closed cars (blockerMenus s required)⟩

/-- CLASSIC uses pre-step vacancy for every needed cell, including an
optional box tail. Until its first move, a car can only use the supplied
option envelope. A waiting car remains on its original cell. Hop and exit
events are explicit, including an exit followed by immediate re-entry. -/
structure ClassicTrace (required : Car → List (List Cell)) where
  state : Nat → Snapshot Cell Car
  moves : Nat → Car → Prop
  stays : ∀ t k c, (state t).pos k = some c → ¬ moves t k → (state (t + 1)).pos k = some c
  vacant : ∀ t k, (∀ i < t, ¬ moves i k) → moves t k →
    ∃ need ∈ required k, ∀ c ∈ need, (state t).occ c = none

theorem SnapshotTrap.classic_immobile {required : Car → List (List Cell)} {members : List Car}
    (run : ClassicTrace required) (trap : SnapshotTrap (run.state 0) required members)
    {k : Car} (hk : k ∈ members) :
    ∀ t, (run.state t).pos k = (run.state 0).pos k ∧ ¬ run.moves t k := by
  have stop (t : Nat) (same : ∀ j ∈ members, (run.state t).pos j = (run.state 0).pos j)
      (past : ∀ i < t, ∀ j ∈ members, ¬ run.moves i j) (j : Car) (hj : j ∈ members) :
      ¬ run.moves t j := by
    intro hm
    obtain ⟨need, hneed, empty⟩ := run.vacant t j (fun i hi => past i hi j hj) hm
    obtain ⟨c, hc, b, hb, occ⟩ := trap.2 j hj need hneed
    have atT := ((run.state t).occ_iff_pos c b).mpr
      ((same b hb).trans (((run.state 0).occ_iff_pos c b).mp occ))
    rw [empty c hc] at atT
    cases atT
  have through (t : Nat) :
      (∀ j ∈ members, (run.state t).pos j = (run.state 0).pos j) ∧
      (∀ i < t, ∀ j ∈ members, ¬ run.moves i j) := by
    induction t with
    | zero => exact ⟨fun _ _ => rfl, fun i hi => False.elim (Nat.not_lt_zero i hi)⟩
    | succ t ih =>
      refine ⟨?_, ?_⟩
      · intro j hj
        obtain ⟨c, hc⟩ := trap.1 j hj
        exact (run.stays t j c ((ih.1 j hj).trans hc) (stop t ih.1 ih.2 j hj)).trans hc.symm
      · intro i hi j hj
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | same
        · exact ih.2 i h j hj
        · subst i
          exact stop t ih.1 ih.2 j hj
  exact fun t => ⟨(through t).1 k hk, stop t (through t).1 (through t).2 k hk⟩

end Snapshot

section SafeCells

open LaneDeadlock (Snapshot)
variable {Cell Car : Type}

/-- A distinct option list for every supported arrival. `none` is EXIT.
The list for an arrival may be empty. -/
abbrev Turns (Cell : Type) := Cell → List (List (Option Cell))

def enables (turns : Turns Cell) (inSet : Cell → Bool) (c : Cell) : Bool :=
  (turns c).all fun menu => menu.any fun d => d.elim true inSet

def certified (rank : Cell → Option Nat) (c : Cell) : Bool := (rank c).isSome

def descends (rank : Cell → Option Nat) (n : Nat) (d : Option Cell) : Bool :=
  d.elim true fun c => (rank c).any (fun r => r < n)

/-- Check rank descent on included cells, and a blocking arrival on every
excluded road. The latter condition certifies completeness of the safe set. -/
def checkRanks (roads : List Cell) (turns : Turns Cell) (rank : Cell → Option Nat) : Bool :=
  roads.all fun c =>
    match rank c with
    | some n => (turns c).all fun menu => menu.any (descends rank n)
    | none => !(enables turns (certified rank) c)

theorem rank_witness {roads : List Cell} {turns : Turns Cell} {rank : Cell → Option Nat}
    (checked : checkRanks roads turns rank = true) {c : Cell} (road : c ∈ roads)
    {n : Nat} (r : rank c = some n) {menu : List (Option Cell)} (arrived : menu ∈ turns c) :
    ∃ d ∈ menu, descends rank n d = true := by
  have row := List.all_eq_true.mp checked c road
  simp only [r, List.all_eq_true, List.any_eq_true] at row
  exact row menu arrived

theorem checkRanks_fixed {roads : List Cell} {turns : Turns Cell} {rank : Cell → Option Nat}
    (checked : checkRanks roads turns rank = true) {c : Cell} (road : c ∈ roads) :
    certified rank c = enables turns (certified rank) c := by
  cases hr : rank c with
  | none =>
    have row := List.all_eq_true.mp checked c road
    simp [hr] at row
    simp [certified, hr, row]
  | some n =>
    have mark : certified rank c = true := by simp [certified, hr]
    rw [mark]
    symm
    apply List.all_eq_true.mpr
    intro menu arrived
    obtain ⟨d, hd, lower⟩ := rank_witness checked road hr arrived
    apply List.any_eq_true.mpr
    refine ⟨d, hd, ?_⟩
    cases d with
    | none => rfl
    | some q => cases hq : rank q <;> simp_all [descends, certified]

/-- Checked ranks belong to every pre-fixed safe set. Together with
`checkRanks_fixed` this is the least-fixed-point characterization. -/
theorem checkRanks_least {roads : List Cell} {turns : Turns Cell} {rank : Cell → Option Nat}
    (checked : checkRanks roads turns rank = true)
    (onRoad : ∀ c n, rank c = some n → c ∈ roads)
    (other : Cell → Bool) (closed : ∀ c ∈ roads, enables turns other c = true → other c = true)
    {c : Cell} (safe : certified rank c = true) : other c = true := by
  have inductionRank (n : Nat) : ∀ c, rank c = some n → other c = true := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro c hr
      have road := onRoad c n hr
      apply closed c road
      simp only [enables, List.all_eq_true, List.any_eq_true]
      intro menu arrived
      obtain ⟨d, hd, lower⟩ := rank_witness checked road hr arrived
      refine ⟨d, hd, ?_⟩
      cases d with
      | none => rfl
      | some q =>
        cases hq : rank q with
        | none => simp [descends, hq] at lower
        | some m =>
          exact ih m (by simpa [descends, hq] using lower) q hq
  cases hr : rank c with
  | none => simp [certified, hr] at safe
  | some n => exact inductionRank n c hr

/-- A supported arrival offers its exit or singleton-destination moves to
the snapshot menu. Fixed-species and box-committed cars need not satisfy
this premise. All members of the proposed trap must satisfy it. -/
def ReRoutes (s : Snapshot Cell Car) (roads : List Cell) (turns : Turns Cell)
    (required : Car → List (List Cell)) (members : List Car) : Prop :=
  ∀ k ∈ members, ∀ c, s.pos k = some c →
    c ∈ roads ∧ ∃ menu ∈ turns c, ∀ d ∈ menu, d.toList ∈ required k

theorem SnapshotTrap.no_ranked_member {s : Snapshot Cell Car} {required : Car → List (List Cell)}
    {roads : List Cell} {turns : Turns Cell} {rank : Cell → Option Nat} {members : List Car}
    (trap : SnapshotTrap s required members) (routing : ReRoutes s roads turns required members)
    (checked : checkRanks roads turns rank = true) {k : Car} (hk : k ∈ members)
    {c : Cell} (pos : s.pos k = some c) : rank c = none := by
  have excluded (n : Nat) : ∀ k ∈ members, ∀ c, s.pos k = some c → rank c ≠ some n := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro j hj q posj rq
      obtain ⟨road, menu, arrived, offers⟩ := routing j hj q posj
      obtain ⟨d, hd, lower⟩ := rank_witness checked road rq arrived
      obtain ⟨x, hx, b, hb, occ⟩ := trap.2 j hj d.toList (offers d hd)
      cases d with
      | none => simp at hx
      | some dest =>
        have same : x = dest := by simpa using hx
        subst x
        cases rd : rank dest with
        | none => simp [descends, rd] at lower
        | some m =>
          exact ih m (by simpa [descends, rd] using lower) b hb dest
            ((s.occ_iff_pos dest b).mp occ) rd
  cases hr : rank c with
  | none => rfl
  | some n => exact False.elim (excluded n k hk c pos hr)

theorem SnapshotTrap.empty_of_all_ranked {s : Snapshot Cell Car} {required : Car → List (List Cell)}
    {roads : List Cell} {turns : Turns Cell} {rank : Cell → Option Nat} {members : List Car}
    (trap : SnapshotTrap s required members) (routing : ReRoutes s roads turns required members)
    (checked : checkRanks roads turns rank = true)
    (allRanked : ∀ c ∈ roads, certified rank c = true) : members = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro k hk
  obtain ⟨c, pos⟩ := trap.1 k hk
  have h := allRanked c (routing k hk c pos).1
  simp [certified, trap.no_ranked_member routing checked hk pos] at h

theorem greatestTrap_empty_of_all_ranked [DecidableEq Car] {s : Snapshot Cell Car}
    {required : Car → List (List Cell)} {cars : List Car} {roads : List Cell} {turns : Turns Cell}
    {rank : Cell → Option Nat} (onStreet : ∀ k ∈ cars, ∃ c, s.pos k = some c)
    (routing : ReRoutes s roads turns required cars)
    (checked : checkRanks roads turns rank = true)
    (allRanked : ∀ c ∈ roads, certified rank c = true) :
    greatestTrap cars (blockerMenus s required) = [] :=
  (greatestTrap_snapshot s required cars onStreet).empty_of_all_ranked
    (fun k hk => routing k (greatestTrap_subset cars _ hk)) checked allRanked

end SafeCells
end BML.RouteTrap
