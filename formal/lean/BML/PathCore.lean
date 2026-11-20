import BML.Blocking
import BML.Counting
import BML.Fixation

/-!
The maximal occupied successor-closed core of an actual CLASSIC snapshot.

The path length parameter counts edges: a path of `edges` edges tests
`edges + 1` occupied vertices, including its root. Core membership means that
every finite direct blocker path from the root is occupied. It is a spatial
predicate that is monotone along the actual dynamics, unlike the presence of
an arbitrary long finite path.
-/
namespace BML

section General

variable {α : Type} (east north : Direction α)

/-- The direct target in the current snapshot; the empty branch is immaterial
for occupied paths and is chosen north to agree with `BML.blocker`. -/
def directBlocker (s : Config α) (p : α) : α :=
  if s p = .east then east.next p else north.next p

/-- `edges` edges, hence `edges + 1` occupied vertices including the root. -/
def OccupiedBlockerPath (s : Config α) (p : α) (edges : Nat) : Prop :=
  ∀ k, k ≤ edges → s (iterate (directBlocker east north s) k p) ≠ .empty

/-- Roots whose direct blocker orbit never reaches an empty site. -/
def PathCoreMember (s : Config α) (p : α) : Prop :=
  ∀ k, s (iterate (directBlocker east north s) k p) ≠ .empty

theorem pathCoreMember_iff_all_paths (s : Config α) (p : α) :
    PathCoreMember east north s p ↔ ∀ edges, OccupiedBlockerPath east north s p edges := by
  constructor
  · exact fun hp _ k _ => hp k
  · exact fun hp k => hp k k (Nat.le_refl k)

theorem PathCoreMember.occupied {s : Config α} {p : α}
    (hp : PathCoreMember east north s p) : s p ≠ .empty := hp 0

theorem PathCoreMember.successor {s : Config α} {p : α}
    (hp : PathCoreMember east north s p) :
    PathCoreMember east north s (directBlocker east north s p) := by
  intro k
  have hk := hp (1+k)
  simpa only [iterate_add, iterate] using hk

/-- Every occupied successor-closed core is contained in the direct-path core. -/
theorem BlockingCore.pathCoreMember {s : Config α}
    (core : BlockingCore east north s) {p : α} (hp : core.sites p) :
    PathCoreMember east north s p := by
  have hclosed : ∀ q, core.sites q → core.sites (directBlocker east north s q) := by
    intro q hq
    cases hc : s q with
    | empty => exact False.elim (core.occupied q hq hc)
    | east => simpa [directBlocker, hc] using core.east_closed q hq hc
    | north => simpa [directBlocker, hc] using core.north_closed q hq hc
  intro k
  apply core.occupied
  induction k with
  | zero => exact hp
  | succ k ih => exact hclosed _ ih

/-- The largest occupied successor-closed set, allowing the empty core. -/
def pathCore (s : Config α) : BlockingCore east north s where
  sites := PathCoreMember east north s
  occupied _ hp := hp.occupied east north
  east_closed p hp he := by
    simpa [directBlocker, he] using hp.successor east north
  north_closed p hp hn := by
    simpa [directBlocker, hn] using hp.successor east north

theorem pathCore_maximal (s : Config α) (core : BlockingCore east north s)
    (p : α) (hp : core.sites p) : (pathCore east north s).sites p :=
  core.pathCoreMember east north hp

/-- Root membership fixes the original species at that site for every future
full round, independently of the exterior configuration. -/
theorem PathCoreMember.persists {s : Config α} {p : α}
    (hp : PathCoreMember east north s p) (t : Nat) :
    iterate (step east north) t s p = s p :=
  (pathCore east north s).persists t p hp

/-- Agreement on any blocking core transports that same set into the maximal
core of the agreeing snapshot. -/
theorem BlockingCore.pathCoreMember_of_agrees {s u : Config α}
    (core : BlockingCore east north s) (ha : core.Agrees u)
    {p : α} (hp : core.sites p) : PathCoreMember east north u p := by
  let copy : BlockingCore east north u := {
    sites := core.sites
    occupied := by intro q hq; rw [ha q hq]; exact core.occupied q hq
    east_closed := by
      intro q hq hqE
      apply core.east_closed q hq
      rw [← ha q hq]
      exact hqE
    north_closed := by
      intro q hq hqN
      apply core.north_closed q hq
      rw [← ha q hq]
      exact hqN }
  exact copy.pathCoreMember east north hp

/-- Core membership at a fixed spatial site is monotone under full rounds. -/
theorem PathCoreMember.iterate {s : Config α} {p : α}
    (hp : PathCoreMember east north s p) (t : Nat) :
    PathCoreMember east north (iterate (step east north) t s) p :=
  (pathCore east north s).pathCoreMember_of_agrees east north
    ((pathCore east north s).persists t) hp

theorem PathCoreMember.step {s : Config α} {p : α}
    (hp : PathCoreMember east north s p) :
    PathCoreMember east north (step east north s) p := hp.iterate east north 1

/-- Every occupied root of a frozen snapshot belongs to its maximal core. -/
theorem pathCoreMember_iff_occupied_of_frozen (s : Config α)
    (hf : Frozen east north s) (p : α) :
    PathCoreMember east north s p ↔ s p ≠ .empty := by
  constructor
  · exact fun hp => hp.occupied east north
  · intro hp
    let core : BlockingCore east north s := {
      sites := fun q => s q ≠ .empty
      occupied := fun _ hq => hq
      east_closed := fun q _ he => hf.1 q he
      north_closed := fun q _ hn => hf.2 q hn }
    exact core.pathCoreMember east north hp

/-- Membership reached at a full-round checkpoint gives eventual permanent
occupancy of this same spatial site. -/
theorem permanent_site_of_eventual_pathCoreMember (s : Config α) (p : α)
    (hp : ∃ start, PathCoreMember east north (iterate (step east north) start s) p) :
    ∃ sp, EventuallyPermanent east north s sp p := by
  obtain ⟨start, hp⟩ := hp
  have ho := hp.occupied east north
  cases hc : iterate (step east north) start s p with
  | empty => exact False.elim (ho hc)
  | east =>
    refine ⟨.east, start, ?_⟩
    intro t
    rw [iterate_add, hp.persists east north t]
    exact hc
  | north =>
    refine ⟨.north, start, ?_⟩
    intro t
    rw [iterate_add, hp.persists east north t]
    exact hc

/-- An original car that reaches the spatial core never moves thereafter. -/
theorem tagEventuallyStopped_of_pathCoreMember (sp : Species) (s : Config α)
    (p : α) (hc : s p = sp.cell) (start : Nat)
    (hp : PathCoreMember east north (iterate (step east north) start s)
      (carTrace east north sp s start p)) :
    TagEventuallyStopped east north sp s p := by
  have hperm : PermanentFrom east north s sp
      (carTrace east north sp s start p) start := by
    intro t
    rw [iterate_add, hp.persists east north t]
    exact carTrace_preserves_car east north sp s p hc start
  refine ⟨start, ?_⟩
  intro t
  induction t with
  | zero => simp only [Nat.add_zero]
  | succ t ih =>
    rw [show start+(t+1) = start+t+1 by omega]
    change roundTransport east north sp (iterate (step east north) (start+t) s)
      (carTrace east north sp s (start+t) p) = carTrace east north sp s start p
    rw [ih]
    exact roundTransport_eq_of_no_round_move east north sp _ _
      (hperm.no_round_move east north t)

end General

private theorem finite_prefix_repeats {α : Type} (f : α → α) (carrier : List α)
    (p : α) (hp : ∀ k, k ≤ carrier.length → iterate f k p ∈ carrier) :
    ∃ i j, i < j ∧ j ≤ carrier.length ∧ iterate f i p = iterate f j p := by
  classical
  apply Classical.byContradiction
  intro hnone
  let orbit := List.ofFn (fun i : Fin (carrier.length + 1) => iterate f i.val p)
  have hsub : orbit ⊆ carrier := by
    intro q hq
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hq
    rw [← hi]
    exact hp i.val (by have hlt := i.isLt; omega)
  have hnodup : orbit.Nodup := by
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j hi hj heq
    have hi' : i < carrier.length + 1 := by simpa [orbit] using hi
    have hj' : j < carrier.length + 1 := by simpa [orbit] using hj
    have he : iterate f i p = iterate f j p := by
      simpa only [orbit, List.getElem_ofFn] using heq
    by_cases hij : i < j
    · exact False.elim (hnone ⟨i, j, hij, by omega, he⟩)
    · by_cases hji : j < i
      · exact False.elim (hnone ⟨j, i, hji, by omega, he.symm⟩)
      · omega
  have hlen := hnodup.length_le_of_subset hsub
  simp only [orbit, List.length_ofFn] at hlen
  omega

private theorem orbit_property_of_prefix_repeat {α : Type} (f : α → α)
    (P : α → Prop) (p : α) (i j : Nat) (hij : i < j)
    (hp : ∀ k, k < j → P (iterate f k p))
    (hrepeat : iterate f i p = iterate f j p) : ∀ k, P (iterate f k p) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hk : k < j
    · exact hp k hk
    · have he := congrArg (iterate f (k-j)) hrepeat
      rw [← iterate_add, ← iterate_add] at he
      have hsum : j + (k-j) = k := by omega
      rw [hsum] at he
      rw [← he]
      exact ih (i+(k-j)) (by omega)

section Finite

variable {w h : Nat} (east north : Direction (Position w h))

/-- A core root repeats a direct-path vertex by `carCount` edges. The repeated
endpoint is included, so this tests `carCount + 1` occupied vertices. -/
theorem PathCoreMember.repeats_by_carCount {s : Config (Position w h)}
    {p : Position w h} (hp : PathCoreMember east north s p) :
    ∃ i j, i < j ∧ j ≤ carCount w h s ∧
      BML.iterate (directBlocker east north s) i p =
        BML.iterate (directBlocker east north s) j p := by
  exact finite_prefix_repeats (directBlocker east north s) (occupiedCells w h s) p
    (fun k _ => (mem_occupiedCells w h s _).mpr (hp k))

/-- Exact finite test for membership in the maximal core. The cutoff is the
number of occupied sites in this snapshot, measured in edges, so it requires
one more occupied path vertex than the population. No lane or jam assumption
is used. -/
theorem pathCoreMember_iff_occupiedBlockerPath_carCount
    (s : Config (Position w h)) (p : Position w h) :
    PathCoreMember east north s p ↔
      OccupiedBlockerPath east north s p (carCount w h s) := by
  constructor
  · exact fun hp k _ => hp k
  · intro hp
    obtain ⟨i, j, hij, hj, hrepeat⟩ :=
      finite_prefix_repeats (directBlocker east north s) (occupiedCells w h s) p
        (fun k hk => (mem_occupiedCells w h s _).mpr (hp k hk))
    exact orbit_property_of_prefix_repeat (directBlocker east north s)
      (fun q => s q ≠ .empty) p i j hij
      (fun k hk => hp k (by change j ≤ carCount w h s at hj; omega)) hrepeat

/-- On a finite torus, the maximal core eventually equals exactly the set of
all eventually permanent spatial sites, simultaneously and permanently. -/
theorem pathCore_eventually_eq_permanent_sites (s : Config (Position w h)) :
    ∃ start, ∀ t p,
      PathCoreMember east north (iterate (step east north) (start+t) s) p ↔
        ∃ sp, EventuallyPermanent east north s sp p := by
  obtain ⟨start, core, hsites⟩ :=
    future_blockingCore_of_eventually_permanent_sites east north s
  refine ⟨start, ?_⟩
  intro t p
  constructor
  · intro hp
    exact permanent_site_of_eventual_pathCoreMember east north s p ⟨start+t, hp⟩
  · intro hp
    have hroot := core.pathCoreMember east north ((hsites p).mpr hp)
    rw [iterate_add]
    exact hroot.iterate east north t

theorem eventual_pathCoreMember_iff_permanent_site (s : Config (Position w h))
    (p : Position w h) :
    (∃ start, PathCoreMember east north (iterate (step east north) start s) p) ↔
      ∃ sp, EventuallyPermanent east north s sp p := by
  constructor
  · exact permanent_site_of_eventual_pathCoreMember east north s p
  · intro hp
    obtain ⟨start, hall⟩ := pathCore_eventually_eq_permanent_sites east north s
    exact ⟨start, (by simpa only [Nat.add_zero] using (hall 0 p).mpr hp)⟩

/-- Exact original-tag interpretation of the eventual core: a specified car
eventually stops if and only if its actual trace eventually enters the core.
Together with `carTrace_bijection`, this identifies the limiting core size
with the number of eventually stopped original cars. -/
theorem tagEventuallyStopped_iff_eventual_pathCoreMember (sp : Species)
    (s : Config (Position w h)) (p : Position w h) (hc : s p = sp.cell) :
    TagEventuallyStopped east north sp s p ↔
      ∃ start, PathCoreMember east north (iterate (step east north) start s)
        (carTrace east north sp s start p) := by
  constructor
  · rintro ⟨u, hu⟩
    have hperm : EventuallyPermanent east north s sp
        (carTrace east north sp s u p) := by
      refine ⟨u, ?_⟩
      intro t
      have hcar := carTrace_preserves_car east north sp s p hc (u+t)
      simpa only [hu t] using hcar
    obtain ⟨v, hv⟩ := pathCore_eventually_eq_permanent_sites east north s
    refine ⟨v+u, ?_⟩
    have htrace : carTrace east north sp s (v+u) p = carTrace east north sp s u p := by
      simpa only [Nat.add_comm v u] using hu v
    rw [htrace]
    exact (hv u _).mpr ⟨sp, hperm⟩
  · rintro ⟨start, hp⟩
    exact tagEventuallyStopped_of_pathCoreMember east north sp s p hc start hp

end Finite

theorem directBlocker_eq_blocker (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) :
    directBlocker (eastDirection w h hw) (northDirection w h hh) s =
      blocker w h hw hh s := rfl

end BML
