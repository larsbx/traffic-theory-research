import BML.Capture
import BML.Lanes
import Train.Finite

/-!
Eventual fixation of individual cars in the actual CLASSIC kernel.

The only imported TRAIN-namespaced result used here is finite cyclic predicate
propagation from `Train.Finite`, which imports only `BML.Torus`. No TRAIN
transition or movement theorem enters this module.
-/
namespace BML

section General

variable {α : Type} (east north : Direction α)

/-- A specified species occupies one fixed site at every round from `start`. -/
def PermanentFrom (s : Config α) (sp : Species) (p : α) (start : Nat) : Prop :=
  ∀ t, iterate (step east north) (start + t) s p = sp.cell

def EventuallyPermanent (s : Config α) (sp : Species) (p : α) : Prop :=
  ∃ start, PermanentFrom east north s sp p start

def HasPermanentSite (s : Config α) : Prop :=
  ∃ sp p, EventuallyPermanent east north s sp p

/-- An original tag eventually stays at one position in the actual car trace. -/
def TagEventuallyStopped (sp : Species) (s : Config α) (p : α) : Prop :=
  ∃ start, ∀ t, carTrace east north sp s (start + t) p =
    carTrace east north sp s start p

def HasEventuallyStoppedCar (s : Config α) : Prop :=
  ∃ sp p, s p = sp.cell ∧ TagEventuallyStopped east north sp s p

def AllCarsEventuallyStopped (s : Config α) : Prop :=
  ∀ sp p, s p = sp.cell → TagEventuallyStopped east north sp s p

def EventuallyJammed (s : Config α) : Prop :=
  ∃ t, Jam east north (iterate (step east north) t s)

theorem halfStep_own_of_occupied (d : Direction α) (sp : Species)
    (s : Config α) (p : α) (hp : s p = sp.cell)
    (ho : halfStep d sp s p ≠ .empty) : halfStep d sp s p = sp.cell := by
  by_cases hz : s (d.next p) = .empty
  · simp [halfStep, hp, hz] at ho
  · simp [halfStep, hp, hz]

/-- At full-round checkpoints a north car cannot be replaced by another
nonempty cell value in a single round. -/
theorem step_north_of_occupied (s : Config α) (p : α)
    (hp : s p = .north) (ho : step east north s p ≠ .empty) :
    step east north s p = .north := by
  apply halfStep_own_of_occupied north .north _ p _ ho
  exact (other_species_unchanged east .east s p .north (by decide) (by decide)).mpr hp

/-- Preserving the species at its source across a complete CLASSIC round
excludes hidden motion of that car. -/
theorem same_cell_no_round_move (sp : Species) (s : Config α) (p : α)
    (hp : s p = sp.cell) (hn : step east north s p = sp.cell) :
    ¬ RoundCanMove east north sp s p := by
  cases sp with
  | east =>
    intro hm
    have hz := moving_source_emptied east .east s p hm
    have he := (other_species_unchanged north .north (halfStep east .east s)
      p .east (by decide) (by decide)).mp hn
    rw [hz] at he
    cases he
  | north =>
    intro hm
    have hz := moving_source_emptied north .north (halfStep east .east s) p hm
    change halfStep north .north (halfStep east .east s) p = .north at hn
    rw [hz] at hn
    cases hn

theorem roundTransport_eq_of_no_round_move (sp : Species) (s : Config α) (p : α)
    (hm : ¬ RoundCanMove east north sp s p) :
    roundTransport east north sp s p = p := by
  cases sp <;> simp_all [roundTransport, RoundCanMove, transport]

theorem PermanentFrom.no_round_move {s : Config α} {sp : Species} {p : α}
    {start : Nat} (hp : PermanentFrom east north s sp p start) (t : Nat) :
    ¬ RoundCanMove east north sp (iterate (step east north) (start+t) s) p := by
  apply same_cell_no_round_move east north sp _ p (hp t)
  have hn := hp (t+1)
  rw [show start+(t+1) = start+t+1 by omega] at hn
  exact hn

theorem EventuallyPermanent.species_unique {s : Config α} {p : α}
    {a b : Species} (ha : EventuallyPermanent east north s a p)
    (hb : EventuallyPermanent east north s b p) : a = b := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  have he : a.cell = b.cell := by
    rw [← hu v, ← hv u, Nat.add_comm u v]
  cases a <;> cases b <;> simp_all [Species.cell]

theorem tagEventuallyStopped_has_permanent_site (sp : Species) (s : Config α)
    (p : α) (hp : s p = sp.cell) (hs : TagEventuallyStopped east north sp s p) :
    HasPermanentSite east north s := by
  obtain ⟨start, hs⟩ := hs
  refine ⟨sp, carTrace east north sp s start p, start, ?_⟩
  intro t
  have hc := carTrace_preserves_car east north sp s p hp (start+t)
  simpa only [hs t] using hc

theorem eventuallyPermanent_has_stopped_tag (sp : Species) (s : Config α)
    (p : α) (hp : EventuallyPermanent east north s sp p) :
    HasEventuallyStoppedCar east north s := by
  obtain ⟨start, hp⟩ := hp
  obtain ⟨q, hq, htrace⟩ := carTrace_surjective_on_cars east north sp s start p
    (by simpa only [Nat.add_zero] using hp 0)
  refine ⟨sp, q, hq, start, ?_⟩
  have hall : ∀ t, carTrace east north sp s (start+t) q = p := by
    intro t
    induction t with
    | zero => simpa only [Nat.add_zero] using htrace
    | succ t ih =>
      rw [show start+(t+1) = start+t+1 by omega]
      change roundTransport east north sp (iterate (step east north) (start+t) s)
        (carTrace east north sp s (start+t) q) = p
      rw [ih]
      exact roundTransport_eq_of_no_round_move east north sp _ p
        (hp.no_round_move east north t)
  intro t
  rw [hall t, htrace]

theorem hasPermanentSite_iff_hasEventuallyStoppedCar (s : Config α) :
    HasPermanentSite east north s ↔ HasEventuallyStoppedCar east north s := by
  constructor
  · rintro ⟨sp, p, hp⟩
    exact eventuallyPermanent_has_stopped_tag east north sp s p hp
  · rintro ⟨sp, p, hp, hs⟩
    exact tagEventuallyStopped_has_permanent_site east north sp s p hp hs

/-- Eventual constancy of an actual original tag is equivalent to finitely
many actual movement rounds. No assumption that direction shifts lack fixed
points is needed: an occupied car cannot move into its occupied self. -/
theorem tagEventuallyStopped_iff_finitely_many_moves (sp : Species)
    (s : Config α) (p : α) (hp : s p = sp.cell) :
    TagEventuallyStopped east north sp s p ↔
      ∃ start, ∀ t, ¬ RoundCanMove east north sp
        (iterate (step east north) (start+t) s)
        (carTrace east north sp s (start+t) p) := by
  constructor
  · rintro ⟨start, hs⟩
    refine ⟨start, ?_⟩
    intro t
    have hn := carTrace_preserves_car east north sp s p hp (start+(t+1))
    have ht : carTrace east north sp s (start+(t+1)) p =
        carTrace east north sp s (start+t) p := (hs (t+1)).trans (hs t).symm
    rw [ht, show start+(t+1) = start+t+1 by omega] at hn
    exact same_cell_no_round_move east north sp _ _
      (carTrace_preserves_car east north sp s p hp (start+t)) hn
  · rintro ⟨start, hn⟩
    refine ⟨start, ?_⟩
    intro t
    induction t with
    | zero => simp only [Nat.add_zero]
    | succ t ih =>
      rw [show start+(t+1) = start+t+1 by omega]
      change roundTransport east north sp (iterate (step east north) (start+t) s)
        (carTrace east north sp s (start+t) p) = carTrace east north sp s start p
      rw [roundTransport_eq_of_no_round_move east north sp _ _ (hn t)]
      exact ih

private theorem occupied_sequence_stabilizes (u : Nat → Cell) (absorbing : Species)
    (ho : ∀ t, u t ≠ .empty)
    (ha : ∀ t, u t = absorbing.cell → u (t+1) = absorbing.cell) :
    ∃ sp : Species, ∃ start, ∀ t, u (start+t) = sp.cell := by
  classical
  by_cases hh : ∃ start, u start = absorbing.cell
  · obtain ⟨start, hh⟩ := hh
    refine ⟨absorbing, start, ?_⟩
    intro t
    induction t with
    | zero => simpa only [Nat.add_zero] using hh
    | succ t ih => simpa only [Nat.add_succ] using ha (start+t) ih
  · have hn : ∀ t, u t ≠ absorbing.cell := fun t ht => hh ⟨t, ht⟩
    cases absorbing with
    | east =>
      refine ⟨.north, 0, ?_⟩
      intro t
      have he := hn t
      have hz := ho t
      cases hc : u t <;> simp_all [Species.cell]
    | north =>
      refine ⟨.east, 0, ?_⟩
      intro t
      have he := hn t
      have hz := ho t
      cases hc : u t <;> simp_all [Species.cell]

/-- Persistent occupancy at full-round checkpoints eventually stabilizes to
one species: the only possible occupied change is east to north. -/
theorem occupied_forever_has_permanent_site (s : Config α) (p : α)
    (start : Nat) (ho : ∀ t, iterate (step east north) (start+t) s p ≠ .empty) :
    ∃ sp, EventuallyPermanent east north s sp p := by
  obtain ⟨sp, u, hu⟩ := occupied_sequence_stabilizes
    (fun t => iterate (step east north) (start+t) s p) .north ho (by
      intro t hn
      have hs := step_north_of_occupied east north
        (iterate (step east north) (start+t) s) p hn
        (by
          have hz := ho (t+1)
          rw [show start+(t+1) = start+t+1 by omega] at hz
          exact hz)
      rw [show start+(t+1) = start+t+1 by omega]
      exact hs)
  exact ⟨sp, start+u, fun t => by simpa only [Nat.add_assoc] using hu t⟩

theorem eventuallyPermanent_east_successor (s : Config α) (p : α)
    (hp : EventuallyPermanent east north s .east p) :
    ∃ sp, EventuallyPermanent east north s sp (east.next p) := by
  obtain ⟨start, hp⟩ := hp
  apply occupied_forever_has_permanent_site east north s (east.next p) start
  intro t hz
  apply hp.no_round_move east north t
  exact ⟨hp t, hz⟩

/-- The north successor is observed after the east phase. At those checkpoints
the only occupied species change is north to east, so the successor also
eventually contains one permanent car. -/
theorem eventuallyPermanent_north_successor (s : Config α) (p : α)
    (hp : EventuallyPermanent east north s .north p) :
    ∃ sp, EventuallyPermanent east north s sp (north.next p) := by
  obtain ⟨start, hp⟩ := hp
  let mid := fun t => halfStep east .east (iterate (step east north) (start+t) s)
  have ho : ∀ t, mid t (north.next p) ≠ .empty := by
    intro t hz
    apply hp.no_round_move east north t
    refine ⟨?_, hz⟩
    exact (other_species_unchanged east .east _ p .north (by decide) (by decide)).mpr (hp t)
  have ha : ∀ t, mid t (north.next p) = .east → mid (t+1) (north.next p) = .east := by
    intro t he
    have hs : iterate (step east north) (start+(t+1)) s (north.next p) = .east := by
      rw [show start+(t+1) = start+t+1 by omega]
      change halfStep north .north (mid t) (north.next p) = .east
      exact (other_species_unchanged north .north _ (north.next p) .east
        (by decide) (by decide)).mpr he
    exact halfStep_own_of_occupied east .east _ (north.next p) hs (ho (t+1))
  obtain ⟨sp, u, hu⟩ := occupied_sequence_stabilizes (fun t => mid t (north.next p))
    .east ho ha
  cases sp with
  | east =>
    refine ⟨.east, start+u+1, ?_⟩
    intro t
    change iterate (step east north) (start+u+1+t) s (north.next p) = .east
    have hs : iterate (step east north) (start+(u+t)+1) s (north.next p) = .east := by
      simp only [iterate, step]
      exact (other_species_unchanged north .north _ (north.next p) .east
        (by decide) (by decide)).mpr (hu t)
    simpa only [Nat.add_assoc, Nat.add_comm 1 t] using hs
  | north =>
    refine ⟨.north, start+u, ?_⟩
    intro t
    change iterate (step east north) (start+u+t) s (north.next p) = .north
    have hs := (other_species_unchanged east .east _ (north.next p) .north
      (by decide) (by decide)).mp (hu t)
    simpa only [Nat.add_assoc] using hs

theorem eventuallyJammed_has_permanent_site (s : Config α)
    (hj : EventuallyJammed east north s) : HasPermanentSite east north s := by
  obtain ⟨start, hn, hf⟩ := hj
  obtain ⟨p, hp⟩ := hn
  cases hc : iterate (step east north) start s p with
  | empty => exact False.elim (hp hc)
  | east =>
    refine ⟨.east, p, start, ?_⟩
    intro t
    rw [reached_frozen_persists east north s start hf t]
    exact hc
  | north =>
    refine ⟨.north, p, start, ?_⟩
    intro t
    rw [reached_frozen_persists east north s start hf t]
    exact hc

theorem eventuallyJammed_every_tag_stops (s : Config α)
    (hj : EventuallyJammed east north s) (sp : Species) (p : α)
    (hp : s p = sp.cell) : TagEventuallyStopped east north sp s p := by
  obtain ⟨start, _, hf⟩ := hj
  have hperm : PermanentFrom east north s sp (carTrace east north sp s start p) start := by
    intro t
    rw [reached_frozen_persists east north s start hf t]
    exact carTrace_preserves_car east north sp s p hp start
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

private theorem finite_eventually_uniform {α : Type} (xs : List α)
    (P : Nat → α → Prop)
    (hp : ∀ p, p ∈ xs → ∃ start, ∀ t, P (start+t) p) :
    ∃ start, ∀ p, p ∈ xs → ∀ t, P (start+t) p := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons a xs ih =>
    obtain ⟨u, hu⟩ := hp a (by simp)
    obtain ⟨v, hv⟩ := ih (fun p hm => hp p (by simp [hm]))
    refine ⟨u+v, ?_⟩
    intro p hm t
    rcases List.mem_cons.mp hm with rfl | hm
    · simpa only [Nat.add_assoc] using hu (v+t)
    · simpa only [Nat.add_assoc, Nat.add_left_comm u v] using hv p hm (u+t)

private theorem nat_rank_minimum {α : Type} (P : α → Prop) (r : α → Nat)
    (hne : ∃ p, P p) : ∃ p, P p ∧ ∀ q, P q → r p ≤ r q := by
  classical
  have aux : ∀ n, (∃ p, P p ∧ r p = n) → ∃ p, P p ∧ ∀ q, P q → r p ≤ r q := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      by_cases hl : ∃ q, P q ∧ r q < n
      · obtain ⟨q, hq, hqn⟩ := hl
        exact ih (r q) hqn ⟨q, hq, rfl⟩
      · obtain ⟨p, hp, hpn⟩ := hn
        refine ⟨p, hp, ?_⟩
        intro q hq
        have hnot : ¬ r q < n := fun hlt => hl ⟨q, hq, hlt⟩
        omega
  obtain ⟨p, hp⟩ := hne
  exact aux (r p) ⟨p, hp, rfl⟩

section Finite

variable {w h : Nat} (east north : Direction (Position w h))

/-- Finitely many tags have a common last-movement bound. Nonemptiness is
necessary because the empty configuration also fixes all its tags vacuously. -/
theorem eventuallyJammed_of_all_cars_stopped (s : Config (Position w h))
    (ha : AllCarsEventuallyStopped east north s) (hne : Nonempty s) :
    EventuallyJammed east north s := by
  let P := fun t p => ∀ sp, s p = sp.cell →
    ¬ RoundCanMove east north sp (iterate (step east north) t s)
      (carTrace east north sp s t p)
  have hp : ∀ p, ∃ start, ∀ t, P (start+t) p := by
    intro p
    cases hc : s p with
    | empty =>
      refine ⟨0, ?_⟩
      intro t sp hs
      cases sp <;> simp_all [Species.cell]
    | east =>
      obtain ⟨start, hm⟩ := (tagEventuallyStopped_iff_finitely_many_moves
        east north .east s p hc).mp (ha .east p hc)
      refine ⟨start, ?_⟩
      intro t sp hs
      cases sp with
      | east => exact hm t
      | north => simp_all [Species.cell]
    | north =>
      obtain ⟨start, hm⟩ := (tagEventuallyStopped_iff_finitely_many_moves
        east north .north s p hc).mp (ha .north p hc)
      refine ⟨start, ?_⟩
      intro t sp hs
      cases sp with
      | east => simp_all [Species.cell]
      | north => exact hm t
  obtain ⟨start, hall⟩ := finite_eventually_uniform (positions w h) P (fun p _ => hp p)
  have hm : ∀ sp q, ¬ RoundCanMove east north sp (iterate (step east north) start s) q := by
    intro sp q hmove
    obtain ⟨p, hp, htrace⟩ := carTrace_surjective_on_cars east north sp s start q
      (roundCanMove_source_car east north sp _ q hmove)
    have hn := hall p (positions_contains p) 0 sp hp
    simp only [Nat.add_zero, htrace] at hn
    exact hn hmove
  have hf : Frozen east north (iterate (step east north) start s) := by
    apply (noMoves_iff_frozen east north _).mp
    exact ⟨hm .east, hm .north⟩
  refine ⟨start, ?_, hf⟩
  exact (iterate_nonempty_iff east north s start).mpr hne

theorem allCarsEventuallyStopped_iff_empty_or_jam (s : Config (Position w h)) :
    AllCarsEventuallyStopped east north s ↔ ¬ Nonempty s ∨ EventuallyJammed east north s := by
  classical
  constructor
  · intro ha
    by_cases hn : Nonempty s
    · exact Or.inr (eventuallyJammed_of_all_cars_stopped east north s ha hn)
    · exact Or.inl hn
  · rintro (he | hj)
    · intro sp p hp
      exact False.elim (he ⟨p, by rw [hp]; exact sp.cell_ne_empty⟩)
    · exact fun sp p hp => eventuallyJammed_every_tag_stops east north s hj sp p hp

/-- All eventually permanent sites simultaneously form a nonempty occupied
successor-closed core at some actual future full-round state. -/
theorem future_blockingCore_of_permanent_site (s : Config (Position w h))
    (hs : HasPermanentSite east north s) :
    ∃ start, ∃ core : BlockingCore east north (iterate (step east north) start s),
      ∃ p, core.sites p := by
  classical
  let P := fun t p => ∀ sp, EventuallyPermanent east north s sp p →
    iterate (step east north) t s p = sp.cell
  have hu : ∀ p, ∃ start, ∀ t, P (start+t) p := by
    intro p
    by_cases hp : ∃ sp, EventuallyPermanent east north s sp p
    · obtain ⟨sp, start, hsp⟩ := hp
      refine ⟨start, ?_⟩
      intro t other hother
      have he := EventuallyPermanent.species_unique east north ⟨start, hsp⟩ hother
      subst other
      exact hsp t
    · refine ⟨0, ?_⟩
      intro t sp hsp
      exact False.elim (hp ⟨sp, hsp⟩)
  obtain ⟨start, hall⟩ := finite_eventually_uniform (positions w h) P (fun p _ => hu p)
  have hat : ∀ p sp, EventuallyPermanent east north s sp p →
      iterate (step east north) start s p = sp.cell := by
    intro p sp hp
    simpa only [Nat.add_zero] using hall p (positions_contains p) 0 sp hp
  let core : BlockingCore east north (iterate (step east north) start s) := {
    sites := fun p => ∃ sp, EventuallyPermanent east north s sp p
    occupied := by
      rintro p ⟨sp, hp⟩
      rw [hat p sp hp]
      exact sp.cell_ne_empty
    east_closed := by
      rintro p ⟨sp, hp⟩ he
      have hc := hat p sp hp
      have hsp : sp = .east := by cases sp <;> simp_all [Species.cell]
      subst sp
      exact eventuallyPermanent_east_successor east north s p hp
    north_closed := by
      rintro p ⟨sp, hp⟩ hn
      have hc := hat p sp hp
      have hsp : sp = .north := by cases sp <;> simp_all [Species.cell]
      subst sp
      exact eventuallyPermanent_north_successor east north s p hp }
  obtain ⟨sp, p, hp⟩ := hs
  exact ⟨start, core, p, sp, hp⟩

end Finite

section Torus

variable {w h : Nat} {hw : 0 < w} {hh : 0 < h}
variable {s : Config (Position w h)}

/-- If a nonempty closed core misses a row, a minimizing cyclic row-distance
forces an entire east row inside the core. -/
theorem BlockingCore.full_east_row_of_missed_row
    (core : BlockingCore (eastDirection w h hw) (northDirection w h hh) s)
    (hne : ∃ p, core.sites p) (row : Fin h)
    (hmiss : ∀ x, ¬ core.sites (x,row)) : ∃ y, FullEastRow s y := by
  obtain ⟨p, hp, hmin⟩ := nat_rank_minimum core.sites
    (fun q => cyclicDistance h q.2 row) hne
  have hrow : p.2 ≠ row := by
    intro he
    apply hmiss p.1
    simpa only [← he] using hp
  have heast : ∀ x, core.sites (x,p.2) → s (x,p.2) = .east := by
    intro x hx
    cases hc : s (x,p.2) with
    | empty => exact False.elim (core.occupied _ hx hc)
    | east => rfl
    | north =>
      have hq := core.north_closed (x,p.2) hx hc
      have hb := hmin ((northDirection w h hh).next (x,p.2)) hq
      have hd := cyclicDistance_next h hh p.2 row hrow
      change cyclicDistance h p.2 row ≤ cyclicDistance h (cyclicNext h hh p.2) row at hb
      omega
  have hall : ∀ x, core.sites (x,p.2) := by
    apply Train.cyclic_all_of_step hw (fun x => core.sites (x,p.2))
      (fun x hx => core.east_closed (x,p.2) hx (heast x hx)) p.1
    exact hp
  exact ⟨p.2, fun x => heast x (hall x)⟩

theorem BlockingCore.full_north_column_of_missed_column
    (core : BlockingCore (eastDirection w h hw) (northDirection w h hh) s)
    (hne : ∃ p, core.sites p) (column : Fin w)
    (hmiss : ∀ y, ¬ core.sites (column,y)) : ∃ x, FullNorthColumn s x := by
  obtain ⟨p, hp, hmin⟩ := nat_rank_minimum core.sites
    (fun q => cyclicDistance w q.1 column) hne
  have hcolumn : p.1 ≠ column := by
    intro he
    apply hmiss p.2
    simpa only [← he] using hp
  have hnorth : ∀ y, core.sites (p.1,y) → s (p.1,y) = .north := by
    intro y hy
    cases hc : s (p.1,y) with
    | empty => exact False.elim (core.occupied _ hy hc)
    | east =>
      have hq := core.east_closed (p.1,y) hy hc
      have hb := hmin ((eastDirection w h hw).next (p.1,y)) hq
      have hd := cyclicDistance_next w hw p.1 column hcolumn
      change cyclicDistance w p.1 column ≤ cyclicDistance w (cyclicNext w hw p.1) column at hb
      omega
    | north => rfl
  have hall : ∀ y, core.sites (p.1,y) := by
    apply Train.cyclic_all_of_step hh (fun y => core.sites (p.1,y))
      (fun y hy => core.north_closed (p.1,y) hy (hnorth y hy)) p.2
    exact hp
  exact ⟨p.1, fun y => hnorth y (hall y)⟩

/-- No winding or cycle-extraction premise is needed: a nonempty closed core
without a full monochromatic lane already supplies all route obstacles. -/
theorem BlockingCore.routeCover_of_no_full_lane
    (core : BlockingCore (eastDirection w h hw) (northDirection w h hh) s)
    (hne : ∃ p, core.sites p) (hr : ¬ HasFullMonochromaticLane s) :
    _root_.Nonempty (RouteCover w h hw hh s) := by
  classical
  have hrows : ∀ y, ∃ x, core.sites (x,y) := by
    intro y
    apply Classical.byContradiction
    intro hm
    have hmiss : ∀ x, ¬ core.sites (x,y) := fun x hx => hm ⟨x, hx⟩
    exact hr (Or.inl (core.full_east_row_of_missed_row hne y hmiss))
  have hcolumns : ∀ x, ∃ y, core.sites (x,y) := by
    intro x
    apply Classical.byContradiction
    intro hm
    have hmiss : ∀ y, ¬ core.sites (x,y) := fun y hy => hm ⟨y, hy⟩
    exact hr (Or.inr (core.full_north_column_of_missed_column hne x hmiss))
  exact ⟨{
    core := core
    eastObstacle := fun y => Classical.choose (hrows y)
    east_mem := fun y => Classical.choose_spec (hrows y)
    northObstacle := fun x => Classical.choose (hcolumns x)
    north_mem := fun x => Classical.choose_spec (hcolumns x) }⟩

theorem BlockingCore.routeCover_or_full_lane
    (core : BlockingCore (eastDirection w h hw) (northDirection w h hh) s)
    (hne : ∃ p, core.sites p) :
    _root_.Nonempty (RouteCover w h hw hh s) ∨ HasFullMonochromaticLane s := by
  classical
  by_cases hr : HasFullMonochromaticLane s
  · exact Or.inr hr
  · exact Or.inl (core.routeCover_of_no_full_lane hne hr)

theorem BlockingCore.jammed_by_budget_of_no_full_lane
    (core : BlockingCore (eastDirection w h hw) (northDirection w h hh) s)
    (hne : ∃ p, core.sites p) (hr : ¬ HasFullMonochromaticLane s) :
    Jam (eastDirection w h hw) (northDirection w h hh)
      (iterate (torusStep w h hw hh) (movementBudget w h s) s) := by
  obtain ⟨cover⟩ := core.routeCover_of_no_full_lane hne hr
  exact cover.jammed_by_movementBudget

theorem full_lane_has_permanent_site (hr : HasFullMonochromaticLane s) :
    HasPermanentSite (eastDirection w h hw) (northDirection w h hh) s := by
  rcases hr with ⟨y, hy⟩ | ⟨x, hx⟩
  · refine ⟨.east, (⟨0,hw⟩,y), 0, ?_⟩
    intro t
    simpa only [Nat.zero_add, torusStep, Species.cell] using
      fullEastRow_persists hw hh s y hy t ⟨0,hw⟩
  · refine ⟨.north, (x,⟨0,hh⟩), 0, ?_⟩
    intro t
    simpa only [Nat.zero_add, torusStep, Species.cell] using
      fullNorthColumn_persists hw hh s x hx t ⟨0,hh⟩

theorem eventuallyJammed_of_permanent_site_of_no_full_lane
    (hs : HasPermanentSite (eastDirection w h hw) (northDirection w h hh) s)
    (hr : ¬ HasFullMonochromaticLane s) :
    EventuallyJammed (eastDirection w h hw) (northDirection w h hh) s := by
  obtain ⟨start, core, hne⟩ := future_blockingCore_of_permanent_site
    (eastDirection w h hw) (northDirection w h hh) s hs
  have hr' : ¬ HasFullMonochromaticLane
      (iterate (step (eastDirection w h hw) (northDirection w h hh)) start s) := by
    intro hfull
    exact hr ((hasFullMonochromaticLane_iterate_iff hw hh s start).mp hfull)
  have hj := core.jammed_by_budget_of_no_full_lane hne hr'
  refine ⟨start + movementBudget w h
    (iterate (step (eastDirection w h hw) (northDirection w h hh)) start s), ?_⟩
  rw [iterate_add]
  exact hj

/-- Exact finite-torus event reduction: some permanent car occurs precisely
when the orbit eventually jams or an initial full monochromatic lane exists. -/
theorem hasPermanentSite_iff_jam_or_full_lane :
    HasPermanentSite (eastDirection w h hw) (northDirection w h hh) s ↔
      EventuallyJammed (eastDirection w h hw) (northDirection w h hh) s ∨
        HasFullMonochromaticLane s := by
  classical
  constructor
  · intro hs
    by_cases hr : HasFullMonochromaticLane s
    · exact Or.inr hr
    · exact Or.inl (eventuallyJammed_of_permanent_site_of_no_full_lane hs hr)
  · rintro (hj | hr)
    · exact eventuallyJammed_has_permanent_site _ _ s hj
    · exact full_lane_has_permanent_site hr

/-- The event identity uses original car identities, through the actual
CLASSIC full-round `carTrace`, and includes singleton dimensions. -/
theorem hasEventuallyStoppedCar_iff_jam_or_full_lane :
    HasEventuallyStoppedCar (eastDirection w h hw) (northDirection w h hh) s ↔
      EventuallyJammed (eastDirection w h hw) (northDirection w h hh) s ∨
        HasFullMonochromaticLane s := by
  rw [← hasPermanentSite_iff_hasEventuallyStoppedCar]
  exact hasPermanentSite_iff_jam_or_full_lane

theorem every_site_empty_arbitrarily_late
    (hj : ¬ EventuallyJammed (eastDirection w h hw) (northDirection w h hh) s)
    (hr : ¬ HasFullMonochromaticLane s) (p : Position w h) (start : Nat) :
    ∃ t, iterate (torusStep w h hw hh) (start+t) s p = .empty := by
  classical
  apply Classical.byContradiction
  intro hhits
  have ho : ∀ t, iterate (torusStep w h hw hh) (start+t) s p ≠ .empty :=
    fun t ht => hhits ⟨t, ht⟩
  obtain ⟨sp, hp⟩ := occupied_forever_has_permanent_site
    (eastDirection w h hw) (northDirection w h hh) s p start ho
  exact hj (eventuallyJammed_of_permanent_site_of_no_full_lane ⟨sp, p, hp⟩ hr)

theorem every_tag_moves_arbitrarily_late
    (hj : ¬ EventuallyJammed (eastDirection w h hw) (northDirection w h hh) s)
    (hr : ¬ HasFullMonochromaticLane s) (sp : Species) (p : Position w h)
    (hp : s p = sp.cell) (start : Nat) :
    ∃ t, RoundCanMove (eastDirection w h hw) (northDirection w h hh) sp
      (iterate (torusStep w h hw hh) (start+t) s)
      (carTrace (eastDirection w h hw) (northDirection w h hh) sp s (start+t) p) := by
  classical
  apply Classical.byContradiction
  intro hm
  have hn : ∀ t, ¬ RoundCanMove (eastDirection w h hw) (northDirection w h hh) sp
      (iterate (torusStep w h hw hh) (start+t) s)
      (carTrace (eastDirection w h hw) (northDirection w h hh) sp s (start+t) p) :=
    fun t ht => hm ⟨t, ht⟩
  have hs : TagEventuallyStopped (eastDirection w h hw) (northDirection w h hh) sp s p := by
    exact (tagEventuallyStopped_iff_finitely_many_moves _ _ sp s p hp).mpr ⟨start, hn⟩
  have he := hasEventuallyStoppedCar_iff_jam_or_full_lane.mp ⟨sp, p, hp, hs⟩
  exact he.elim hj hr

end Torus

end BML
