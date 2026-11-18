import Train.Conservation
import Train.Torus

/-!
# Tagged TRAIN dynamics and corrected diagonal transport

The clock in this module counts complete east-then-north updates. Each original
occupied position labels one car. Its species is preserved by the actual
snapshot kernel, and the labelled positions cover every later occupied cell.
-/

namespace BML.Train

/-- Transport every occupied site, leaving the inactive species in place. -/
theorem phaseTransport_preserves_cell (d : CyclicDirection α) (sp : Species)
    (s : Config α) (p : α) (hp : s p ≠ .empty) :
    halfStep d sp s (transport d sp s p) = s p := by
  by_cases ho : s p = sp.cell
  · rw [transport_preserves_car d sp s p ho, ho]
  · have hm : ¬ CanMove d sp s p := fun h => ho h.1
    simpa only [transport, ite_eq_right hm] using
      (other_species_unchanged d sp s p (s p) hp ho).mpr rfl

theorem phaseTransport_injective (d : CyclicDirection α) (sp : Species)
    (s : Config α) (p q : α) (hp : s p ≠ .empty) (hq : s q ≠ .empty)
    (heq : transport d sp s p = transport d sp s q) : p = q := by
  have hc : s p = s q := by
    calc
      s p = halfStep d sp s (transport d sp s p) :=
        (phaseTransport_preserves_cell d sp s p hp).symm
      _ = halfStep d sp s (transport d sp s q) := congrArg _ heq
      _ = s q := phaseTransport_preserves_cell d sp s q hq
  by_cases ho : s p = sp.cell
  · exact transport_injective_on_cars d sp s p q ho (hc.symm.trans ho) heq
  · have hmo : ¬ CanMove d sp s p := fun h => ho h.1
    have hmq : ¬ CanMove d sp s q := fun h => ho (hc.trans h.1)
    simpa only [transport, ite_eq_right hmo, ite_eq_right hmq] using heq

theorem phaseTransport_surjective (d : CyclicDirection α) (sp : Species)
    (s : Config α) (q : α) (hq : halfStep d sp s q ≠ .empty) :
    ∃ p, s p ≠ .empty ∧ transport d sp s p = q := by
  by_cases ho : halfStep d sp s q = sp.cell
  · obtain ⟨p, hp, he⟩ := transport_surjective_on_cars d sp s q ho
    exact ⟨p, by rw [hp]; exact sp.cell_ne_empty, he⟩
  · have hc : s q = halfStep d sp s q :=
      (other_species_unchanged d sp s q (halfStep d sp s q) hq ho).mp rfl
    have hm : ¬ CanMove d sp s q := fun h => ho (hc.symm.trans h.1)
    exact ⟨q, by rw [hc]; exact hq, by simp only [transport, ite_eq_right hm]⟩

/-- The ordered composition transports identities, including rotating rings. -/
def fullTransport (east north : CyclicDirection α) (s : Config α) (p : α) : α :=
  transport north .north (halfStep east .east s) (transport east .east s p)

/-- A car moves in its own phase of this complete update. -/
def FullCanMove (east north : CyclicDirection α) (s : Config α) (p : α) : Prop :=
  match s p with
  | .empty => False
  | .east => CanMove east .east s p
  | .north => CanMove north .north (halfStep east .east s) p

instance (east north : CyclicDirection α) (s : Config α) (p : α) :
    Decidable (FullCanMove east north s p) := by
  unfold FullCanMove
  split <;> infer_instance

theorem fullTransport_preserves_cell (east north : CyclicDirection α)
    (s : Config α) (p : α) (hp : s p ≠ .empty) :
    step east north s (fullTransport east north s p) = s p := by
  have he := phaseTransport_preserves_cell east .east s p hp
  have hn := phaseTransport_preserves_cell north .north (halfStep east .east s)
    (transport east .east s p) (by rw [he]; exact hp)
  exact hn.trans he

theorem fullTransport_injective (east north : CyclicDirection α)
    (s : Config α) (p q : α) (hp : s p ≠ .empty) (hq : s q ≠ .empty)
    (heq : fullTransport east north s p = fullTransport east north s q) : p = q := by
  have hep := phaseTransport_preserves_cell east .east s p hp
  have heq' := phaseTransport_preserves_cell east .east s q hq
  have hh := phaseTransport_injective north .north (halfStep east .east s)
    (transport east .east s p) (transport east .east s q)
    (by rw [hep]; exact hp) (by rw [heq']; exact hq) heq
  exact phaseTransport_injective east .east s p q hp hq hh

theorem fullTransport_surjective (east north : CyclicDirection α)
    (s : Config α) (q : α) (hq : step east north s q ≠ .empty) :
    ∃ p, s p ≠ .empty ∧ fullTransport east north s p = q := by
  obtain ⟨r, hr, hnr⟩ := phaseTransport_surjective north .north (halfStep east .east s) q hq
  obtain ⟨p, hp, hep⟩ := phaseTransport_surjective east .east s r hr
  exact ⟨p, hp, by simp only [fullTransport, hep, hnr]⟩

theorem fullTransport_of_east (east north : CyclicDirection α)
    (s : Config α) (p : α) (hp : s p = .east) :
    fullTransport east north s p = transport east .east s p := by
  have hc := transport_preserves_car east .east s p hp
  have hm : ¬ CanMove north .north (halfStep east .east s) (transport east .east s p) := by
    intro h
    have hf := hc.symm.trans h.1
    cases hf
  exact ite_eq_right hm

theorem fullTransport_of_north (east north : CyclicDirection α)
    (s : Config α) (p : α) (hp : s p = .north) :
    fullTransport east north s p = transport north .north (halfStep east .east s) p := by
  have hm : ¬ CanMove east .east s p := by
    intro h
    have hf := hp.symm.trans h.1
    cases hf
  simp only [fullTransport, transport, ite_eq_right hm]

/-- Labels are the initial positions; time counts complete ordered updates. -/
def trace (east north : CyclicDirection α) (s : Config α) : Nat → α → α
  | 0, p => p
  | t + 1, p => fullTransport east north (BML.iterate (step east north) t s)
      (trace east north s t p)

theorem trace_cell (east north : CyclicDirection α) (s : Config α)
    (t : Nat) (p : α) (hp : s p ≠ .empty) :
    BML.iterate (step east north) t s (trace east north s t p) = s p := by
  induction t with
  | zero => rfl
  | succ t ih =>
    exact (fullTransport_preserves_cell east north (BML.iterate (step east north) t s)
      (trace east north s t p) (by rw [ih]; exact hp)).trans ih

theorem trace_injective (east north : CyclicDirection α) (s : Config α)
    (t : Nat) (p q : α) (hp : s p ≠ .empty) (hq : s q ≠ .empty)
    (heq : trace east north s t p = trace east north s t q) : p = q := by
  induction t with
  | zero => exact heq
  | succ t ih =>
    apply ih
    exact fullTransport_injective east north (BML.iterate (step east north) t s)
      (trace east north s t p) (trace east north s t q)
      (by rw [trace_cell east north s t p hp]; exact hp)
      (by rw [trace_cell east north s t q hq]; exact hq) heq

theorem trace_coverage (east north : CyclicDirection α) (s : Config α)
    (t : Nat) (q : α) (hq : BML.iterate (step east north) t s q ≠ .empty) :
    ∃ p, s p ≠ .empty ∧ trace east north s t p = q := by
  induction t generalizing q with
  | zero => exact ⟨q, hq, rfl⟩
  | succ t ih =>
    obtain ⟨r, hr, htr⟩ := fullTransport_surjective east north
      (BML.iterate (step east north) t s) q hq
    obtain ⟨p, hp, heq⟩ := ih r hr
    exact ⟨p, hp, by simp only [trace, heq, htr]⟩

/-- The ordinary northeast diagonal class on a square torus. -/
def diagonal (n : Nat) (hn : 0 < n) (p : Position n n) : Fin n :=
  ⟨(p.1.val + p.2.val) % n, Nat.mod_lt _ hn⟩

/-- Subtract the number of complete updates in the cyclic group. -/
def corrected (n : Nat) (hn : 0 < n) (t : Nat) (p : Position n n) : Fin n :=
  BML.iterate (BML.cyclicPrev n hn) t (diagonal n hn p)

def correctedTrace (n : Nat) (hn : 0 < n) (s : Config (Position n n))
    (t : Nat) (p : Position n n) : Fin n :=
  corrected n hn t (trace (eastRing n n hn) (northRing n n hn) s t p)

theorem diagonal_east (n : Nat) (hn : 0 < n) (p : Position n n) :
    diagonal n hn ((eastRing n n hn).next p) =
      BML.cyclicNext n hn (diagonal n hn p) := by
  apply Fin.ext
  change ((BML.cyclicNext n hn p.1).val + p.2.val) % n =
    (BML.cyclicNext n hn (diagonal n hn p)).val
  rw [cyclicNext_val, cyclicNext_val]
  change ((p.1.val + 1) % n + p.2.val) % n = ((p.1.val + p.2.val) % n + 1) % n
  rw [Nat.mod_add_mod, Nat.mod_add_mod]
  congr 1
  omega

theorem diagonal_north (n : Nat) (hn : 0 < n) (p : Position n n) :
    diagonal n hn ((northRing n n hn).next p) =
      BML.cyclicNext n hn (diagonal n hn p) := by
  apply Fin.ext
  change (p.1.val + (BML.cyclicNext n hn p.2).val) % n =
    (BML.cyclicNext n hn (diagonal n hn p)).val
  rw [cyclicNext_val, cyclicNext_val]
  change (p.1.val + (p.2.val + 1) % n) % n = ((p.1.val + p.2.val) % n + 1) % n
  rw [Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]

theorem corrected_succ (n : Nat) (hn : 0 < n) (t : Nat) (p : Position n n) :
    corrected n hn (t + 1) p = BML.cyclicPrev n hn (corrected n hn t p) := rfl

theorem corrected_succ_of_diagonal_next (n : Nat) (hn : 0 < n) (t : Nat)
    (p q : Position n n)
    (hd : diagonal n hn q = BML.cyclicNext n hn (diagonal n hn p)) :
    corrected n hn (t + 1) q = corrected n hn t p := by
  unfold corrected
  rw [hd, iterate_succ_start, BML.cyclicPrev_next]

theorem corrected_succ_east (n : Nat) (hn : 0 < n) (t : Nat) (p : Position n n) :
    corrected n hn (t + 1) ((eastRing n n hn).next p) = corrected n hn t p :=
  corrected_succ_of_diagonal_next n hn t p _ (diagonal_east n hn p)

theorem corrected_succ_north (n : Nat) (hn : 0 < n) (t : Nat) (p : Position n n) :
    corrected n hn (t + 1) ((northRing n n hn).next p) = corrected n hn t p :=
  corrected_succ_of_diagonal_next n hn t p _ (diagonal_north n hn p)

theorem corrected_east (n : Nat) (hn : 0 < n) (t : Nat) (p : Position n n) :
    corrected n hn t ((eastRing n n hn).next p) =
      BML.cyclicNext n hn (corrected n hn t p) := by
  have he := congrArg (BML.cyclicNext n hn) (corrected_succ_east n hn t p)
  simpa only [corrected_succ, BML.cyclicNext_prev] using he

theorem corrected_north (n : Nat) (hn : 0 < n) (t : Nat) (p : Position n n) :
    corrected n hn t ((northRing n n hn).next p) =
      BML.cyclicNext n hn (corrected n hn t p) := by
  have he := congrArg (BML.cyclicNext n hn) (corrected_succ_north n hn t p)
  simpa only [corrected_succ, BML.cyclicNext_prev] using he

theorem corrected_west (n : Nat) (hn : 0 < n) (t : Nat) (p : Position n n) :
    corrected n hn t ((eastRing n n hn).prev p) =
      BML.cyclicPrev n hn (corrected n hn t p) := by
  have he := congrArg (BML.cyclicPrev n hn)
    (corrected_east n hn t ((eastRing n n hn).prev p))
  simpa only [(eastRing n n hn).next_prev, BML.cyclicPrev_next] using he.symm

theorem cyclicPrev_ne_self (n : Nat) (hn : 0 < n) (hlarge : 1 < n) (b : Fin n) :
    BML.cyclicPrev n hn b ≠ b := by
  intro he
  have hv := congrArg Fin.val he
  unfold BML.cyclicPrev at hv
  split at hv <;> simp only at hv <;> omega

/-- Actual motion keeps the corrected class; actual blocking decreases it once. -/
theorem corrected_fullTransport (n : Nat) (hn : 0 < n) (t : Nat)
    (s : Config (Position n n)) (p : Position n n) (hp : s p ≠ .empty) :
    corrected n hn (t + 1) (fullTransport (eastRing n n hn) (northRing n n hn) s p) =
      if FullCanMove (eastRing n n hn) (northRing n n hn) s p then
        corrected n hn t p
      else BML.cyclicPrev n hn (corrected n hn t p) := by
  cases hc : s p with
  | empty => exact False.elim (hp hc)
  | east =>
    rw [fullTransport_of_east _ _ s p hc]
    simp only [FullCanMove, hc]
    by_cases hm : CanMove (eastRing n n hn) .east s p
    · simp only [transport, ite_eq_left hm, corrected_succ_east]
    · simp only [transport, ite_eq_right hm, corrected_succ]
  | north =>
    rw [fullTransport_of_north _ _ s p hc]
    simp only [FullCanMove, hc]
    by_cases hm : CanMove (northRing n n hn) .north (halfStep (eastRing n n hn) .east s) p
    · simp only [transport, ite_eq_left hm, corrected_succ_north]
    · simp only [transport, ite_eq_right hm, corrected_succ]

theorem corrected_trace_step (n : Nat) (hn : 0 < n)
    (s : Config (Position n n)) (t : Nat) (p : Position n n)
    (hp : p ∈ occupiedPositions s) :
    correctedTrace n hn s (t + 1) p =
      if FullCanMove (eastRing n n hn) (northRing n n hn)
        (BML.iterate (torusStep n n hn hn) t s)
        (trace (eastRing n n hn) (northRing n n hn) s t p) then
        correctedTrace n hn s t p
      else BML.cyclicPrev n hn (correctedTrace n hn s t p) := by
  have hne := (mem_occupiedPositions s p).mp hp
  exact corrected_fullTransport n hn t _ _
    (by rw [trace_cell _ _ s t p hne]; exact hne)

theorem corrected_trace_step_cases (n : Nat) (hn : 0 < n)
    (s : Config (Position n n)) (t : Nat) (p : Position n n)
    (hp : p ∈ occupiedPositions s) :
    correctedTrace n hn s (t + 1) p = correctedTrace n hn s t p ∨
      correctedTrace n hn s (t + 1) p = BML.cyclicPrev n hn (correctedTrace n hn s t p) := by
  rw [corrected_trace_step n hn s t p hp]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem corrected_trace_stable_iff_move (n : Nat) (hn : 0 < n) (hlarge : 1 < n)
    (s : Config (Position n n)) (t : Nat) (p : Position n n)
    (hp : p ∈ occupiedPositions s) :
    correctedTrace n hn s (t + 1) p = correctedTrace n hn s t p ↔
      FullCanMove (eastRing n n hn) (northRing n n hn)
        (BML.iterate (torusStep n n hn hn) t s)
        (trace (eastRing n n hn) (northRing n n hn) s t p) := by
  rw [corrected_trace_step n hn s t p hp]
  split
  · simp_all
  · simp_all [cyclicPrev_ne_self n hn hlarge]

/-- A diagonal followed by an empty diagonal releases at least one actual car. -/
theorem corrected_release_car (n : Nat) (hn : 0 < n) (t : Nat)
    (s : Config (Position n n)) (b : Fin n)
    (hoccupied : ∃ p, s p ≠ .empty ∧ corrected n hn t p = b)
    (hempty : ∀ p, corrected n hn t p = BML.cyclicNext n hn b → s p = .empty) :
    ∃ p, s p ≠ .empty ∧ corrected n hn t p = b ∧
      FullCanMove (eastRing n n hn) (northRing n n hn) s p := by
  classical
  by_cases heast : ∃ p, s p = .east ∧ corrected n hn t p = b
  · obtain ⟨p, hp, hb⟩ := heast
    have hv : s ((eastRing n n hn).next p) = .empty :=
      hempty _ (by rw [corrected_east, hb])
    have hm : CanMove (eastRing n n hn) .east s p :=
      (canMove_local _ .east s p).mpr ⟨hp, Or.inl hv⟩
    exact ⟨p, by simp [hp], hb, by simpa only [FullCanMove, hp] using hm⟩
  · obtain ⟨p, hp, hb⟩ := hoccupied
    have hnorth : s p = .north := by
      cases hc : s p with
      | empty => exact False.elim (hp hc)
      | east => exact False.elim (heast ⟨p, hc, hb⟩)
      | north => rfl
    have hv : s ((northRing n n hn).next p) = .empty :=
      hempty _ (by rw [corrected_north, hb])
    have hwest : corrected n hn t
        ((eastRing n n hn).prev ((northRing n n hn).next p)) = b := by
      rw [corrected_west, corrected_north, hb, BML.cyclicPrev_next]
    have hnoincoming : ¬ CanMove (eastRing n n hn) .east s
        ((eastRing n n hn).prev ((northRing n n hn).next p)) := by
      intro hm
      exact heast ⟨_, hm.1, hwest⟩
    have hnodeparture : ¬ CanMove (eastRing n n hn) .east s
        ((northRing n n hn).next p) := by
      intro hm
      have hf := hv.symm.trans hm.1
      cases hf
    have hvafter : halfStep (eastRing n n hn) .east s
        ((northRing n n hn).next p) = .empty := by
      simp only [halfStep, ite_eq_right hnoincoming, ite_eq_right hnodeparture, hv]
    have hpafter : halfStep (eastRing n n hn) .east s p = .north :=
      (other_species_unchanged _ .east s p .north (by decide) (by decide)).mpr hnorth
    have hm : CanMove (northRing n n hn) .north (halfStep (eastRing n n hn) .east s) p :=
      (canMove_local _ .north _ p).mpr ⟨hpafter, Or.inl hvafter⟩
    exact ⟨p, hp, hb, by simpa only [FullCanMove, hnorth] using hm⟩

theorem corrected_release (n : Nat) (hn : 0 < n) (t : Nat)
    (s : Config (Position n n)) (b : Fin n)
    (hoccupied : ∃ p, s p ≠ .empty ∧ corrected n hn t p = b)
    (hempty : ∀ p, corrected n hn t p = BML.cyclicNext n hn b → s p = .empty) :
    ∃ q, torusStep n n hn hn s q ≠ .empty ∧ corrected n hn (t + 1) q = b := by
  obtain ⟨p, hp, hb, hm⟩ := corrected_release_car n hn t s b hoccupied hempty
  refine ⟨fullTransport (eastRing n n hn) (northRing n n hn) s p, ?_, ?_⟩
  · rw [show torusStep n n hn hn s = step (eastRing n n hn) (northRing n n hn) s from rfl,
      fullTransport_preserves_cell _ _ s p hp]
    exact hp
  · rw [corrected_fullTransport n hn t s p hp, ite_eq_left hm, hb]

/-- The release hypothesis for the finite original-label diagonal argument. -/
theorem corrected_trace_release (n : Nat) (hn : 0 < n)
    (s : Config (Position n n)) (t : Nat) (b : Fin n)
    (hoccupied : ∃ p ∈ occupiedPositions s, correctedTrace n hn s t p = b)
    (hempty : ∀ p, p ∈ occupiedPositions s →
      correctedTrace n hn s t p ≠ BML.cyclicNext n hn b) :
    ∃ p ∈ occupiedPositions s, correctedTrace n hn s (t + 1) p = b := by
  let u := BML.iterate (torusStep n n hn hn) t s
  have hoc : ∃ q, u q ≠ .empty ∧ corrected n hn t q = b := by
    obtain ⟨p, hp, hb⟩ := hoccupied
    have hne := (mem_occupiedPositions s p).mp hp
    refine ⟨trace (eastRing n n hn) (northRing n n hn) s t p, ?_, hb⟩
    change BML.iterate (step (eastRing n n hn) (northRing n n hn)) t s
      (trace (eastRing n n hn) (northRing n n hn) s t p) ≠ .empty
    rw [trace_cell _ _ s t p hne]
    exact hne
  have he : ∀ q, corrected n hn t q = BML.cyclicNext n hn b → u q = .empty := by
    intro q hq
    by_cases hne : u q = .empty
    · exact hne
    exfalso
    obtain ⟨p, hp, htrace⟩ := trace_coverage (eastRing n n hn) (northRing n n hn) s t q hne
    apply hempty p ((mem_occupiedPositions s p).mpr hp)
    change corrected n hn t (trace (eastRing n n hn) (northRing n n hn) s t p) = _
    rw [htrace, hq]
  obtain ⟨q, hq, hb⟩ := corrected_release n hn t u b hoc he
  obtain ⟨p, hp, htrace⟩ := trace_coverage (eastRing n n hn) (northRing n n hn) s (t + 1) q hq
  refine ⟨p, (mem_occupiedPositions s p).mpr hp, ?_⟩
  change corrected n hn (t + 1)
    (trace (eastRing n n hn) (northRing n n hn) s (t + 1) p) = b
  rw [htrace, hb]

end BML.Train
