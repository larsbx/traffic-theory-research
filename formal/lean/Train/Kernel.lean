import BML.Transport

/-!
# TRAIN updates on finite cyclic directions

The bounded scan reads only the input snapshot. It stops at the first vacancy
or opposite species; reaching the period without either rotates a full ring.
Incoming cars overwrite departing cars in the synchronous update.
-/

namespace BML.Train

structure CyclicDirection (α : Type) extends Direction α where
  period : Nat
  positive : 0 < period
  closes : ∀ p, BML.iterate next period p = p

def other : Species → Species
  | .east => .north
  | .north => .east

@[simp] theorem other_cell_ne (sp : Species) : (other sp).cell ≠ sp.cell := by
  cases sp <;> decide

theorem cell_cases (sp : Species) (c : Cell) :
    c = .empty ∨ c = sp.cell ∨ c = (other sp).cell := by
  cases sp <;> cases c <;> simp [Species.cell, other]

theorem iterate_succ_start (f : α → α) (n : Nat) (p : α) :
    BML.iterate f (n + 1) p = BML.iterate f n (f p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change f (BML.iterate f (n + 1) p) = f (BML.iterate f n (f p))
    exact congrArg f ih

/-- `true` means no opposite car was found before the first vacancy or bound. -/
def clear (d : Direction α) (sp : Species) (s : Config α) : Nat → α → Bool
  | 0, _ => true
  | n + 1, p =>
    if s p = .empty then true
    else if s p = sp.cell then clear d sp s n (d.next p)
    else false

/-- A finite initial segment consists entirely of the active species. -/
def AllOwn (d : Direction α) (sp : Species) (s : Config α) : Nat → α → Prop
  | 0, _ => True
  | n + 1, p => s p = sp.cell ∧ AllOwn d sp s n (d.next p)

instance (d : Direction α) (sp : Species) (s : Config α) (n : Nat) (p : α) :
    Decidable (AllOwn d sp s n p) := by
  induction n generalizing p with
  | zero => exact isTrue True.intro
  | succ n ih =>
    change Decidable (s p = sp.cell ∧ AllOwn d sp s n (d.next p))
    exact @instDecidableAnd _ _ (inferInstance) (ih (d.next p))

/-- A vacancy is reached within the bound through active-species cars. -/
def QueueReady (d : Direction α) (sp : Species) (s : Config α) : Nat → α → Prop
  | 0, _ => False
  | n + 1, p => s p = .empty ∨
    (s p = sp.cell ∧ QueueReady d sp s n (d.next p))

/-- Literal snapshot mask propagation: seed front cars, then propagate backwards. -/
def propagated (d : Direction α) (sp : Species) (s : Config α) : Nat → α → Bool
  | 0, p => decide (BML.CanMove d sp s p)
  | n + 1, p => propagated d sp s n p ||
    (decide (s p = sp.cell) && propagated d sp s n (d.next p))

theorem queueReady_mono (d : Direction α) (sp : Species) (s : Config α)
    (n : Nat) (p : α) (h : QueueReady d sp s n p) :
    QueueReady d sp s (n + 1) p := by
  induction n generalizing p with
  | zero => exact False.elim h
  | succ n ih =>
    rcases h with he | ⟨ho, hq⟩
    · exact Or.inl he
    · exact Or.inr ⟨ho, ih (d.next p) hq⟩

theorem propagated_iff_queueReady (d : Direction α) (sp : Species) (s : Config α)
    (n : Nat) (p : α) :
    propagated d sp s n p = true ↔ s p = sp.cell ∧
      QueueReady d sp s (n + 1) (d.next p) := by
  induction n generalizing p with
  | zero =>
    constructor
    · intro h
      have hm : BML.CanMove d sp s p := of_decide_eq_true h
      exact ⟨hm.1, Or.inl hm.2⟩
    · rintro ⟨hp, he | ⟨_, hfalse⟩⟩
      · exact decide_eq_true (show BML.CanMove d sp s p from ⟨hp, he⟩)
      · exact False.elim hfalse
  | succ n ih =>
    simp only [propagated, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro (⟨hp, hq⟩ | ⟨hp, hn, hq⟩)
      · exact ⟨hp, queueReady_mono d sp s (n + 1) (d.next p) hq⟩
      · exact ⟨hp, Or.inr ⟨hn, hq⟩⟩
    · rintro ⟨hp, he | ⟨hn, hq⟩⟩
      · exact Or.inl ⟨hp, Or.inl he⟩
      · exact Or.inr ⟨hp, hn, hq⟩

theorem queueReady_extend_own (d : Direction α) (sp : Species) (s : Config α)
    (n : Nat) (p : α) (h : s (BML.iterate d.next n p) = sp.cell) :
    QueueReady d sp s (n + 1) p ↔ QueueReady d sp s n p := by
  induction n generalizing p with
  | zero =>
    simp only [BML.iterate] at h
    simp [QueueReady, h]
  | succ n ih =>
    have hrest : s (BML.iterate d.next n (d.next p)) = sp.cell := by
      simpa only [iterate_succ_start] using h
    change (s p = .empty ∨ (s p = sp.cell ∧ QueueReady d sp s (n + 1) (d.next p))) ↔
      (s p = .empty ∨ (s p = sp.cell ∧ QueueReady d sp s n (d.next p)))
    rw [ih (d.next p) hrest]

theorem queueReady_period_shift (d : CyclicDirection α) (sp : Species)
    (s : Config α) (p : α) (hp : s p = sp.cell) :
    QueueReady d.toDirection sp s d.period p ↔
      QueueReady d.toDirection sp s d.period (d.next p) := by
  have he := queueReady_extend_own d.toDirection sp s d.period p (by rw [d.closes]; exact hp)
  have hs : QueueReady d.toDirection sp s (d.period + 1) p ↔
      QueueReady d.toDirection sp s d.period (d.next p) := by
    simp [QueueReady, hp]
  exact he.symm.trans hs

def FullRing (d : CyclicDirection α) (sp : Species) (s : Config α) (p : α) : Prop :=
  AllOwn d.toDirection sp s d.period p

instance (d : CyclicDirection α) (sp : Species) (s : Config α) (p : α) :
    Decidable (FullRing d sp s p) := inferInstanceAs (Decidable (AllOwn _ _ _ _ _))

/-- Executable TRAIN eligibility, including the full-ring rotation case. -/
def CanMove (d : CyclicDirection α) (sp : Species) (s : Config α) (p : α) : Prop :=
  s p = sp.cell ∧ clear d.toDirection sp s d.period p = true

instance (d : CyclicDirection α) (sp : Species) (s : Config α) (p : α) :
    Decidable (CanMove d sp s p) := inferInstanceAs (Decidable (_ ∧ _))

theorem clear_iff_queue_or_allOwn (d : Direction α) (sp : Species)
    (s : Config α) (n : Nat) (p : α) :
    clear d sp s n p = true ↔ QueueReady d sp s n p ∨ AllOwn d sp s n p := by
  induction n generalizing p with
  | zero => simp [clear, QueueReady, AllOwn]
  | succ n ih =>
    by_cases he : s p = .empty
    · simp [clear, QueueReady, AllOwn, he]
    · by_cases ho : s p = sp.cell
      · simp [clear, QueueReady, AllOwn, ho, ih]
      · simp [clear, QueueReady, AllOwn, he, ho]

theorem canMove_iff_queue_or_fullRing (d : CyclicDirection α) (sp : Species)
    (s : Config α) (p : α) :
    CanMove d sp s p ↔ s p = sp.cell ∧
      (QueueReady d.toDirection sp s d.period p ∨ FullRing d sp s p) := by
  simp only [CanMove, FullRing, clear_iff_queue_or_allOwn]

theorem allOwn_head (d : Direction α) (sp : Species) (s : Config α)
    (n : Nat) (hn : 0 < n) (p : α) (h : AllOwn d sp s n p) : s p = sp.cell := by
  cases n with
  | zero => omega
  | succ n => exact h.1

theorem allOwn_iff_iterates (d : Direction α) (sp : Species) (s : Config α)
    (n : Nat) (p : α) :
    AllOwn d sp s n p ↔ ∀ k, k < n → s (BML.iterate d.next k p) = sp.cell := by
  induction n generalizing p with
  | zero => simp [AllOwn]
  | succ n ih =>
    constructor
    · rintro ⟨hp, hrest⟩ k hk
      cases k with
      | zero => exact hp
      | succ k =>
        rw [iterate_succ_start]
        exact (ih (d.next p)).mp hrest k (by omega)
    · intro h
      refine ⟨h 0 (by omega), (ih (d.next p)).mpr ?_⟩
      intro k hk
      simpa only [← iterate_succ_start] using h (k + 1) (by omega)

theorem fullRing_canMove (d : CyclicDirection α) (sp : Species)
    (s : Config α) (p : α) (h : FullRing d sp s p) : CanMove d sp s p := by
  refine ⟨allOwn_head _ _ _ _ d.positive _ h, ?_⟩
  exact (clear_iff_queue_or_allOwn _ _ _ _ _).mpr (Or.inr h)

/-- The exported bounded scan equals the literal Python-style propagation mask. -/
theorem canMove_iff_propagation (d : CyclicDirection α) (sp : Species)
    (s : Config α) (p : α) :
    CanMove d sp s p ↔
      propagated d.toDirection sp s (d.period - 1) p = true ∨ FullRing d sp s p := by
  have hperiod : d.period - 1 + 1 = d.period := by have hp := d.positive; omega
  have hprop : propagated d.toDirection sp s (d.period - 1) p = true ↔
      s p = sp.cell ∧ QueueReady d.toDirection sp s d.period (d.next p) := by
    simpa only [hperiod] using propagated_iff_queueReady d.toDirection sp s (d.period - 1) p
  constructor
  · intro h
    rcases (canMove_iff_queue_or_fullRing d sp s p).mp h with ⟨hp, hq | hf⟩
    · exact Or.inl (hprop.mpr ⟨hp, (queueReady_period_shift d sp s p hp).mp hq⟩)
    · exact Or.inr hf
  · rintro (h | h)
    · obtain ⟨hp, hq⟩ := hprop.mp h
      exact (canMove_iff_queue_or_fullRing d sp s p).mpr
        ⟨hp, Or.inl ((queueReady_period_shift d sp s p hp).mpr hq)⟩
    · exact fullRing_canMove d sp s p h

theorem fullRing_next (d : CyclicDirection α) (sp : Species)
    (s : Config α) (p : α) (h : FullRing d sp s p) :
    FullRing d sp s (d.next p) := by
  apply (allOwn_iff_iterates d.toDirection sp s d.period (d.next p)).mpr
  intro k hk
  rw [← iterate_succ_start]
  by_cases hl : k + 1 < d.period
  · exact (allOwn_iff_iterates _ _ _ _ _).mp h (k + 1) hl
  · have he : k + 1 = d.period := by omega
    rw [he, d.closes]
    exact allOwn_head _ _ _ _ d.positive _ h

/-- Extending a scan by one active-species endpoint does not change its answer. -/
theorem clear_extend_own (d : Direction α) (sp : Species) (s : Config α)
    (n : Nat) (p : α) (h : s (BML.iterate d.next n p) = sp.cell) :
    clear d sp s (n + 1) p = clear d sp s n p := by
  induction n generalizing p with
  | zero => simp [BML.iterate] at h; simp [clear, h, sp.cell_ne_empty]
  | succ n ih =>
    have hrest : s (BML.iterate d.next n (d.next p)) = sp.cell := by
      simpa only [iterate_succ_start] using h
    simp only [clear]
    split
    · rfl
    · split
      · exact ih (d.next p) hrest
      · rfl

theorem clear_period_shift (d : CyclicDirection α) (sp : Species)
    (s : Config α) (p : α) (hp : s p = sp.cell) :
    clear d.toDirection sp s d.period p =
      clear d.toDirection sp s d.period (d.next p) := by
  have h := clear_extend_own d.toDirection sp s d.period p (by rw [d.closes]; exact hp)
  calc
    clear d.toDirection sp s d.period p = clear d.toDirection sp s (d.period + 1) p := h.symm
    _ = clear d.toDirection sp s d.period (d.next p) := by simp [clear, hp]

theorem clear_positive_cases (d : Direction α) (sp : Species) (s : Config α)
    (n : Nat) (hn : 0 < n) (p : α) (h : clear d sp s n p = true) :
    s p = .empty ∨ s p = sp.cell := by
  cases n with
  | zero => omega
  | succ n =>
    by_cases he : s p = .empty
    · exact Or.inl he
    · right
      by_cases ho : s p = sp.cell
      · exact ho
      · simp [clear, he, ho] at h

theorem clear_of_empty (d : Direction α) (sp : Species) (s : Config α)
    (n : Nat) (p : α) (h : s p = .empty) : clear d sp s n p = true := by
  cases n <;> simp [clear, h]

/-- Local queue propagation is valid because the finite scan closes cyclically. -/
theorem canMove_local (d : CyclicDirection α) (sp : Species)
    (s : Config α) (p : α) :
    CanMove d sp s p ↔ s p = sp.cell ∧
      (s (d.next p) = .empty ∨ CanMove d sp s (d.next p)) := by
  constructor
  · rintro ⟨hp, hclear⟩
    have hc : clear d.toDirection sp s d.period (d.next p) = true := by
      rw [← clear_period_shift d sp s p hp]
      exact hclear
    refine ⟨hp, ?_⟩
    rcases clear_positive_cases d.toDirection sp s d.period d.positive _ hc with he | ho
    · exact Or.inl he
    · exact Or.inr ⟨ho, hc⟩
  · rintro ⟨hp, he | hm⟩
    · refine ⟨hp, ?_⟩
      rw [clear_period_shift d sp s p hp]
      exact clear_of_empty _ _ _ _ _ he
    · refine ⟨hp, ?_⟩
      rw [clear_period_shift d sp s p hp]
      exact hm.2

theorem queue_propagates_backward (d : CyclicDirection α) (sp : Species)
    (s : Config α) (p : α) (hp : s p = sp.cell)
    (hnext : CanMove d sp s (d.next p)) : CanMove d sp s p :=
  (canMove_local d sp s p).mpr ⟨hp, Or.inr hnext⟩

/-- A blocked scan has an actual opposite-species car ahead, not just an assumed obstruction. -/
theorem clear_failure_blocker (d : Direction α) (sp : Species) (s : Config α)
    (n : Nat) (p : α) (h : clear d sp s n p ≠ true) :
    ∃ k, k < n ∧ AllOwn d sp s k p ∧
      s (BML.iterate d.next k p) = (other sp).cell := by
  induction n generalizing p with
  | zero => simp [clear] at h
  | succ n ih =>
    rcases cell_cases sp (s p) with he | ho | hb
    · simp [clear, he] at h
    · have hrest : clear d sp s n (d.next p) ≠ true := by
        simpa [clear, ho] using h
      obtain ⟨k, hk, hall, hblock⟩ := ih (d.next p) hrest
      refine ⟨k + 1, by omega, ⟨ho, hall⟩, ?_⟩
      simpa only [iterate_succ_start] using hblock
    · exact ⟨0, by omega, True.intro, hb⟩

theorem stopped_car_has_blocker (d : CyclicDirection α) (sp : Species)
    (s : Config α) (p : α) (hp : s p = sp.cell) (hm : ¬ CanMove d sp s p) :
    ∃ k, k < d.period ∧ AllOwn d.toDirection sp s k p ∧
      s (BML.iterate d.next k p) = (other sp).cell := by
  apply clear_failure_blocker d.toDirection sp s d.period p
  intro hc
  exact hm ⟨hp, hc⟩

theorem clear_failure_of_blocker (d : Direction α) (sp : Species) (s : Config α)
    (k n : Nat) (p : α) (hk : k < n) (hall : AllOwn d sp s k p)
    (hb : s (BML.iterate d.next k p) = (other sp).cell) :
    clear d sp s n p ≠ true := by
  induction k generalizing n p with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      simp only [BML.iterate] at hb
      simp [clear, hb, other_cell_ne]
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have hb' : s (BML.iterate d.next k (d.next p)) = (other sp).cell := by
        simpa only [iterate_succ_start] using hb
      have hf := ih n (d.next p) (by omega) hall.2 hb'
      simpa [clear, hall.1] using hf

theorem stopped_car_iff_blocker (d : CyclicDirection α) (sp : Species)
    (s : Config α) (p : α) (hp : s p = sp.cell) :
    ¬ CanMove d sp s p ↔ ∃ k, k < d.period ∧ AllOwn d.toDirection sp s k p ∧
      s (BML.iterate d.next k p) = (other sp).cell := by
  constructor
  · exact stopped_car_has_blocker d sp s p hp
  · rintro ⟨k, hk, hall, hb⟩ hm
    exact clear_failure_of_blocker d.toDirection sp s k d.period p hk hall hb hm.2

/-- Incoming active cars overwrite departing cars, as required for whole queues. -/
def halfStep (d : CyclicDirection α) (sp : Species) (s : Config α) : Config α := fun p =>
  if CanMove d sp s (d.prev p) then sp.cell
  else if CanMove d sp s p then .empty
  else s p

def transport (d : CyclicDirection α) (sp : Species) (s : Config α) (p : α) : α :=
  if CanMove d sp s p then d.next p else p

theorem moving_destination_filled (d : CyclicDirection α) (sp : Species)
    (s : Config α) (p : α) (h : CanMove d sp s p) :
    halfStep d sp s (d.next p) = sp.cell := by
  simp [halfStep, d.prev_next, h]

theorem source_emptied_without_arrival (d : CyclicDirection α) (sp : Species)
    (s : Config α) (p : α) (h : CanMove d sp s p)
    (hn : ¬ CanMove d sp s (d.prev p)) : halfStep d sp s p = .empty := by
  simp [halfStep, hn, h]

theorem no_incoming_to_stationary_car (d : CyclicDirection α) (sp : Species)
    (s : Config α) (p : α) (hp : s p = sp.cell) (hm : ¬ CanMove d sp s p) :
    ¬ CanMove d sp s (d.prev p) := by
  intro hi
  rcases (canMove_local d sp s (d.prev p)).mp hi with ⟨_, he | ht⟩
  · rw [d.next_prev, hp] at he
    exact sp.cell_ne_empty he
  · rw [d.next_prev] at ht
    exact hm ht

theorem transport_preserves_car (d : CyclicDirection α) (sp : Species)
    (s : Config α) (p : α) (hp : s p = sp.cell) :
    halfStep d sp s (transport d sp s p) = sp.cell := by
  by_cases hm : CanMove d sp s p
  · simpa [transport, hm] using moving_destination_filled d sp s p hm
  · simp [transport, halfStep, hm, no_incoming_to_stationary_car d sp s p hp hm, hp]

theorem transport_injective_on_cars (d : CyclicDirection α) (sp : Species)
    (s : Config α) (p q : α) (hp : s p = sp.cell) (hq : s q = sp.cell)
    (heq : transport d sp s p = transport d sp s q) : p = q := by
  by_cases hm : CanMove d sp s p
  · by_cases hn : CanMove d sp s q
    · have he : d.next p = d.next q := by simpa [transport, hm, hn] using heq
      have hi := congrArg d.prev he
      simpa only [d.prev_next] using hi
    · have he : d.next p = q := by simpa [transport, hm, hn] using heq
      rcases (canMove_local d sp s p).mp hm with ⟨_, hempty | hmove⟩
      · rw [he, hq] at hempty
        exact False.elim (sp.cell_ne_empty hempty)
      · rw [he] at hmove
        exact False.elim (hn hmove)
  · by_cases hn : CanMove d sp s q
    · have he : d.next q = p := by simpa [transport, hm, hn] using heq.symm
      rcases (canMove_local d sp s q).mp hn with ⟨_, hempty | hmove⟩
      · rw [he, hp] at hempty
        exact False.elim (sp.cell_ne_empty hempty)
      · rw [he] at hmove
        exact False.elim (hm hmove)
    · simpa [transport, hm, hn] using heq

theorem transport_surjective_on_cars (d : CyclicDirection α) (sp : Species)
    (s : Config α) (q : α) (hq : halfStep d sp s q = sp.cell) :
    ∃ p, s p = sp.cell ∧ transport d sp s p = q := by
  by_cases hi : CanMove d sp s (d.prev q)
  · exact ⟨d.prev q, hi.1, by simp [transport, hi, d.next_prev]⟩
  · by_cases hm : CanMove d sp s q
    · have hz : halfStep d sp s q = .empty := by simp [halfStep, hi, hm]
      rw [hq] at hz
      exact False.elim (sp.cell_ne_empty hz)
    · have hc : s q = sp.cell := by simpa [halfStep, hi, hm] using hq
      exact ⟨q, hc, by simp [transport, hm]⟩

theorem transport_bijection (d : CyclicDirection α) (sp : Species) (s : Config α) :
    (∀ p, s p = sp.cell → halfStep d sp s (transport d sp s p) = sp.cell) ∧
    (∀ p q, s p = sp.cell → s q = sp.cell →
      transport d sp s p = transport d sp s q → p = q) ∧
    (∀ q, halfStep d sp s q = sp.cell →
      ∃ p, s p = sp.cell ∧ transport d sp s p = q) :=
  ⟨transport_preserves_car d sp s, transport_injective_on_cars d sp s,
    transport_surjective_on_cars d sp s⟩

theorem other_species_unchanged (d : CyclicDirection α) (sp : Species)
    (s : Config α) (p : α) (c : Cell) (hne : c ≠ .empty) (hsp : c ≠ sp.cell) :
    halfStep d sp s p = c ↔ s p = c := by
  constructor
  · intro h
    unfold halfStep at h
    split at h
    · exact False.elim (hsp h.symm)
    · split at h
      · exact False.elim (hne h.symm)
      · exact h
  · intro hc
    have hm : ¬ CanMove d sp s p := by intro hm; exact hsp (hc.symm.trans hm.1)
    have hi : ¬ CanMove d sp s (d.prev p) := by
      intro hi
      rcases (canMove_local d sp s (d.prev p)).mp hi with ⟨_, he | ht⟩
      · rw [d.next_prev] at he
        exact hne (hc.symm.trans he)
      · rw [d.next_prev] at ht
        exact hm ht
    simp [halfStep, hi, hm, hc]

def NoMovers (d : CyclicDirection α) (sp : Species) (s : Config α) : Prop :=
  ∀ p, ¬ CanMove d sp s p

theorem halfStep_eq_of_no_movers (d : CyclicDirection α) (sp : Species)
    (s : Config α) (h : NoMovers d sp s) : halfStep d sp s = s := by
  funext p
  simp [halfStep, h p, h (d.prev p)]

theorem blocked_mover_allOwn (d : CyclicDirection α) (sp : Species)
    (s : Config α) (hb : BML.Blocked d.toDirection sp s) (n : Nat) (p : α)
    (hm : CanMove d sp s p) : AllOwn d.toDirection sp s n p := by
  induction n generalizing p with
  | zero => exact True.intro
  | succ n ih =>
    refine ⟨hm.1, ih (d.next p) ?_⟩
    rcases (canMove_local d sp s p).mp hm with ⟨hp, he | hn⟩
    · exact False.elim (hb p hp he)
    · exact hn

theorem no_movers_iff_blocked_no_fullRing (d : CyclicDirection α) (sp : Species)
    (s : Config α) :
    NoMovers d sp s ↔ BML.Blocked d.toDirection sp s ∧
      ∀ p, ¬ FullRing d sp s p := by
  constructor
  · intro h
    constructor
    · intro p hp he
      exact h p ((canMove_local d sp s p).mpr ⟨hp, Or.inl he⟩)
    · intro p hfull
      exact h p (fullRing_canMove d sp s p hfull)
  · rintro ⟨hb, hn⟩ p hm
    exact hn p (blocked_mover_allOwn d sp s hb d.period p hm)

def step (east north : CyclicDirection α) (s : Config α) : Config α :=
  halfStep north .north (halfStep east .east s)

/-- Both species have zero movers in the same input configuration. -/
def Stuck (east north : CyclicDirection α) (s : Config α) : Prop :=
  NoMovers east .east s ∧ NoMovers north .north s

/-- The movement count is zero in each of the two successive half-steps. -/
def NoMoves (east north : CyclicDirection α) (s : Config α) : Prop :=
  NoMovers east .east s ∧ NoMovers north .north (halfStep east .east s)

def Jam (east north : CyclicDirection α) (s : Config α) : Prop :=
  BML.Nonempty s ∧ Stuck east north s

theorem noMoves_iff_stuck (east north : CyclicDirection α) (s : Config α) :
    NoMoves east north s ↔ Stuck east north s := by
  constructor
  · rintro ⟨he, hn⟩
    exact ⟨he, by simpa only [halfStep_eq_of_no_movers east .east s he] using hn⟩
  · rintro ⟨he, hn⟩
    exact ⟨he, by simpa only [halfStep_eq_of_no_movers east .east s he] using hn⟩

theorem stuck_iff_classic_no_fullRing (east north : CyclicDirection α) (s : Config α) :
    Stuck east north s ↔ BML.Frozen east.toDirection north.toDirection s ∧
      (∀ p, ¬ FullRing east .east s p) ∧ (∀ p, ¬ FullRing north .north s p) := by
  simp only [Stuck, no_movers_iff_blocked_no_fullRing, BML.Frozen]
  constructor
  · rintro ⟨⟨he, hfe⟩, hn, hfn⟩
    exact ⟨⟨he, hn⟩, hfe, hfn⟩
  · rintro ⟨⟨he, hn⟩, hfe, hfn⟩
    exact ⟨⟨he, hfe⟩, hn, hfn⟩

theorem step_eq_of_stuck (east north : CyclicDirection α) (s : Config α)
    (h : Stuck east north s) : step east north s = s := by
  simp only [step, halfStep_eq_of_no_movers east .east s h.1,
    halfStep_eq_of_no_movers north .north s h.2]

theorem stuck_persists (east north : CyclicDirection α) (s : Config α)
    (h : Stuck east north s) (n : Nat) : BML.iterate (step east north) n s = s :=
  BML.iterate_eq_of_fixed _ _ (step_eq_of_stuck east north s h) n

/-- Full rings move even when their unlabeled occupancy is unchanged. -/
theorem full_species_moves (d : CyclicDirection α) (sp : Species) (p : α) :
    CanMove d sp (fun _ => sp.cell) p := by
  apply fullRing_canMove
  apply (allOwn_iff_iterates _ _ _ _ _).mpr
  intro k _
  rfl

theorem full_species_halfStep_fixed (d : CyclicDirection α) (sp : Species) :
    halfStep d sp (fun _ => sp.cell) = (fun _ => sp.cell) := by
  funext p
  simp [halfStep, full_species_moves]

end BML.Train
