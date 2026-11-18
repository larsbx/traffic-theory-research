import BML.Lanes

/-!
Certified finite cutoffs for an absorbing target.

A reached target is positive evidence. A repeated non-target state is an
all-time avoidance certificate, including intermediate moving cycles. Every
other trajectory remains unresolved. Finite nonnegative integer weights stay
attached to the initial states; no independent law on evolved cells is used.
The actual CLASSIC instantiation uses nonempty jams, not occupancy recurrence
alone. This module supplies no size-uniform estimate on unresolved mass.
-/
namespace BML.Absorption

def Closed (f : α → α) (P : α → Prop) : Prop :=
  ∀ s, P s → P (f s)

def Eventually (f : α → α) (P : α → Prop) (s : α) : Prop :=
  ∃ t, P (iterate f t s)

def Avoids (f : α → α) (P : α → Prop) (s : α) : Prop :=
  ∀ t, ¬ P (iterate f t s)

theorem closed_iterate (f : α → α) (P : α → Prop)
    (hclosed : Closed f P) (s : α) (hs : P s) (t : Nat) :
    P (iterate f t s) := by
  induction t with
  | zero => exact hs
  | succ t ih => exact hclosed _ ih

theorem avoids_iff_not_eventually (f : α → α) (P : α → Prop) (s : α) :
    Avoids f P s ↔ ¬ Eventually f P s := by
  simp only [Avoids, Eventually, not_exists]

/-- A supplied safe predicate must be closed under the actual transition and
disjoint from the target. Mere absence of the target at one cutoff is not enough. -/
structure SafeInvariant (f : α → α) (P U : α → Prop) : Prop where
  closed : Closed f U
  disjoint : ∀ s, U s → ¬ P s

theorem safe_at_cutoff_avoids (f : α → α) (P U : α → Prop)
    (hp : Closed f P) (hu : SafeInvariant f P U) (s : α) (T : Nat)
    (hs : U (iterate f T s)) : Avoids f P s := by
  intro t ht
  have hp' := closed_iterate f P hp _ ht T
  have hu' := closed_iterate f U hu.closed _ hs t
  rw [← iterate_add] at hp' hu'
  rw [Nat.add_comm t T] at hp'
  exact hu.disjoint _ hu' hp'

/-- The conditional invariant-safe-set reduction, before summing initial weights. -/
theorem eventual_cutoff_cover (f : α → α) (P U : α → Prop)
    (hp : Closed f P) (hu : SafeInvariant f P U) (s : α) (T : Nat)
    (he : Eventually f P s) :
    P (iterate f T s) ∨ (¬ P (iterate f T s) ∧ ¬ U (iterate f T s)) := by
  classical
  by_cases h : P (iterate f T s)
  · exact Or.inl h
  · refine Or.inr ⟨h, ?_⟩
    intro hsafe
    exact (avoids_iff_not_eventually f P s).mp
      (safe_at_cutoff_avoids f P U hp hu s T hsafe) he

theorem iterate_mul_of_return (f : α → α) (s : α) (k : Nat)
    (hk : iterate f k s = s) (n : Nat) : iterate f (k * n) s = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ, iterate_add, ih, hk]

/-- Recurrence at positive period certifies all-time target avoidance when the
recurrent state is outside an absorbing target. It need not have full movement. -/
theorem return_avoids (f : α → α) (P : α → Prop) (hp : Closed f P)
    (s : α) (k : Nat) (hk : 0 < k) (hreturn : iterate f k s = s)
    (hs : ¬ P s) : Avoids f P s := by
  intro t ht
  have hle : t ≤ k * t := by
    have hmul := Nat.mul_le_mul_right t (Nat.succ_le_of_lt hk)
    simpa using hmul
  have hfuture := closed_iterate f P hp _ ht (k * t - t)
  rw [← iterate_add, Nat.add_sub_of_le hle,
    iterate_mul_of_return f s k hreturn t] at hfuture
  exact hs hfuture

/-- A recurrent endpoint supplies a safe certificate for the entire initial
trajectory, including times before the witnessed recurrence. -/
theorem repeated_endpoint_avoids (f : α → α) (P : α → Prop)
    (hp : Closed f P) (s : α) (a T : Nat) (ha : a < T)
    (hreturn : iterate f a s = iterate f T s)
    (hs : ¬ P (iterate f T s)) : Avoids f P s := by
  have hk : 0 < T - a := by omega
  have hret : iterate f (T - a) (iterate f a s) = iterate f a s := by
    rw [← iterate_add, Nat.add_sub_of_le (Nat.le_of_lt ha)]
    exact hreturn.symm
  have hsafe := return_avoids f P hp (iterate f a s) (T-a) hk hret
    (by simpa [hreturn] using hs)
  intro t ht
  have hfuture := closed_iterate f P hp _ ht a
  rw [← iterate_add, Nat.add_comm t a, iterate_add] at hfuture
  exact hsafe t hfuture

inductive Verdict where
  | hit | safe | unresolved
  deriving DecidableEq, BEq, Repr

/-- Evaluate the terminal state and search the earlier prefix for an exact
recurrence. A zero cutoff can certify a hit, but cannot certify recurrence. -/
def probe (f : α → α) (isTarget : α → Bool) (same : α → α → Bool)
    (s : α) (cutoff : Nat) : Verdict :=
  let last := iterate f cutoff s
  if isTarget last then .hit
  else if (List.range cutoff).any (fun a => same (iterate f a s) last) then .safe
  else .unresolved

theorem probe_hit_iff (f : α → α) (isTarget : α → Bool)
    (same : α → α → Bool) (s : α) (T : Nat) :
    probe f isTarget same s T = .hit ↔ isTarget (iterate f T s) = true := by
  dsimp only [probe]
  split <;> simp_all
  split <;> simp_all

theorem probe_safe_iff (f : α → α) (isTarget : α → Bool)
    (same : α → α → Bool) (s : α) (T : Nat) :
    probe f isTarget same s T = .safe ↔
      isTarget (iterate f T s) = false ∧
      ∃ a, a < T ∧ same (iterate f a s) (iterate f T s) = true := by
  dsimp only [probe]
  split <;> simp_all [List.any_eq_true, List.mem_range]

theorem probe_hit_sound (f : α → α) (P : α → Prop)
    (isTarget : α → Bool) (same : α → α → Bool)
    (htarget : ∀ s, isTarget s = true ↔ P s) (s : α) (T : Nat)
    (h : probe f isTarget same s T = .hit) : Eventually f P s :=
  ⟨T, (htarget _).mp ((probe_hit_iff f isTarget same s T).mp h)⟩

theorem probe_safe_sound (f : α → α) (P : α → Prop)
    (isTarget : α → Bool) (same : α → α → Bool)
    (hp : Closed f P) (htarget : ∀ s, isTarget s = true ↔ P s)
    (hequal : ∀ x y, same x y = true ↔ x = y) (s : α) (T : Nat)
    (h : probe f isTarget same s T = .safe) : Avoids f P s := by
  obtain ⟨hn, a, ha, he⟩ := (probe_safe_iff f isTarget same s T).mp h
  apply repeated_endpoint_avoids f P hp s a T ha ((hequal _ _).mp he)
  intro hlast
  have ht := (htarget _).mpr hlast
  rw [hn] at ht
  cases ht

/-- Every genuine eventual hit is either already detected or explicitly
unresolved; a recurrent safe verdict cannot conceal an eventual hit. -/
theorem probe_eventual_cover (f : α → α) (P : α → Prop)
    (isTarget : α → Bool) (same : α → α → Bool)
    (hp : Closed f P) (htarget : ∀ s, isTarget s = true ↔ P s)
    (hequal : ∀ x y, same x y = true ↔ x = y) (s : α) (T : Nat)
    (h : Eventually f P s) :
    probe f isTarget same s T = .hit ∨ probe f isTarget same s T = .unresolved := by
  cases hv : probe f isTarget same s T with
  | hit => exact Or.inl rfl
  | unresolved => exact Or.inr rfl
  | safe =>
    exact False.elim ((avoids_iff_not_eventually f P s).mp
      (probe_safe_sound f P isTarget same hp htarget hequal s T hv) h)

theorem probe_hit_persists (f : α → α) (P : α → Prop)
    (isTarget : α → Bool) (same : α → α → Bool)
    (hp : Closed f P) (htarget : ∀ s, isTarget s = true ↔ P s)
    (s : α) (T d : Nat) (h : probe f isTarget same s T = .hit) :
    probe f isTarget same s (T+d) = .hit := by
  apply (probe_hit_iff f isTarget same s (T+d)).mpr
  apply (htarget _).mpr
  rw [iterate_add]
  exact closed_iterate f P hp _
    ((htarget _).mp ((probe_hit_iff f isTarget same s T).mp h)) d

theorem probe_safe_persists (f : α → α) (P : α → Prop)
    (isTarget : α → Bool) (same : α → α → Bool)
    (hp : Closed f P) (htarget : ∀ s, isTarget s = true ↔ P s)
    (hequal : ∀ x y, same x y = true ↔ x = y)
    (s : α) (T d : Nat) (h : probe f isTarget same s T = .safe) :
    probe f isTarget same s (T+d) = .safe := by
  have hsafe := probe_safe_sound f P isTarget same hp htarget hequal s T h
  obtain ⟨_, a, ha, he⟩ := (probe_safe_iff f isTarget same s T).mp h
  apply (probe_safe_iff f isTarget same s (T+d)).mpr
  constructor
  · cases ht : isTarget (iterate f (T+d) s) with
    | false => rfl
    | true => exact False.elim (hsafe (T+d) ((htarget _).mp ht))
  · refine ⟨a+d, Nat.add_lt_add_right ha d, ?_⟩
    apply (hequal _ _).mpr
    rw [iterate_add, iterate_add, (hequal _ _).mp he]

/-- Increasing the cutoff can resolve an unknown trajectory, but cannot turn
a proved hit or a proved safe cycle back into an unresolved verdict. -/
theorem probe_unresolved_antitone (f : α → α) (P : α → Prop)
    (isTarget : α → Bool) (same : α → α → Bool)
    (hp : Closed f P) (htarget : ∀ s, isTarget s = true ↔ P s)
    (hequal : ∀ x y, same x y = true ↔ x = y)
    (s : α) (T d : Nat)
    (h : probe f isTarget same s (T+d) = .unresolved) :
    probe f isTarget same s T = .unresolved := by
  cases hv : probe f isTarget same s T with
  | unresolved => rfl
  | hit =>
    have hh := probe_hit_persists f P isTarget same hp htarget s T d hv
    rw [hh] at h
    cases h
  | safe =>
    have hh := probe_safe_persists f P isTarget same hp htarget hequal s T d hv
    rw [hh] at h
    cases h

/-- Initial-state mass. Repetitions in the support list count with multiplicity;
no completeness or no-duplicate assumption is hidden in the inequalities. -/
def mass (states : List α) (weight : α → Nat) (event : α → Bool) : Nat :=
  (states.map fun s => if event s then weight s else 0).sum

theorem mass_mono (states : List α) (weight : α → Nat) (a b : α → Bool)
    (h : ∀ s, s ∈ states → a s = true → b s = true) :
    mass states weight a ≤ mass states weight b := by
  induction states with
  | nil => simp [mass]
  | cons s states ih =>
    have hs := h s (by simp)
    have hi := ih (fun x hx => h x (by simp [hx]))
    have hl : (if a s then weight s else 0) ≤ (if b s then weight s else 0) := by
      cases ha : a s <;> cases hb : b s <;> simp_all
    simpa only [mass, List.map_cons, List.sum_cons] using Nat.add_le_add hl hi

theorem mass_le_add_of_cover (states : List α) (weight : α → Nat)
    (event a b : α → Bool)
    (h : ∀ s, s ∈ states → event s = true → a s = true ∨ b s = true) :
    mass states weight event ≤ mass states weight a + mass states weight b := by
  induction states with
  | nil => simp [mass]
  | cons s states ih =>
    have hs := h s (by simp)
    have hi := ih (fun x hx => h x (by simp [hx]))
    have hl : (if event s then weight s else 0) ≤
        (if a s then weight s else 0) + (if b s then weight s else 0) := by
      cases he : event s <;> cases ha : a s <;> cases hb : b s <;> simp_all
    simp only [mass, List.map_cons, List.sum_cons] at *
    omega

noncomputable def eventualFlag (f : α → α) (P : α → Prop) (s : α) : Bool := by
  classical
  exact decide (Eventually f P s)

theorem eventualFlag_iff (f : α → α) (P : α → Prop) (s : α) :
    eventualFlag f P s = true ↔ Eventually f P s := by
  classical
  simp [eventualFlag]

/-- A rigorous interval for arbitrary finite initial integer weights. Dividing
all terms by a common positive denominator gives the corresponding rational
probability interval. The middle eventual mass is semantic, not an executable
oracle used by the bounded probe. -/
theorem probe_mass_bounds (f : α → α) (P : α → Prop)
    (isTarget : α → Bool) (same : α → α → Bool)
    (hp : Closed f P) (htarget : ∀ s, isTarget s = true ↔ P s)
    (hequal : ∀ x y, same x y = true ↔ x = y)
    (states : List α) (weight : α → Nat) (T : Nat) :
    mass states weight (fun s => decide (probe f isTarget same s T = .hit)) ≤
      mass states weight (eventualFlag f P) ∧
    mass states weight (eventualFlag f P) ≤
      mass states weight (fun s => decide (probe f isTarget same s T = .hit)) +
      mass states weight (fun s => decide (probe f isTarget same s T = .unresolved)) := by
  constructor
  · apply mass_mono
    intro s _ hs
    apply (eventualFlag_iff f P s).mpr
    exact probe_hit_sound f P isTarget same htarget s T (of_decide_eq_true hs)
  · apply mass_le_add_of_cover
    intro s _ hs
    have h := probe_eventual_cover f P isTarget same hp htarget hequal s T
      ((eventualFlag_iff f P s).mp hs)
    rcases h with h | h
    · exact Or.inl (decide_eq_true h)
    · exact Or.inr (decide_eq_true h)

/-- Zero unresolved initial weight closes the finite probability interval
exactly. It does not require every zero-weight state to have been classified. -/
theorem probe_zero_unresolved_exact (f : α → α) (P : α → Prop)
    (isTarget : α → Bool) (same : α → α → Bool)
    (hp : Closed f P) (htarget : ∀ s, isTarget s = true ↔ P s)
    (hequal : ∀ x y, same x y = true ↔ x = y)
    (states : List α) (weight : α → Nat) (T : Nat)
    (hzero : mass states weight
      (fun s => decide (probe f isTarget same s T = .unresolved)) = 0) :
    mass states weight (eventualFlag f P) =
      mass states weight (fun s => decide (probe f isTarget same s T = .hit)) := by
  have h := probe_mass_bounds f P isTarget same hp htarget hequal states weight T
  rw [hzero, Nat.add_zero] at h
  exact Nat.le_antisymm h.2 h.1

theorem probe_unresolved_mass_antitone (f : α → α) (P : α → Prop)
    (isTarget : α → Bool) (same : α → α → Bool)
    (hp : Closed f P) (htarget : ∀ s, isTarget s = true ↔ P s)
    (hequal : ∀ x y, same x y = true ↔ x = y)
    (states : List α) (weight : α → Nat) (T d : Nat) :
    mass states weight (fun s => decide (probe f isTarget same s (T+d) = .unresolved)) ≤
      mass states weight (fun s => decide (probe f isTarget same s T = .unresolved)) := by
  apply mass_mono
  intro s _ hs
  exact decide_eq_true (probe_unresolved_antitone f P isTarget same hp htarget hequal
    s T d (of_decide_eq_true hs))

/-- Every initial weight is assigned to exactly one of the three verdicts. -/
theorem probe_mass_partition (f : α → α) (isTarget : α → Bool)
    (same : α → α → Bool) (states : List α) (weight : α → Nat) (T : Nat) :
    mass states weight (fun _ => true) =
      mass states weight (fun s => decide (probe f isTarget same s T = .hit)) +
      mass states weight (fun s => decide (probe f isTarget same s T = .safe)) +
      mass states weight (fun s => decide (probe f isTarget same s T = .unresolved)) := by
  induction states with
  | nil => simp [mass]
  | cons s states ih =>
    cases hv : probe f isTarget same s T <;> simp [mass, hv] at * <;> omega

/-- The certified lower bound grows and the upper bound shrinks with the
cutoff. No limit exchange is used to prove this finite refinement property. -/
theorem probe_mass_intervals_nested (f : α → α) (P : α → Prop)
    (isTarget : α → Bool) (same : α → α → Bool)
    (hp : Closed f P) (htarget : ∀ s, isTarget s = true ↔ P s)
    (hequal : ∀ x y, same x y = true ↔ x = y)
    (states : List α) (weight : α → Nat) (T d : Nat) :
    mass states weight (fun s => decide (probe f isTarget same s T = .hit)) ≤
      mass states weight (fun s => decide (probe f isTarget same s (T+d) = .hit)) ∧
    mass states weight (fun s => decide (probe f isTarget same s (T+d) = .hit)) +
        mass states weight (fun s => decide (probe f isTarget same s (T+d) = .unresolved)) ≤
      mass states weight (fun s => decide (probe f isTarget same s T = .hit)) +
        mass states weight (fun s => decide (probe f isTarget same s T = .unresolved)) := by
  constructor
  · apply mass_mono
    intro s _ hs
    exact decide_eq_true (probe_hit_persists f P isTarget same hp htarget
      s T d (of_decide_eq_true hs))
  · have hsafe : mass states weight
        (fun s => decide (probe f isTarget same s T = .safe)) ≤
        mass states weight (fun s => decide (probe f isTarget same s (T+d) = .safe)) := by
      apply mass_mono
      intro s _ hs
      exact decide_eq_true (probe_safe_persists f P isTarget same hp htarget hequal
        s T d (of_decide_eq_true hs))
    have hT := probe_mass_partition f isTarget same states weight T
    have hTd := probe_mass_partition f isTarget same states weight (T+d)
    omega

end BML.Absorption

namespace BML

/-- An executable equality check for complete finite torus configurations. -/
def configEqual (w h : Nat) (s u : Config (Position w h)) : Bool :=
  (positions w h).all fun p => decide (s p = u p)

theorem configEqual_iff (w h : Nat) (s u : Config (Position w h)) :
    configEqual w h s u = true ↔ s = u := by
  constructor
  · intro hc
    funext p
    have hall := List.all_eq_true.mp hc
    exact of_decide_eq_true (hall p (Train.Counting.mem_positions w h p))
  · rintro rfl
    simp [configEqual]

/-- Actual nonempty CLASSIC jam detection. Empty fixed configurations are safe
once recurrent, and must not be labeled as a hit. -/
def jamCheck (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) : Bool :=
  (positions w h).any (fun p => decide (s p ≠ .empty)) &&
    configEqual w h (torusStep w h hw hh s) s

theorem jamCheck_iff (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) :
    jamCheck w h hw hh s = true ↔
      Jam (eastDirection w h hw) (northDirection w h hh) s := by
  rw [jam_iff_nonempty_fixed]
  simp only [jamCheck, Bool.and_eq_true, List.any_eq_true, configEqual_iff,
    decide_eq_true_eq, Nonempty, torusStep]
  constructor
  · rintro ⟨⟨p, _, hp⟩, hf⟩
    exact ⟨⟨p, hp⟩, hf⟩
  · rintro ⟨⟨p, hp⟩, hf⟩
    exact ⟨⟨p, Train.Counting.mem_positions w h p, hp⟩, hf⟩

theorem jam_closed (east north : Direction α) :
    Absorption.Closed (step east north) (Jam east north) := by
  intro s hs
  have hf := (step_eq_iff_frozen east north s).mpr hs.2
  simpa only [hf] using hs

/-- Data-valued states prevent the compiler from turning a configuration
cache into a function that rematerializes its board at every lookup. -/
abbrev MaterializedBoard (w h : Nat) := Vector (Vector Cell w) h

def materialize (w h : Nat) (s : Config (Position w h)) : MaterializedBoard w h :=
  Vector.ofFn fun y => Vector.ofFn fun x => s (x,y)

def boardConfig {w h : Nat} (board : MaterializedBoard w h) : Config (Position w h) :=
  fun p => board[p.2.val][p.1.val]

theorem boardConfig_materialize (w h : Nat) (s : Config (Position w h)) :
    boardConfig (materialize w h s) = s := by
  funext p
  simp [boardConfig, materialize]

/-- The materialized step calls the actual CLASSIC kernel, then stores its
complete output as data before the next round starts. -/
def boardStep (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (board : MaterializedBoard w h) : MaterializedBoard w h :=
  materialize w h (torusStep w h hw hh (boardConfig board))

theorem boardConfig_step (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (board : MaterializedBoard w h) :
    boardConfig (boardStep w h hw hh board) = torusStep w h hw hh (boardConfig board) :=
  boardConfig_materialize w h _

/-- Refinement of every materialized iterate to the original configuration
kernel. This is universal in the initial board and time. -/
theorem boardConfig_iterate (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (board : MaterializedBoard w h) (t : Nat) :
    boardConfig (iterate (boardStep w h hw hh) t board) =
      iterate (torusStep w h hw hh) t (boardConfig board) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [iterate, boardConfig_step, ih]

def absorptionProbe (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (cutoff : Nat) : Absorption.Verdict :=
  Absorption.probe (boardStep w h hw hh)
    (fun b => jamCheck w h hw hh (boardConfig b))
    (fun a b => configEqual w h (boardConfig a) (boardConfig b))
    (materialize w h s) cutoff

/-- The fast data-state probe returns exactly the verdict of the original
configuration-state contract, not a surrogate traffic dynamics. -/
theorem absorptionProbe_eq (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (T : Nat) :
    absorptionProbe w h hw hh s T =
      Absorption.probe (torusStep w h hw hh) (jamCheck w h hw hh)
        (configEqual w h) s T := by
  simp only [absorptionProbe, Absorption.probe, boardConfig_iterate, boardConfig_materialize]

theorem absorptionProbe_hit_sound (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (T : Nat)
    (hs : absorptionProbe w h hw hh s T = .hit) :
    ∃ t, Jam (eastDirection w h hw) (northDirection w h hh)
      (iterate (torusStep w h hw hh) t s) := by
  apply Absorption.probe_hit_sound _ _ _ _ (jamCheck_iff w h hw hh) s T
  simpa only [absorptionProbe_eq, torusStep] using hs

theorem absorptionProbe_safe_sound (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (T : Nat)
    (hs : absorptionProbe w h hw hh s T = .safe) :
    ∀ t, ¬ Jam (eastDirection w h hw) (northDirection w h hh)
      (iterate (torusStep w h hw hh) t s) := by
  apply Absorption.probe_safe_sound _ _ _ _ (jam_closed _ _)
    (jamCheck_iff w h hw hh) (configEqual_iff w h) s T
  simpa only [absorptionProbe_eq, torusStep] using hs

theorem absorptionProbe_mass_bounds (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (states : List (Config (Position w h)))
    (weight : Config (Position w h) → Nat) (T : Nat) :
    Absorption.mass states weight (fun s => decide (absorptionProbe w h hw hh s T = .hit)) ≤
      Absorption.mass states weight
        (Absorption.eventualFlag (torusStep w h hw hh)
          (Jam (eastDirection w h hw) (northDirection w h hh))) ∧
    Absorption.mass states weight
        (Absorption.eventualFlag (torusStep w h hw hh)
          (Jam (eastDirection w h hw) (northDirection w h hh))) ≤
      Absorption.mass states weight (fun s => decide (absorptionProbe w h hw hh s T = .hit)) +
      Absorption.mass states weight
        (fun s => decide (absorptionProbe w h hw hh s T = .unresolved)) := by
  simpa only [absorptionProbe_eq, torusStep] using
    Absorption.probe_mass_bounds _ _ _ _ (jam_closed _ _)
      (jamCheck_iff w h hw hh) (configEqual_iff w h) states weight T

end BML
