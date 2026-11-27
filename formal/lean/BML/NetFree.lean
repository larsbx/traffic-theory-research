import BML.Net

/-!
# Free flow on traffic nets

A state is *free* if no car is ever delayed by another car: in every tick,
every car whose gate is open moves. Cars may still wait for a closed gate.

Proved here for every net:

* `free_run_iff`: in a free state every car follows its solo timetable, the
  path it would take alone on the net;
* `Free.sub`: freeness is hereditary, removing cars from a free state leaves
  it free;
* `free_iff_pairs`: freeness is a pairwise property, a state is free iff each
  of its two-car sub-states is free.

So the free states of a net are exactly the cliques of a compatibility
relation between cars, which is what every capacity search in this repository
relies on.
-/
namespace BML.Net

variable {Cell Class : Type} [DecidableEq Class]

/-- In tick `t`, every car whose gate is open moves. -/
def Undelayed (net : Net Cell Class) (t : Nat) (u : Config Cell Class) : Prop :=
  ∀ p k c, u p = some k → net.next k p = some c → net.gate t k c = true →
    winner net t u c = some k

/-- No car is ever delayed by another car. -/
def Free (net : Net Cell Class) (s : Config Cell Class) : Prop :=
  ∀ t, Undelayed net t (run net s t)

/-- What a lone class-`k` car in cell `p` does in tick `t`: `none` is an exit. -/
def advance (net : Net Cell Class) (t : Nat) (k : Class) (p : Cell) : Option Cell :=
  match net.next k p with
  | none => none
  | some c => if net.gate t k c then some c else some p

/-- The solo timetable: where a lone class-`k` car started in `p` is at tick `t`. -/
def solo (net : Net Cell Class) (k : Class) (p : Cell) : Nat → Option Cell
  | 0 => some p
  | t + 1 => (solo net k p t).bind (advance net t k)

/-- `s'` is `s` with some cars removed. -/
def Sub (s' s : Config Cell Class) : Prop := ∀ p k, s' p = some k → s p = some k

variable {net : Net Cell Class} {u : Config Cell Class} {t : Nat}

theorem wants_iff {k : Class} {c : Cell} :
    wants net u k c = true ↔ ∃ p, net.prev k c = some p ∧ u p = some k := by
  unfold wants
  cases hp : net.prev k c with
  | none => simp
  | some p => simp

theorem winner_spec {k : Class} {c : Cell} (h : winner net t u c = some k) :
    u c = none ∧ net.gate t k c = true ∧ ∃ p, net.next k p = some c ∧ u p = some k := by
  have hv := winner_vacant h
  unfold winner at h
  simp only [hv, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h
  have hP := List.find?_some h
  simp only [Bool.and_eq_true] at hP
  obtain ⟨p, hp, hu⟩ := wants_iff.mp hP.2
  exact ⟨hv, hP.1, p, (net.prev_iff k p c).mp hp, hu⟩

/-- **One undelayed tick is the parallel solo advance.** -/
theorem step_undelayed (hu : Undelayed net t u) (c : Cell) (k : Class) :
    step net t u c = some k ↔ ∃ p, u p = some k ∧ advance net t k p = some c := by
  constructor
  · intro h
    unfold step at h
    cases hw : winner net t u c with
    | some j =>
      rw [hw] at h
      have hjk : j = k := by simpa using h
      subst hjk
      obtain ⟨_, hg, p, hn, hp⟩ := winner_spec hw
      exact ⟨p, hp, by simp [advance, hn, hg]⟩
    | none =>
      rw [hw] at h
      by_cases hl : leaves net t u c = true
      · simp [hl] at h
      · simp only [hl, Bool.false_eq_true, ↓reduceIte] at h
        refine ⟨c, h, ?_⟩
        unfold leaves at hl
        rw [h] at hl
        cases hn : net.next k c with
        | none => simp [hn] at hl
        | some d =>
          simp only [hn, decide_eq_true_eq] at hl
          have hg : net.gate t k d = false := by
            cases hg : net.gate t k d with
            | false => rfl
            | true => exact absurd (hu c k d h hn hg) hl
          simp [advance, hn, hg]
  · rintro ⟨p, hp, ha⟩
    unfold advance at ha
    cases hn : net.next k p with
    | none => simp [hn] at ha
    | some d =>
      rw [hn] at ha
      cases hg : net.gate t k d with
      | true =>
        have hcd : d = c := by simpa [hg] using ha
        subst hcd
        simp [step, hu p k d hp hn hg]
      | false =>
        have hcp : p = c := by simpa [hg] using ha
        subst hcp
        have hw : winner net t u p = none := by simp [winner, hp]
        have hnot : winner net t u d ≠ some k := by
          intro hwd
          have := (winner_spec hwd).2.1
          rw [hg] at this
          cases this
        simp [step, hw, leaves, hp, hn, hnot]

/-- **Solo timetables.** In a free state, the car in a cell at tick `t` is the
one whose solo timetable puts it there. -/
theorem free_run_iff {s : Config Cell Class} (hf : Free net s) (t : Nat) (c : Cell) (k : Class) :
    run net s t c = some k ↔ ∃ p, s p = some k ∧ solo net k p t = some c := by
  induction t generalizing c with
  | zero =>
    constructor
    · intro h
      exact ⟨c, h, rfl⟩
    · rintro ⟨p, hp, hs⟩
      have : p = c := by simpa [solo] using hs
      exact this ▸ hp
  | succ t ih =>
    rw [run, step_undelayed (hf t)]
    constructor
    · rintro ⟨q, hq, ha⟩
      obtain ⟨p, hp, hs⟩ := (ih q).mp hq
      exact ⟨p, hp, by simp [solo, hs, ha]⟩
    · rintro ⟨p, hp, hs⟩
      cases hq : solo net k p t with
      | none => simp [solo, hq] at hs
      | some q =>
        refine ⟨q, (ih q).mpr ⟨p, hp, hq⟩, ?_⟩
        simpa [solo, hq] using hs

/-! ## Heredity -/

/-- The timetable description of the run at tick `t`. -/
def Timetabled (net : Net Cell Class) (s : Config Cell Class) (t : Nat) : Prop :=
  ∀ c k, run net s t c = some k ↔ ∃ p, s p = some k ∧ solo net k p t = some c

theorem timetabled_zero (s : Config Cell Class) : Timetabled net s 0 := by
  intro c k
  constructor
  · intro h
    exact ⟨c, h, rfl⟩
  · rintro ⟨p, hp, hs⟩
    have : p = c := by simpa [solo] using hs
    exact this ▸ hp

theorem timetabled_succ {s : Config Cell Class} (ht : Timetabled net s t)
    (hu : Undelayed net t (run net s t)) : Timetabled net s (t + 1) := by
  intro c k
  rw [run, step_undelayed hu]
  constructor
  · rintro ⟨q, hq, ha⟩
    obtain ⟨p, hp, hs⟩ := (ht q k).mp hq
    exact ⟨p, hp, by simp [solo, hs, ha]⟩
  · rintro ⟨p, hp, hs⟩
    cases hq : solo net k p t with
    | none => simp [solo, hq] at hs
    | some q =>
      refine ⟨q, (ht q k).mpr ⟨p, hp, hq⟩, ?_⟩
      simpa [solo, hq] using hs

/-- If every tick so far was undelayed, the run is on its timetables. -/
theorem timetabled_of_undelayed {s : Config Cell Class} (T : Nat)
    (h : ∀ t, t < T → Undelayed net t (run net s t)) : Timetabled net s T := by
  induction T with
  | zero => exact timetabled_zero s
  | succ T ih => exact timetabled_succ (ih fun t ht => h t (by omega)) (h T (by omega))

omit [DecidableEq Class] in
private theorem find?_mono {l : List Class} {P P' : Class → Bool} {k : Class}
    (h : l.find? P = some k) (hsub : ∀ j, P' j = true → P j = true) (hk : P' k = true) :
    l.find? P' = some k := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases ha : P a = true
    · have hak : a = k := by simpa [List.find?, ha] using h
      subst hak
      simp [List.find?, hk]
    · have ha' : P' a = false := by
        cases hpa : P' a with
        | false => rfl
        | true => exact absurd (hsub a hpa) ha
      have h' : l.find? P = some k := by simpa [List.find?, ha] using h
      simpa [List.find?, ha'] using ih h'

/-- A merge winner still wins after other cars are removed. -/
theorem winner_sub {u' : Config Cell Class} {k : Class} {c : Cell}
    (hsub : Sub u' u) (hw : winner net t u c = some k)
    (hk : ∃ p, net.next k p = some c ∧ u' p = some k) : winner net t u' c = some k := by
  obtain ⟨hv, hg, _⟩ := winner_spec hw
  have hv' : u' c = none := by
    cases hc : u' c with
    | none => rfl
    | some j => rw [hsub c j hc] at hv; cases hv
  have hw' := hw
  unfold winner at hw' ⊢
  simp only [hv, hv', Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hw' ⊢
  refine find?_mono hw' (fun j hj => ?_) ?_
  · simp only [Bool.and_eq_true] at hj ⊢
    obtain ⟨p, hp, hup⟩ := wants_iff.mp hj.2
    exact ⟨hj.1, wants_iff.mpr ⟨p, hp, hsub p j hup⟩⟩
  · obtain ⟨p, hn, hup⟩ := hk
    simp only [Bool.and_eq_true]
    exact ⟨hg, wants_iff.mpr ⟨p, (net.prev_iff k p c).mpr hn, hup⟩⟩

/-- **Heredity.** Removing cars from a free state leaves it free. -/
theorem Free.sub {s s' : Config Cell Class} (hf : Free net s) (hsub : Sub s' s) : Free net s' := by
  have key : ∀ T, ∀ t, t < T → Undelayed net t (run net s' t) := by
    intro T
    induction T with
    | zero => intro t ht; omega
    | succ T ih =>
      intro t ht
      by_cases hlt : t < T
      · exact ih t hlt
      · have hT : t = T := by omega
        subst hT
        have htt := timetabled_of_undelayed t ih
        have hrun : Sub (run net s' t) (run net s t) := by
          intro q k hq
          obtain ⟨p, hp, hs⟩ := (htt q k).mp hq
          exact (free_run_iff hf t q k).mpr ⟨p, hsub p k hp, hs⟩
        intro q k c hq hn hg
        exact winner_sub hrun (hf t q k c (hrun q k hq) hn hg) ⟨q, hn, hq⟩
  exact fun t => key (t + 1) t (by omega)

/-- The run of a sub-state of a free state is the corresponding sub-state of its run. -/
theorem Free.run_sub {s s' : Config Cell Class} (hf : Free net s) (hsub : Sub s' s) (t : Nat) :
    Sub (run net s' t) (run net s t) := by
  intro q k hq
  obtain ⟨p, hp, hs⟩ := (free_run_iff (hf.sub hsub) t q k).mp hq
  exact (free_run_iff hf t q k).mpr ⟨p, hsub p k hp, hs⟩

/-! ## Freeness is pairwise -/

section Pairs

variable [DecidableEq Cell]

/-- The state `s` with every car removed except those in cells `p` and `p'`. -/
def only (s : Config Cell Class) (p p' : Cell) : Config Cell Class :=
  fun c => if c = p ∨ c = p' then s c else none

omit [DecidableEq Class] in
theorem only_sub (s : Config Cell Class) (p p' : Cell) : Sub (only s p p') s := by
  intro c k h
  unfold only at h
  split at h
  · exact h
  · cases h

/-- **Freeness is a pairwise property.** A state is free iff each of its
two-car sub-states is free. -/
theorem free_iff_pairs (s : Config Cell Class) :
    Free net s ↔ ∀ p p', Free net (only s p p') := by
  constructor
  · exact fun hf p p' => hf.sub (only_sub s p p')
  · intro hpairs
    have key : ∀ T, ∀ t, t < T → Undelayed net t (run net s t) := by
      intro T
      induction T with
      | zero => intro t ht; omega
      | succ T ih =>
        intro t ht
        by_cases hlt : t < T
        · exact ih t hlt
        · have hT : t = T := by omega
          subst hT
          have htt := timetabled_of_undelayed t ih
          intro q k c hq hn hg
          obtain ⟨p, hp, hs⟩ := (htt q k).mp hq
          -- the pair state made of this car and one other, on its own run
          have pair : ∀ p' : Cell, run net (only s p p') t q = some k ∧
              Sub (run net (only s p p') t) (run net s t) ∧
              winner net t (run net (only s p p') t) c = some k := by
            intro p'
            have hfree := hpairs p p'
            have hq2 : run net (only s p p') t q = some k :=
              (free_run_iff hfree t q k).mpr ⟨p, by simp [only, hp], hs⟩
            refine ⟨hq2, ?_, hfree t q k c hq2 hn hg⟩
            intro d j hd
            obtain ⟨o, ho, hso⟩ := (free_run_iff hfree t d j).mp hd
            exact (htt d j).mpr ⟨o, only_sub s p p' o j ho, hso⟩
          cases hc : run net s t c with
          | some j =>
            -- the next cell is occupied: the pair with its occupant is not free
            obtain ⟨p', hp', hs'⟩ := (htt c j).mp hc
            obtain ⟨_, _, hw⟩ := pair p'
            have hocc : run net (only s p p') t c = some j :=
              (free_run_iff (hpairs p p') t c j).mpr ⟨p', by simp [only, hp'], hs'⟩
            rw [winner_vacant hw] at hocc
            cases hocc
          | none =>
            cases hwin : winner net t (run net s t) c with
            | some j =>
              -- another class wins the merge: the pair with that car is not free
              obtain ⟨_, _, q', hn', hq'⟩ := winner_spec hwin
              obtain ⟨p', hp', hs'⟩ := (htt q' j).mp hq'
              obtain ⟨_, hsub2, hw⟩ := pair p'
              have hq2' : run net (only s p p') t q' = some j :=
                (free_run_iff (hpairs p p') t q' j).mpr ⟨p', by simp [only, hp'], hs'⟩
              have := winner_sub hsub2 hwin ⟨q', hn', hq2'⟩
              rw [hw] at this
              exact this.symm
            | none =>
              -- nobody may enter: then this class is not admitted at all
              obtain ⟨_, _, hw⟩ := pair p
              have hw' := hw
              unfold winner at hw' hwin
              have hv2 := winner_vacant hw
              simp only [hc, hv2, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hw' hwin
              have hmem := List.mem_of_find?_eq_some hw'
              have hnone := List.find?_eq_none.mp hwin k hmem
              have hwant : wants net (run net s t) k c = true :=
                wants_iff.mpr ⟨q, (net.prev_iff k q c).mpr hn, hq⟩
              simp [hg, hwant] at hnone
    exact fun t => key (t + 1) t (by omega)

end Pairs

end BML.Net
