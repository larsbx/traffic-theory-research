import BML.Ring

/-!
# Permanent blocking on lane graphs (P1)

The cell and car carriers can be `Fin cells` and `Fin cars`. Only the witness
cycle needs to be finite for the proof. Road geometry and routing supply the
committed targets. They play no role in the permanence argument.
-/
namespace BML.LaneDeadlock

inductive Rule where
  | classic | train
  deriving DecidableEq

inductive BlockKind where
  | direct | box
  deriving DecidableEq

/-- A missing next cell represents EXIT. The tail lists the recorded cells
after that hop, in order, with non-cell sentinels omitted. -/
structure Plan (Cell : Type) where
  next : Option Cell
  axis : Species
  ahead : List Cell

/-- Exclusion and identity tracking. Off-street tags have no position. -/
structure Snapshot (Cell Car : Type) where
  pos : Car → Option Cell
  occ : Cell → Option Car
  plan : Car → Plan Cell
  occ_iff_pos : ∀ c k, occ c = some k ↔ pos k = some c

variable {Cell Car : Type}

/-- Use the map's junction predicate with the box rule on, or constant false
with it off. The gate applies only when entering from outside. -/
def Snapshot.entersBox (s : Snapshot Cell Car) (junction : Cell → Bool) (k : Car) : Bool :=
  match s.pos k, (s.plan k).next with
  | some p, some q => !junction p && junction q
  | _, _ => false

def Snapshot.AgreesAt (s u : Snapshot Cell Car) (k : Car) : Prop :=
  u.pos k = s.pos k ∧ u.plan k = s.plan k

/-- The selection used by `blockerOf` prefers a direct blocker. Under the active
entry gate, its fallback is the first occupied recorded tail cell. -/
def Snapshot.blocker (s : Snapshot Cell Car) (junction : Cell → Bool) (k : Car) :
    Option (Car × BlockKind) :=
  match s.pos k, (s.plan k).next with
  | some _, some q =>
    match s.occ q with
    | some j => some (j, .direct)
    | none =>
      if s.entersBox junction k then
        ((s.plan k).ahead.findSome? s.occ).map (fun j => (j, .box))
      else none
  | _, _ => none

/-- A sufficient blocking witness. Every occupied tail cell can witness box
blocking. `Snapshot.blocker` selects one of those witnesses. -/
inductive Blocks (junction : Cell → Bool) (s : Snapshot Cell Car) :
    Car → Car → BlockKind → Prop where
  | direct {k j p q} : s.pos k = some p → (s.plan k).next = some q →
      s.occ q = some j → Blocks junction s k j .direct
  | box {k j q} : s.entersBox junction k = true → q ∈ (s.plan k).ahead →
      s.occ q = some j → Blocks junction s k j .box

theorem Snapshot.blocker_sound {junction : Cell → Bool} {s : Snapshot Cell Car}
    {k j : Car} {kind : BlockKind} (h : s.blocker junction k = some (j, kind)) :
    Blocks junction s k j kind := by
  cases hp : s.pos k with
  | none => simp [blocker, hp] at h
  | some p =>
    cases hn : (s.plan k).next with
    | none => simp [blocker, hp, hn] at h
    | some q =>
      cases ho : s.occ q with
      | some b =>
        have he : (b, BlockKind.direct) = (j, kind) := by simpa [blocker, hp, hn, ho] using h
        cases he
        exact .direct hp hn ho
      | none =>
        by_cases hg : s.entersBox junction k = true
        · cases hf : (s.plan k).ahead.findSome? s.occ with
          | none => simp [blocker, hp, hn, ho, hg, hf] at h
          | some b =>
            have he : (b, BlockKind.box) = (j, kind) := by
              simpa [blocker, hp, hn, ho, hg, hf] using h
            cases he
            obtain ⟨r, hr, hocc⟩ := List.exists_of_findSome?_eq_some hf
            exact .box hg hr hocc
        · simp [blocker, hp, hn, ho, hg] at h

variable {junction : Cell → Bool} {s u : Snapshot Cell Car}
variable {rule : Rule} {phase : Species} {moves : Car → Prop}
variable {k j : Car} {kind : BlockKind}

private theorem Blocks.source (edge : Blocks junction s k j kind) : ∃ p, s.pos k = some p := by
  cases edge with
  | direct hp _ _ => exact ⟨_, hp⟩
  | box hg _ _ =>
    cases hp : s.pos k with
    | none => simp [Snapshot.entersBox, hp] at hg
    | some p => exact ⟨p, rfl⟩

private theorem Blocks.at_snapshot (edge : Blocks junction s k j kind)
    (hk : s.AgreesAt u k) (hj : s.AgreesAt u j) : Blocks junction u k j kind := by
  have occupant {q : Cell} (ho : s.occ q = some j) : u.occ q = some j :=
    (u.occ_iff_pos q j).mpr (hj.1.trans ((s.occ_iff_pos q j).mp ho))
  cases edge with
  | direct hp hn ho =>
    exact .direct (hk.1.trans hp) (congrArg Plan.next hk.2 |>.trans hn) (occupant ho)
  | box hg hm ho =>
    exact .box (by simpa [Snapshot.entersBox, hk.1, hk.2] using hg)
      (by simpa only [hk.2] using hm) (occupant ho)

/-- A local contract for a legal half-step. `moves` records actual hop/exit
events, which may be invisible in the occupancy pattern. A stationary
on-street car keeps its position and entire plan. A TRAIN mover may enter an
occupied direct target only with its occupant moving in the same half-step.
TRAIN movers all have the active axis. The box tail always requires pre-step
vacancy when the entry gate applies. -/
structure HalfStep (rule : Rule) (junction : Cell → Bool) (s u : Snapshot Cell Car)
    (phase : Species) (moves : Car → Prop) : Prop where
  stays : ∀ k p, s.pos k = some p → ¬ moves k → s.AgreesAt u k
  train_axis : rule = .train → ∀ k, moves k → (s.plan k).axis = phase
  arrives : ∀ k q, moves k → (s.plan k).next = some q → u.pos k = some q
  occupied_target : ∀ k j q, moves k → (s.plan k).next = some q →
    s.occ q = some j → rule = .train ∧ moves j
  clear_box : ∀ k q, moves k → s.entersBox junction k = true →
    q ∈ (s.plan k).ahead → s.occ q = none

theorem Blocks.moves_with_blocker (edge : Blocks junction s k j kind)
    (step : HalfStep rule junction s u phase moves) (hm : moves k) :
    rule = .train ∧ kind = .direct ∧ moves j ∧ u.pos k = s.pos j := by
  cases edge with
  | direct _ hn ho =>
    obtain ⟨hr, hj⟩ := step.occupied_target k j _ hm hn ho
    exact ⟨hr, rfl, hj, (step.arrives k _ hm hn).trans ((s.occ_iff_pos _ j).mp ho).symm⟩
  | box hg hmem ho =>
    rw [step.clear_box k _ hm hg hmem] at ho
    cases ho

structure Trace (rule : Rule) (junction : Cell → Bool) where
  state : Nat → Snapshot Cell Car
  phase : Nat → Species
  moves : Nat → Car → Prop
  legal : ∀ t, HalfStep rule junction (state t) (state (t + 1)) (phase t) (moves t)

def Trace.Immobile (run : Trace (Cell := Cell) (Car := Car) rule junction) (k : Car) : Prop :=
  ∀ t, (run.state 0).AgreesAt (run.state t) k ∧ ¬ run.moves t k

/-- A nonempty finite closed blocker walk. Distinct tags are unnecessary for
permanence, so this also accepts a singleton self-blocking cycle. -/
structure Cycle (junction : Cell → Bool) (s : Snapshot Cell Car) where
  length : Nat
  positive : 0 < length
  car : Fin length → Car
  kind : Fin length → BlockKind
  blocks : ∀ i, Blocks junction s (car i) (car (BML.cyclicNext length positive i)) (kind i)

/-- The necessary TRAIN exception, evaluated at the original commitments. -/
def Cycle.DirectOnAxis (cycle : Cycle junction s) (phase : Species) : Prop :=
  ∀ i, cycle.kind i = .direct ∧ (s.plan (cycle.car i)).axis = phase

/-- If a cycle has retained its original positions and commitments and any
member moves, TRAIN simultaneously moves every member into its direct
blocker's former cell, all in one phase. -/
theorem Cycle.moves_rotate (cycle : Cycle junction s) {v : Snapshot Cell Car}
    (step : HalfStep rule junction u v phase moves)
    (same : ∀ i, s.AgreesAt u (cycle.car i)) (i : Fin cycle.length) (hm : moves (cycle.car i)) :
    rule = .train ∧ cycle.DirectOnAxis phase ∧
      ∀ j, moves (cycle.car j) ∧
        v.pos (cycle.car j) = s.pos (cycle.car (BML.cyclicNext _ cycle.positive j)) := by
  have follows (j : Fin cycle.length) (hj : moves (cycle.car j)) :=
    ((cycle.blocks j).at_snapshot (same j) (same (BML.cyclicNext _ cycle.positive j)))
      |>.moves_with_blocker step hj
  have allMove (j : Fin cycle.length) : moves (cycle.car j) := by
    obtain ⟨n, rfl⟩ := BML.cyclicNext_reaches _ cycle.positive i j
    induction n with
    | zero => exact hm
    | succ n ih => exact (follows _ ih).2.2.1
  have isTrain := (follows i hm).1
  refine ⟨isTrain, ?_, ?_⟩
  · intro j
    exact ⟨(follows j (allMove j)).2.1,
      (congrArg Plan.axis (same j).2).symm.trans (step.train_axis isTrain _ (allMove j))⟩
  · intro j
    exact ⟨allMove j, (follows j (allMove j)).2.2.2.trans (same _).1⟩

private theorem Cycle.immobile (run : Trace (Cell := Cell) (Car := Car) rule junction)
    (cycle : Cycle junction (run.state 0))
    (guard : rule = .classic ∨ ¬ ∃ axis, cycle.DirectOnAxis axis) (i : Fin cycle.length) :
    run.Immobile (cycle.car i) := by
  have stopped (t : Nat) (same : ∀ j, (run.state 0).AgreesAt (run.state t) (cycle.car j))
      (j : Fin cycle.length) : ¬ run.moves t (cycle.car j) := by
    intro hm
    obtain ⟨hr, hrotates, _⟩ := cycle.moves_rotate (run.legal t) same j hm
    rcases guard with hclassic | hno
    · cases hclassic.symm.trans hr
    · exact hno ⟨_, hrotates⟩
  have agrees (t : Nat) : ∀ j, (run.state 0).AgreesAt (run.state t) (cycle.car j) := by
    induction t with
    | zero => intro j; exact ⟨rfl, rfl⟩
    | succ t ih =>
      intro j
      obtain ⟨p, hp⟩ := (cycle.blocks j).source
      have hs := (run.legal t).stays _ p ((ih j).1.trans hp) (stopped t ih j)
      exact ⟨hs.1.trans (ih j).1, hs.2.trans (ih j).2⟩
  exact fun t => ⟨agrees t i, stopped t (agrees t) i⟩

theorem Cycle.classic_immobile (run : Trace (Cell := Cell) (Car := Car) .classic junction)
    (cycle : Cycle junction (run.state 0)) (i : Fin cycle.length) :
    run.Immobile (cycle.car i) :=
  cycle.immobile run (Or.inl rfl) i

theorem Cycle.train_immobile (run : Trace (Cell := Cell) (Car := Car) .train junction)
    (cycle : Cycle junction (run.state 0))
    (noRotation : ¬ ∃ axis, cycle.DirectOnAxis axis) (i : Fin cycle.length) :
    run.Immobile (cycle.car i) :=
  cycle.immobile run (Or.inr noRotation) i

private theorem Blocks.immobile_of_blocker
    (run : Trace (Cell := Cell) (Car := Car) rule junction)
    (edge : Blocks junction (run.state 0) k j kind) (blocker : run.Immobile j) :
    run.Immobile k := by
  have stopped (t : Nat) (same : (run.state 0).AgreesAt (run.state t) k) : ¬ run.moves t k := by
    intro hm
    have current := edge.at_snapshot same (blocker t).1
    exact (blocker t).2 (current.moves_with_blocker (run.legal t) hm).2.2.1
  have agrees (t : Nat) : (run.state 0).AgreesAt (run.state t) k := by
    induction t with
    | zero => exact ⟨rfl, rfl⟩
    | succ t ih =>
      obtain ⟨p, hp⟩ := edge.source
      have hs := (run.legal t).stays k p (ih.1.trans hp) (stopped t ih)
      exact ⟨hs.1.trans ih.1, hs.2.trans ih.2⟩
  exact fun t => ⟨agrees t, stopped t (agrees t)⟩

/-- A finite path in the initial committed blocking relation. -/
inductive Reaches (junction : Cell → Bool) (s : Snapshot Cell Car) : Car → Car → Prop where
  | refl (k : Car) : Reaches junction s k k
  | cons {k j goal : Car} {edgeKind : BlockKind} :
      Blocks junction s k j edgeKind → Reaches junction s j goal →
      Reaches junction s k goal

/-- Capture under either rule, given a permanently immobilized endpoint. -/
theorem Reaches.immobile (run : Trace (Cell := Cell) (Car := Car) rule junction)
    (path : Reaches junction (run.state 0) k j) (endpoint : run.Immobile j) : run.Immobile k := by
  induction path with
  | refl => exact endpoint
  | cons edge _ ih => exact edge.immobile_of_blocker run (ih endpoint)

theorem Cycle.classic_capture (run : Trace (Cell := Cell) (Car := Car) .classic junction)
    (cycle : Cycle junction (run.state 0)) (i : Fin cycle.length)
    (path : Reaches junction (run.state 0) k (cycle.car i)) : run.Immobile k :=
  path.immobile run (cycle.classic_immobile run i)

theorem Cycle.train_capture (run : Trace (Cell := Cell) (Car := Car) .train junction)
    (cycle : Cycle junction (run.state 0)) (noRotation : ¬ ∃ axis, cycle.DirectOnAxis axis)
    (i : Fin cycle.length) (path : Reaches junction (run.state 0) k (cycle.car i)) :
    run.Immobile k :=
  path.immobile run (cycle.train_immobile run noRotation i)

end BML.LaneDeadlock
