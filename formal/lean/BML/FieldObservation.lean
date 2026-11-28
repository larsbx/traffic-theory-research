import BML.LaneDeadlock

/-!
# Objects and evidence in sampled traffic data

Measured samples and model events are different types. A sample supplies a
source-scoped vehicle, frame, timestamp, lane label and exact decimal values.
A crossing is an adjacent-frame bracket, not a guessed instantaneous event.
Missing observations do not mean an exit or a vacancy. Physical geometry and
controller-clock registration remain separate evidence obligations.
-/
namespace BML.FieldObservation

inductive Unit where
  | feet | feetPerSecond
  deriving DecidableEq, Repr

/-- Exact value of a source decimal in its declared unit. Positivity is
checked during decoding; invalid denominators never enter the model. -/
structure Quantity (unit : Unit) where
  num : Int
  den : Nat
  positive : 0 < den
  deriving DecidableEq, Repr

namespace Quantity

def ofInt {unit : Unit} (value : Int) : Quantity unit := ⟨value, 1, by decide⟩

def lt {unit : Unit} (a b : Quantity unit) : Bool :=
  decide (a.num * (b.den : Int) < b.num * (a.den : Int))

def le {unit : Unit} (a b : Quantity unit) : Bool :=
  decide (a.num * (b.den : Int) ≤ b.num * (a.den : Int))

theorem le_not_lt {unit : Unit} (a b : Quantity unit) (ordered : le a b = true) :
    lt b a = false := by
  simp only [le, decide_eq_true_eq] at ordered
  simp only [lt, decide_eq_false_iff_not]
  omega

end Quantity

abbrev Feet := Quantity .feet
abbrev FeetPerSecond := Quantity .feetPerSecond

structure RowRef where
  partSha256 : String
  csvRow : Nat
  deriving DecidableEq, Repr

/-- `source` names a capture/query manifest, not an individual CSV part.
Vehicle IDs may be reused by another capture. Parts may share a capture. -/
structure Sample where
  source : Nat
  vehicle : Nat
  frame : Nat
  timeMs : Nat
  y : Feet
  speed : FeetPerSecond
  lane : Nat
  «section» : Nat
  intersection : Nat
  rowRef : RowRef
  deriving DecidableEq, Repr

def sameIdentity (before after : Sample) : Bool :=
  before.source == after.source && before.vehicle == after.vehicle

/-- NGSIM's declared 100-ms cadence is checked together with frame succession.
Using only one of the two clocks would accept missing or inconsistent data. -/
def adjacent (before after : Sample) : Bool :=
  sameIdentity before after && after.frame == before.frame + 1 &&
    after.timeMs == before.timeMs + 100

def forwardBracket (before after : Sample) (cut : Feet) : Bool :=
  Quantity.lt before.y cut && Quantity.le cut after.y

def crossing (before after : Sample) (cut : Feet) : Bool :=
  adjacent before after && forwardBracket before after cut

/-- This reproduces the baseline's slow-sample predicate. It is a kinematic
measurement predicate; it makes no assertion about a queue or its cause. -/
def slowSample (s : Sample) : Bool :=
  s.section == 2 && Quantity.le (Quantity.ofInt 240) s.y &&
    Quantity.lt s.y (Quantity.ofInt 250) &&
    Quantity.le (Quantity.ofInt 0) s.speed && Quantity.le s.speed (Quantity.ofInt 3)

structure Classification where
  identity : Bool
  adjacent : Bool
  forwardBracket : Bool
  crossing : Bool
  changedLane : Bool
  gapCandidate : Bool
  slowBefore : Bool
  deriving DecidableEq, Repr

def classify (before after : Sample) (cut : Feet) : Classification := {
  identity := sameIdentity before after
  adjacent := adjacent before after
  forwardBracket := forwardBracket before after cut
  crossing := crossing before after cut
  changedLane := sameIdentity before after && before.lane != after.lane
  gapCandidate := sameIdentity before after && forwardBracket before after cut &&
    !(adjacent before after)
  slowBefore := slowSample before
}

theorem adjacent_iff (before after : Sample) : adjacent before after = true ↔
    before.source = after.source ∧ before.vehicle = after.vehicle ∧
      after.frame = before.frame + 1 ∧ after.timeMs = before.timeMs + 100 := by
  simp [adjacent, sameIdentity, Bool.and_eq_true, and_assoc]

theorem crossing_iff (before after : Sample) (cut : Feet) : crossing before after cut = true ↔
    before.source = after.source ∧ before.vehicle = after.vehicle ∧
      after.frame = before.frame + 1 ∧ after.timeMs = before.timeMs + 100 ∧
      before.y.num * (cut.den : Int) < cut.num * (before.y.den : Int) ∧
      cut.num * (after.y.den : Int) ≤ after.y.num * (cut.den : Int) := by
  simp [crossing, adjacent_iff, forwardBracket, Quantity.lt, Quantity.le, and_assoc]

theorem crossing_time_strict (before after : Sample) (cut : Feet)
    (accepted : crossing before after cut = true) : before.timeMs < after.timeMs := by
  have time := ((crossing_iff before after cut).mp accepted).2.2.2.1
  omega

theorem source_mismatch_not_crossing (before after : Sample) (cut : Feet)
    (different : before.source ≠ after.source) : crossing before after cut = false := by
  simp [crossing, adjacent, sameIdentity, different]

theorem vehicle_mismatch_not_crossing (before after : Sample) (cut : Feet)
    (different : before.vehicle ≠ after.vehicle) : crossing before after cut = false := by
  simp [crossing, adjacent, sameIdentity, different]

theorem frame_gap_not_crossing (before after : Sample) (cut : Feet)
    (gap : after.frame ≠ before.frame + 1) : crossing before after cut = false := by
  simp [crossing, adjacent, gap]

theorem clock_gap_not_crossing (before after : Sample) (cut : Feet)
    (gap : after.timeMs ≠ before.timeMs + 100) : crossing before after cut = false := by
  simp [crossing, adjacent, gap]

theorem gap_candidate_not_crossing (before after : Sample) (cut : Feet)
    (candidate : (classify before after cut).gapCandidate = true) :
    crossing before after cut = false := by
  simp only [classify, Bool.and_eq_true, Bool.not_eq_true'] at candidate
  simp [crossing, candidate.2]

/-- The endpoint convention cannot count both sides of one shared sample
as immediate successive forward crossings of the same screenline. -/
theorem no_immediate_double_crossing (a b c : Sample) (cut : Feet)
    (first : crossing a b cut = true) : crossing b c cut = false := by
  have above : Quantity.le cut b.y = true := by
    simpa only [crossing, forwardBracket, Bool.and_eq_true] using
      (show adjacent a b = true ∧ Quantity.lt a.y cut = true ∧ Quantity.le cut b.y = true by
        simpa [crossing, forwardBracket, Bool.and_eq_true, and_assoc] using first) |>.2.2
  simp [crossing, forwardBracket, Quantity.le_not_lt cut b.y above]

/-- A bracketed crossing has an interval (begin,end], not an observed exact
crossing timestamp. The downstream timestamp is only its reporting endpoint. -/
def inCrossingWindow (before after : Sample) (t : Nat) : Prop :=
  before.timeMs < t ∧ t ≤ after.timeMs

theorem crossing_window_width (before after : Sample) (cut : Feet)
    (accepted : crossing before after cut = true) :
    after.timeMs = before.timeMs + 100 ∧
    inCrossingWindow before after after.timeMs ∧
    ¬ inCrossingWindow before after before.timeMs := by
  have time := ((crossing_iff before after cut).mp accepted).2.2.2.1
  refine ⟨time, ?_, ?_⟩ <;> simp only [inCrossingWindow] <;> omega

inductive GeometryRole where
  | virtualScreenline | physicalStopLine
  deriving DecidableEq, Repr

inductive Registration where
  | missing | candidate | independentlyRegistered
  deriving DecidableEq, Repr

/-- A conservative interval test for a crossing window (lo,hi], offset
uncertainty [offsetLo,offsetHi], and half-open controller phase [phaseLo,phaseHi).
Times between recorded millisecond ticks remain possible. The test does not
itself authenticate the geometry or clock calibration. -/
def robustPhase (lo hi offsetLo offsetHi phaseLo phaseHi : Int) : Bool :=
  decide (lo < hi ∧ offsetLo ≤ offsetHi ∧ phaseLo < phaseHi ∧
    phaseLo ≤ lo + offsetLo ∧ hi + offsetHi < phaseHi)

theorem robustPhase_iff (lo hi offsetLo offsetHi phaseLo phaseHi : Int) :
    robustPhase lo hi offsetLo offsetHi phaseLo phaseHi = true ↔
    lo < hi ∧ offsetLo ≤ offsetHi ∧ phaseLo < phaseHi ∧
      ∀ scale : Int, 0 < scale → ∀ t offset : Int,
        lo * scale < t → t ≤ hi * scale →
        offsetLo * scale ≤ offset → offset ≤ offsetHi * scale →
        phaseLo * scale ≤ t + offset ∧ t + offset < phaseHi * scale := by
  simp only [robustPhase, decide_eq_true_eq]
  constructor
  · rintro ⟨window, offsets, phase, left, right⟩
    refine ⟨window, offsets, phase, ?_⟩
    intro scale positive t offset ht hend lower upper
    have low := Int.mul_le_mul_of_nonneg_right left (Int.le_of_lt positive)
    have high := Int.mul_lt_mul_of_pos_right right positive
    simp only [Int.add_mul] at low high
    omega
  · rintro ⟨window, offsets, phase, all⟩
    have left := all 2 (by decide) (lo * 2 + 1) (offsetLo * 2)
      (by omega) (by omega) (by omega) (by omega)
    have right := all 1 (by decide) hi offsetHi (by omega) (by omega) (by omega) (by omega)
    refine ⟨window, offsets, phase, ?_, ?_⟩ <;> omega

/-- A spatial envelope test after all lengths are expressed in one common
positive scale. `beforeHi` bounds the true earlier position from above,
`afterLo` bounds the true later position from below, and the true surveyed
cut lies in [cutLo,cutHi]. Recorded decimals alone supply none of those
physical error guarantees. -/
def robustSpatial (beforeHi afterLo cutLo cutHi : Int) : Bool :=
  decide (beforeHi < cutLo ∧ cutLo ≤ cutHi ∧ cutHi ≤ afterLo)

theorem robustSpatial_sound (beforeHi afterLo cutLo cutHi : Int)
    (accepted : robustSpatial beforeHi afterLo cutLo cutHi = true)
    (before after cut : Int) (earlier : before ≤ beforeHi) (later : afterLo ≤ after)
    (cutLower : cutLo ≤ cut) (cutUpper : cut ≤ cutHi) :
    before < cut ∧ cut ≤ after := by
  simp only [robustSpatial, decide_eq_true_eq] at accepted
  omega

/-- Geometry, clock and spatial error registration must be supplied
independently. Observed discharge cannot register the phase used to score
it, and nominal decimal brackets cannot supply physical error bounds. -/
def phaseComparable (role : GeometryRole) (geometry clock spatial : Registration)
    (isCrossing spatialBracket withinPhase : Bool) : Bool :=
  decide (role = .physicalStopLine) && decide (geometry = .independentlyRegistered) &&
    decide (clock = .independentlyRegistered) && decide (spatial = .independentlyRegistered) &&
    isCrossing && spatialBracket && withinPhase

theorem virtual_not_phase_comparable (geometry clock spatial : Registration)
    (cross bracket within : Bool) :
    phaseComparable .virtualScreenline geometry clock spatial cross bracket within = false := by
  simp [phaseComparable]

theorem candidate_clock_not_phase_comparable (role : GeometryRole) (geometry spatial : Registration)
    (cross bracket within : Bool) :
    phaseComparable role geometry .candidate spatial cross bracket within = false := by
  simp [phaseComparable]

theorem missing_spatial_not_phase_comparable (role : GeometryRole) (geometry clock : Registration)
    (cross bracket within : Bool) :
    phaseComparable role geometry clock .missing cross bracket within = false := by
  simp [phaseComparable]

theorem phase_comparable_requires_registrations (role : GeometryRole)
    (geometry clock spatial : Registration) (cross bracket within : Bool)
    (accepted : phaseComparable role geometry clock spatial cross bracket within = true) :
    role = .physicalStopLine ∧ geometry = .independentlyRegistered ∧
      clock = .independentlyRegistered ∧ spatial = .independentlyRegistered ∧
      cross = true ∧ bracket = true ∧ within = true := by
  simpa [phaseComparable, and_assoc] using accepted

section PartialOccupancy

variable {Cell Car : Type}

/-- Outer none means unobserved; some none means positively known outside;
some (some c) means a positively observed cell assignment. -/
abbrev Observation (Cell Car : Type) := Car → Option (Option Cell)

def Complete (observation : Observation Cell Car) : Prop :=
  ∀ k, ∃ p, observation k = some p

def Compatible (observation : Observation Cell Car) (position : Car → Option Cell) : Prop :=
  ∀ k p, observation k = some p → position k = p

theorem unknown_allows_any_position (position : Car → Option Cell) :
    Compatible (fun _ => none) position := by
  intro k p known
  contradiction

/-- Absence of observed occupants implies vacancy only with complete
population observations and a sound location mapping. The filtered NGSIM
query does not provide that completeness premise. -/
theorem vacancy_of_complete_observation (s : LaneDeadlock.Snapshot Cell Car)
    (observation : Observation Cell Car) (complete : Complete observation)
    (agrees : Compatible observation s.pos) (c : Cell)
    (noObservedOccupant : ∀ k, observation k ≠ some (some c)) : s.occ c = none := by
  cases occupied : s.occ c with
  | none => rfl
  | some k =>
    obtain ⟨p, observed⟩ := complete k
    have pos := ((s.occ_iff_pos c k).mp occupied)
    have identity := agrees k p observed
    have cell : p = some c := identity.symm.trans pos
    exact (noObservedOccupant k (cell ▸ observed)).elim

/-- Even for a single vehicle, a missing sample is compatible with both
absence and occupancy. Missingness is not an exit or vacancy certificate. -/
theorem missing_sample_is_nonidentifying (c : Cell) :
    Compatible (fun _ : PUnit => (none : Option (Option Cell))) (fun _ => none) ∧
    Compatible (fun _ : PUnit => (none : Option (Option Cell))) (fun _ => some c) :=
  ⟨unknown_allows_any_position _, unknown_allows_any_position _⟩

end PartialOccupancy

end BML.FieldObservation
