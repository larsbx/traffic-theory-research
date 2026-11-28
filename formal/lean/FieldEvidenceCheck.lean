import BML.FieldObservation
import Lean.Data.Json
import Std.Data.HashSet
import Std.Data.HashMap

/-!
Executable correspondence with source-bound sample pairs. The Python adapter
authenticates CSV bytes. This checker independently decodes exact values,
reconstructs the complete consecutive pair inventory for recorded tracks, and
evaluates the Lean predicates on every pair/cut. Neither the CSV parser nor
SHA-256 is proved here; synthetic adversarial pairs need not be real tracks.
-/
namespace FieldEvidenceCheck

open Lean BML.FieldObservation

structure RationalWire where
  num : String
  den : String
  deriving FromJson

deriving instance FromJson for RowRef
deriving instance FromJson for Classification

structure SampleWire where
  source : Nat
  vehicle : Nat
  frame : Nat
  timeMs : Nat
  y : RationalWire
  speed : RationalWire
  lane : Nat
  «section» : Nat
  intersection : Nat
  provenance : RowRef
  deriving FromJson

structure SourceWire where
  index : Nat
  kind : String
  sourceId : String
  deriving FromJson

structure PairWire where
  before : Nat
  after : Nat
  expected : Array Classification
  deriving FromJson

structure Packet where
  schema : String
  sources : Array SourceWire
  samples : Array SampleWire
  cuts : Array RationalWire
  pairs : Array PairWire
  expectedFirstCrossings : Array Nat
  deriving FromJson

private def quantity (unit : BML.FieldObservation.Unit) (wire : RationalWire) :
    Except String (Quantity unit) := do
  let some numerator := wire.num.toInt? | throw "invalid integer numerator"
  let some denominator := wire.den.toNat? | throw "invalid natural denominator"
  if positive : 0 < denominator then return ⟨numerator, denominator, positive⟩
  else throw "rational denominator must be positive"

private def sample (wire : SampleWire) : Except String Sample := do
  unless wire.provenance.partSha256.length == 64 && wire.provenance.csvRow >= 2 do
    throw "missing CSV byte/row provenance"
  return {
    source := wire.source, vehicle := wire.vehicle, frame := wire.frame,
    timeMs := wire.timeMs, y := ← quantity .feet wire.y,
    speed := ← quantity .feetPerSecond wire.speed,
    lane := wire.lane, «section» := wire.section, intersection := wire.intersection,
    rowRef := wire.provenance
  }

structure Result where
  samples : Nat
  pairs : Nat
  cuts : Nat
  decisions : Nat
  firstCrossings : Array Nat
  adjacentPairs : Nat
  gapPairs : Nat
  laneChanges : Nat
  phaseClaims : Nat := 0
  modelTransitionClaims : Nat := 0
  deriving ToJson

private def check (packet : Packet) : Except String Result := do
  unless packet.schema == "gridlock-field-observation-evidence-v1" do
    throw "unknown field evidence schema"
  if packet.samples.isEmpty || packet.pairs.isEmpty || packet.cuts.isEmpty ||
      packet.sources.isEmpty then throw "empty field evidence inventory"
  unless packet.expectedFirstCrossings.size == packet.cuts.size do
    throw "crossing count/cut dimensions differ"
  let mut sourceIndices : Std.HashSet Nat := {}
  let mut recordedSources : Std.HashSet Nat := {}
  for source in packet.sources do
    if sourceIndices.contains source.index then throw "duplicate source identity"
    unless (source.kind == "recorded_trajectory_capture" || source.kind == "synthetic_control") &&
        !source.sourceId.isEmpty do throw "untyped or unnamed source identity"
    sourceIndices := sourceIndices.insert source.index
    if source.kind == "recorded_trajectory_capture" then
      recordedSources := recordedSources.insert source.index
  let samples ← packet.samples.mapM sample
  let cuts ← packet.cuts.mapM (quantity .feet)
  for s in samples do
    unless sourceIndices.contains s.source do throw "sample names an undefined source"
  let mut last : Std.HashMap (Nat × Nat) Nat := {}
  let mut expectedPairs : Std.HashSet (Nat × Nat) := {}
  for (s, index) in samples.toList.zipIdx do
    if recordedSources.contains s.source then
      let identity := (s.source, s.vehicle)
      if let some prior := last[identity]? then
        let some before := samples[prior]? | throw "invalid recorded sample inventory"
        unless before.timeMs < s.timeMs do
          throw "recorded track has duplicate or unordered sample timestamps"
        expectedPairs := expectedPairs.insert (prior, index)
      last := last.insert identity index
  let mut recordedPairs : Std.HashSet (Nat × Nat) := {}
  let mut first : Std.HashSet (Nat × Nat × Nat) := {}
  let mut counts := Array.replicate cuts.size 0
  let mut adjacentPairs := 0
  let mut gapPairs := 0
  let mut laneChanges := 0
  for (pair, i) in packet.pairs.toList.zipIdx do
    let some before := samples[pair.before]? | throw s!"pair {i}: before index out of range"
    let some after := samples[pair.after]? | throw s!"pair {i}: after index out of range"
    if recordedSources.contains before.source || recordedSources.contains after.source then
      let edge := (pair.before, pair.after)
      unless expectedPairs.contains edge do throw s!"pair {i}: not consecutive in its recorded track"
      if recordedPairs.contains edge then throw s!"pair {i}: duplicate recorded pair"
      recordedPairs := recordedPairs.insert edge
    unless pair.expected.size == cuts.size do throw s!"pair {i}: missing classifications"
    if adjacent before after then adjacentPairs := adjacentPairs + 1
    else gapPairs := gapPairs + 1
    if sameIdentity before after && before.lane != after.lane then laneChanges := laneChanges + 1
    for (cut, j) in cuts.toList.zipIdx do
      let actual := classify before after cut
      let some expected := pair.expected[j]? | throw s!"pair {i}: missing cut {j}"
      unless decide (actual = expected) do
        throw s!"pair {i}, cut {j}: Lean classification differs: {repr actual}"
      if actual.crossing then
        let key := (before.source, before.vehicle, j)
        unless first.contains key do
          first := first.insert key
          counts := counts.modify j (· + 1)
  unless counts == packet.expectedFirstCrossings do
    throw s!"first crossing counts differ: {repr counts}"
  unless recordedPairs.size == expectedPairs.size do
    throw "recorded consecutive pair inventory is incomplete"
  return {
    samples := samples.size, pairs := packet.pairs.size, cuts := cuts.size,
    decisions := packet.pairs.size * cuts.size, firstCrossings := counts,
    adjacentPairs, gapPairs, laneChanges
  }

/-- Synthetic phase controls exercise registration and all interval endpoints.
They are not observed signal data. Proofs in FieldObservation establish the
general soundness properties; these checks detect executable drift. -/
private def phaseControls : Bool :=
  robustPhase 0 100 0 0 0 101 &&
  !(robustPhase 0 100 0 0 1 101) &&
  !(robustPhase 0 100 0 0 0 100) &&
  robustPhase 0 100 (-10) 10 (-10) 111 &&
  !(robustPhase 0 100 (-10) 10 (-9) 111) &&
  !(robustPhase 0 100 10 (-10) 0 200) &&
  !(robustPhase 100 100 0 0 0 200) &&
  robustSpatial 349 351 350 350 &&
  !(robustSpatial 353 347 350 350) &&
  !(robustSpatial 350 351 350 350) &&
  !(phaseComparable .virtualScreenline .independentlyRegistered .independentlyRegistered
    .independentlyRegistered true true true) &&
  !(phaseComparable .physicalStopLine .independentlyRegistered .candidate
    .independentlyRegistered true true true) &&
  !(phaseComparable .physicalStopLine .independentlyRegistered .independentlyRegistered
    .missing true true true) &&
  !(phaseComparable .physicalStopLine .independentlyRegistered .independentlyRegistered
    .independentlyRegistered true false true) &&
  phaseComparable .physicalStopLine .independentlyRegistered .independentlyRegistered
    .independentlyRegistered true true true

def run (path : System.FilePath) : IO UInt32 := do
  unless phaseControls do
    IO.eprintln "synthetic geometry/clock/uncertainty controls failed"
    return 1
  let body ← IO.FS.readFile path
  match Json.parse body >>= fromJson? with
  | .error error =>
    IO.eprintln error
    return 1
  | .ok (packet : Packet) =>
    match check packet with
    | .error error =>
      IO.eprintln error
      return 1
    | .ok result =>
      IO.println (toJson result).compress
      return 0

end FieldEvidenceCheck
