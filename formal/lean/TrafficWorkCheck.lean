import BML.TrafficWork
import BML.TrafficPolicy
import Lean.Data.Json

/-!
Native correspondence checks of the PR #46 reference scheduler's actual
event batches. Inputs contain named finite objects, before/after positions,
and event constructors. Potential and all counts are derived here. Original
pre-phase owners, stopped ages, and movement permissions are also checked;
the stronger any-eligible-car rule is explicitly falsified by its real
reference counterframe. This is finite reference-model evidence, not a
production or field-data certificate.
-/
namespace TrafficWorkCheck

open Lean BML.TrafficEvents BML.TrafficWork BML.TrafficPolicy

structure EventInput where
  kind : String
  source : Option Nat
  target : Option Nat
  deriving FromJson

structure Frame where
  t : Nat
  before : Array (Option Nat)
  after : Array (Option Nat)
  ageBefore : Array Nat
  ageAfter : Array Nat
  owners : Array (Array Nat)
  events : Array EventInput
  reportedMovements : Nat
  reportedAdmissions : Nat
  deriving FromJson

structure WorkCase where
  id : String
  mode : String
  geometric : Bool
  merges : Nat
  heights : Array Nat
  menus : Array (List (Option Nat))
  entries : Array Nat
  initial : Array (Option Nat)
  Q : Nat
  focal : Nat
  enforcedQuota : Option Nat
  prospective : Bool
  strongerPolicyNegativeAt : Option Nat
  frames : Array Frame
  deriving FromJson

structure RejectedCase where
  candidate : WorkCase
  expectedError : String
  deriving FromJson

structure Input where
  scope : String
  sourceSha256 : String
  cases : Array WorkCase
  rejected : Array RejectedCase
  deriving FromJson

structure Statistics where
  frames : Nat := 0
  tagEvents : Nat := 0
  movements : Nat := 0
  admissions : Nat := 0
  combinedExitAdmissions : Nat := 0
  prefixChecks : Nat := 0
  completeBlocks : Nat := 0
  focalDeadlines : Nat := 0
  evacuations : Nat := 0
  ownerPolicyChecks : Nat := 0
  stoppedAgeChecks : Nat := 0
  signalChecks : Nat := 0
  strongerPolicyFailures : Nat := 0
  specificStrongerNegative : Nat := 0
  deriving ToJson

private def requireTrue (test : Bool) (message : String) : Except String (PLift (test = true)) :=
  if accepted : test = true then .ok ⟨accepted⟩ else .error message

private def toCell (cells value : Nat) : Except String (Fin cells) :=
  if inside : value < cells then .ok ⟨value, inside⟩ else .error s!"cell {value} outside {cells} objects"

private def toPosition (cells : Nat) : Option Nat → Except String (Option (Fin cells))
  | none => .ok none
  | some c => return some (← toCell cells c)

private def decodeEvent (cells : Nat) (event : EventInput) : Except String (Event (Fin cells)) := do
  let source ← toPosition cells event.source
  let target ← toPosition cells event.target
  match event.kind, source, target with
  | "stay", p, q =>
    if p == q then return .stay p else throw "stay changes model position"
  | "hop", some p, some q => return .hop p q
  | "exit", some p, none => return .exit p
  | "admit", none, some q => return .admit q
  | "exit_admit", some p, some q => return .exitAdmit p q
  | _, _, _ => throw s!"malformed event {event.kind}"

private def checkCase (input : WorkCase) : Except String Statistics := do
  let cells := input.heights.size
  let cars := input.initial.size
  if cells == 0 || cars == 0 || input.frames.isEmpty || input.Q != blockLength 0 1 ||
      input.menus.size != cells || input.focal >= cars || cells != 2 * input.merges + 1 then
    throw "invalid finite object inventory"
  if input.mode != "open" && input.mode != "closed" then throw "unknown admission mode"
  if input.prospective && (input.mode != "closed" || input.enforcedQuota != some 0) then
    throw "prospective quota is not enforced by the reference admission rule"
  if input.mode == "closed" && input.enforcedQuota != some 0 then
    throw "closed reference rule requires zero admission quota"
  let initial ← input.initial.mapM (toPosition cells)
  let menus ← input.menus.mapM fun row => row.mapM (toPosition cells)
  let doors ← input.entries.mapM (toCell cells)
  let pos (k : Fin cars) := initial[k.val]?.getD none
  let valid ← requireTrue (checkState pos) "initial positions are not exclusive"
  let mut state := stateOfChecked pos (fun _ => none) valid.down
  let routes : Routes cells := fun _ c => menus[c.val]?.getD []
  let entries (c : Fin cells) : Bool := doors.contains c
  let height (c : Fin cells) := input.heights[c.val]?.getD 0
  let D := input.heights.foldl max 0
  let dag ← requireTrue (checkDAG routes height D) "DAG certificate does not decrease on every legal non-self hop"
  let _productive ← requireTrue (checkProductive routes) "nonproductive arrival menu"
  let graph := checkDAG_sound dag.down
  let initialWork := framePotential height state
  let focalCell ← match initial[input.focal]?.join with
    | none => throw "focal object must initially be on street"
    | some c => pure c
  let credit := height focalCell
  let axis : AxisMap cells := fun prev cell target =>
    match target with
    | some _ => if input.geometric && cell.val > input.merges then 1 else 0
    | none => if input.geometric && prev.any (fun p => p.val > input.merges) then 1 else 0
  let junction : Fin cells → Bool := fun _ => false
  let mut ageState := (input.frames[0]?.map (·.ageBefore)).getD #[]
  let mut moveHistory : Array Nat := #[]
  let mut admissionHistory : Array Nat := #[]
  let mut potentialHistory : Array Nat := #[initialWork]
  let mut firstFocal : Option Nat := none
  let mut totalMoves := 0
  let mut totalAdmissions := 0
  let mut combined := 0
  let mut strongerFailures := 0
  let mut specificNegative := 0
  for (frame, index) in input.frames.toList.zipIdx do
    if frame.t != index || frame.before.size != cars || frame.after.size != cars || frame.events.size != cars ||
        frame.ageBefore.size != cars || frame.ageAfter.size != cars then
      throw "frame time or finite object count mismatch"
    if frame.ageBefore != ageState then throw "age history does not continue previous batch"
    let before ← frame.before.mapM (toPosition cells)
    let after ← frame.after.mapM (toPosition cells)
    let decoded ← frame.events.mapM (decodeEvent cells)
    let events (k : Fin cars) := decoded[k.val]?.getD (.stay none)
    let age (k : Fin cars) := frame.ageBefore[k.val]?.getD 0
    let nextAge (k : Fin cars) := frame.ageAfter[k.val]?.getD 0
    let mut ownerArray : Array (Option (Fin cars)) := Array.replicate cells none
    for entry in frame.owners do
      if entry.size != 2 then throw "owner table row is not a target/tag pair"
      let target ← toCell cells (entry[0]?.getD cells)
      let owner ← toCell cars (entry[1]?.getD cars)
      if (ownerArray[target.val]?.getD none).isSome then throw "owner table duplicates a target"
      ownerArray := ownerArray.set! target.val (some owner)
    let owners (c : Fin cells) := ownerArray[c.val]?.getD none
    for k in List.finRange cars do
      if state.pos k != before[k.val]?.getD none then throw "frame source state does not continue previous batch"
    let certification ← requireTrue (checkBatch state routes entries events) "invalid event batch: source, route, vacancy, or exclusivity"
    let accepted := certification.down
    let next := applyBatch state routes entries events accepted
    for k in List.finRange cars do
      if next.pos k != after[k.val]?.getD none then throw "computed event target differs from recorded state"
    unless checkStoppedAge state events age nextAge do throw "full stopped aging failed on actual stay events"
    for k in List.finRange cars do
      if (events k).moves || (events k).admitted || (state.pos k).isNone then
        unless nextAge k == 0 do throw "reset/off-street age differs from reference rule"
    unless checkSignalPermission state events 1 index axis junction do throw "signal permission failed for an actual movement"
    unless checkOwnerTable state routes age 0 owners do throw "owner table does not match complete oldest legal claimants"
    unless checkOwnerConservingFrame state routes events age 0 1 index axis junction owners do
      throw "owner work conservation withheld an eligible owner or exit"
    let anyEligible := checkWorkConservingFrame state routes events age 0 1 index axis junction
    if !anyEligible then strongerFailures := strongerFailures + 1
    if input.strongerPolicyNegativeAt == some index then
      if anyEligible then throw "expected stronger-policy counterframe was accepted"
      specificNegative := specificNegative + 1
    let allowed := checked_work_of_DAG height D graph.1 graph.2.1 state routes entries graph.2.2 events accepted
    let accounting := checked_batch_accounting height D state routes entries events accepted allowed
    let beforeWork := framePotential height state
    let afterWork := framePotential height next
    let moved := movementCount events
    let admitted := admissionCount events
    if moved != frame.reportedMovements then throw "reported movements omit or invent actual movement events"
    if admitted != frame.reportedAdmissions then throw "reported admissions omit or invent actual admission events"
    unless afterWork + moved ≤ beforeWork + D * admitted do
      throw "event-local work inequality disagrees with proved kernel"
    -- Keep the proved accounting expression instantiated by the exact batch.
    have _checkedAccounting := accounting
    for k in List.finRange cars do
      if (events k).moves && (events k).admitted then combined := combined + 1
    if firstFocal.isNone && (decoded[input.focal]?.getD (.stay none)).moves then
      firstFocal := some index
    moveHistory := moveHistory.push moved
    admissionHistory := admissionHistory.push admitted
    potentialHistory := potentialHistory.push afterWork
    totalMoves := totalMoves + moved
    totalAdmissions := totalAdmissions + admitted
    let lengthNow := index + 1
    if count (fun t => moveHistory[t]?.getD 0) 0 lengthNow != totalMoves ||
        count (fun t => admissionHistory[t]?.getD 0) 0 lengthNow != totalAdmissions then
      throw "cumulative event count disagrees with Lean window kernel"
    unless afterWork + totalMoves ≤ initialWork + D * totalAdmissions do
      throw "prefix work telescoping inequality failed"
    if let some quota := input.enforcedQuota then
      if totalAdmissions > quota then throw "admission quota exceeded by actual event objects"
    state := next
    ageState := frame.ageAfter
  let horizon := input.frames.size
  if let some expectedAt := input.strongerPolicyNegativeAt then
    if expectedAt >= horizon || specificNegative != 1 then
      throw "stronger-policy negative control was not exercised"
  let events (t : Nat) := moveHistory[t]?.getD 0 + admissionHistory[t]?.getD 0
  let mut completeBlocks := 0
  for start in List.range (horizon + 1 - input.Q) do
    if (List.range input.Q).all (fun i => potentialHistory[start + i]?.getD 0 > 0) then
      unless count events start input.Q > 0 do throw "observed nonempty block has no actual event"
      completeBlocks := completeBlocks + 1
  let mut focalDeadlines := 0
  let mut evacuations := 0
  if input.mode == "closed" then
    let deadline := waitBound input.Q initialWork credit D 0
    let drain := input.Q * initialWork
    if deadline > horizon || drain > horizon then throw "closed certificate horizon ends before its deadline"
    unless firstFocal.any (fun t => t < deadline) do throw "focal event absent before closed work deadline"
    unless potentialHistory[drain]? == some 0 do throw "positive work remains at closed evacuation deadline"
    if drain > 0 then
      unless (input.frames[drain - 1]?.map (fun frame => frame.after.all Option.isNone)).getD false do
        throw "tagged model object remains on street at zero-work deadline"
    focalDeadlines := 1
    evacuations := 1
  return {
    frames := horizon
    tagEvents := horizon * cars
    movements := totalMoves
    admissions := totalAdmissions
    combinedExitAdmissions := combined
    prefixChecks := horizon
    completeBlocks := completeBlocks
    focalDeadlines := focalDeadlines
    evacuations := evacuations
    ownerPolicyChecks := horizon
    stoppedAgeChecks := horizon
    signalChecks := horizon
    strongerPolicyFailures := strongerFailures
    specificStrongerNegative := specificNegative
  }

private def Statistics.add (a b : Statistics) : Statistics :=
  { frames := a.frames + b.frames, tagEvents := a.tagEvents + b.tagEvents,
    movements := a.movements + b.movements, admissions := a.admissions + b.admissions,
    combinedExitAdmissions := a.combinedExitAdmissions + b.combinedExitAdmissions,
    prefixChecks := a.prefixChecks + b.prefixChecks, completeBlocks := a.completeBlocks + b.completeBlocks,
    focalDeadlines := a.focalDeadlines + b.focalDeadlines, evacuations := a.evacuations + b.evacuations,
    ownerPolicyChecks := a.ownerPolicyChecks + b.ownerPolicyChecks,
    stoppedAgeChecks := a.stoppedAgeChecks + b.stoppedAgeChecks, signalChecks := a.signalChecks + b.signalChecks,
    strongerPolicyFailures := a.strongerPolicyFailures + b.strongerPolicyFailures,
    specificStrongerNegative := a.specificStrongerNegative + b.specificStrongerNegative }

private def check (input : Input) : Except String Statistics := do
  if input.scope != "independent-pr46-reference" || input.sourceSha256.length != 64 ||
      input.cases.isEmpty || input.rejected.isEmpty then throw "missing reference scope or case inventory"
  let mut totals : Statistics := {}
  for candidate in input.cases do
    match checkCase candidate with
    | .ok result => totals := totals.add result
    | .error error => throw s!"{candidate.id}: {error}"
  for negative in input.rejected do
    match checkCase negative.candidate with
    | .ok _ => throw s!"accepted negative control {negative.candidate.id}"
    | .error error =>
      unless error.startsWith negative.expectedError do
        throw s!"{negative.candidate.id}: unexpected rejection {error}"
  return totals

def run (path : System.FilePath) : IO UInt32 := do
  let body ← IO.FS.readFile path
  match Json.parse body >>= fromJson? with
  | .error error => IO.eprintln error; return 1
  | .ok (input : Input) =>
    match check input with
    | .error error => IO.eprintln error; return 1
    | .ok statistics =>
      IO.println (Lean.toJson statistics).compress
      IO.println s!"TrafficWork checked {input.cases.size} reference traces and {input.rejected.size} targeted rejections; observations do not establish a production admission quota."
      return 0

end TrafficWorkCheck
