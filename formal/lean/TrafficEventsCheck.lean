import BML.TrafficEvents
import Lean.Data.Json

/-! Strict wire decoding and executable correspondence for typed event batches. -/
namespace TrafficEventsCheck

open Lean BML.TrafficEvents

structure RouteRow where
  prev : Int
  cell : Nat
  targets : List Int
  deriving FromJson

structure EventRow where
  kind : String
  source : Int
  target : Int
  deriving FromJson

structure EventCase where
  id : String
  provenance : String
  cells : Nat
  cars : Nat
  pos : Array Int
  prev : Array Int
  routes : List RouteRow
  entries : Array Bool
  events : Array EventRow
  expectedValid : Bool
  expectedPos : Array Int
  expectedPrev : Array Int
  expectedOcc : Array Int
  expectedMoved : Array Bool
  expectedAdmitted : Array Bool
  deriving FromJson

structure HistoryCase where
  id : String
  model : EventCase
  batches : List (Array EventRow)
  expectedValid : Bool
  expectedPrefixes : List (Array Int)
  deriving FromJson

structure Cases where
  cases : List Json
  invalidWire : List Json
  histories : List HistoryCase
  deriving FromJson

private def decodePosition (cells : Nat) (n : Int) : Except String (Option (Fin cells)) :=
  if n = -1 then pure none
  else if bounded : 0 ≤ n ∧ n.toNat < cells then pure (some ⟨n.toNat, bounded.2⟩)
  else throw "invalid cell ID or negative sentinel"

private def decodeCell (cells : Nat) (n : Int) : Except String (Fin cells) := do
  match ← decodePosition cells n with
  | none => throw "a street cell is required"
  | some c => pure c

private def decodeEvent (cells : Nat) (row : EventRow) : Except String (Event (Fin cells)) := do
  match row.kind with
  | "stay" =>
    unless row.target == row.source do throw "stay endpoints differ"
    return .stay (← decodePosition cells row.source)
  | "hop" => return .hop (← decodeCell cells row.source) (← decodeCell cells row.target)
  | "exit" =>
    unless row.target == -1 do throw "exit must target outside"
    return .exit (← decodeCell cells row.source)
  | "admit" =>
    unless row.source == -1 do throw "admission must start outside"
    return .admit (← decodeCell cells row.target)
  | "exit_admit" => return .exitAdmit (← decodeCell cells row.source) (← decodeCell cells row.target)
  | _ => throw "unknown event kind"

structure Decoded (cells cars : Nat) where
  pos : Positions cells cars
  prev : Positions cells cars
  routes : Routes cells
  entries : Fin cells → Bool
  events : Fin cars → Event (Fin cells)

private def decode (c : EventCase) : Except String (Decoded c.cells c.cars) := do
  unless c.pos.size == c.cars && c.prev.size == c.cars && c.events.size == c.cars &&
      c.entries.size == c.cells do throw "input array length mismatch"
  unless !c.id.isEmpty && !c.provenance.isEmpty do throw "missing case provenance"
  if c.expectedValid then
    unless c.expectedPos.size == c.cars && c.expectedPrev.size == c.cars &&
        c.expectedOcc.size == c.cells && c.expectedMoved.size == c.cars &&
        c.expectedAdmitted.size == c.cars do throw "expected array length mismatch"
  let positions ← c.pos.toList.mapM (decodePosition c.cells)
  let previous ← c.prev.toList.mapM (decodePosition c.cells)
  let eventList ← c.events.toList.mapM (decodeEvent c.cells)
  let mut keys : List (Int × Nat) := []
  let mut rows : List (Option (Fin c.cells) × Fin c.cells × List (Option (Fin c.cells))) := []
  for row in c.routes do
    if keys.contains (row.prev, row.cell) then throw "duplicate route-table key"
    keys := (row.prev, row.cell) :: keys
    let prior ← decodePosition c.cells row.prev
    let cell ← decodeCell c.cells (Int.ofNat row.cell)
    let targets ← row.targets.mapM (decodePosition c.cells)
    rows := (prior, cell, targets) :: rows
  return {
    pos := fun k => positions[k.val]?.getD none
    prev := fun k => previous[k.val]?.getD none
    routes := fun prior cell =>
      ((rows.find? fun row => row.1 == prior && row.2.1 == cell).map (·.2.2)).getD []
    entries := fun q => c.entries[q.val]?.getD false
    events := fun k => eventList[k.val]?.getD (.stay none)
  }

private def encodePosition (p : Option (Fin n)) : Int :=
  p.elim (-1) (fun q => Int.ofNat q.val)

private def agrees (c : EventCase) (d : Decoded c.cells c.cars) : Except String Unit := do
  if goodState : checkState d.pos = true then
    let state := stateOfChecked d.pos d.prev goodState
    if accepted : checkBatch state d.routes d.entries d.events = true then
      unless c.expectedValid do throw "accepted a batch expected to be rejected"
      let next := applyBatch state d.routes d.entries d.events accepted
      let tags := List.finRange c.cars
      let cells := List.finRange c.cells
      unless (tags.map (fun k => encodePosition (next.pos k))).toArray == c.expectedPos do
        throw "postpositions differ"
      unless (tags.map (fun k => encodePosition (next.prev k))).toArray == c.expectedPrev do
        throw "arrival history differs"
      unless (cells.map (fun q => encodePosition (next.occ q))).toArray == c.expectedOcc do
        throw "computed occupancy differs"
      unless (tags.map (fun k => (d.events k).moves)).toArray == c.expectedMoved do
        throw "movement event flags differ"
      unless (tags.map (fun k => (d.events k).admitted)).toArray == c.expectedAdmitted do
        throw "admission event flags differ"
    else
      if c.expectedValid then throw "rejected a batch expected to be accepted"
  else
    if c.expectedValid then throw "rejected a state expected to be exclusive"

private def historyAgrees (c : HistoryCase) : Except String Unit := do
  let d ← decode c.model
  if valid : checkState d.pos = true then
    let initial := stateOfChecked d.pos d.prev valid
    let mut batches : List (Fin c.model.cars → Event (Fin c.model.cells)) := []
    for rows in c.batches do
      unless rows.size == c.model.cars do throw "history tag count differs"
      let events ← rows.toList.mapM (decodeEvent c.model.cells)
      batches := batches ++ [fun (k : Fin c.model.cars) => events[k.val]?.getD (.stay none)]
    match replay? d.routes d.entries initial batches with
    | none => if c.expectedValid then throw "rejected expected finite history"
    | some _ =>
      unless c.expectedValid do throw "accepted an invalid finite history"
      unless c.expectedPrefixes.length == batches.length + 1 do throw "missing prefix expectations"
      for (expected, count) in c.expectedPrefixes.zipIdx do
        unless expected.size == c.model.cars do throw "prefix expected tag count differs"
        match replay? d.routes d.entries initial (batches.take count) with
        | none => throw "accepted history has rejected prefix"
        | some state =>
          let positions := ((List.finRange c.model.cars).map fun k => encodePosition (state.pos k)).toArray
          unless positions == expected do throw s!"prefix {count} positions differ"
  else
    if c.expectedValid then throw "rejected finite history initial state"

private def check (packet : Cases) : Except String (Nat × Nat × Nat × Nat) := do
  if packet.cases.isEmpty || packet.invalidWire.isEmpty || packet.histories.isEmpty then
    throw "empty event case inventory"
  let mut positive := 0
  let mut negative := 0
  for raw in packet.cases do
    let c : EventCase ← fromJson? raw
    let d ← decode c |>.mapError (fun error => s!"{c.id}: {error}")
    agrees c d |>.mapError (fun error => s!"{c.id}: {error}")
    if c.expectedValid then positive := positive + 1 else negative := negative + 1
  if positive == 0 || negative == 0 then throw "event controls require acceptance and rejection"
  for (raw, i) in packet.invalidWire.zipIdx do
    match (fromJson? raw : Except String EventCase) with
    | .error _ => pure ()
    | .ok c =>
      match decode c with
      | .error _ => pure ()
      | .ok _ => throw s!"accepted malformed wire control {i}"
  unless packet.histories.any (·.expectedValid) && packet.histories.any (! ·.expectedValid) do
    throw "history controls require acceptance and rejection"
  for history in packet.histories do
    historyAgrees history |>.mapError (fun error => s!"{history.id}: {error}")
  return (positive, negative, packet.invalidWire.length, packet.histories.length)

def run (path : System.FilePath) : IO UInt32 := do
  let body ← IO.FS.readFile path
  match Json.parse body >>= fromJson? with
  | .error error =>
    IO.eprintln error
    return 1
  | .ok (packet : Cases) =>
    match check packet with
    | .error error =>
      IO.eprintln error
      return 1
    | .ok (positive, negative, malformed, histories) =>
      IO.println s!"TrafficEvents checked {positive} accepted batches, {negative} rejected batches, {malformed} malformed wire controls, and {histories} finite histories"
      return 0

end TrafficEventsCheck
