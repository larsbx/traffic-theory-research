import BML.RouteAmortized
import Lean.Data.Json

/-! Execute the proved R2 kernels on finite tables exported by the simulator. -/
namespace R2Check

open Lean BML.RouteTrap

structure Arrival where
  prev : Int
  cells : List Int
  deriving FromJson

structure MapCase where
  id : String
  law : String
  width : Nat
  height : Nat
  table : Array (Option (List Arrival))
  ranks : Array (Option Nat)
  deriving FromJson

structure TrapCase where
  cars : List Nat
  menus : Array (List (List Nat))
  expected : List Nat
  deriving FromJson

structure Cases where
  maps : List MapCase
  rejectedMaps : List MapCase
  traps : List TrapCase
  deriving FromJson

private def MapCase.accepts (m : MapCase) : Bool := Id.run do
  if m.width == 0 || m.height == 0 || m.width * m.height != m.table.size ||
      m.ranks.size != m.table.size then
    return false
  let row (c : Nat) := m.table[c]?.join
  let rank (c : Nat) := m.ranks[c]?.join
  let slots := List.range m.table.size
  let validRoad (c : Nat) := (row c).isSome
  let validCell (c : Int) := c ≥ 0 && validRoad c.toNat
  let valid := slots.all fun c =>
    match row c with
    | none => (rank c).isNone
    | some arrivals => !arrivals.isEmpty && arrivals.all fun a =>
      (a.prev == -1 || validCell a.prev) && a.cells.all (fun q => q == -2 || validCell q)
  let target (q : Int) := if q == -2 then none else some q.toNat
  let turns c := ((row c).getD []).map fun a => a.cells.map target
  return valid && checkRanks (slots.filter validRoad) turns rank

private def TrapCase.agrees (t : TrapCase) : Bool :=
  t.cars.all (fun k => k < t.menus.size) &&
    greatestTrap t.cars (fun k => t.menus[k]?.getD []) == t.expected

private def check (input : Cases) : Except String Unit := do
  if input.maps.isEmpty || input.rejectedMaps.isEmpty || input.traps.isEmpty then
    throw "empty R2 case inventory"
  for m in input.maps do
    unless m.accepts do
      throw s!"rejected rank certificate for {m.id} ({m.law})"
  for m in input.rejectedMaps do
    if m.accepts then
      throw s!"accepted invalid rank certificate for {m.id} ({m.law})"
  for (t, i) in input.traps.zipIdx do
    unless t.agrees do
      throw s!"greatest trap disagrees in case {i}"

def run (path : System.FilePath) : IO UInt32 := do
  let body ← IO.FS.readFile path
  match Json.parse body >>= fromJson? with
  | .error err =>
    IO.eprintln err
    return 1
  | .ok (input : Cases) =>
    match check input with
    | .error err =>
      IO.eprintln err
      return 1
    | .ok () =>
      IO.println s!"R2 checked {input.maps.length} rank certificates, {input.rejectedMaps.length} rejections, and {input.traps.length} trap cases"
      return 0

structure ClockCase where
  green : Nat
  t : Nat
  axis : Nat
  junction : Bool
  expected : Bool
  deriving FromJson

structure MergeCase where
  age : Array Nat
  available : Array Int
  expected : Array Bool
  deriving FromJson

structure DeadlineCase where
  cars : Nat
  gap : Nat
  expected : Nat
  deriving FromJson

structure RankDeadlineCase where
  cars : Nat
  delay : Nat
  rank : Nat
  expected : String
  deriving FromJson

structure ServiceCases where
  clocks : List ClockCase
  merges : List MergeCase
  deadlines : List DeadlineCase
  rankDeadlines : List RankDeadlineCase
  deriving FromJson

private def MergeCase.agrees (m : MergeCase) : Bool := Id.run do
  if m.age.size != m.available.size || m.expected.size != m.available.size then return false
  let tags := List.range m.available.size
  let request (k : Nat) := m.available[k]?.getD (-3)
  let age (k : Nat) := m.age[k]?.getD 0
  for k in tags do
    let q := request k
    let grant := q == -2 || (q ≥ 0 &&
      BML.RouteService.chooseWinner age (tags.filter fun j => request j == q) == some k)
    if m.expected[k]? != some grant then return false
  return true

private def checkService (input : ServiceCases) : Except String Unit := do
  if input.clocks.isEmpty || input.merges.isEmpty || input.deadlines.isEmpty || input.rankDeadlines.isEmpty then
    throw "empty R2 service case inventory"
  for (c, i) in input.clocks.zipIdx do
    unless c.green > 0 && c.axis < 2 &&
        BML.RouteService.clockAllows c.green c.t c.axis c.junction == c.expected do
      throw s!"clock disagreement in case {i}"
  for (m, i) in input.merges.zipIdx do
    unless m.agrees do throw s!"merge disagreement in case {i}"
  for (d, i) in input.deadlines.zipIdx do
    unless BML.RouteService.mergeDeadline d.cars d.gap == d.expected do
      throw s!"deadline disagreement in case {i}"
  for (d, i) in input.rankDeadlines.zipIdx do
    unless toString (BML.RouteService.rankDeadline d.cars d.delay d.rank) == d.expected do
      throw s!"rank deadline disagreement in case {i}"

def runService (path : System.FilePath) : IO UInt32 := do
  let body ← IO.FS.readFile path
  match Json.parse body >>= fromJson? with
  | .error err =>
    IO.eprintln err
    return 1
  | .ok (input : ServiceCases) =>
    match checkService input with
    | .error err =>
      IO.eprintln err
      return 1
    | .ok () =>
      IO.println s!"R2 checked {input.clocks.length} clock cases, {input.merges.length} merge cases, {input.deadlines.length} merge deadlines, and {input.rankDeadlines.length} rank deadlines"
      return 0

end R2Check

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] => R2Check.run path
  | ["--service", path] => R2Check.runService path
  | ["--amortized", depth] =>
    match depth.toNat? with
    | some n =>
      let rows := (List.range n).map fun i =>
        [BML.RouteAmortized.mergeStart 0 4 (i+1), BML.RouteAmortized.mergeStart 4 6 i]
      IO.println (Lean.toJson rows).compress
      return 0
    | none => return 2
  | ["--wait-bounds", cap, maxRank] =>
    match cap.toNat?, maxRank.toNat? with
    | some k, some n =>
      let bounds := (List.range (n + 1)).map fun r => toString (BML.RouteProgress.waitBound k r)
      IO.println (Lean.toJson bounds).compress
      return 0
    | _, _ =>
      IO.eprintln "expected a natural service cap and maximum rank"
      return 2
  | _ =>
    IO.eprintln "usage: r2_check CASES.json | r2_check --service CASES.json | r2_check --wait-bounds CAP MAX_RANK | r2_check --amortized DEPTH"
    return 2
