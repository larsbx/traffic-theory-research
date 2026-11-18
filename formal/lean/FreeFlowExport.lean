import BML.FreeFlow
import BML.Counting

/-!
Finite decisions of the actual CLASSIC `StaticFree` and `AllMove` predicates,
with actual kernel traces through all rounds strictly before `lcm w h`.
This exporter is acceptance evidence; the universal equivalence is in BML.FreeFlow.
-/
namespace BML.FreeFlowExport

/-- Constructive finite quantification over the actual torus positions. -/
local instance positionForall (w h : Nat) (P : Position w h → Prop)
    [DecidablePred P] : Decidable (∀ p, P p) :=
  decidable_of_iff (∀ p ∈ positions w h, P p)
    ⟨fun hp p => hp p (mem_positions w h p), fun hp p _ => hp p⟩

local instance staticFreeDecidable (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) : Decidable (StaticFree w h hw hh s) := by
  unfold StaticFree
  infer_instance

local instance allMoveDecidable (w h : Nat)
    (east north : Direction (Position w h)) (s : Config (Position w h)) :
    Decidable (AllMove east north s) := by
  unfold AllMove
  infer_instance

def staticFreeFlag (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) : Nat :=
  if StaticFree w h hw hh s then 1 else 0

def allMoveFlag (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) : Nat :=
  if AllMove (eastDirection w h hw) (northDirection w h hh) s then 1 else 0

/-- Cache every completed phase/round to avoid nested orbit evaluation. -/
def materialize (w h : Nat) (s : Config (Position w h)) : Array Cell :=
  ((positions w h).map s).toArray

def arrayConfig (w h : Nat) (cells : Array Cell) : Config (Position w h) :=
  fun p => cells.getD (p.1.val + w * p.2.val) .empty

def sequenceField (values : Array Nat) : String :=
  String.intercalate "," (values.toList.map toString)

/-- One row contains all `L = lcm w h` rounds, including the final closing edge.
`firstBlocked = L` is the sentinel for no blocked round in that window. -/
def traceState (w h : Nat) (hw : 0 < w) (hh : 0 < h) (code : Nat) : IO Unit := do
  let period := Nat.lcm w h
  let east := eastDirection w h hw
  let north := northDirection w h hh
  let mut cells := materialize w h (decode w h code)
  let initial := arrayConfig w h cells
  let staticFlag := staticFreeFlag w h hw hh initial
  let mut stateCodes := #[encode w h initial]
  let mut eastCodes : Array Nat := #[]
  let mut eastMoves : Array Nat := #[]
  let mut northMoves : Array Nat := #[]
  let mut allMoves : Array Nat := #[]
  let mut windowFlag : Nat := 1
  let mut firstBlocked := period
  for time in [0:period] do
    let s := arrayConfig w h cells
    let flag := allMoveFlag w h hw hh s
    if flag == 0 then
      windowFlag := 0
      if firstBlocked == period then firstBlocked := time
    let eastCells := materialize w h (halfStep east .east s)
    let eastState := arrayConfig w h eastCells
    let nextCells := materialize w h (torusStep w h hw hh s)
    let nextState := arrayConfig w h nextCells
    eastCodes := eastCodes.push (encode w h eastState)
    stateCodes := stateCodes.push (encode w h nextState)
    eastMoves := eastMoves.push (moveCount w h east .east s)
    northMoves := northMoves.push (moveCount w h north .north eastState)
    allMoves := allMoves.push flag
    cells := nextCells
  let fields := [toString w, toString h, toString code, toString period,
    toString staticFlag, toString windowFlag, toString firstBlocked,
    sequenceField stateCodes, sequenceField eastCodes, sequenceField eastMoves,
    sequenceField northMoves, sequenceField allMoves]
  (← IO.getStdout).putStrLn (String.intercalate "\t" fields)

def exportThrough (maxCells : Nat) : IO Unit := do
  for w in [1:maxCells + 1] do
    if hw : 0 < w then
      for h in [1:maxCells / w + 1] do
        if hh : 0 < h then
          for code in [0:3 ^ (w * h)] do
            traceState w h hw hh code

end BML.FreeFlowExport

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      BML.FreeFlowExport.exportThrough 9
      return 0
  | ["--max-cells", value] =>
      match value.toNat? with
      | some maxCells =>
          if 0 < maxCells ∧ maxCells ≤ 9 then
            BML.FreeFlowExport.exportThrough maxCells
            return 0
          else
            IO.eprintln "max-cells must be between 1 and 9"
            return 2
      | none =>
          IO.eprintln "max-cells must be a natural number"
          return 2
  | _ =>
      IO.eprintln "usage: freeflow_export [--max-cells MAX_CELLS] (default: 9)"
      IO.eprintln "TSV: width,height,input_code,lcm,static_free,all_move_window,first_blocked,state_codes,east_codes,east_moves,north_moves,all_move_flags"
      return 2
