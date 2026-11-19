import BML.FreeMaximum

/-!
Actual Theorem F constructors and CLASSIC kernel traces, including every edge
of the complete lcm window. Row-major digit strings avoid fixed-width encodings.
This finite acceptance evidence is separate from the universal capacity proof.
-/
namespace BML.FreeMaxExport

local instance positionForall (w h : Nat) (P : Position w h → Prop)
    [DecidablePred P] : Decidable (∀ p, P p) :=
  decidable_of_iff (∀ p ∈ positions w h, P p)
    ⟨fun hp p => hp p (mem_positions w h p), fun hp p _ => hp p⟩

local instance staticFreeDecidable (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) : Decidable (StaticFree w h hw hh s) := by
  unfold StaticFree
  infer_instance

def staticFreeFlag (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) : Nat :=
  if StaticFree w h hw hh s then 1 else 0

/-- Cache actual configurations between phases rather than nesting orbit queries. -/
def materialize (w h : Nat) (s : Config (Position w h)) : Array Cell :=
  ((positions w h).map s).toArray

def arrayConfig (w h : Nat) (cells : Array Cell) : Config (Position w h) :=
  fun p => cells.getD (p.1.val + w * p.2.val) .empty

def boardDigits (cells : Array Cell) : String :=
  String.intercalate "" (cells.toList.map (fun c => toString (cellDigit c)))

def sequenceField (values : Array Nat) : String :=
  String.intercalate "," (values.toList.map toString)

/-- Emit one exact-count constructor, all east intermediates, and the closing
full state at time `lcm w h`. Predicate and population fields are Lean decisions. -/
def traceConstruction (w h : Nat) (hw : 0 < w) (hh : 0 < h) (n : Nat) : IO Unit := do
  let period := Nat.lcm w h
  let east := eastDirection w h hw
  let north := northDirection w h hh
  let mut cells := materialize w h (freeWith w h hw n)
  let initial := arrayConfig w h cells
  let population := carCount w h initial
  let eastCount := speciesCount w h .east initial
  let northCount := speciesCount w h .north initial
  let staticFlag := staticFreeFlag w h hw hh initial
  let mut stateDigits := #[boardDigits cells]
  let mut eastDigits : Array String := #[]
  let mut eastMoves : Array Nat := #[]
  let mut northMoves : Array Nat := #[]
  for _time in [0:period] do
    let s := arrayConfig w h cells
    let eastCells := materialize w h (halfStep east .east s)
    let eastState := arrayConfig w h eastCells
    let nextCells := materialize w h (torusStep w h hw hh s)
    eastDigits := eastDigits.push (boardDigits eastCells)
    stateDigits := stateDigits.push (boardDigits nextCells)
    eastMoves := eastMoves.push (moveCount w h east .east s)
    northMoves := northMoves.push (moveCount w h north .north eastState)
    cells := nextCells
  let fields := [toString w, toString h, toString n, toString (freeMax w h),
    toString period, toString population, toString eastCount, toString northCount,
    toString staticFlag, String.intercalate "," stateDigits.toList,
    String.intercalate "," eastDigits.toList, sequenceField eastMoves,
    sequenceField northMoves]
  (← IO.getStdout).putStrLn (String.intercalate "\t" fields)

def exportThrough (maxSide : Nat) : IO Unit := do
  for w in [1:maxSide + 1] do
    if hw : 0 < w then
      for h in [1:maxSide + 1] do
        if hh : 0 < h then
          for n in [0:freeMax w h + 1] do
            traceConstruction w h hw hh n

end BML.FreeMaxExport

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      BML.FreeMaxExport.exportThrough 12
      return 0
  | ["--max-side", value] =>
      match value.toNat? with
      | some maxSide =>
          if 0 < maxSide then
            BML.FreeMaxExport.exportThrough maxSide
            return 0
          else
            IO.eprintln "max-side must be positive"
            return 2
      | none =>
          IO.eprintln "max-side must be a natural number"
          return 2
  | _ =>
      IO.eprintln "usage: free_max_export [--max-side MAX_SIDE] (default: 12)"
      IO.eprintln "TSV: width,height,requested_count,free_max,lcm,car_count,east_count,north_count,static_free,state_digits,east_digits,east_moves,north_moves"
      return 2
