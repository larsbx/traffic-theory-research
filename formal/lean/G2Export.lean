import BML.NonGridlock

/-!
Finite traces of the actual CLASSIC G2 constructor and actual torus kernel.
The trace horizon is a replay bound, not a proof of perpetual non-gridlock.
Boards use row-major digit strings, avoiding fixed-width base-three overflow.
-/
namespace BML.G2Export

/-- Cache the finite configuration between steps, avoiding nested evaluations
of the whole previous orbit when a neighbor is read. Enumeration is row-major.
Return the array itself so Lean does not defer its computation by eta-expanding
a configuration-valued function. -/
def materialize (w h : Nat) (s : Config (Position w h)) : Array Cell :=
  ((positions w h).map s).toArray

def arrayConfig (w h : Nat) (cells : Array Cell) : Config (Position w h) :=
  fun p => cells.getD (p.1.val + w * p.2.val) .empty

def boardDigits (w h : Nat) (s : Config (Position w h)) : String :=
  String.intercalate "" ((positions w h).map fun p => toString (cellDigit (s p)))

/-- Operational CLASSIC jam flag: positive population and zero actual moves.
In particular an empty fixed state is not a jam. -/
def observedJam (population eastMoves northMoves : Nat) : Nat :=
  if 0 < population ∧ eastMoves + northMoves = 0 then 1 else 0

def emitTransition (w h n time : Nat) (s eastState nextState : Config (Position w h))
    (eastMoves northMoves : Nat) : IO Unit := do
  let population := carCount w h s
  let fields := [toString w, toString h, toString n, toString time,
    toString population, toString (speciesCount w h .east s),
    toString (speciesCount w h .north s), toString eastMoves, toString northMoves,
    toString (observedJam population eastMoves northMoves),
    boardDigits w h s, boardDigits w h eastState, boardDigits w h nextState]
  (← IO.getStdout).putStrLn (String.intercalate "\t" fields)

/-- Emit `2*max(w,h)+1` successive full-step transitions, including time zero. -/
def traceConstruction (w h : Nat) (hw : 0 < w) (hh : 0 < h) (n : Nat) : IO Unit := do
  let east := eastDirection w h hw
  let north := northDirection w h hh
  let mut cells := materialize w h (nonGridlockWith w h n)
  for time in [0:2 * max w h + 1] do
    let s := arrayConfig w h cells
    let eastCells := materialize w h (halfStep east .east s)
    let eastState := arrayConfig w h eastCells
    let nextCells := materialize w h (torusStep w h hw hh s)
    let nextState := arrayConfig w h nextCells
    let eastMoves := moveCount w h east .east s
    let northMoves := moveCount w h north .north eastState
    emitTransition w h n time s eastState nextState eastMoves northMoves
    cells := nextCells

def exportThrough (maxSide : Nat) : IO Unit := do
  for w in [1:maxSide + 1] do
    if hw : 0 < w then
      for h in [1:maxSide + 1] do
        if hh : 0 < h then
          for n in [0:w * h] do
            traceConstruction w h hw hh n

end BML.G2Export

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      BML.G2Export.exportThrough 12
      return 0
  | ["--max-side", value] =>
      match value.toNat? with
      | some maxSide =>
          if 0 < maxSide then
            BML.G2Export.exportThrough maxSide
            return 0
          else
            IO.eprintln "max-side must be positive"
            return 2
      | none =>
          IO.eprintln "max-side must be a natural number"
          return 2
  | _ =>
      IO.eprintln "usage: g2_export [--max-side MAX_SIDE] (default: 12)"
      IO.eprintln "TSV: width,height,count,time,population,eastCount,northCount,eastMoves,northMoves,jam,before,east,after"
      return 2
