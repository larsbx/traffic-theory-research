import Train

namespace BML.Train

/-- Executable zero-movement test, including the empty configuration. -/
def stuckCheck (w h : Nat) (east north : CyclicDirection (Position w h))
    (s : Config (Position w h)) : Bool :=
  decide (moveCount w h east .east s = 0) &&
    decide (moveCount w h north .north s = 0)

theorem stuckCheck_eq_true_iff (w h : Nat)
    (east north : CyclicDirection (Position w h)) (s : Config (Position w h)) :
    stuckCheck w h east north s = true ↔ Stuck east north s := by
  simp [stuckCheck, Stuck, moveCount_eq_zero_iff]

/-- Both standalone half-steps and the east-then-north cycle, with actual mover counts. -/
def replayValues (w h : Nat) (hw : 0 < w) (hh : 0 < h) (code : Nat)
    (s : Config (Position w h)) : List Nat :=
  let east := eastRing w h hw
  let north := northRing w h hh
  let e := halfStep east .east s
  let n := halfStep north .north s
  let f := halfStep north .north e
  [w, h, code, encode w h e, encode w h n, encode w h f,
    moveCount w h east .east s, moveCount w h north .north s,
    moveCount w h north .north e, if stuckCheck w h east north s then 1 else 0]

def emitValues (values : List Nat) : IO Unit := do
  (← IO.getStdout).putStrLn (String.intercalate "\t" (values.map toString))

def replayRectangle (w h : Nat) (hw : 0 < w) (hh : 0 < h) : IO Unit := do
  for code in [0:3 ^ (w*h)] do
    emitValues (replayValues w h hw hh code (decode w h code))

def replayThrough (maxCells : Nat) : IO Unit := do
  for w in [1:maxCells + 1] do
    if hw : 0 < w then
      for h in [1:maxCells / w + 1] do
        if hh : 0 < h then
          replayRectangle w h hw hh

/-- All population values for every rectangle with both dimensions in 2..maxSide.
The two fields after width/height are requested and actual population; the
remaining eight fields are the standard replay row after width/height. -/
def replayConstructions (maxSide : Nat) : IO Unit := do
  for w in [2:maxSide + 1] do
    if hw : 0 < w then
      for h in [2:maxSide + 1] do
        if hh : 0 < h then
          for n in [w+h:w*h + 1] do
            let s := stuckConfig w h (n - (w+h))
            let row := replayValues w h hw hh (encode w h s) s
            emitValues ([w, h, n, population s] ++ row.drop 2)

def replaySelected (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (codes : List String) : IO UInt32 := do
  for value in codes do
    match value.toNat? with
    | none =>
        IO.eprintln "board code must be a natural number"
        return 2
    | some code =>
        if code < 3 ^ (w*h) then
          emitValues (replayValues w h hw hh code (decode w h code))
        else
          IO.eprintln "board code exceeds the stated grid"
          return 2
  return 0

end BML.Train

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--max-cells", ns] =>
      match ns.toNat? with
      | some n =>
          if 0 < n && n ≤ 9 then
            BML.Train.replayThrough n
            return 0
          else
            IO.eprintln "max-cells must be in 1..9"
            return 2
      | none =>
          IO.eprintln "max-cells must be a natural number"
          return 2
  | ["--construct", ns] =>
      match ns.toNat? with
      | some n =>
          if 2 ≤ n then
            BML.Train.replayConstructions n
            return 0
          else
            IO.eprintln "max-side must be at least two"
            return 2
      | none =>
          IO.eprintln "max-side must be a natural number"
          return 2
  | ws :: hs :: codes =>
      match ws.toNat?, hs.toNat? with
      | some w, some h =>
          if hw : 0 < w then
            if hh : 0 < h then
              if codes.isEmpty then
                BML.Train.replayRectangle w h hw hh
                return 0
              else
                BML.Train.replaySelected w h hw hh codes
            else
              IO.eprintln "height must be positive"
              return 2
          else
            IO.eprintln "width must be positive"
            return 2
      | _, _ =>
          IO.eprintln "width and height must be natural numbers"
          return 2
  | _ =>
      IO.eprintln "usage: train_replay WIDTH HEIGHT [CODE ...]"
      IO.eprintln "       train_replay --max-cells N | --construct MAX_SIDE"
      IO.eprintln "TSV: width,height,input,east,north,full,eastMoves,northMoves,cycleNorthMoves,stuck"
      return 2
