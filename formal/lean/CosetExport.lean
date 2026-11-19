import BML.Cosets

/-!
Finite observations of the actual diagonal step, phase map, and east translate.
The independent checker reconstructs complete orbits from these successor rows.
The general coset identity is proved separately in `BML.Cosets`.
-/
namespace BML.CosetExport

def emitPosition (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (p : Position w h) : IO Unit := do
  let next := diagonalStep w h hw hh p
  let shifted := (eastDirection w h hw).next p
  let fields := [toString w, toString h, toString (Nat.gcd w h),
    toString (Nat.lcm w h), toString p.1.val, toString p.2.val,
    toString next.1.val, toString next.2.val, toString (phaseClass w h p),
    toString shifted.1.val, toString shifted.2.val, toString (phaseClass w h shifted)]
  (← IO.getStdout).putStrLn (String.intercalate "\t" fields)

def exportThrough (maxSide : Nat) : IO Unit := do
  for w in [1:maxSide + 1] do
    if hw : 0 < w then
      for h in [1:maxSide + 1] do
        if hh : 0 < h then
          for p in positions w h do
            emitPosition w h hw hh p

end BML.CosetExport

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      BML.CosetExport.exportThrough 12
      return 0
  | ["--max-side", value] =>
      match value.toNat? with
      | some maxSide =>
          if 0 < maxSide then
            BML.CosetExport.exportThrough maxSide
            return 0
          else
            IO.eprintln "max-side must be positive"
            return 2
      | none =>
          IO.eprintln "max-side must be a natural number"
          return 2
  | _ =>
      IO.eprintln "usage: coset_export [--max-side MAX_SIDE] (default: 12)"
      IO.eprintln "TSV: width,height,gcd,lcm,x,y,nextX,nextY,phase,shiftX,shiftY,shiftPhase"
      return 2
