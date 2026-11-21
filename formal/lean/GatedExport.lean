import BML.Absorption
import BML.GatedTranspose

/-! Finite replay of the actual gated constructors, both CLASSIC phases, and
the original car's kernel transport. Coordinates in the tag fields are x,y. -/
namespace BML.GatedExport

private def digits (w h : Nat) (s : Config (Position w h)) : String :=
  String.intercalate "" ((positions w h).map fun p => toString (cellDigit (s p)))

private def tagField (tag : Option (Species × Position w h)) : String :=
  match tag with
  | none => "-"
  | some (_, x, y) => s!"{x.val},{y.val}"

private def trace (w h : Nat) (hw : 0 < w) (hh : 0 < h) (closed : Bool)
    (initial : Config (Position w h)) (tag : Option (Species × Position w h)) : IO Unit := do
  let out ← IO.getStdout
  let east := eastDirection w h hw
  let north := northDirection w h hh
  let mut board := materialize w h initial
  let mut currentTag := tag
  for t in [0:2 * max w h + 1] do
    let s := boardConfig board
    let midBoard := materialize w h (halfStep east .east s)
    let mid := boardConfig midBoard
    let nextBoard := materialize w h (halfStep north .north mid)
    let nextTag := currentTag.map fun (sp, p) => (sp, roundTransport east north sp s p)
    let fields := [toString w, toString h, if closed then "Y" else "X", toString t,
      toString (moveCount w h east .east s), toString (moveCount w h north .north mid),
      digits w h s, digits w h mid, digits w h (boardConfig nextBoard),
      tagField currentTag, tagField nextTag]
    out.putStrLn (String.intercalate "\t" fields)
    board := nextBoard
    currentTag := nextTag

def run (maxSide : Nat) : IO Unit := do
  for w in [2:maxSide + 1] do
    for h in [2:maxSide + 1] do
      if hw : 4 ≤ w then
        if hh : 2 ≤ h then
          trace w h (by omega) (by omega) false (Gated.gatedX hw hh) none
          trace w h (by omega) (by omega) true (Gated.gatedY hw hh)
            (some (.north, Gated.freeCar hw hh 0))
      else if hh : 4 ≤ h then
        if hw' : 2 ≤ w then
          trace w h (by omega) (by omega) false (Gated.gatedRowX hh hw') none
          trace w h (by omega) (by omega) true (Gated.gatedRowY hh hw')
            (some (.east, (Gated.freeCar hh hw' 0).swap))

end BML.GatedExport

def main (args : List String) : IO UInt32 := do
  if let [arg] := args then
    if let some maxSide := arg.toNat? then
      if 4 ≤ maxSide then
        BML.GatedExport.run maxSide
        return 0
  IO.eprintln "usage: gated_export MAX_SIDE (at least 4)"
  return 2
