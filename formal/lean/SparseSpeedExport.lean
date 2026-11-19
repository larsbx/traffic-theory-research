import BML.SparseSpeed
import BML.Absorption

/-! Finite CLASSIC traces using the proved data-state evaluator and actual
tag transport. Tag order is the row-major order of the original cars. -/
namespace BML.SparseSpeedExport

def siteIndex (w : Nat) (p : Position w h) : Nat :=
  p.2.val * w + p.1.val

def row (w h : Nat) (hw : 0 < w) (hh : 0 < h) (code horizon : Nat) : String := Id.run do
  let east := eastDirection w h hw
  let north := northDirection w h hh
  let mut board := materialize w h (decode w h code)
  let initial := boardConfig board
  let population := carCount w h initial
  let sparse := if 2 * population < Nat.gcd w h then 1 else 0
  let deadline := if sparse == 1 then toString (sparseSpeedDeadline w h initial) else "-"
  let mut tags := (occupiedCells w h initial).map fun p =>
    (if initial p == .east then Species.east else Species.north, p)
  let mut fields := #[toString w, toString h, toString code, toString horizon,
    toString population, toString sparse, deadline]
  for t in [:horizon] do
    let s := boardConfig board
    let mid := halfStep east .east s
    let next := boardStep w h hw hh board
    let allMove := if AllMove east north s then 1 else 0
    let tagged := tags.map fun (sp, p) =>
      let moved := if RoundCanMove east north sp s p then 1 else 0
      let q := roundTransport east north sp s p
      (sp, q, moved)
    let tagFields := tagged.flatMap fun (_, q, moved) =>
      [siteIndex w q, moved, (correctedClass hw (t + 1) q).val]
    let round := [encode w h mid, encode w h (boardConfig next), allMove] ++ tagFields
    fields := fields.push (String.intercalate "," (round.map toString))
    tags := tagged.map fun (sp, q, _) => (sp, q)
    board := next
  return String.intercalate "\t" fields.toList

/-- Each stdin row is WIDTH HEIGHT CODE HORIZON. Reject invalid dimensions
and codes before decoding the torus. -/
def run (stdin stdout : IO.FS.Stream) : IO UInt32 := do
  repeat
    let line ← stdin.getLine
    if line.isEmpty then
      return 0
    match (line.trimAscii.toString.splitOn " ").mapM String.toNat? with
    | some [w, h, code, horizon] =>
      if hw : 0 < w then
        if hh : 0 < h then
          if code < 3 ^ (w * h) then
            stdout.putStrLn (row w h hw hh code horizon)
            continue
    | _ => pure ()
    IO.eprintln "expected positive WIDTH HEIGHT, a complete ternary board CODE, and HORIZON"
    return 2
  return 0

end BML.SparseSpeedExport

def main : IO UInt32 := do
  BML.SparseSpeedExport.run (← IO.getStdin) (← IO.getStdout)
