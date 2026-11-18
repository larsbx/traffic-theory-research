import BML.AllCounts

/-!
Finite export of the actual CLASSIC all-count jam constructor. Boards are
emitted as row-major digit strings, so large boards do not rely on a host's
fixed-width encoding of a base-three state identifier.
-/
namespace BML.G1Export

/-- Digits run left-to-right in each row, with rows in increasing y order. -/
def boardDigits (w h : Nat) (s : Config (Position w h)) : String :=
  String.intercalate "" ((positions w h).map fun p => toString (cellDigit (s p)))

/-- One row contains the requested count, independently evaluated Lean counts,
and the actual board supplied to those counting functions. -/
def emitConstruction (w h n : Nat) : IO Unit := do
  let s := gridlockWith w h n
  let fields := [toString w, toString h, toString n,
    toString (carCount w h s), toString (speciesCount w h .east s),
    toString (speciesCount w h .north s), boardDigits w h s]
  (← IO.getStdout).putStrLn (String.intercalate "\t" fields)

/-- All admissible exact counts on every ordered rectangle in the chosen range. -/
def exportThrough (maxSide : Nat) : IO Unit := do
  for w in [1:maxSide + 1] do
    for h in [1:maxSide + 1] do
      for n in [min w h:w * h + 1] do
        emitConstruction w h n

end BML.G1Export

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      BML.G1Export.exportThrough 12
      return 0
  | ["--max-side", value] =>
      match value.toNat? with
      | some maxSide =>
          if 0 < maxSide then
            BML.G1Export.exportThrough maxSide
            return 0
          else
            IO.eprintln "max-side must be positive"
            return 2
      | none =>
          IO.eprintln "max-side must be a natural number"
          return 2
  | _ =>
      IO.eprintln "usage: g1_export [--max-side MAX_SIDE] (default: 12)"
      IO.eprintln "TSV: width,height,requested_count,car_count,east_count,north_count,row_major_digits"
      return 2
