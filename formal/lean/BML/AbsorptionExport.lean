import BML

/-! Finite evaluation of the proved CLASSIC absorption probe. No alternative
transition or semantic oracle is used by this exporter. -/
namespace BML.AbsorptionExport

def verdictDigit : Absorption.Verdict → Nat
  | .hit => 0
  | .safe => 1
  | .unresolved => 2

def row (w h : Nat) (hw : 0 < w) (hh : 0 < h) (code cutoff : Nat) : String :=
  let initial := decode w h code
  let board := iterate (boardStep w h hw hh) cutoff (materialize w h initial)
  let terminal := boardConfig board
  let verdict := absorptionProbe w h hw hh initial cutoff
  let population := speciesCount w h .east initial + speciesCount w h .north initial
  s!"{code},{cutoff},{encode w h terminal},{verdictDigit verdict},{population}"

def run (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (cutoffs codes : List Nat) : IO Unit := do
  let stdout ← IO.getStdout
  for cutoff in cutoffs do
    for code in codes do
      stdout.putStrLn (row w h hw hh code cutoff)

end BML.AbsorptionExport

/-- Comma-separated cutoffs; optional explicit codes avoid enumerating a large
state space. All input codes must describe complete ternary boards. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ws :: hs :: ts :: cs =>
    match ws.toNat?, hs.toNat?, (ts.splitOn ",").mapM String.toNat?,
        cs.mapM String.toNat? with
    | some w, some h, some cutoffs, some codes =>
      if hw : 0 < w then
        if hh : 0 < h then
          if codes.any (fun code => code ≥ 3 ^ (w*h)) then
            IO.eprintln "a code is outside the complete board state space"
            return 2
          if codes.isEmpty && w*h > 9 then
            IO.eprintln "provide explicit codes above nine cells"
            return 2
          let selected := if codes.isEmpty then List.range (3 ^ (w*h)) else codes
          BML.AbsorptionExport.run w h hw hh cutoffs selected
          return 0
        else
          IO.eprintln "height must be positive"
          return 2
      else
        IO.eprintln "width must be positive"
        return 2
    | _, _, _, _ =>
      IO.eprintln "expected natural dimensions, comma-separated cutoffs, and optional codes"
      return 2
  | _ =>
    IO.eprintln "usage: absorption_export WIDTH HEIGHT CUTOFF[,CUTOFF...] [CODE...]"
    IO.eprintln "CSV: initial_code,cutoff,terminal_code,verdict(0=hit,1=safe,2=unresolved),population"
    return 2
