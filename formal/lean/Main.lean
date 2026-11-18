import BML

open BML

/-- Exhaustive replay of the actual formal kernel, in row-major base-three order. -/
def replay (w h : Nat) (hw : 0 < w) (hh : 0 < h) : IO Unit := do
  let stdout ← IO.getStdout
  let east := eastDirection w h hw
  let north := northDirection w h hh
  for code in [0:3 ^ (w*h)] do
    let s := decode w h code
    let e := halfStep east .east s
    let n := halfStep north .north e
    let em := moveCount w h east .east s
    let nm := moveCount w h north .north e
    stdout.putStrLn s!"{code},{encode w h e},{encode w h n},{em},{nm}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [ws, hs] =>
      match ws.toNat?, hs.toNat? with
      | some w, some h =>
          if hw : 0 < w then
            if hh : 0 < h then
              replay w h hw hh
              return 0
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
      IO.eprintln "usage: bml_replay WIDTH HEIGHT"
      IO.eprintln "CSV columns: index,east_state,next_state,east_moves,north_moves"
      return 2
