import BML.NetInstances
import BML.Torus

/-! Finite replay of the generic net step on mixed signal/roundabout grids.
Each output line is one tick: `width height link ring tick before after`.
`ring` has one bit per intersection and the states five digits per
intersection (junction, east quadrant, north quadrant, east link, north link;
0 empty, 1 east, 2 north), both row-major with index x + width*y. -/
namespace BML.NetExport

open BML.Net

abbrev Grid (w h : Nat) := Site (Position w h)

def sites (w h : Nat) : List (Grid w h) :=
  (positions w h).flatMap fun p => [.junction p, .quadE p, .quadN p, .linkE p, .linkN p]

def index (w : Nat) {h : Nat} : Grid w h → Nat
  | .junction p => 5 * (p.1.val + w * p.2.val)
  | .quadE p => 5 * (p.1.val + w * p.2.val) + 1
  | .quadN p => 5 * (p.1.val + w * p.2.val) + 2
  | .linkE p => 5 * (p.1.val + w * p.2.val) + 3
  | .linkN p => 5 * (p.1.val + w * p.2.val) + 4

def digitClass : Nat → Option Species
  | 1 => some .east
  | 2 => some .north
  | _ => none

def classDigit : Option Species → Nat
  | none => 0
  | some .east => 1
  | some .north => 2

def thaw (w h : Nat) (cells : Array Nat) : Net.Config (Grid w h) Species := fun c =>
  digitClass (cells.getD (index w c) 0)

def freeze (w h : Nat) (s : Net.Config (Grid w h) Species) : Array Nat :=
  ((sites w h).map fun c => classDigit (s c)).toArray

def layout (w h : Nat) (hw : 0 < w) (hh : 0 < h) (ring : Array Bool) (link : Bool) :
    Layout (Position w h) where
  east := eastDirection w h hw
  north := northDirection w h hh
  ring p := ring.getD (p.1.val + w * p.2.val) false
  link := link

def text (digits : Array Nat) : String := String.join (digits.toList.map toString)

/-- The species a cell of this kind can hold, as digits; empty first. -/
def choices (ring : Array Bool) (link : Bool) (i : Nat) : List Nat :=
  match i % 5 with
  | 0 => [0, 1, 2]
  | 1 => if ring.getD (i / 5) false then [0, 1] else [0]
  | 2 => if ring.getD (i / 5) false then [0, 2] else [0]
  | 3 => if link then [0, 1] else [0]
  | _ => if link then [0, 2] else [0]

def emit (w h : Nat) (hw : 0 < w) (hh : 0 < h) (ring : Array Bool) (link : Bool)
    (tick : Nat) (before : Array Nat) : IO (Array Nat) := do
  let after := freeze w h (Net.step (mixed (layout w h hw hh ring link)) tick (thaw w h before))
  let bits := String.join (ring.toList.map fun b => if b then "1" else "0")
  IO.println s!"{w} {h} {if link then 1 else 0} {bits} {tick} {text before} {text after}"
  return after

/-- Every valid state of the board, both tick parities. -/
def exhaustive (w h : Nat) (hw : 0 < w) (hh : 0 < h) : IO Unit := do
  for mask in [0:2 ^ (w * h)] do
    let ring := (Array.range (w * h)).map fun i => mask / 2 ^ i % 2 == 1
    for link in [false, true] do
      let options := (List.range (5 * w * h)).map (choices ring link)
      let states := options.foldr (fun ds acc => ds.flatMap fun d => acc.map (d :: ·)) [[]]
      for state in states do
        for tick in [0, 1] do
          discard <| emit w h hw hh ring link tick state.toArray

def lcg (seed : Nat) : Nat := (seed * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Pseudo-random runs of `ticks` consecutive ticks. -/
def sampled (w h : Nat) (hw : 0 < w) (hh : 0 < h) (runs ticks : Nat) : IO Unit := do
  let mut seed := w * 1000003 + h * 10007 + 1
  for _ in [0:runs] do
    let mut ring := #[]
    for _ in [0:w * h] do
      seed := lcg seed
      ring := ring.push (seed / 2 ^ 40 % 2 == 1)
    seed := lcg seed
    let link := seed / 2 ^ 40 % 2 == 1
    let mut state := #[]
    for i in [0:5 * w * h] do
      seed := lcg seed
      let ds := choices ring link i
      let pick := if seed / 2 ^ 40 % 5 < 2 then ds.getD (1 + seed / 2 ^ 50 % (ds.length - 1)) 0 else 0
      state := state.push pick
    for tick in [0:ticks] do
      state ← emit w h hw hh ring link tick state

end BML.NetExport

open BML.NetExport in
def main : IO UInt32 := do
  for (w, h) in [(1, 1), (2, 1), (1, 2)] do
    if hw : 0 < w then if hh : 0 < h then exhaustive w h hw hh
  for (w, h) in [(2, 2), (3, 2), (2, 3), (3, 3), (4, 3), (4, 4), (5, 4)] do
    if hw : 0 < w then if hh : 0 < h then sampled w h hw hh 200 8
  return 0
