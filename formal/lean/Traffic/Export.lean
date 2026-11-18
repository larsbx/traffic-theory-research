import Traffic.Torus
import Traffic.Wang

namespace Traffic.Export

def cellCode : Cell → Nat
  | .empty => 0
  | .east => 1
  | .north => 2

def phaseCode : Phase → Nat
  | .east => 1
  | .north => 2

def decodeCell (n : Nat) : Cell :=
  if n == 0 then .empty else if n == 1 then .east else .north

/-- Complete row-major enumeration, with x varying fastest and north increasing y. -/
def positions (w h : Nat) : List (Fin (w + 1) × Fin (h + 1)) :=
  (List.finRange (h + 1)).flatMap fun y =>
    (List.finRange (w + 1)).map fun x => (x, y)

theorem mem_positions (w h : Nat) (x : Fin (w + 1) × Fin (h + 1)) :
    x ∈ positions w h := by
  rcases x with ⟨x, y⟩
  simp [positions, List.mem_flatMap, List.mem_map]

def decodeBoard (w h code : Nat) : Config (Fin (w + 1) × Fin (h + 1)) :=
  fun x => decodeCell ((code / 3 ^ (x.1.val + (w + 1) * x.2.val)) % 3)

def encodeBoard (w h : Nat) (c : Config (Fin (w + 1) × Fin (h + 1))) : Nat :=
  (positions w h).foldl
    (fun n x => n + cellCode (c x) * 3 ^ (x.1.val + (w + 1) * x.2.val)) 0

def frozenCheck (w h : Nat) (c : Config (Fin (w + 1) × Fin (h + 1))) : Bool :=
  allPhases.all fun p => (positions w h).all fun x =>
    !(decide (Moves (torusGrid w h) c p x))

theorem frozenCheck_iff (w h : Nat) (c : Config (Fin (w + 1) × Fin (h + 1))) :
    frozenCheck w h c = true ↔ Frozen (torusGrid w h) c := by
  rw [frozen_iff_no_moves]
  simp only [frozenCheck, List.all_eq_true]
  constructor
  · intro hf p x
    simpa using hf p (mem_allPhases p) x (mem_positions w h x)
  · intro hf p _ x _
    simpa using hf p x

def validTilesCheck (w h : Nat)
    (ts : Wang.Tiling (Fin (w + 1) × Fin (h + 1))) : Bool :=
  (positions w h).all fun x =>
    decide (Wang.Allowed (ts x)) &&
    decide ((ts x).east = (ts ((torusGrid w h).next .east x)).center) &&
    decide ((ts x).north = (ts ((torusGrid w h).next .north x)).center)

theorem validTilesCheck_iff (w h : Nat)
    (ts : Wang.Tiling (Fin (w + 1) × Fin (h + 1))) :
    validTilesCheck w h ts = true ↔ Wang.Valid (torusGrid w h) ts := by
  simp only [validTilesCheck, List.all_eq_true]
  constructor
  · intro hf
    have hx (x) := hf x (mem_positions w h x)
    have hc (x) : Wang.Allowed (ts x) ∧
        (ts x).east = (ts ((torusGrid w h).next .east x)).center ∧
        (ts x).north = (ts ((torusGrid w h).next .north x)).center := by
      simpa [Bool.and_assoc] using hx x
    exact ⟨fun x => (hc x).1, fun x => (hc x).2⟩
  · rintro ⟨ha, hm⟩ x _
    have hx := And.intro (ha x) (hm x)
    simpa [Bool.and_assoc] using hx

def row (w h code : Nat) (p : Phase) : String :=
  let g := torusGrid w h
  let c := decodeBoard w h code
  let tiles := Wang.encode g c
  let values := [
    w + 1, h + 1, code, phaseCode p, encodeBoard w h (halfStep g p c),
    3 - phaseCode p, if frozenCheck w h c then 1 else 0,
    if validTilesCheck w h tiles then 1 else 0,
    encodeBoard w h (Wang.decode tiles), Wang.allowedTiles.length
  ]
  String.intercalate "\t" (values.map toString)

def emitGrid (w h : Nat) : IO Unit := do
  for code in List.range (3 ^ ((w + 1) * (h + 1))) do
    for p in allPhases do
      IO.println (row w h code p)

end Traffic.Export

def main : IO Unit := do
  Traffic.Export.emitGrid 0 0
  Traffic.Export.emitGrid 0 1
  Traffic.Export.emitGrid 1 0
  Traffic.Export.emitGrid 1 1
  Traffic.Export.emitGrid 2 1
  Traffic.Export.emitGrid 1 2
