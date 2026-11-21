import BML.StoppedCore
import BML.Absorption

/-!
Executable snapshot/core and original-tag counts for the actual CLASSIC
kernel. Materialized boards and tag lists avoid rebuilding function-valued
histories. Their refinement to `iterate` and `carTrace` is proved below.
-/
namespace BML.StoppedCoreExport

structure State (w h : Nat) where
  board : MaterializedBoard w h
  eastTags : List (Position w h)
  northTags : List (Position w h)

def eval (w h : Nat) (hw : 0 < w) (hh : 0 < h) (s : Config (Position w h)) :
    Nat → State w h
  | 0 => ⟨materialize w h s, speciesCells w h .east s, speciesCells w h .north s⟩
  | t+1 =>
    let previous := eval w h hw hh s t
    let current := boardConfig previous.board
    ⟨boardStep w h hw hh previous.board,
      previous.eastTags.map (roundTransport (eastDirection w h hw) (northDirection w h hh)
        .east current),
      previous.northTags.map (roundTransport (eastDirection w h hw) (northDirection w h hh)
        .north current)⟩

theorem eval_board (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (t : Nat) :
    boardConfig (eval w h hw hh s t).board = iterate (torusStep w h hw hh) t s := by
  induction t with
  | zero => exact boardConfig_materialize w h s
  | succ t ih => simp only [eval, boardConfig_step, ih, iterate]

theorem eval_eastTags (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (t : Nat) :
    (eval w h hw hh s t).eastTags = (speciesCells w h .east s).map
      (carTrace (eastDirection w h hw) (northDirection w h hh) .east s t) := by
  induction t with
  | zero => simp [eval, carTrace]
  | succ t ih => simp only [eval, ih, eval_board, List.map_map,
      Function.comp_def, carTrace, torusStep]

theorem eval_northTags (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (t : Nat) :
    (eval w h hw hh s t).northTags = (speciesCells w h .north s).map
      (carTrace (eastDirection w h hw) (northDirection w h hh) .north s t) := by
  induction t with
  | zero => simp [eval, carTrace]
  | succ t ih => simp only [eval, ih, eval_board, List.map_map,
      Function.comp_def, carTrace, torusStep]

def coreTagCount (w h : Nat) (hw : 0 < w) (hh : 0 < h) (state : State w h) : Nat :=
  let flag := pathCoreFlag (eastDirection w h hw) (northDirection w h hh)
    (boardConfig state.board)
  (state.eastTags.filter flag).length + (state.northTags.filter flag).length

/-- The executable labeled count is the proved original-trace count, at
every checkpoint and for every complete initial board. -/
theorem coreTagCount_eq_tracedCoreCount (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (t : Nat) :
    coreTagCount w h hw hh (eval w h hw hh s t) =
      tracedCoreCount (eastDirection w h hw) (northDirection w h hh) s t := by
  simp only [coreTagCount, eval_eastTags, eval_northTags, eval_board,
    List.filter_map, List.length_map, tracedCoreCount, tracedCoreSpeciesCount,
    Function.comp_def, torusStep]

def fullLaneCheck (w h : Nat) (s : Config (Position w h)) : Bool :=
  (List.finRange h).any (fun y => (List.finRange w).all (fun x => decide (s (x,y) = .east))) ||
    (List.finRange w).any (fun x => (List.finRange h).all (fun y => decide (s (x,y) = .north)))

theorem fullLaneCheck_iff (w h : Nat) (s : Config (Position w h)) :
    fullLaneCheck w h s = true ↔ HasFullMonochromaticLane s := by
  simp only [fullLaneCheck, Bool.or_eq_true, List.any_eq_true, List.all_eq_true,
    List.mem_finRange, true_and, forall_const, decide_eq_true_eq,
    HasFullMonochromaticLane, FullEastRow, FullNorthColumn]

def row (w h : Nat) (hw : 0 < w) (hh : 0 < h) (code time : Nat) : String :=
  let initial := decode w h code
  let state := eval w h hw hh initial time
  let terminal := boardConfig state.board
  let core := pathCoreCount (eastDirection w h hw) (northDirection w h hh) terminal
  let tags := coreTagCount w h hw hh state
  let jam := if jamCheck w h hw hh terminal then 1 else 0
  let lane := if fullLaneCheck w h initial then 1 else 0
  String.intercalate "," ([w,h,code,time,encode w h terminal,carCount w h initial,
    core,tags,jam,lane].map toString)

end BML.StoppedCoreExport

/-- Batch requests share dimensions. Times are supplied by the independent
finite labeled recurrence check, not claimed as a general stabilization bound. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ws :: hs :: requests =>
    match ws.toNat?, hs.toNat? with
    | some w, some h =>
      if hw : 0 < w then
        if hh : 0 < h then
          let stdout ← IO.getStdout
          for request in requests do
            match (request.splitOn ":").mapM String.toNat? with
            | some [code,time] =>
              if code < 3 ^ (w*h) then
                stdout.putStrLn (BML.StoppedCoreExport.row w h hw hh code time)
              else
                IO.eprintln "code is outside the complete ternary board space"
                return 2
            | _ =>
              IO.eprintln "expected CODE:TIME requests"
              return 2
          return 0
        else
          IO.eprintln "height must be positive"
          return 2
      else
        IO.eprintln "width must be positive"
        return 2
    | _, _ =>
      IO.eprintln "expected natural dimensions"
      return 2
  | _ =>
    IO.eprintln "usage: stopped_core_export WIDTH HEIGHT CODE:TIME [CODE:TIME ...]"
    IO.eprintln "CSV: width,height,code,time,terminal_code,population,core_count,tag_core_count,jam,initial_lane"
    return 2
