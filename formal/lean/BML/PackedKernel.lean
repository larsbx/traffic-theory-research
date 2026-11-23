import BML.Enumeration
import BML.Capture

/-!
A packed evaluator for finite certificates. Each bit denotes one row-major
site. The four shift tables are accepted only when their read indices agree
with the actual CLASSIC directions at every site.
-/
namespace BML.Packed

structure Board where
  east : Nat
  north : Nat
  deriving DecidableEq, BEq

def Board.mask (b : Board) : Species → Nat
  | .east => b.east
  | .north => b.north

def Board.withMask (b : Board) (mask : Nat) : Species → Board
  | .east => ⟨mask, b.north⟩
  | .north => ⟨b.east, mask⟩

structure Shift where
  leftMask : Nat
  leftBy : Nat
  rightMask : Nat
  rightBy : Nat

def Shift.run (r : Shift) (mask : Nat) : Nat :=
  ((mask &&& r.leftMask) <<< r.leftBy) ||| ((mask &&& r.rightMask) >>> r.rightBy)

private def Shift.sources (r : Shift) (i : Nat) : List Nat :=
  (if r.leftBy ≤ i ∧ r.leftMask.testBit (i - r.leftBy) then [i - r.leftBy] else []) ++
  (if r.rightMask.testBit (r.rightBy + i) then [r.rightBy + i] else [])

private theorem Shift.testBit_run (r : Shift) (mask i : Nat) :
    (r.run mask).testBit i = (r.sources i).any mask.testBit := by
  simp only [Shift.run, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_and, Shift.sources, List.any_append]
  by_cases hl : r.leftBy ≤ i <;>
    cases hx : r.leftMask.testBit (i - r.leftBy) <;>
    cases hy : r.rightMask.testBit (r.rightBy + i) <;> simp [*]

def Shift.matches {w h : Nat} (r : Shift) (source : Position w h → Position w h) : Bool :=
  (positions w h).all fun p =>
    r.sources (rowMajorRank w h p).val == [(rowMajorRank w h (source p)).val]

theorem Shift.read {w h : Nat} {r : Shift} {source : Position w h → Position w h}
    (hr : r.matches source = true) (mask : Nat) (p : Position w h) :
    (r.run mask).testBit (rowMajorRank w h p).val =
      mask.testBit (rowMajorRank w h (source p)).val := by
  have hsource := eq_of_beq ((List.all_eq_true.mp hr) p (mem_positions w h p))
  rw [Shift.testBit_run, hsource]
  simp

structure Layout where
  eastNext : Shift
  eastPrev : Shift
  northNext : Shift
  northPrev : Shift

def torusLayout (w h : Nat) : Layout :=
  let occupied := 2 ^ (w*h) - 1
  let left := ((List.range h).map fun y => 2 ^ (w*y)).sum
  let right := left <<< (w-1)
  let bottom := 2^w - 1
  let top := bottom <<< (w * (h-1))
  ⟨⟨occupied ^^^ right, 1, right, w-1⟩, ⟨left, w-1, occupied ^^^ left, 1⟩,
    ⟨occupied ^^^ top, w, top, w * (h-1)⟩, ⟨bottom, w * (h-1), occupied ^^^ bottom, w⟩⟩

structure Layout.Valid {w h : Nat} (r : Layout) (hw : 0 < w) (hh : 0 < h) : Prop where
  eastNext : r.eastNext.matches (eastDirection w h hw).prev = true
  eastPrev : r.eastPrev.matches (eastDirection w h hw).next = true
  northNext : r.northNext.matches (northDirection w h hh).prev = true
  northPrev : r.northPrev.matches (northDirection w h hh).next = true

def Represents {w h : Nat} (b : Board) (s : Config (Position w h)) : Prop :=
  ∀ sp p, (b.mask sp).testBit (rowMajorRank w h p).val = decide (s p = sp.cell)

def movers (area : Nat) (back : Shift) (sp : Species) (b : Board) : Nat :=
  b.mask sp &&& back.run ((2^area - 1) ^^^ (b.east ||| b.north))

def phase (area : Nat) (forward back : Shift) (sp : Species) (b : Board) : Board :=
  let m := movers area back sp b
  b.withMask (((b.mask sp) ^^^ m) ||| forward.run m) sp

def eastPhase (area : Nat) (r : Layout) :=
  phase area r.eastNext r.eastPrev .east

def round (area : Nat) (r : Layout) (b : Board) : Board :=
  phase area r.northNext r.northPrev .north (eastPhase area r b)

theorem movers_read {w h : Nat} {d : Direction (Position w h)} {back : Shift}
    (hb : back.matches d.next = true) (sp : Species) {b : Board}
    {s : Config (Position w h)} (hs : Represents b s) (p : Position w h) :
    (movers (w*h) back sp b).testBit (rowMajorRank w h p).val = decide (CanMove d sp s p) := by
  have he : b.east.testBit (rowMajorRank w h (d.next p)).val =
      decide (s (d.next p) = .east) := hs .east _
  have hn : b.north.testBit (rowMajorRank w h (d.next p)).val =
      decide (s (d.next p) = .north) := hs .north _
  have hp := hs sp p
  have hi := (rowMajorRank w h (d.next p)).isLt
  simp only [movers, Nat.testBit_and, Shift.read hb, Nat.testBit_xor, Nat.testBit_or,
    Nat.testBit_two_pow_sub_one, hi, decide_true, hp, he, hn, CanMove]
  have hEmpty (c : Cell) :
      (true ^^ (decide (c = .east) || decide (c = .north))) = decide (c = .empty) := by
    cases c <;> decide
  rw [hEmpty]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    simp only [Bool.and_eq_true] at h
    exact decide_eq_true ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩
  · intro h
    have hc : s p = sp.cell ∧ s (d.next p) = .empty := of_decide_eq_true h
    simp only [Bool.and_eq_true]
    exact ⟨decide_eq_true hc.1, decide_eq_true hc.2⟩

theorem phase_rep {w h : Nat} {d : Direction (Position w h)} {forward back : Shift}
    (hf : forward.matches d.prev = true) (hb : back.matches d.next = true)
    (sp : Species) {b : Board} {s : Config (Position w h)} (hs : Represents b s) :
    Represents (phase (w*h) forward back sp b) (halfStep d sp s) := by
  intro observed p
  have hcur :
      (((b.mask sp) ^^^ movers (w*h) back sp b) ||| forward.run (movers (w*h) back sp b)).testBit
        (rowMajorRank w h p).val = decide (halfStep d sp s p = sp.cell) := by
    rw [Nat.testBit_or, Nat.testBit_xor, Shift.read hf, movers_read hb sp hs,
      movers_read hb sp hs, hs sp p]
    simp only [CanMove, d.next_prev]
    by_cases hcar : s p = sp.cell
    · have hoc : s p ≠ .empty := fun h => sp.cell_ne_empty (hcar.symm.trans h)
      by_cases hz : s (d.next p) = .empty
      · simp [halfStep, hcar, hz, Ne.symm sp.cell_ne_empty]
      · simp [halfStep, hcar, hz]
    · by_cases hin : s p = .empty ∧ s (d.prev p) = sp.cell
      · simp [halfStep, hin, Ne.symm sp.cell_ne_empty]
      · simp [halfStep, hcar, hin, and_comm]
  cases sp <;> cases observed
  · exact hcur
  · change (b.mask .north).testBit (rowMajorRank w h p).val =
      decide (halfStep d .east s p = Species.north.cell)
    rw [hs .north p]
    apply Bool.eq_iff_iff.mpr
    have h := other_species_unchanged d .east s p .north (by decide) (by decide)
    exact ⟨fun he => decide_eq_true (h.mpr (of_decide_eq_true he)),
      fun he => decide_eq_true (h.mp (of_decide_eq_true he))⟩
  · change (b.mask .east).testBit (rowMajorRank w h p).val =
      decide (halfStep d .north s p = Species.east.cell)
    rw [hs .east p]
    apply Bool.eq_iff_iff.mpr
    have h := other_species_unchanged d .north s p .east (by decide) (by decide)
    exact ⟨fun he => decide_eq_true (h.mpr (of_decide_eq_true he)),
      fun he => decide_eq_true (h.mp (of_decide_eq_true he))⟩
  · exact hcur

theorem eastPhase_rep {w h : Nat} {hw : 0 < w} {hh : 0 < h}
    {r : Layout} (hr : r.Valid hw hh) {b : Board} {s : Config (Position w h)}
    (hs : Represents b s) :
    Represents (eastPhase (w*h) r b) (halfStep (eastDirection w h hw) .east s) :=
  phase_rep hr.eastNext hr.eastPrev .east hs

theorem round_rep {w h : Nat} {hw : 0 < w} {hh : 0 < h}
    {r : Layout} (hr : r.Valid hw hh) {b : Board} {s : Config (Position w h)}
    (hs : Represents b s) :
    Represents (round (w*h) r b) (torusStep w h hw hh s) :=
  phase_rep hr.northNext hr.northPrev .north (eastPhase_rep hr hs)

theorem iterate_rep {w h : Nat} {hw : 0 < w} {hh : 0 < h}
    {r : Layout} (hr : r.Valid hw hh) {b : Board} {s : Config (Position w h)}
    (hs : Represents b s) (t : Nat) :
    Represents (iterate (round (w*h) r) t b) (iterate (torusStep w h hw hh) t s) := by
  induction t with
  | zero => exact hs
  | succ t ih => exact round_rep hr ih

def same (area : Nat) (b c : Board) : Bool :=
  (b.east % 2^area == c.east % 2^area) && (b.north % 2^area == c.north % 2^area)

theorem same_iff {w h : Nat} (hw : 0 < w) {b c : Board} {s u : Config (Position w h)}
    (hs : Represents b s) (hu : Represents c u) :
    same (w*h) b c = true ↔ s = u := by
  have hmask : same (w*h) b c = true ↔ ∀ sp, b.mask sp % 2^(w*h) = c.mask sp % 2^(w*h) := by
    simp only [same, Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨he, hn⟩ sp
      cases sp <;> assumption
    · intro hh
      exact ⟨hh .east, hh .north⟩
  rw [hmask]
  constructor
  · intro he
    funext p
    have hread (sp : Species) := congrArg (fun m : Nat => m.testBit (rowMajorRank w h p).val) (he sp)
    have hval (sp : Species) : decide (s p = sp.cell) = decide (u p = sp.cell) := by
      simpa only [Nat.testBit_mod_two_pow, (rowMajorRank w h p).isLt, decide_true,
        Bool.true_and, hs sp p, hu sp p] using hread sp
    have heast := hval .east
    have hnorth := hval .north
    cases hx : s p <;> cases hy : u p <;> simp_all [Species.cell]
  · rintro rfl sp
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < w*h
    · let p := rowMajorPosition w h hw ⟨i, hi⟩
      have hp : (rowMajorRank w h p).val = i := congrArg Fin.val (rowMajorRank_position w h hw ⟨i, hi⟩)
      simp only [Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and]
      rw [← hp, hs sp p, hu sp p]
    · simp [hi]

end BML.Packed
