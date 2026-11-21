import BML.Gated

/-!
The row witness exchanges coordinates and species. Transposition reverses the
order of the two CLASSIC phases, so the open gate is transferred through a
north checkpoint. On the closed gate the east phase is always blocked.
-/
namespace BML.Gated

variable {w h : Nat}

private def swapCell : Cell → Cell
  | .empty => .empty
  | .east => .north
  | .north => .east

@[simp] private theorem swapCell_empty (c : Cell) : swapCell c = .empty ↔ c = .empty := by
  cases c <;> decide

@[simp] private theorem swapCell_east (c : Cell) : swapCell c = .east ↔ c = .north := by
  cases c <;> decide

@[simp] private theorem swapCell_north (c : Cell) : swapCell c = .north ↔ c = .east := by
  cases c <;> decide

private def transpose (s : Config (Position w h)) : Config (Position h w) :=
  fun (x, y) => swapCell (s (y, x))

/-- The open row gate on a board of width `h` and height `w`. -/
def gatedRowX (hw : 4 ≤ w) (hh : 2 ≤ h) : Config (Position h w) :=
  transpose (gatedX hw hh)

/-- The closed row gate adds one east car at the origin. -/
def gatedRowY (hw : 4 ≤ w) (hh : 2 ≤ h) : Config (Position h w) :=
  transpose (gatedY hw hh)

theorem row_adds_one_east (hw : 4 ≤ w) (hh : 2 ≤ h) :
    gatedRowX hw hh (bottom hh, gate hw) = .empty ∧
    gatedRowY hw hh (bottom hh, gate hw) = .east ∧
    ∀ p, p ≠ (bottom hh, gate hw) → gatedRowY hw hh p = gatedRowX hw hh p := by
  obtain ⟨hx, hy, hsame⟩ := adds_one_north hw hh
  refine ⟨by simpa [gatedRowX, transpose] using hx, by simpa [gatedRowY, transpose] using hy, ?_⟩
  intro p hp
  have hz : p.swap ≠ (gate hw, bottom hh) := by
    intro he
    apply hp
    exact congrArg Prod.swap he
  exact congrArg swapCell (hsame p.swap hz)

private abbrev east (hw : 4 ≤ w) := eastDirection w h (by omega)
private abbrev north (hh : 2 ≤ h) := northDirection w h (by omega)
private abbrev east' (hh : 2 ≤ h) := eastDirection h w (by omega)
private abbrev north' (hw : 4 ≤ w) := northDirection h w (by omega)
private abbrev round (hw : 4 ≤ w) (hh : 2 ≤ h) := torusStep w h (by omega) (by omega)
private abbrev round' (hw : 4 ≤ w) (hh : 2 ≤ h) := torusStep h w (by omega) (by omega)
private abbrev reversed (hw : 4 ≤ w) (hh : 2 ≤ h) (s : Config (Position w h)) :=
  halfStep (east hw) .east (halfStep (north hh) .north s)

private theorem transpose_east (hw : 4 ≤ w) (s : Config (Position w h)) :
    transpose (halfStep (east hw) .east s) = halfStep (north' hw) .north (transpose s) := by
  funext ⟨x, y⟩
  simp only [transpose, halfStep, northDirection, eastDirection, Species.cell, swapCell_north,
    swapCell_empty]
  split
  · by_cases hz : s (cyclicNext w (by omega) y, x) = .empty <;> simp [hz, swapCell]
  · by_cases hz : s (y, x) = .empty ∧ s (cyclicPrev w (by omega) y, x) = .east <;>
      simp [hz, swapCell]

private theorem transpose_north (hh : 2 ≤ h) (s : Config (Position w h)) :
    transpose (halfStep (north hh) .north s) = halfStep (east' hh) .east (transpose s) := by
  funext ⟨x, y⟩
  simp only [transpose, halfStep, eastDirection, northDirection, Species.cell, swapCell_east,
    swapCell_empty]
  split
  · by_cases hz : s (y, cyclicNext h (by omega) x) = .empty <;> simp [hz, swapCell]
  · by_cases hz : s (y, x) = .empty ∧ s (y, cyclicPrev h (by omega) x) = .north <;>
      simp [hz, swapCell]

private theorem transpose_reversed (hw : 4 ≤ w) (hh : 2 ≤ h)
    (s : Config (Position w h)) : transpose (reversed hw hh s) = round' hw hh (transpose s) := by
  change transpose (halfStep (east hw) .east (halfStep (north hh) .north s)) = _
  rw [transpose_east, transpose_north]
  rfl

private theorem transpose_iterate (hw : 4 ≤ w) (hh : 2 ≤ h)
    (s : Config (Position w h)) (t : Nat) :
    transpose (iterate (reversed hw hh) t s) = iterate (round' hw hh) t (transpose s) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [iterate, ← ih, transpose_reversed]

private theorem transpose_jam (hw : 4 ≤ w) (hh : 2 ≤ h)
    {s : Config (Position w h)} (hj : Jam (east hw) (north hh) s) :
    Jam (east' hh) (north' hw) (transpose s) := by
  apply (jam_iff_nonempty_fixed _ _ _).mpr
  obtain ⟨p, hp⟩ := hj.1
  refine ⟨⟨p.swap, by simpa [transpose] using hp⟩, ?_⟩
  change round' hw hh (transpose s) = _
  rw [← transpose_reversed]
  change transpose (halfStep (east hw) .east (halfStep (north hh) .north s)) = _
  rw [halfStep_eq_of_blocked _ _ _ hj.2.2, halfStep_eq_of_blocked _ _ _ hj.2.1]

private theorem north_checkpoint (hw : 4 ≤ w) (hh : 2 ≤ h)
    (s : Config (Position w h)) (t : Nat) :
    halfStep (north hh) .north (iterate (reversed hw hh) t s) =
      iterate (round hw hh) t (halfStep (north hh) .north s) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change round hw hh (halfStep (north hh) .north (iterate (reversed hw hh) t s)) =
      round hw hh (iterate (round hw hh) t (halfStep (north hh) .north s))
    rw [ih]

/-- A jam at a north checkpoint is already fixed under the following east phase. -/
theorem gatedRowX_eventually_jams (hw : 4 ≤ w) (hh : 2 ≤ h) :
    EventuallyJammed (east' hh) (north' hw) (gatedRowX hw hh) := by
  obtain ⟨t, hj⟩ := gatedX_after_north_eventually_jams hw hh
  refine ⟨t+1, ?_⟩
  change Jam (east' hh) (north' hw) (iterate (round' hw hh) (t+1) (transpose (gatedX hw hh)))
  rw [← transpose_iterate]
  apply transpose_jam hw hh
  change Jam (east hw) (north hh)
    (halfStep (east hw) .east (halfStep (north hh) .north (iterate (reversed hw hh) t (gatedX hw hh))))
  rw [north_checkpoint]
  exact (halfStep_eq_of_blocked _ _ _ hj.2.1).symm ▸ hj

private theorem reversed_closed (hw : 4 ≤ w) (hh : 2 ≤ h) (t : Nat) :
    iterate (reversed hw hh) t (gatedY hw hh) = iterate (round hw hh) t (gatedY hw hh) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hn : halfStep (north hh) .north (iterate (round hw hh) t (gatedY hw hh)) =
        iterate (round hw hh) (t+1) (gatedY hw hh) := by
      change _ = halfStep (north hh) .north (halfStep (east hw) .east
        (iterate (round hw hh) t (gatedY hw hh)))
      rw [halfStep_eq_of_blocked _ _ _ (gatedY_east_blocked hw hh t)]
    change halfStep (east hw) .east (halfStep (north hh) .north
      (iterate (reversed hw hh) t (gatedY hw hh))) = _
    rw [ih, hn]
    exact halfStep_eq_of_blocked _ _ _ (gatedY_east_blocked hw hh (t+1))

theorem gatedRow_freeCar_canMove (hw : 4 ≤ w) (hh : 2 ≤ h) (t : Nat) :
    CanMove (east' hh) .east (iterate (round' hw hh) t (gatedRowY hw hh))
      (freeCar hw hh t).swap := by
  change CanMove (east' hh) .east (iterate (round' hw hh) t (transpose (gatedY hw hh))) _
  rw [← transpose_iterate, reversed_closed]
  have hm := freeCar_canMove hw hh t
  rw [halfStep_eq_of_blocked _ _ _ (gatedY_east_blocked hw hh t)] at hm
  exact ⟨by simpa [transpose, Species.cell] using hm.1,
    by simpa [transpose, northDirection, eastDirection] using hm.2⟩

theorem gatedRow_freeCar_trace (hw : 4 ≤ w) (hh : 2 ≤ h) (t : Nat) :
    carTrace (east' hh) (north' hw) .east (gatedRowY hw hh) t (freeCar hw hh 0).swap =
      (freeCar hw hh t).swap := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [carTrace, ih, roundTransport, transport]
    change (if CanMove (east' hh) .east (iterate (round' hw hh) t (gatedRowY hw hh))
      (freeCar hw hh t).swap then (east' hh).next (freeCar hw hh t).swap
      else (freeCar hw hh t).swap) = _
    simp only [gatedRow_freeCar_canMove hw hh t, ↓reduceIte]
    rfl

/-- Theorem U's row witness under the actual east-first convention. -/
theorem gatedRow_genuine (hw : 4 ≤ w) (hh : 2 ≤ h) :
    EventuallyJammed (east' hh) (north' hw) (gatedRowX hw hh) ∧
    (∀ t, ¬ Jam (east' hh) (north' hw) (iterate (round' hw hh) t (gatedRowY hw hh))) ∧
    gatedRowX hw hh (freeCar hw hh 0).swap = .east ∧
    ∀ t, RoundCanMove (east' hh) (north' hw) .east (iterate (round' hw hh) t (gatedRowY hw hh))
      (carTrace (east' hh) (north' hw) .east (gatedRowY hw hh) t (freeCar hw hh 0).swap) := by
  refine ⟨gatedRowX_eventually_jams hw hh, ?_, ?_, ?_⟩
  · intro t hj
    have hm := gatedRow_freeCar_canMove hw hh t
    exact hj.2.1 _ hm.1 hm.2
  · simpa [gatedRowX, transpose] using freeCar_is_original hw hh
  · intro t
    rw [gatedRow_freeCar_trace hw hh t]
    exact gatedRow_freeCar_canMove hw hh t

/-- One added car changes an eventual jam into an orbit on which a specific
original car moves arbitrarily late. -/
def GenuineUnjamming (hw : 0 < w) (hh : 0 < h) (x y : Config (Position w h)) : Prop :=
  let e := eastDirection w h hw
  let n := northDirection w h hh
  let f := torusStep w h hw hh
  (∃ p sp, x p = .empty ∧ y p = Species.cell sp ∧ ∀ q, q ≠ p → y q = x q) ∧
    EventuallyJammed e n x ∧ (∀ t, ¬ Jam e n (iterate f t y)) ∧
    ∃ p sp, x p = Species.cell sp ∧ y p = Species.cell sp ∧
      ∀ start, ∃ t, start ≤ t ∧
        RoundCanMove e n sp (iterate f t y) (carTrace e n sp y t p)

private theorem genuine_of_every_round (hw : 0 < w) (hh : 0 < h)
    {x y : Config (Position w h)} {sp : Species} {p : Position w h}
    (ha : ∃ q added, x q = .empty ∧ y q = Species.cell added ∧ ∀ r, r ≠ q → y r = x r)
    (hj : EventuallyJammed (eastDirection w h hw) (northDirection w h hh) x)
    (hn : ∀ t, ¬ Jam (eastDirection w h hw) (northDirection w h hh) (iterate (torusStep w h hw hh) t y))
    (hp : x p = sp.cell)
    (hm : ∀ t, RoundCanMove (eastDirection w h hw) (northDirection w h hh) sp
      (iterate (torusStep w h hw hh) t y)
      (carTrace (eastDirection w h hw) (northDirection w h hh) sp y t p)) :
    GenuineUnjamming hw hh x y :=
  ⟨ha, hj, hn, p, sp, hp, roundCanMove_source_car _ _ _ _ _ (hm 0),
    fun t => ⟨t, Nat.le_refl t, hm t⟩⟩

/-- The sufficient dimension condition in Theorem U, for both orientations. -/
theorem exists_genuine_unjamming (hw : 2 ≤ w) (hh : 2 ≤ h) (hmax : 4 ≤ max w h) :
    ∃ x y, GenuineUnjamming (by omega : 0 < w) (by omega : 0 < h) x y := by
  by_cases hw' : 4 ≤ w
  · obtain ⟨hj, hn, hp, hm⟩ := gated_genuine hw' hh
    refine ⟨gatedX hw' hh, gatedY hw' hh, genuine_of_every_round (by omega) (by omega) ?_ hj hn hp hm⟩
    exact ⟨(gate hw', bottom hh), .north, adds_one_north hw' hh⟩
  · have hh' : 4 ≤ h := by omega
    obtain ⟨hj, hn, hp, hm⟩ := gatedRow_genuine hh' hw
    refine ⟨gatedRowX hh' hw, gatedRowY hh' hw,
      genuine_of_every_round (by omega) (by omega) ?_ hj hn hp hm⟩
    exact ⟨(bottom hw, gate hh'), .east, row_adds_one_east hh' hw⟩

end BML.Gated
