import BML.Enumeration

/-!
Constructive CLASSIC G1 sufficiency for every exact car count. A complete east
row blocks north cars stacked behind it; the transposed construction uses a
complete north column and east cars. The functions are total, while their jam
and exact-count guarantees state the required dimension and count hypotheses.
-/
namespace BML

/-- Fill rows from the last row downwards, and within each row from the left.
The complete last row faces east; the remaining occupied cells face north. -/
def gridlockRows (w h n : Nat) : Config (Position w h) := fun p =>
  if p.1.val + w * (h - 1 - p.2.val) < n then
    if p.2.val + 1 = h then .east else .north
  else .empty

/-- Fill columns from the last column leftwards, and within each column from
the bottom. The complete last column faces north; other cars face east. -/
def gridlockColumns (w h n : Nat) : Config (Position w h) := fun p =>
  if p.2.val + h * (w - 1 - p.1.val) < n then
    if p.1.val + 1 = w then .north else .east
  else .empty

/-- Choose the shorter complete blocking line. This definition uses no proof
arguments and can be evaluated by the independent construction replay. -/
def gridlockWith (w h n : Nat) : Config (Position w h) :=
  if w ≤ h then gridlockRows w h n else gridlockColumns w h n

theorem gridlockRows_occupied_iff (w h n : Nat) (p : Position w h) :
    gridlockRows w h n p ≠ .empty ↔ p.1.val + w * (h - 1 - p.2.val) < n := by
  by_cases hr : p.1.val + w * (h - 1 - p.2.val) < n <;>
    by_cases hy : p.2.val + 1 = h <;> simp [gridlockRows, hr, hy]

theorem gridlockColumns_occupied_iff (w h n : Nat) (p : Position w h) :
    gridlockColumns w h n p ≠ .empty ↔ p.2.val + h * (w - 1 - p.1.val) < n := by
  by_cases hr : p.2.val + h * (w - 1 - p.1.val) < n <;>
    by_cases hx : p.1.val + 1 = w <;> simp [gridlockColumns, hr, hx]

theorem gridlockRows_east_iff (w h n : Nat) (p : Position w h) :
    gridlockRows w h n p = .east ↔
      p.1.val + w * (h - 1 - p.2.val) < n ∧ p.2.val + 1 = h := by
  by_cases hr : p.1.val + w * (h - 1 - p.2.val) < n <;>
    by_cases hy : p.2.val + 1 = h <;> simp [gridlockRows, hr, hy]

theorem gridlockRows_north_iff (w h n : Nat) (p : Position w h) :
    gridlockRows w h n p = .north ↔
      p.1.val + w * (h - 1 - p.2.val) < n ∧ p.2.val + 1 ≠ h := by
  by_cases hr : p.1.val + w * (h - 1 - p.2.val) < n <;>
    by_cases hy : p.2.val + 1 = h <;>
    simp only [gridlockRows, hr, hy, ↓reduceIte] <;> simp_all

theorem gridlockColumns_east_iff (w h n : Nat) (p : Position w h) :
    gridlockColumns w h n p = .east ↔
      p.2.val + h * (w - 1 - p.1.val) < n ∧ p.1.val + 1 ≠ w := by
  by_cases hr : p.2.val + h * (w - 1 - p.1.val) < n <;>
    by_cases hx : p.1.val + 1 = w <;>
    simp only [gridlockColumns, hr, hx, ↓reduceIte] <;> simp_all

theorem gridlockColumns_north_iff (w h n : Nat) (p : Position w h) :
    gridlockColumns w h n p = .north ↔
      p.2.val + h * (w - 1 - p.1.val) < n ∧ p.1.val + 1 = w := by
  by_cases hr : p.2.val + h * (w - 1 - p.1.val) < n <;>
    by_cases hx : p.1.val + 1 = w <;> simp [gridlockColumns, hr, hx]

/-- The row construction is frozen as soon as the whole anchor row is present. -/
theorem gridlockRows_frozen (w h n : Nat) (hw : 0 < w) (hh : 0 < h)
    (hn : w ≤ n) :
    Frozen (eastDirection w h hw) (northDirection w h hh) (gridlockRows w h n) := by
  constructor
  · intro p hp
    obtain ⟨_, hy⟩ := (gridlockRows_east_iff w h n p).mp hp
    apply (gridlockRows_occupied_iff w h n _).mpr
    have hzero : h - 1 - p.2.val = 0 := by omega
    simp only [eastDirection, hzero, Nat.mul_zero, Nat.add_zero]
    have hx := (cyclicNext w hw p.1).isLt
    omega
  · intro p hp
    obtain ⟨hr, hy⟩ := (gridlockRows_north_iff w h n p).mp hp
    apply (gridlockRows_occupied_iff w h n _).mpr
    have hpy := p.2.isLt
    have hnext : p.2.val + 1 < h := by omega
    simp only [northDirection, cyclicNext, hnext, ↓reduceDIte]
    have hsub : h - 1 - (p.2.val + 1) ≤ h - 1 - p.2.val := by omega
    have hmul := Nat.mul_le_mul_left w hsub
    omega

/-- The column construction is frozen as soon as its anchor column is present. -/
theorem gridlockColumns_frozen (w h n : Nat) (hw : 0 < w) (hh : 0 < h)
    (hn : h ≤ n) :
    Frozen (eastDirection w h hw) (northDirection w h hh) (gridlockColumns w h n) := by
  constructor
  · intro p hp
    obtain ⟨hr, hx⟩ := (gridlockColumns_east_iff w h n p).mp hp
    apply (gridlockColumns_occupied_iff w h n _).mpr
    have hpx := p.1.isLt
    have hnext : p.1.val + 1 < w := by omega
    simp only [eastDirection, cyclicNext, hnext, ↓reduceDIte]
    have hsub : w - 1 - (p.1.val + 1) ≤ w - 1 - p.1.val := by omega
    have hmul := Nat.mul_le_mul_left h hsub
    omega
  · intro p hp
    obtain ⟨_, hx⟩ := (gridlockColumns_north_iff w h n p).mp hp
    apply (gridlockColumns_occupied_iff w h n _).mpr
    have hzero : w - 1 - p.1.val = 0 := by omega
    simp only [northDirection, hzero, Nat.mul_zero, Nat.add_zero]
    have hy := (cyclicNext h hh p.2).isLt
    omega

theorem gridlockRows_nonempty (w h n : Nat) (hw : 0 < w) (hh : 0 < h)
    (hn : w ≤ n) : Nonempty (gridlockRows w h n) := by
  refine ⟨(⟨0, hw⟩, ⟨h - 1, by omega⟩), ?_⟩
  apply (gridlockRows_occupied_iff w h n _).mpr
  simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
  omega

theorem gridlockColumns_nonempty (w h n : Nat) (hw : 0 < w) (hh : 0 < h)
    (hn : h ≤ n) : Nonempty (gridlockColumns w h n) := by
  refine ⟨(⟨w - 1, by omega⟩, ⟨0, hh⟩), ?_⟩
  apply (gridlockColumns_occupied_iff w h n _).mpr
  simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
  omega

theorem gridlockRows_is_jam (w h n : Nat) (hw : 0 < w) (hh : 0 < h)
    (hn : w ≤ n) :
    Jam (eastDirection w h hw) (northDirection w h hh) (gridlockRows w h n) :=
  ⟨gridlockRows_nonempty w h n hw hh hn, gridlockRows_frozen w h n hw hh hn⟩

theorem gridlockColumns_is_jam (w h n : Nat) (hw : 0 < w) (hh : 0 < h)
    (hn : h ≤ n) :
    Jam (eastDirection w h hw) (northDirection w h hh) (gridlockColumns w h n) :=
  ⟨gridlockColumns_nonempty w h n hw hh hn, gridlockColumns_frozen w h n hw hh hn⟩

theorem gridlockWith_is_jam (w h n : Nat) (hw : 0 < w) (hh : 0 < h)
    (hn : min w h ≤ n) :
    Jam (eastDirection w h hw) (northDirection w h hh) (gridlockWith w h n) := by
  by_cases hwh : w ≤ h
  · have hn' : w ≤ n := by simpa [Nat.min_eq_left hwh] using hn
    simpa [gridlockWith, hwh] using gridlockRows_is_jam w h n hw hh hn'
  · have hhw : h ≤ w := by omega
    have hn' : h ≤ n := by simpa [Nat.min_eq_right hhw] using hn
    simpa [gridlockWith, hwh] using gridlockColumns_is_jam w h n hw hh hn'

/-- The row prefix contains exactly the requested number of cars, even below
the jam threshold; the threshold is needed only for the blocking property. -/
theorem gridlockRows_carCount (w h n : Nat) (hw : 0 < w) (hn : n ≤ w * h) :
    carCount w h (gridlockRows w h n) = n :=
  carCount_of_reverseRowRank w h hw (gridlockRows w h n) n hn
    (gridlockRows_occupied_iff w h n)

theorem gridlockColumns_carCount (w h n : Nat) (hh : 0 < h) (hn : n ≤ w * h) :
    carCount w h (gridlockColumns w h n) = n :=
  carCount_of_reverseColumnRank w h hh (gridlockColumns w h n) n hn
    (gridlockColumns_occupied_iff w h n)

theorem gridlockWith_carCount (w h n : Nat) (hw : 0 < w) (hh : 0 < h)
    (hn : n ≤ w * h) : carCount w h (gridlockWith w h n) = n := by
  by_cases hwh : w ≤ h
  · simpa [gridlockWith, hwh] using gridlockRows_carCount w h n hw hn
  · simpa [gridlockWith, hwh] using gridlockColumns_carCount w h n hh hn

/-- G1 sufficiency at every exact count in the closed admissible interval. -/
theorem exists_jam_with_count (w h n : Nat) (hw : 0 < w) (hh : 0 < h)
    (hmin : min w h ≤ n) (hmax : n ≤ w * h) :
    ∃ s : Config (Position w h),
      Jam (eastDirection w h hw) (northDirection w h hh) s ∧ carCount w h s = n :=
  ⟨gridlockWith w h n, gridlockWith_is_jam w h n hw hh hmin,
    gridlockWith_carCount w h n hw hh hmax⟩

end BML
