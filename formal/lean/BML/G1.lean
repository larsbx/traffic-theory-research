import BML.Torus
import BML.Arithmetic

/-!
# G1: least gridlock on the W×H torus

In a nonempty frozen configuration, every car is blocked by the car in front of it
(east for an east car, north for a north car). Following blockers from any car gives a
walk through occupied cells whose coordinates advance by unit east/north steps.

If the walk revisits a cell after `j - i` steps, those steps form a closed nonnegative
winding, so `min W H ≤ j - i` by `winding_length_lower_bound`. Hence the first
`min W H` cells of the walk are pairwise distinct cars (`jam_has_min_side_cars`).

The bound is attained: a full east row and a full north column are jams
(`fullRow_jam`, `fullColumn_jam`), occupying exactly one row or column.
-/
namespace BML

theorem cyclicNext_val (n : Nat) (hn : 0 < n) (i : Fin n) :
    (cyclicNext n hn i).val = (i.val + 1) % n := by
  by_cases h : i.val + 1 < n
  · unfold cyclicNext
    rw [dif_pos h]
    exact (Nat.mod_eq_of_lt h).symm
  · unfold cyclicNext
    rw [dif_neg h]
    have hi := i.isLt
    have hn' : i.val + 1 = n := by omega
    show 0 = (i.val + 1) % n
    rw [hn', Nat.mod_self]

/-- The cell directly in front of the car at `p`. -/
def blocker (w h : Nat) (hw : 0 < w) (hh : 0 < h) (s : Config (Position w h))
    (p : Position w h) : Position w h :=
  if s p = .east then (eastDirection w h hw).next p else (northDirection w h hh).next p

/-- The `i`-th cell of the blocker walk from `c`. -/
def walk (w h : Nat) (hw : 0 < w) (hh : 0 < h) (s : Config (Position w h))
    (c : Position w h) (i : Nat) : Position w h :=
  iterate (blocker w h hw hh s) i c

/-- Number of east steps among the first `i` steps of the walk. -/
def eastSteps (w h : Nat) (hw : 0 < w) (hh : 0 < h) (s : Config (Position w h))
    (c : Position w h) : Nat → Nat
  | 0 => 0
  | i+1 => eastSteps w h hw hh s c i + (if s (walk w h hw hh s c i) = .east then 1 else 0)

theorem blocker_occupied (w h : Nat) (hw : 0 < w) (hh : 0 < h) (s : Config (Position w h))
    (hfz : Frozen (eastDirection w h hw) (northDirection w h hh) s)
    (q : Position w h) (hq : s q ≠ .empty) : s (blocker w h hw hh s q) ≠ .empty := by
  unfold blocker
  by_cases he : s q = .east
  · rw [if_pos he]
    exact hfz.1 q he
  · rw [if_neg he]
    have hn : s q = .north := by
      cases hsq : s q with
      | empty => exact absurd hsq hq
      | east => exact absurd hsq he
      | north => rfl
    exact hfz.2 q hn

theorem walk_occupied (w h : Nat) (hw : 0 < w) (hh : 0 < h) (s : Config (Position w h))
    (hfz : Frozen (eastDirection w h hw) (northDirection w h hh) s)
    (c : Position w h) (hc : s c ≠ .empty) (i : Nat) :
    s (walk w h hw hh s c i) ≠ .empty := by
  induction i with
  | zero => exact hc
  | succ i ih => exact blocker_occupied w h hw hh s hfz _ ih

theorem eastSteps_le (w h : Nat) (hw : 0 < w) (hh : 0 < h) (s : Config (Position w h))
    (c : Position w h) (i : Nat) : eastSteps w h hw hh s c i ≤ i := by
  induction i with
  | zero => exact Nat.zero_le 0
  | succ i ih =>
    show eastSteps w h hw hh s c i +
      (if s (walk w h hw hh s c i) = .east then 1 else 0) ≤ i + 1
    split <;> omega

theorem eastSteps_window (w h : Nat) (hw : 0 < w) (hh : 0 < h) (s : Config (Position w h))
    (c : Position w h) (i k : Nat) :
    eastSteps w h hw hh s c i ≤ eastSteps w h hw hh s c (i + k) ∧
    eastSteps w h hw hh s c (i + k) ≤ eastSteps w h hw hh s c i + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : eastSteps w h hw hh s c (i + (k + 1)) = eastSteps w h hw hh s c (i + k) +
        (if s (walk w h hw hh s c (i + k)) = .east then 1 else 0) := rfl
    rw [hstep]
    split <;> omega

/-- One blocker step adds 1 to exactly one coordinate. -/
theorem blocker_coords (w h : Nat) (hw : 0 < w) (hh : 0 < h) (s : Config (Position w h))
    (q : Position w h) (X Y e k : Nat)
    (hx : q.1.val = (X + e) % w) (hy : q.2.val = (Y + k) % h) :
    (blocker w h hw hh s q).1.val = (X + (e + (if s q = .east then 1 else 0))) % w ∧
    (blocker w h hw hh s q).2.val = (Y + (k + (if s q = .east then 0 else 1))) % h := by
  by_cases hq : s q = .east
  · simp only [if_pos hq]
    have hb : blocker w h hw hh s q = (cyclicNext w hw q.1, q.2) := by
      unfold blocker
      rw [if_pos hq]
      try rfl
    rw [hb]
    refine ⟨?_, ?_⟩
    · show (cyclicNext w hw q.1).val = _
      rw [cyclicNext_val, hx, Nat.mod_add_mod, Nat.add_assoc]
    · show q.2.val = _
      rw [Nat.add_zero]
      exact hy
  · simp only [if_neg hq]
    have hb : blocker w h hw hh s q = (q.1, cyclicNext h hh q.2) := by
      unfold blocker
      rw [if_neg hq]
      try rfl
    rw [hb]
    refine ⟨?_, ?_⟩
    · show q.1.val = _
      rw [Nat.add_zero]
      exact hx
    · show (cyclicNext h hh q.2).val = _
      rw [cyclicNext_val, hy, Nat.mod_add_mod, Nat.add_assoc]

/-- Coordinates of the walk: `eastSteps` east steps and the rest north steps. -/
theorem walk_coords (w h : Nat) (hw : 0 < w) (hh : 0 < h) (s : Config (Position w h))
    (c : Position w h) (i : Nat) :
    (walk w h hw hh s c i).1.val = (c.1.val + eastSteps w h hw hh s c i) % w ∧
    (walk w h hw hh s c i).2.val =
      (c.2.val + (i - eastSteps w h hw hh s c i)) % h := by
  induction i with
  | zero =>
    simp only [walk, iterate, eastSteps, Nat.add_zero, Nat.sub_zero]
    exact ⟨(Nat.mod_eq_of_lt c.1.isLt).symm, (Nat.mod_eq_of_lt c.2.isLt).symm⟩
  | succ i ih =>
    obtain ⟨hx, hy⟩ := ih
    have hle := eastSteps_le w h hw hh s c i
    have key := blocker_coords w h hw hh s (walk w h hw hh s c i) c.1.val c.2.val
      (eastSteps w h hw hh s c i) (i - eastSteps w h hw hh s c i) hx hy
    have hW : walk w h hw hh s c (i + 1) =
        blocker w h hw hh s (walk w h hw hh s c i) := rfl
    have hE : eastSteps w h hw hh s c (i + 1) = eastSteps w h hw hh s c i +
        (if s (walk w h hw hh s c i) = .east then 1 else 0) := rfl
    have harith : (i - eastSteps w h hw hh s c i) +
        (if s (walk w h hw hh s c i) = .east then 0 else 1) =
        i + 1 - (eastSteps w h hw hh s c i +
          (if s (walk w h hw hh s c i) = .east then 1 else 0)) := by
      by_cases hq : s (walk w h hw hh s c i) = .east
      · simp only [if_pos hq] <;> omega
      · simp only [if_neg hq] <;> omega
    rw [hW, hE]
    refine ⟨key.1, ?_⟩
    rw [key.2, harith]

/-- A walk that returns to a cell has travelled at least `min W H` steps. -/
theorem walk_period_ge (w h : Nat) (hw : 0 < w) (hh : 0 < h) (s : Config (Position w h))
    (c : Position w h) (i j : Nat) (hij : i < j)
    (heq : walk w h hw hh s c i = walk w h hw hh s c j) : min w h ≤ j - i := by
  obtain ⟨hxi, hyi⟩ := walk_coords w h hw hh s c i
  obtain ⟨hxj, hyj⟩ := walk_coords w h hw hh s c j
  obtain ⟨hlo, hhi⟩ := eastSteps_window w h hw hh s c i (j - i)
  have hj : i + (j - i) = j := by omega
  rw [hj] at hlo hhi
  have hlei := eastSteps_le w h hw hh s c i
  have hlej := eastSteps_le w h hw hh s c j
  have hx : (c.1.val + eastSteps w h hw hh s c i) % w =
      (c.1.val + eastSteps w h hw hh s c j) % w := by
    rw [← hxi, ← hxj, heq]
  have hy : (c.2.val + (i - eastSteps w h hw hh s c i)) % h =
      (c.2.val + (j - eastSteps w h hw hh s c j)) % h := by
    rw [← hyi, ← hyj, heq]
  have ha : w ∣ (eastSteps w h hw hh s c j - eastSteps w h hw hh s c i) := by
    have hm := Nat.sub_mod_eq_zero_of_mod_eq hx.symm
    have hd : c.1.val + eastSteps w h hw hh s c j - (c.1.val + eastSteps w h hw hh s c i) =
        eastSteps w h hw hh s c j - eastSteps w h hw hh s c i := by omega
    rw [hd] at hm
    exact Nat.dvd_of_mod_eq_zero hm
  have hb : h ∣ ((j - eastSteps w h hw hh s c j) - (i - eastSteps w h hw hh s c i)) := by
    have hm := Nat.sub_mod_eq_zero_of_mod_eq hy.symm
    have hd : c.2.val + (j - eastSteps w h hw hh s c j) -
        (c.2.val + (i - eastSteps w h hw hh s c i)) =
        (j - eastSteps w h hw hh s c j) - (i - eastSteps w h hw hh s c i) := by omega
    rw [hd] at hm
    exact Nat.dvd_of_mod_eq_zero hm
  have hwind := winding_length_lower_bound w h _ _ ha hb (by omega)
  omega

/-- **G1 lower bound.** A jam on the W×H torus contains at least `min W H` distinct cars. -/
theorem jam_has_min_side_cars (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h))
    (hjam : Jam (eastDirection w h hw) (northDirection w h hh) s) :
    ∃ f : Fin (min w h) → Position w h,
      (∀ i j, f i = f j → i = j) ∧ ∀ i, s (f i) ≠ .empty := by
  obtain ⟨hne, hfz⟩ := hjam
  obtain ⟨c, hc⟩ := hne
  refine ⟨fun i => walk w h hw hh s c i.val, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    rcases Nat.lt_trichotomy i.val j.val with hlt | hval | hgt
    · have hp := walk_period_ge w h hw hh s c i.val j.val hlt hij
      have hj := j.isLt
      omega
    · exact hval
    · have hp := walk_period_ge w h hw hh s c j.val i.val hgt hij.symm
      have hi := i.isLt
      omega
  · intro i
    exact walk_occupied w h hw hh s hfz c hc i.val

/-- A full row of east cars at `y = 0`; every other cell empty. -/
def fullRow (w h : Nat) : Config (Position w h) := fun p =>
  if p.2.val = 0 then .east else .empty

/-- A full column of north cars at `x = 0`; every other cell empty. -/
def fullColumn (w h : Nat) : Config (Position w h) := fun p =>
  if p.1.val = 0 then .north else .empty

theorem fullRow_occupied_iff (w h : Nat) (p : Position w h) :
    fullRow w h p ≠ .empty ↔ p.2.val = 0 := by
  unfold fullRow
  by_cases h0 : p.2.val = 0 <;> simp [h0]

theorem fullColumn_occupied_iff (w h : Nat) (p : Position w h) :
    fullColumn w h p ≠ .empty ↔ p.1.val = 0 := by
  unfold fullColumn
  by_cases h0 : p.1.val = 0 <;> simp [h0]

/-- **G1 tightness (width).** A full east row is a jam occupying exactly the row `y = 0`. -/
theorem fullRow_jam (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    Jam (eastDirection w h hw) (northDirection w h hh) (fullRow w h) := by
  refine ⟨⟨(⟨0, hw⟩, ⟨0, hh⟩), ?_⟩, ?_, ?_⟩
  · simp [fullRow]
  · intro p hp
    show fullRow w h (cyclicNext w hw p.1, p.2) ≠ .empty
    simp only [fullRow] at hp ⊢
    by_cases h0 : p.2.val = 0
    · simp [h0]
    · simp [h0, Species.cell] at hp
  · intro p hp
    simp only [fullRow] at hp
    by_cases h0 : p.2.val = 0
    · simp [h0, Species.cell] at hp
    · simp [h0, Species.cell] at hp

/-- **G1 tightness (height).** A full north column is a jam occupying exactly `x = 0`. -/
theorem fullColumn_jam (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    Jam (eastDirection w h hw) (northDirection w h hh) (fullColumn w h) := by
  refine ⟨⟨(⟨0, hw⟩, ⟨0, hh⟩), ?_⟩, ?_, ?_⟩
  · simp [fullColumn]
  · intro p hp
    simp only [fullColumn] at hp
    by_cases h0 : p.1.val = 0
    · simp [h0, Species.cell] at hp
    · simp [h0, Species.cell] at hp
  · intro p hp
    show fullColumn w h (p.1, cyclicNext h hh p.2) ≠ .empty
    simp only [fullColumn] at hp ⊢
    by_cases h0 : p.1.val = 0
    · simp [h0]
    · simp [h0, Species.cell] at hp

end BML
