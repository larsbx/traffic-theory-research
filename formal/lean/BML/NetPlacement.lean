import BML.NetMixed

/-!
# How the least gridlock depends on where the roundabouts are (Corollary MX-E)

On the `w × h` torus with `k` roundabouts, write `w' = (1 + ℓ)·w` and
`h' = (1 + ℓ)·h` for the junction-and-link length of a row and a column.

* `exists_light_row`, `exists_light_col`: some row has at most `⌊k/h⌋`
  roundabouts and some column at most `⌊k/w⌋`; so every placement has a
  gridlock with at most `min(w' + ⌊k/h⌋, h' + ⌊k/w⌋)` cars (`best_bound`);
* `row_heavy`, `col_heavy`: every row has at least `k − w(h−1)` roundabouts
  and every column at least `k − h(w−1)`; so every gridlock of every placement
  has at least `min(w' + (k − w(h−1)), h' + (k − h(w−1)))` cars (`worst_bound`);
* `worst_attained`: some placement of `k` roundabouts has a gridlock with that
  many cars.
-/
namespace BML.Net

/-! ## Sums of natural numbers over lists -/

theorem length_mul_le_sum {α : Type} (l : List α) (f : α → Nat) (m : Nat)
    (h : ∀ a, a ∈ l → m ≤ f a) : l.length * m ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.succ_mul]
    have := ih fun b hb => h b (List.mem_cons_of_mem a hb)
    have := h a List.mem_cons_self
    omega

theorem sum_le_length_mul {α : Type} (l : List α) (f : α → Nat) (M : Nat)
    (h : ∀ a, a ∈ l → f a ≤ M) : (l.map f).sum ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.succ_mul]
    have := ih fun b hb => h b (List.mem_cons_of_mem a hb)
    have := h a List.mem_cons_self
    omega

/-- One term plus a bound on the others bounds the sum. -/
theorem sum_le_one_add {α : Type} (l : List α) (f : α → Nat) (M : Nat) {a : α} (ha : a ∈ l)
    (h : ∀ b, b ∈ l → f b ≤ M) : (l.map f).sum ≤ f a + (l.length - 1) * M := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_sub_cancel]
    rcases List.mem_cons.mp ha with rfl | ha'
    · have := sum_le_length_mul l f M fun c hc => h c (List.mem_cons_of_mem _ hc)
      omega
    · have hl : 0 < l.length := List.length_pos_of_mem ha'
      have := ih ha' fun c hc => h c (List.mem_cons_of_mem _ hc)
      have := h b List.mem_cons_self
      have e : l.length * M = (l.length - 1) * M + M := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hl]
      omega

/-- Some term is at most the average. -/
theorem exists_le_avg {α : Type} (l : List α) (f : α → Nat) (hl : 0 < l.length) :
    ∃ a, a ∈ l ∧ f a ≤ (l.map f).sum / l.length := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ a, a ∈ l → (l.map f).sum / l.length + 1 ≤ f a := by
    intro a ha
    apply Classical.byContradiction
    intro hlt
    exact hno ⟨a, ha, by omega⟩
  have := length_mul_le_sum l f _ hall
  have hdm := Nat.div_add_mod (l.map f).sum l.length
  have hmod := Nat.mod_lt (l.map f).sum hl
  rw [Nat.mul_add, Nat.mul_one] at this
  omega

section Torus

variable {w h : Nat} {hw : 0 < w} {hh : 0 < h} {ring : Position w h → Bool} {link : Bool}

def rowCount (ring : Position w h → Bool) (y : Fin h) : Nat :=
  ((List.finRange w).filter fun x => ring (x, y)).length

def colCount (ring : Position w h → Bool) (x : Fin w) : Nat :=
  ((List.finRange h).filter fun y => ring (x, y)).length

theorem rowCount_le (y : Fin h) : rowCount ring y ≤ w := by
  unfold rowCount
  simpa using List.length_filter_le (fun x => ring (x, y)) (List.finRange w)

theorem colCount_le (x : Fin w) : colCount ring x ≤ h := by
  unfold colCount
  simpa using List.length_filter_le (fun y => ring (x, y)) (List.finRange h)

/-- The roundabouts, counted row by row. -/
theorem roundabouts_rows : roundabouts ring = ((List.finRange h).map (rowCount ring)).sum := by
  unfold roundabouts positions
  rw [List.filter_flatMap, List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro y _
  rw [List.filter_map, List.length_map]
  rfl

def columnPositions (w h : Nat) : List (Position w h) :=
  (List.finRange w).flatMap fun x => (List.finRange h).map fun y => (x, y)

theorem columnPositions_nodup (w h : Nat) : (columnPositions w h).Nodup := by
  unfold columnPositions
  refine List.pairwise_flatMap.mpr ⟨fun x _ => ?_, ?_⟩
  · exact List.pairwise_map.mpr ((List.nodup_finRange h).imp fun hne heq => hne (by simpa using heq))
  · refine (List.nodup_finRange w).imp fun {a b} hne p hp q hq => ?_
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hp
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hq
    intro heq
    exact hne (congrArg Prod.fst heq)

theorem mem_columnPositions (p : Position w h) : p ∈ columnPositions w h :=
  List.mem_flatMap.mpr ⟨p.1, List.mem_finRange _, List.mem_map.mpr ⟨p.2, List.mem_finRange _, rfl⟩⟩

/-- The roundabouts, counted column by column. -/
theorem roundabouts_cols : roundabouts ring = ((List.finRange w).map (colCount ring)).sum := by
  have heq : roundabouts ring = ((columnPositions w h).filter ring).length := by
    apply Nat.le_antisymm
    · exact length_le_of_injOn _ _ ((positions_nodup w h).sublist List.filter_sublist)
        id (fun _ _ _ _ h => h)
        (fun p hp => List.mem_filter.mpr ⟨mem_columnPositions p, (List.mem_filter.mp hp).2⟩)
    · exact length_le_of_injOn _ _
        ((columnPositions_nodup w h).sublist List.filter_sublist) id (fun _ _ _ _ h => h)
        (fun p hp => List.mem_filter.mpr ⟨mem_positions w h p, (List.mem_filter.mp hp).2⟩)
  rw [heq]
  unfold columnPositions
  rw [List.filter_flatMap, List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro x _
  rw [List.filter_map, List.length_map]
  rfl

/-- Some row has at most `⌊k/h⌋` roundabouts. -/
theorem exists_light_row (hh : 0 < h) : ∃ y, rowCount ring y ≤ roundabouts ring / h := by
  obtain ⟨y, _, hy⟩ := exists_le_avg (List.finRange h) (rowCount ring) (by simpa using hh)
  exact ⟨y, by simpa [← roundabouts_rows] using hy⟩

theorem exists_light_col (hw : 0 < w) : ∃ x, colCount ring x ≤ roundabouts ring / w := by
  obtain ⟨x, _, hx⟩ := exists_le_avg (List.finRange w) (colCount ring) (by simpa using hw)
  exact ⟨x, by simpa [← roundabouts_cols] using hx⟩

/-- Every row has at least `k − w(h−1)` roundabouts. -/
theorem row_heavy (y : Fin h) : roundabouts ring - w * (h - 1) ≤ rowCount ring y := by
  have := sum_le_one_add (List.finRange h) (rowCount ring) w (List.mem_finRange y)
    fun y' _ => rowCount_le y'
  rw [← roundabouts_rows, List.length_finRange, Nat.mul_comm] at this
  omega

theorem col_heavy (x : Fin w) : roundabouts ring - h * (w - 1) ≤ colCount ring x := by
  have := sum_le_one_add (List.finRange w) (colCount ring) h (List.mem_finRange x)
    fun x' _ => colCount_le x'
  rw [← roundabouts_cols, List.length_finRange, Nat.mul_comm] at this
  omega

/-- The junction-and-link length of a row and of a column. -/
def rowBase (w : Nat) (link : Bool) : Nat := w + (if link then w else 0)
def colBase (h : Nat) (link : Bool) : Nat := h + (if link then h else 0)

theorem rowStreet_length' (y : Fin h) :
    (rowStreet ring link y).length = rowBase w link + rowCount ring y := by
  rw [rowStreet_length]; rfl

theorem colStreet_length' (x : Fin w) :
    (colStreet ring link x).length = colBase h link + colCount ring x := by
  rw [colStreet_length]; rfl

/-- **MX-E, best case bound.** Every placement has a gridlock with at most
`min(w' + ⌊k/h⌋, h' + ⌊k/w⌋)` cars. -/
theorem best_bound :
    ∃ s : Config (Grid w h) Species, Stuck (mixed (torus hw hh ring link)) s ∧
      (∃ c, (s c).isSome = true) ∧
      carCount s ≤ min (rowBase w link + roundabouts ring / h) (colBase h link + roundabouts ring / w) := by
  obtain ⟨y, hy⟩ := exists_light_row (ring := ring) hh
  obtain ⟨x, hx⟩ := exists_light_col (ring := ring) hw
  have hcells := gridCells_length (ring := ring) (link := link)
  have hwh : w ≤ w * h := Nat.le_mul_of_pos_right w hh
  have hhw : h ≤ w * h := by rw [Nat.mul_comm]; exact Nat.le_mul_of_pos_right h hw
  have hdh := Nat.div_le_self (roundabouts ring) h
  have hdw := Nat.div_le_self (roundabouts ring) w
  by_cases hmin : rowBase w link + roundabouts ring / h ≤ colBase h link + roundabouts ring / w
  · obtain ⟨s, hs, hne, hc⟩ := (gridlock_count_iff (hw := hw) (hh := hh) (ring := ring) (link := link)
      (rowStreet ring link y).length).mpr ⟨Or.inl ⟨y, Nat.le_refl _⟩, by
        rw [rowStreet_length', hcells]; have := rowCount_le (ring := ring) y
        cases link <;> simp [rowBase] <;> omega⟩
    refine ⟨s, hs, hne, ?_⟩
    rw [hc, rowStreet_length', Nat.min_eq_left hmin]
    omega
  · obtain ⟨s, hs, hne, hc⟩ := (gridlock_count_iff (hw := hw) (hh := hh) (ring := ring) (link := link)
      (colStreet ring link x).length).mpr ⟨Or.inr ⟨x, Nat.le_refl _⟩, by
        rw [colStreet_length', hcells]; have := colCount_le (ring := ring) x
        cases link <;> simp [colBase] <;> omega⟩
    refine ⟨s, hs, hne, ?_⟩
    rw [hc, colStreet_length', Nat.min_eq_right (by omega)]
    omega

/-- **MX-E, worst case bound.** Every gridlock of every placement has at least
`min(w' + (k − w(h−1)), h' + (k − h(w−1)))` cars. -/
theorem worst_bound {s : Config (Grid w h) Species} (hs : Stuck (mixed (torus hw hh ring link)) s)
    (hne : ∃ c, (s c).isSome = true) :
    min (rowBase w link + (roundabouts ring - w * (h - 1)))
        (colBase h link + (roundabouts ring - h * (w - 1))) ≤ carCount s := by
  rcases stuck_carCount_ge_street hs hne with ⟨y, hy⟩ | ⟨x, hx⟩
  · rw [rowStreet_length'] at hy
    have := row_heavy (ring := ring) y
    omega
  · rw [colStreet_length'] at hx
    have := col_heavy (ring := ring) x
    omega

end Torus

section Attain

variable {w h : Nat}

/-! ## Attaining the worst case -/

/-- `#{x < w : x < m} = min w m`. -/
theorem fin_count_lt (pw : 0 < w) (m : Nat) :
    ((List.finRange w).filter fun x => decide (x.val < m)).length = min w m := by
  apply Nat.le_antisymm
  · have := length_le_of_injOn ((List.finRange w).filter fun x => decide (x.val < m))
      (List.range (min w m))
      ((List.nodup_finRange w).sublist List.filter_sublist) (fun x : Fin w => x.val)
      (fun a _ b _ hab => Fin.ext hab)
      (fun x hx => by
        have := of_decide_eq_true (List.mem_filter.mp hx).2
        exact List.mem_range.mpr (Nat.lt_min.mpr ⟨x.isLt, this⟩))
    simpa using this
  · let back : Nat → Fin w := fun i => if hi : i < w then ⟨i, hi⟩ else ⟨0, pw⟩
    have := length_le_of_injOn (List.range (min w m))
      ((List.finRange w).filter fun x => decide (x.val < m)) List.nodup_range back
      (fun a ha b hb hab => by
        have ha' := Nat.lt_min.mp (List.mem_range.mp ha)
        have hb' := Nat.lt_min.mp (List.mem_range.mp hb)
        simpa [back, ha'.1, hb'.1] using hab)
      (fun i hi => by
        have hi' := Nat.lt_min.mp (List.mem_range.mp hi)
        refine List.mem_filter.mpr ⟨List.mem_finRange _, ?_⟩
        simp [back, hi'.1, hi'.2])
    simpa using this

/-- A numbering of the positions with an inverse counts exactly `k` positions below `k`. -/
theorem count_below (idx : Position w h → Nat) (cell : Nat → Position w h)
    (hleft : ∀ p, cell (idx p) = p) (hright : ∀ j, j < w * h → idx (cell j) = j)
    {k : Nat} (hk : k ≤ w * h) :
    ((positions w h).filter fun p => decide (idx p < k)).length = k := by
  apply Nat.le_antisymm
  · have := length_le_of_injOn ((positions w h).filter fun p => decide (idx p < k)) (List.range k)
      ((positions_nodup w h).sublist List.filter_sublist) idx
      (fun a _ b _ hab => by rw [← hleft a, hab, hleft])
      (fun p hp => List.mem_range.mpr (of_decide_eq_true (List.mem_filter.mp hp).2))
    simpa using this
  · have := length_le_of_injOn (List.range k) ((positions w h).filter fun p => decide (idx p < k))
      List.nodup_range cell
      (fun a ha b hb hab => by
        rw [← hright a (Nat.lt_of_lt_of_le (List.mem_range.mp ha) hk), hab,
          hright b (Nat.lt_of_lt_of_le (List.mem_range.mp hb) hk)])
      (fun j hj => List.mem_filter.mpr ⟨mem_positions w h _, decide_eq_true (by
        rw [hright j (Nat.lt_of_lt_of_le (List.mem_range.mp hj) hk)]
        exact List.mem_range.mp hj)⟩)
    simpa using this

private theorem pred_mul_add (n m : Nat) (hn : 0 < n) : (n - 1) * m + m = n * m := by
  rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]

/-- Positions numbered row by row, with row 0 last. -/
def rowIdx (p : Position w h) : Nat :=
  if p.2.val = 0 then (h - 1) * w + p.1.val else (p.2.val - 1) * w + p.1.val

/-- The inverse numbering. -/
def rowCell (pw : 0 < w) (ph : 0 < h) (j : Nat) : Position w h :=
  if hj : j < (h - 1) * w then
    (⟨j % w, Nat.mod_lt _ pw⟩, ⟨j / w + 1, by
      have := (Nat.div_lt_iff_lt_mul pw).mpr hj
      omega⟩)
  else (⟨(j - (h - 1) * w) % w, Nat.mod_lt _ pw⟩, ⟨0, ph⟩)

theorem rowCell_rowIdx (pw : 0 < w) (ph : 0 < h) (p : Position w h) :
    rowCell pw ph (rowIdx p) = p := by
  have hx := p.1.isLt
  have hy := p.2.isLt
  by_cases h0 : p.2.val = 0
  · have hge : ¬ rowIdx p < (h - 1) * w := by simp only [rowIdx, h0, ↓reduceIte]; omega
    simp only [rowCell, hge, ↓reduceDIte]
    have : rowIdx p - (h - 1) * w = p.1.val := by simp only [rowIdx, h0, ↓reduceIte]; omega
    refine Prod.ext (Fin.ext ?_) (Fin.ext h0.symm)
    show (rowIdx p - (h - 1) * w) % w = p.1.val
    rw [this, Nat.mod_eq_of_lt hx]
  · have hrow : rowIdx p = (p.2.val - 1) * w + p.1.val := by simp [rowIdx, h0]
    have hlt : rowIdx p < (h - 1) * w := by
      have : (p.2.val - 1) * w + w ≤ (h - 1) * w := by
        rw [pred_mul_add _ _ (by omega)]; exact Nat.mul_le_mul_right w (by omega)
      omega
    simp only [rowCell, hlt, ↓reduceDIte]
    have hm : rowIdx p % w = p.1.val := by
      rw [hrow, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hx]
    have hd : rowIdx p / w = p.2.val - 1 := by
      rw [hrow, Nat.mul_comm, Nat.mul_add_div pw, Nat.div_eq_of_lt hx, Nat.add_zero]
    exact Prod.ext (Fin.ext hm) (Fin.ext (by simp only [hd]; omega))

theorem rowIdx_rowCell (pw : 0 < w) (ph : 0 < h) {j : Nat} (hj : j < w * h) :
    rowIdx (rowCell pw ph j) = j := by
  by_cases hlt : j < (h - 1) * w
  · have hne : j / w + 1 ≠ 0 := Nat.succ_ne_zero _
    simp only [rowCell, hlt, ↓reduceDIte, rowIdx, hne, ↓reduceIte, Nat.add_sub_cancel]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod j w
  · simp only [rowCell, hlt, ↓reduceDIte, rowIdx, ↓reduceIte]
    have : j - (h - 1) * w < w := by
      have := pred_mul_add h w ph
      rw [Nat.mul_comm w h] at hj
      omega
    rw [Nat.mod_eq_of_lt this]
    omega

/-- The first `k` positions of the row numbering are roundabouts. -/
def rowFill (k : Nat) : Position w h → Bool := fun p => decide (rowIdx p < k)

theorem roundabouts_rowFill (pw : 0 < w) (ph : 0 < h) {k : Nat} (hk : k ≤ w * h) :
    roundabouts (rowFill (w := w) (h := h) k) = k :=
  count_below rowIdx (rowCell pw ph) (rowCell_rowIdx pw ph) (fun _ hj => rowIdx_rowCell pw ph hj) hk

theorem rowCount_rowFill_zero (pw : 0 < w) (ph : 0 < h) {k : Nat} (hk : k ≤ w * h) :
    rowCount (rowFill (w := w) (h := h) k) ⟨0, ph⟩ = k - w * (h - 1) := by
  unfold rowCount rowFill
  have hcongr : ((List.finRange w).filter fun x => decide (rowIdx (x, (⟨0, ph⟩ : Fin h)) < k)) =
      (List.finRange w).filter fun x => decide (x.val < k - w * (h - 1)) := by
    apply List.filter_congr
    intro x _
    simp only [rowIdx, ↓reduceIte, decide_eq_decide]
    rw [Nat.mul_comm w]
    omega
  rw [hcongr, fin_count_lt pw]
  have := pred_mul_add h w ph
  rw [Nat.mul_comm w h] at hk
  rw [Nat.mul_comm w (h - 1)]
  omega

/-- Positions numbered column by column, with column 0 last. -/
def colIdx (p : Position w h) : Nat :=
  if p.1.val = 0 then (w - 1) * h + p.2.val else (p.1.val - 1) * h + p.2.val

def colCell (pw : 0 < w) (ph : 0 < h) (j : Nat) : Position w h :=
  if hj : j < (w - 1) * h then
    (⟨j / h + 1, by
      have := (Nat.div_lt_iff_lt_mul ph).mpr hj
      omega⟩, ⟨j % h, Nat.mod_lt _ ph⟩)
  else (⟨0, pw⟩, ⟨(j - (w - 1) * h) % h, Nat.mod_lt _ ph⟩)

theorem colCell_colIdx (pw : 0 < w) (ph : 0 < h) (p : Position w h) :
    colCell pw ph (colIdx p) = p := by
  have hx := p.1.isLt
  have hy := p.2.isLt
  by_cases h0 : p.1.val = 0
  · have hge : ¬ colIdx p < (w - 1) * h := by simp only [colIdx, h0, ↓reduceIte]; omega
    simp only [colCell, hge, ↓reduceDIte]
    have : colIdx p - (w - 1) * h = p.2.val := by simp only [colIdx, h0, ↓reduceIte]; omega
    refine Prod.ext (Fin.ext h0.symm) (Fin.ext ?_)
    show (colIdx p - (w - 1) * h) % h = p.2.val
    rw [this, Nat.mod_eq_of_lt hy]
  · have hcol : colIdx p = (p.1.val - 1) * h + p.2.val := by simp [colIdx, h0]
    have hlt : colIdx p < (w - 1) * h := by
      have : (p.1.val - 1) * h + h ≤ (w - 1) * h := by
        rw [pred_mul_add _ _ (by omega)]; exact Nat.mul_le_mul_right h (by omega)
      omega
    simp only [colCell, hlt, ↓reduceDIte]
    have hm : colIdx p % h = p.2.val := by
      rw [hcol, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hy]
    have hd : colIdx p / h = p.1.val - 1 := by
      rw [hcol, Nat.mul_comm, Nat.mul_add_div ph, Nat.div_eq_of_lt hy, Nat.add_zero]
    exact Prod.ext (Fin.ext (by simp only [hd]; omega)) (Fin.ext hm)

theorem colIdx_colCell (pw : 0 < w) (ph : 0 < h) {j : Nat} (hj : j < w * h) :
    colIdx (colCell pw ph j) = j := by
  by_cases hlt : j < (w - 1) * h
  · have hne : j / h + 1 ≠ 0 := Nat.succ_ne_zero _
    simp only [colCell, hlt, ↓reduceDIte, colIdx, hne, ↓reduceIte, Nat.add_sub_cancel]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod j h
  · simp only [colCell, hlt, ↓reduceDIte, colIdx, ↓reduceIte]
    have : j - (w - 1) * h < h := by
      have := pred_mul_add w h pw
      omega
    rw [Nat.mod_eq_of_lt this]
    omega

def colFill (k : Nat) : Position w h → Bool := fun p => decide (colIdx p < k)

theorem roundabouts_colFill (pw : 0 < w) (ph : 0 < h) {k : Nat} (hk : k ≤ w * h) :
    roundabouts (colFill (w := w) (h := h) k) = k :=
  count_below colIdx (colCell pw ph) (colCell_colIdx pw ph) (fun _ hj => colIdx_colCell pw ph hj) hk

theorem colCount_colFill_zero (pw : 0 < w) (ph : 0 < h) {k : Nat} (hk : k ≤ w * h) :
    colCount (colFill (w := w) (h := h) k) ⟨0, pw⟩ = k - h * (w - 1) := by
  unfold colCount colFill
  have hcongr : ((List.finRange h).filter fun y => decide (colIdx ((⟨0, pw⟩ : Fin w), y) < k)) =
      (List.finRange h).filter fun y => decide (y.val < k - h * (w - 1)) := by
    apply List.filter_congr
    intro y _
    simp only [colIdx, ↓reduceIte, decide_eq_decide]
    rw [Nat.mul_comm h]
    omega
  rw [hcongr, fin_count_lt ph]
  have := pred_mul_add w h pw
  rw [Nat.mul_comm h (w - 1)]
  omega

/-- **MX-E, worst case attained.** For every `k ≤ w·h`, some placement of `k`
roundabouts has a gridlock with exactly
`min(w' + (k − w(h−1)), h' + (k − h(w−1)))` cars. -/
theorem worst_attained (pw : 0 < w) (ph : 0 < h) (link : Bool) {k : Nat} (hk : k ≤ w * h) :
    ∃ ring : Position w h → Bool, roundabouts ring = k ∧
      ∃ s : Config (Grid w h) Species, Stuck (mixed (torus pw ph ring link)) s ∧
        (∃ c, (s c).isSome = true) ∧
        carCount s = min (rowBase w link + (k - w * (h - 1))) (colBase h link + (k - h * (w - 1))) := by
  have hwh : w ≤ w * h := Nat.le_mul_of_pos_right w ph
  have hhw : h ≤ w * h := by rw [Nat.mul_comm]; exact Nat.le_mul_of_pos_right h pw
  by_cases hmin : rowBase w link + (k - w * (h - 1)) ≤ colBase h link + (k - h * (w - 1))
  · refine ⟨rowFill k, roundabouts_rowFill pw ph hk, ?_⟩
    have hrow := rowCount_rowFill_zero pw ph hk
    rw [Nat.min_eq_left hmin]
    refine (gridlock_count_iff (hw := pw) (hh := ph) _).mpr ⟨Or.inl ⟨⟨0, ph⟩, ?_⟩, ?_⟩
    · rw [rowStreet_length', hrow]; exact Nat.le_refl _
    · rw [gridCells_length, roundabouts_rowFill pw ph hk]
      cases link <;> simp [rowBase] <;> omega
  · refine ⟨colFill k, roundabouts_colFill pw ph hk, ?_⟩
    have hcol := colCount_colFill_zero pw ph hk
    rw [Nat.min_eq_right (by omega)]
    refine (gridlock_count_iff (hw := pw) (hh := ph) _).mpr ⟨Or.inr ⟨⟨0, pw⟩, ?_⟩, ?_⟩
    · rw [colStreet_length', hcol]; exact Nat.le_refl _
    · rw [gridCells_length, roundabouts_colFill pw ph hk]
      cases link <;> simp [colBase] <;> omega

/-! ## Attaining the best case -/

private theorem mod_lt_two {x m : Nat} (_hm : 0 < m) (hx : x < 2 * m) :
    x % m = if x < m then x else x - m := by
  split
  · exact Nat.mod_eq_of_lt ‹_›
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

section Balanced

variable (w h k : Nat)

/-- Roundabouts in row `y`: `⌊k/h⌋`, plus one for the first `k mod h` rows. -/
def bRow (y : Nat) : Nat := k / h + (if y < k % h then 1 else 0)

/-- Where row `y` starts in the cyclic order of columns. -/
def bStart (y : Nat) : Nat := k / h * y + min y (k % h)

/-- Row `y` holds the `bRow y` columns starting at `bStart y`, cyclically. -/
def balanced (p : Position w h) : Bool :=
  decide ((p.1.val + w - bStart h k p.2.val % w) % w < bRow h k p.2.val)

/-- The row whose run of columns contains position `j` of the cyclic order. -/
def bRowOf (j : Nat) : Nat :=
  if j < (k / h + 1) * (k % h) then j / (k / h + 1)
  else k % h + (j - (k / h + 1) * (k % h)) / (k / h)

end Balanced

variable {k : Nat}

theorem bRow_le (_pw : 0 < w) (ph : 0 < h) (hk : k ≤ w * h) (y : Nat) : bRow h k y ≤ w := by
  unfold bRow
  have hq : k / h ≤ w := (Nat.div_le_iff_le_mul_add_pred ph).mpr (by
    have := Nat.mul_comm w h; omega)
  split
  · rename_i hy
    rcases Nat.lt_or_ge (k / h) w with hlt | hge
    · omega
    · -- k / h = w forces k = w*h, so k % h = 0
      have heq : k / h = w := by omega
      have hdm := Nat.div_add_mod k h
      rw [heq, Nat.mul_comm h w] at hdm
      omega
  · omega

theorem bRowOf_spec (ph : 0 < h) {j : Nat} (hj : j < k) :
    bRowOf h k j < h ∧ bStart h k (bRowOf h k j) ≤ j ∧
      j < bStart h k (bRowOf h k j) + bRow h k (bRowOf h k j) := by
  unfold bRowOf bStart bRow
  have hdm := Nat.div_add_mod k h
  have hmod := Nat.mod_lt k ph
  generalize k / h = Q at *
  generalize k % h = R at *
  have hQR : (Q + 1) * R = Q * R + R := Nat.succ_mul Q R
  split
  · rename_i hlt
    have hq1 : 0 < Q + 1 := by omega
    have hd := Nat.div_add_mod j (Q + 1)
    have hm := Nat.mod_lt j hq1
    generalize j / (Q + 1) = y at *
    generalize j % (Q + 1) = m at *
    have hs : (Q + 1) * y = Q * y + y := Nat.succ_mul Q y
    have hyR : y < R := Nat.lt_of_mul_lt_mul_left (a := Q + 1) (by omega)
    simp only [Nat.min_eq_left (Nat.le_of_lt hyR), hyR, ↓reduceIte]
    omega
  · rename_i hge
    rcases Nat.eq_zero_or_pos Q with rfl | hq
    · simp at hdm hge hQR
      omega
    have hd := Nat.div_add_mod (j - (Q + 1) * R) Q
    have hm := Nat.mod_lt (j - (Q + 1) * R) hq
    generalize he : j - (Q + 1) * R = e at *
    generalize e / Q = z at *
    generalize e % Q = m at *
    have hsub := Nat.mul_sub Q h R
    have hcomm := Nat.mul_comm h Q
    have hle : Q * R ≤ Q * h := Nat.mul_le_mul_left Q (by omega)
    have hz : z < h - R := Nat.lt_of_mul_lt_mul_left (a := Q) (by omega)
    have hnot : ¬ (R + z < R) := by omega
    have hadd := Nat.mul_add Q R z
    simp only [Nat.min_eq_right (Nat.le_add_right R z), hnot, ↓reduceIte, Nat.add_zero]
    omega

/-- The position at offset `d < w` from a row's start is in the right column. -/
theorem balanced_offset (pw : 0 < w) {st d : Nat} (hd : d < w) :
    (((st + d) % w) + w - st % w) % w = d := by
  have ha := Nat.mod_lt st pw
  have h1 : (st + d) % w = (st % w + d) % w := by rw [Nat.add_mod, Nat.mod_eq_of_lt hd]
  rw [h1]
  generalize st % w = a at *
  rw [mod_lt_two pw (by omega : a + d < 2 * w)]
  split
  · rw [show a + d + w - a = d + w by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hd]
  · rw [show a + d - w + w - a = d by omega, Nat.mod_eq_of_lt hd]

/-- Row `y` of the balanced placement holds exactly `bRow y` roundabouts. -/
theorem rowCount_balanced (pw : 0 < w) (ph : 0 < h) (hk : k ≤ w * h) (y : Fin h) :
    rowCount (balanced w h k) y = bRow h k y.val := by
  have hr := bRow_le pw ph hk y.val
  have ha := Nat.mod_lt (bStart h k y.val) pw
  apply Nat.le_antisymm
  · have := length_le_of_injOn ((List.finRange w).filter fun x => balanced w h k (x, y))
      (List.range (bRow h k y.val)) ((List.nodup_finRange w).sublist List.filter_sublist)
      (fun x : Fin w => (x.val + w - (bStart h k y.val) % w) % w)
      (fun a _ b _ hab => by
        have hxa := a.isLt
        have hxb := b.isLt
        rw [mod_lt_two pw (show a.val + w - bStart h k y.val % w < 2 * w by omega),
          mod_lt_two pw (show b.val + w - bStart h k y.val % w < 2 * w by omega)] at hab
        exact Fin.ext (by split at hab <;> split at hab <;> omega))
      (fun x hx => List.mem_range.mpr (of_decide_eq_true (List.mem_filter.mp hx).2))
    simpa [rowCount] using this
  · let fwd : Nat → Fin w := fun d => ⟨((bStart h k y.val) + d) % w, Nat.mod_lt _ pw⟩
    have := length_le_of_injOn (List.range (bRow h k y.val))
      ((List.finRange w).filter fun x => balanced w h k (x, y)) List.nodup_range fwd
      (fun a ha b hb hab => by
        have ha' := List.mem_range.mp ha
        have hb' := List.mem_range.mp hb
        have h1 := balanced_offset pw (st := bStart h k y.val) (d := a) (by omega)
        have h2 := balanced_offset pw (st := bStart h k y.val) (d := b) (by omega)
        have : ((bStart h k y.val) + a) % w = ((bStart h k y.val) + b) % w := congrArg Fin.val hab
        rw [this] at h1
        omega)
      (fun d hd => by
        have hd' := List.mem_range.mp hd
        refine List.mem_filter.mpr ⟨List.mem_finRange _, decide_eq_true ?_⟩
        show ((((bStart h k y.val) + d) % w) + w - (bStart h k y.val) % w) % w < bRow h k y.val
        rw [balanced_offset pw (by omega)]
        exact hd')
    simpa [rowCount] using this

private theorem mul_lt_mul_cancel {a b w : Nat} (h : a * w < b * w + w) (h' : b * w < a * w + w) :
    a = b := by
  rcases Nat.lt_trichotomy a b with hab | rfl | hab
  · have := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hab)
    rw [Nat.succ_mul] at this
    omega
  · rfl
  · have := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hab)
    rw [Nat.succ_mul] at this
    omega

/-- Every column of the balanced placement holds at least `⌊k/w⌋` roundabouts. -/
theorem colCount_balanced (pw : 0 < w) (ph : 0 < h) (hk : k ≤ w * h) (x : Fin w) :
    k / w ≤ colCount (balanced w h k) x := by
  -- the column positions x, x + w, x + 2w, … below k lie in distinct rows
  let row : Nat → Fin h := fun i =>
    if hr : bRowOf h k (x.val + i * w) < h then ⟨_, hr⟩ else ⟨0, ph⟩
  have hjk : ∀ i, i < k / w → x.val + i * w < k := by
    intro i hi
    have := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at this
    have := Nat.div_mul_le_self k w
    have := x.isLt
    omega
  have hrow : ∀ i, i < k / w → (row i).val = bRowOf h k (x.val + i * w) := by
    intro i hi
    simp [row, (bRowOf_spec ph (hjk i hi)).1]
  have := length_le_of_injOn (List.range (k / w))
    ((List.finRange h).filter fun y => balanced w h k (x, y)) List.nodup_range row
    (fun a ha b hb hab => by
      have ha' := List.mem_range.mp ha
      have hb' := List.mem_range.mp hb
      have hy := congrArg Fin.val hab
      rw [hrow a ha', hrow b hb'] at hy
      obtain ⟨_, hsa, hea⟩ := bRowOf_spec ph (hjk a ha')
      obtain ⟨_, hsb, heb⟩ := bRowOf_spec ph (hjk b hb')
      rw [hy] at hsa hea
      have hr := bRow_le pw ph hk (bRowOf h k (x.val + b * w))
      exact mul_lt_mul_cancel (w := w) (by omega) (by omega))
    (fun i hi => by
      have hi' := List.mem_range.mp hi
      refine List.mem_filter.mpr ⟨List.mem_finRange _, ?_⟩
      simp only [balanced, decide_eq_true_eq]
      rw [hrow i hi']
      obtain ⟨_, hs, he⟩ := bRowOf_spec ph (hjk i hi')
      generalize bRowOf h k (x.val + i * w) = y at hs he ⊢
      have hr := bRow_le pw ph hk y
      have hx : x.val = (bStart h k y + (x.val + i * w - bStart h k y)) % w := by
        rw [Nat.add_sub_cancel' hs, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt x.isLt]
      rw [hx, balanced_offset pw (by omega)]
      omega)
  simpa [colCount] using this

private theorem sum_add_indicator {α : Type} (l : List α) (q : Nat) (P : α → Bool) :
    (l.map fun a => q + (if P a then 1 else 0)).sum = l.length * q + (l.filter P).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.succ_mul, List.filter_cons]
    cases P a <;> simp <;> omega

/-- The balanced placement has exactly `k` roundabouts. -/
theorem roundabouts_balanced (pw : 0 < w) (ph : 0 < h) (hk : k ≤ w * h) :
    roundabouts (balanced w h k) = k := by
  rw [roundabouts_rows]
  have : (List.finRange h).map (rowCount (balanced w h k)) =
      (List.finRange h).map fun y => k / h + (if decide (y.val < k % h) then 1 else 0) := by
    apply List.map_congr_left
    intro y _
    rw [rowCount_balanced pw ph hk]
    simp [bRow]
  rw [this, sum_add_indicator, List.length_finRange, fin_count_lt ph,
    Nat.min_eq_right (Nat.le_of_lt (Nat.mod_lt k ph))]
  exact Nat.div_add_mod k h

/-- **MX-E, best case attained.** For every `k ≤ w·h`, some placement of `k`
roundabouts has every gridlock with at least `min(w' + ⌊k/h⌋, h' + ⌊k/w⌋)`
cars; with `best_bound`, this is the largest least gridlock over placements. -/
theorem best_attained (pw : 0 < w) (ph : 0 < h) (link : Bool) (hk : k ≤ w * h) :
    roundabouts (balanced w h k) = k ∧
      ∀ s : Config (Grid w h) Species, Stuck (mixed (torus pw ph (balanced w h k) link)) s →
        (∃ c, (s c).isSome = true) →
        min (rowBase w link + k / h) (colBase h link + k / w) ≤ carCount s := by
  refine ⟨roundabouts_balanced pw ph hk, fun s hs hne => ?_⟩
  rcases stuck_carCount_ge_street hs hne with ⟨y, hy⟩ | ⟨x, hx⟩
  · rw [rowStreet_length', rowCount_balanced pw ph hk] at hy
    have : k / h ≤ bRow h k y.val := by unfold bRow; omega
    omega
  · rw [colStreet_length'] at hx
    have := colCount_balanced pw ph hk x
    omega

end Attain

end BML.Net
