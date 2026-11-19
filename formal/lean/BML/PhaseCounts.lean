import BML.Counting
import BML.FreeFlowConditions
import BML.Encounters
import Train.Counting
import Train.Finite

/-!
The geometric-to-numerical bridge for free-flow packing.  Phase classes are the
actual fibers of `(x+y) mod gcd(width,height)`; their equal size and all packing
constraints below are proved by finite bijections on the torus.
-/
namespace BML

/-- All sites of one diagonal phase, each listed once. -/
def phaseFiber (w h : Nat) (hw : 0 < w) (i : Fin (Nat.gcd w h)) :
    List (Position w h) :=
  (positions w h).filter (fun p => decide (phaseIndex w h hw p = i))

@[simp] theorem mem_phaseFiber (w h : Nat) (hw : 0 < w)
    (i : Fin (Nat.gcd w h)) (p : Position w h) :
    p ∈ phaseFiber w h hw i ↔ phaseIndex w h hw p = i := by
  simp [phaseFiber, mem_positions]

theorem phaseFiber_nodup (w h : Nat) (hw : 0 < w) (i : Fin (Nat.gcd w h)) :
    (phaseFiber w h hw i).Nodup := (positions_nodup w h).filter _

private theorem sum_map_add (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem sum_map_mul (xs : List α) (m : Nat) (f : α → Nat) :
    (xs.map (fun x => m * f x)).sum = m * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.mul_add]

private theorem sum_fin_indicator (n : Nat) (i : Fin n) :
    ((List.finRange n).map (fun j => if i = j then 1 else 0)).sum = 1 := by
  rw [Train.Counting.indicator_sum_eq_filter_length]
  have hn := (List.nodup_finRange n).filter (fun j => decide (i = j))
  have hp : ((List.finRange n).filter (fun j => decide (i = j))).Perm [i] := by
    apply (List.perm_ext_iff_of_nodup hn (by simp)).mpr
    intro j
    simp [eq_comm]
  exact hp.length_eq

/-- The finite fibers of an arbitrary index map partition a list. -/
theorem sum_phase_partition (n : Nat) (xs : List α) (index : α → Fin n) :
    ((List.finRange n).map (fun i =>
      (xs.filter (fun x => decide (index x = i))).length)).sum = xs.length := by
  induction xs with
  | nil => simp [List.map_const', List.sum_replicate_nat]
  | cons x xs ih =>
    have he : (fun i : Fin n =>
        ((x :: xs).filter (fun y => decide (index y = i))).length) =
        (fun i => (if index x = i then 1 else 0) +
          (xs.filter (fun y => decide (index y = i))).length) := by
      funext i
      by_cases hxi : index x = i <;> simp [hxi, Nat.add_comm]
    rw [he, sum_map_add, sum_fin_indicator, ih]
    simp [Nat.add_comm]

theorem phaseFiber_length_next (w h : Nat) (hw : 0 < w)
    (i : Fin (Nat.gcd w h)) :
    (phaseFiber w h hw i).length =
      (phaseFiber w h hw
        (cyclicNext (Nat.gcd w h) (Nat.gcd_pos_of_pos_left h hw) i)).length := by
  apply Train.Counting.filter_length_eq_of_bijection
    (positions w h) (positions_nodup w h) (mem_positions w h)
    _ _ (eastDirection w h hw).next
  · intro p hp
    simp only [decide_eq_true_eq] at hp ⊢
    rw [phaseIndex_east, hp]
  · intro p q _ _ he
    have he' := congrArg (eastDirection w h hw).prev he
    simpa only [(eastDirection w h hw).prev_next] using he'
  · intro q hq
    simp only [decide_eq_true_eq] at hq
    refine ⟨(eastDirection w h hw).prev q, ?_, (eastDirection w h hw).next_prev q⟩
    simp only [decide_eq_true_eq]
    have hs := phaseIndex_east w h hw ((eastDirection w h hw).prev q)
    rw [(eastDirection w h hw).next_prev, hq] at hs
    have he := congrArg (cyclicPrev (Nat.gcd w h) (Nat.gcd_pos_of_pos_left h hw)) hs
    simpa only [cyclicPrev_next] using he.symm

/-- Every diagonal phase has exactly `width*height/gcd(width,height)` sites. -/
theorem phaseFiber_length (w h : Nat) (hw : 0 < w)
    (i : Fin (Nat.gcd w h)) :
    (phaseFiber w h hw i).length = w * h / Nat.gcd w h := by
  let g := Nat.gcd w h
  have hg : 0 < g := Nat.gcd_pos_of_pos_left h hw
  have hall : ∀ j, (phaseFiber w h hw j).length = (phaseFiber w h hw i).length := by
    apply Train.cyclic_all_of_step hg
      (fun j => (phaseFiber w h hw j).length = (phaseFiber w h hw i).length)
      (fun j hj => (phaseFiber_length_next w h hw j).symm.trans hj) i rfl
  have hs := sum_phase_partition g (positions w h) (phaseIndex w h hw)
  change ((List.finRange g).map (fun j => (phaseFiber w h hw j).length)).sum = _ at hs
  have hm : ((List.finRange g).map (fun j => (phaseFiber w h hw j).length)) =
      (List.finRange g).map (fun _ => (phaseFiber w h hw i).length) := by
    apply List.map_congr_left
    intro j _
    exact hall j
  rw [hm] at hs
  simp only [List.map_const', List.length_finRange, List.sum_replicate_nat,
    positions_length] at hs
  rw [← hs]
  exact (Nat.mul_div_cancel_left _ hg).symm

/-- Cars of one species in one phase. -/
def phaseSpeciesCells (w h : Nat) (hw : 0 < w) (sp : Species)
    (s : Config (Position w h)) (i : Fin (Nat.gcd w h)) : List (Position w h) :=
  (phaseFiber w h hw i).filter (fun p => decide (s p = sp.cell))

def phaseSpeciesCount (w h : Nat) (hw : 0 < w) (sp : Species)
    (s : Config (Position w h)) (i : Fin (Nat.gcd w h)) : Nat :=
  (phaseSpeciesCells w h hw sp s i).length

@[simp] theorem mem_phaseSpeciesCells (w h : Nat) (hw : 0 < w) (sp : Species)
    (s : Config (Position w h)) (i : Fin (Nat.gcd w h)) (p : Position w h) :
    p ∈ phaseSpeciesCells w h hw sp s i ↔
      phaseIndex w h hw p = i ∧ s p = sp.cell := by
  simp [phaseSpeciesCells]

theorem phaseSpeciesCells_nodup (w h : Nat) (hw : 0 < w) (sp : Species)
    (s : Config (Position w h)) (i : Fin (Nat.gcd w h)) :
    (phaseSpeciesCells w h hw sp s i).Nodup := (phaseFiber_nodup w h hw i).filter _

/-- Counting a species phase by phase gives its original torus population. -/
theorem phaseSpeciesCount_sum (w h : Nat) (hw : 0 < w) (sp : Species)
    (s : Config (Position w h)) :
    ((List.finRange (Nat.gcd w h)).map (phaseSpeciesCount w h hw sp s)).sum =
      speciesCount w h sp s := by
  rw [speciesCount_eq_length_speciesCells]
  unfold phaseSpeciesCount phaseSpeciesCells phaseFiber
  have he := sum_phase_partition (Nat.gcd w h) (speciesCells w h sp s)
    (phaseIndex w h hw)
  simpa [speciesCells, List.filter_filter, Bool.and_comm] using he

/-- The two phase species counts partition the total car population. -/
theorem carCount_eq_sum_phaseSpeciesCount (w h : Nat) (hw : 0 < w)
    (s : Config (Position w h)) :
    carCount w h s = ((List.finRange (Nat.gcd w h)).map (fun i =>
      phaseSpeciesCount w h hw .east s i + phaseSpeciesCount w h hw .north s i)).sum := by
  rw [sum_map_add, phaseSpeciesCount_sum, phaseSpeciesCount_sum,
    carCount_eq_speciesCount]

/-- A phase contains at most its number of sites, regardless of free flow. -/
theorem phaseSpeciesCount_add_le (w h : Nat) (hw : 0 < w)
    (s : Config (Position w h)) (i : Fin (Nat.gcd w h)) :
    phaseSpeciesCount w h hw .east s i + phaseSpeciesCount w h hw .north s i ≤
      w * h / Nat.gcd w h := by
  let es := phaseSpeciesCells w h hw .east s i
  let ns := phaseSpeciesCells w h hw .north s i
  have hd : (es ++ ns).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨phaseSpeciesCells_nodup w h hw .east s i,
      phaseSpeciesCells_nodup w h hw .north s i, ?_⟩
    intro p hp q hq hpq
    have he := (mem_phaseSpeciesCells w h hw .east s i p).mp hp
    have hn := (mem_phaseSpeciesCells w h hw .north s i q).mp hq
    subst q
    rw [he.2] at hn
    cases hn.2
  have hs : es ++ ns ⊆ phaseFiber w h hw i := by
    intro p hp
    apply (mem_phaseFiber w h hw i p).mpr
    rcases List.mem_append.mp hp with hp | hp
    · exact ((mem_phaseSpeciesCells w h hw .east s i p).mp hp).1
    · exact ((mem_phaseSpeciesCells w h hw .north s i p).mp hp).1
  have hl := hd.length_le_of_subset hs
  simpa only [List.length_append, phaseFiber_length, es, ns, phaseSpeciesCount] using hl

private theorem phaseSpeciesCount_add_next_le_of_no_adjacent
    (w h : Nat) (hw : 0 < w) (sp : Species) (s : Config (Position w h))
    (d : Direction (Position w h))
    (hphase : ∀ p, phaseIndex w h hw (d.next p) =
      cyclicNext (Nat.gcd w h) (Nat.gcd_pos_of_pos_left h hw) (phaseIndex w h hw p))
    (hsep : ∀ p, s p = sp.cell → s (d.next p) ≠ sp.cell)
    (i : Fin (Nat.gcd w h)) :
    phaseSpeciesCount w h hw sp s i + phaseSpeciesCount w h hw sp s
      (cyclicNext (Nat.gcd w h) (Nat.gcd_pos_of_pos_left h hw) i) ≤
      w * h / Nat.gcd w h := by
  let j := cyclicNext (Nat.gcd w h) (Nat.gcd_pos_of_pos_left h hw) i
  let as := phaseSpeciesCells w h hw sp s i
  let bs := phaseSpeciesCells w h hw sp s j
  have hi : Function.Injective d.next := by
    intro p q hpq
    have he := congrArg d.prev hpq
    simpa only [d.prev_next] using he
  have hd : (as.map d.next ++ bs).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨Train.nodup_map_of_injective d.next hi
      (phaseSpeciesCells_nodup w h hw sp s i),
      phaseSpeciesCells_nodup w h hw sp s j, ?_⟩
    intro p hp q hq hpq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
    have hr' := (mem_phaseSpeciesCells w h hw sp s i r).mp hr
    have hq' := (mem_phaseSpeciesCells w h hw sp s j q).mp hq
    exact hsep r hr'.2 (hpq ▸ hq'.2)
  have hs : as.map d.next ++ bs ⊆ phaseFiber w h hw j := by
    intro p hp
    apply (mem_phaseFiber w h hw j p).mpr
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
      rw [hphase, ((mem_phaseSpeciesCells w h hw sp s i r).mp hr).1]
    · exact ((mem_phaseSpeciesCells w h hw sp s j p).mp hp).1
  have hl := hd.length_le_of_subset hs
  simpa only [List.length_append, List.length_map, phaseFiber_length,
    as, bs, j, phaseSpeciesCount] using hl

/-- East exclusion gives the adjacent-phase capacity constraint. -/
theorem phaseEastCount_add_next_le (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (hf : StaticFree w h hw hh s)
    (i : Fin (Nat.gcd w h)) :
    phaseSpeciesCount w h hw .east s i + phaseSpeciesCount w h hw .east s
      (cyclicNext (Nat.gcd w h) (Nat.gcd_pos_of_pos_left h hw) i) ≤
      w * h / Nat.gcd w h :=
  phaseSpeciesCount_add_next_le_of_no_adjacent w h hw .east s
    (eastDirection w h hw) (phaseIndex_east w h hw) hf.1 i

/-- North exclusion gives the adjacent-phase capacity constraint. -/
theorem phaseNorthCount_add_next_le (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (hf : StaticFree w h hw hh s)
    (i : Fin (Nat.gcd w h)) :
    phaseSpeciesCount w h hw .north s i + phaseSpeciesCount w h hw .north s
      (cyclicNext (Nat.gcd w h) (Nat.gcd_pos_of_pos_left h hw) i) ≤
      w * h / Nat.gcd w h :=
  phaseSpeciesCount_add_next_le_of_no_adjacent w h hw .north s
    (northDirection w h hh) (phaseIndex_north w h hw hh) hf.2.1 i

/-- Opposite species cannot both occupy the same phase in free flow. -/
theorem phaseCounts_cross_same (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (hf : StaticFree w h hw hh s)
    (i : Fin (Nat.gcd w h)) :
    phaseSpeciesCount w h hw .east s i = 0 ∨
      phaseSpeciesCount w h hw .north s i = 0 := by
  by_cases he : phaseSpeciesCount w h hw .east s i = 0
  · exact Or.inl he
  · right
    by_cases hn : phaseSpeciesCount w h hw .north s i = 0
    · exact hn
    apply False.elim
    obtain ⟨e, he'⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero he)
    obtain ⟨q, hn'⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero hn)
    have hes := (mem_phaseSpeciesCells w h hw .east s i e).mp he'
    have hns := (mem_phaseSpeciesCells w h hw .north s i q).mp hn'
    apply (hf.2.2 e q hes.2 hns.2).1
    exact congrArg Fin.val (hns.1.trans hes.1.symm)

/-- A north car cannot occupy the phase immediately after an east phase. -/
theorem phaseCounts_cross_next (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (hf : StaticFree w h hw hh s)
    (i : Fin (Nat.gcd w h)) :
    phaseSpeciesCount w h hw .east s i = 0 ∨
      phaseSpeciesCount w h hw .north s
        (cyclicNext (Nat.gcd w h) (Nat.gcd_pos_of_pos_left h hw) i) = 0 := by
  by_cases he : phaseSpeciesCount w h hw .east s i = 0
  · exact Or.inl he
  · right
    by_cases hn : phaseSpeciesCount w h hw .north s
        (cyclicNext (Nat.gcd w h) (Nat.gcd_pos_of_pos_left h hw) i) = 0
    · exact hn
    apply False.elim
    obtain ⟨e, he'⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero he)
    obtain ⟨q, hn'⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero hn)
    have hes := (mem_phaseSpeciesCells w h hw .east s i e).mp he'
    have hns := (mem_phaseSpeciesCells w h hw .north s _ q).mp hn'
    apply (hf.2.2 e q hes.2 hns.2).2
    have heq := congrArg Fin.val hns.1
    simpa only [phaseIndex_val, cyclicNext_val, ← hes.1] using heq

/-- Saturate each phase with the cell chosen by a finite cyclic pattern. -/
def phaseConfig (w h : Nat) (hw : 0 < w)
    (pattern : Fin (Nat.gcd w h) → Cell) : Config (Position w h) :=
  fun p => pattern (phaseIndex w h hw p)

theorem phaseSpeciesCount_phaseConfig (w h : Nat) (hw : 0 < w) (sp : Species)
    (pattern : Fin (Nat.gcd w h) → Cell) (i : Fin (Nat.gcd w h)) :
    phaseSpeciesCount w h hw sp (phaseConfig w h hw pattern) i =
      if pattern i = sp.cell then w * h / Nat.gcd w h else 0 := by
  unfold phaseSpeciesCount phaseSpeciesCells
  by_cases hi : pattern i = sp.cell
  · rw [ite_eq_left hi]
    rw [List.filter_eq_self.mpr]
    · exact phaseFiber_length w h hw i
    · intro p hp
      simp only [phaseConfig, (mem_phaseFiber w h hw i p).mp hp, hi, decide_true]
  · rw [ite_eq_right hi]
    rw [List.filter_eq_nil_iff.mpr]
    · rfl
    · intro p hp
      simpa only [phaseConfig, (mem_phaseFiber w h hw i p).mp hp,
        decide_eq_true_eq] using hi

/-- Saturating occupied pattern classes multiplies their count by the fiber size. -/
theorem carCount_phaseConfig (w h : Nat) (hw : 0 < w) (_hh : 0 < h)
    (pattern : Fin (Nat.gcd w h) → Cell) :
    carCount w h (phaseConfig w h hw pattern) =
      (w * h / Nat.gcd w h) *
        ((List.finRange (Nat.gcd w h)).filter (fun i => decide (pattern i ≠ .empty))).length := by
  rw [carCount_eq_sum_phaseSpeciesCount w h hw]
  have he : (fun i => phaseSpeciesCount w h hw .east (phaseConfig w h hw pattern) i +
      phaseSpeciesCount w h hw .north (phaseConfig w h hw pattern) i) =
      (fun i => (w * h / Nat.gcd w h) * (if pattern i ≠ .empty then 1 else 0)) := by
    funext i
    rw [phaseSpeciesCount_phaseConfig, phaseSpeciesCount_phaseConfig]
    cases pattern i <;> simp [Species.cell]
  rw [he, sum_map_mul, Train.Counting.indicator_sum_eq_filter_length]

end BML
