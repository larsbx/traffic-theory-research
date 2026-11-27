import BML.NetGridlock
import BML.NetCount

/-!
# The signal/roundabout torus: conservation and every gridlock count

* `mixed_routeClosed`, `mixed_count_run`: a valid state of the mixed grid keeps
  its number of cars of each species for ever;
* `gridlock_every_count`: for every street and every `n` from its number of
  cells up to the number of cells of the grid, there is a gridlock with exactly
  `n` cars. With `stuck_carCount_ge_street` and `stuck_carCount_le_cells` this
  gives Theorem MX-G: the gridlock populations are exactly the interval from
  the cheapest street to the whole grid.
-/
namespace BML.Net

variable {α : Type}

theorem mixed_routeClosed (L : Layout α) : RouteClosed (mixed L) := by
  intro k p c h
  cases k <;> cases p <;>
    simp only [mixed, Layout.next, Layout.intoE, Layout.outN] at h ⊢ <;>
    (repeat' split at h) <;> (try simp at h) <;> (try subst h) <;>
    simp_all <;> (try split) <;> simp_all

section Torus

variable {w h : Nat} {hw : 0 < w} {hh : 0 < h} {ring : Position w h → Bool} {link : Bool}

abbrev Grid (w h : Nat) := Site (Position w h)

/-- **Conservation on the mixed torus**, for every roundabout set and with or
without links. -/
theorem mixed_count_run {s : Config (Grid w h) Species} (hx : Valid (mixed (torus hw hh ring link)) s)
    (k : Species) (t : Nat) :
    count (allSites w h) (run (mixed (torus hw hh ring link)) s t) k = count (allSites w h) s k :=
  count_run _ (allSites_nodup w h) mem_allSites (mixed_routeClosed _) hx k t

/-- The cells that exist in this layout. -/
def present (ring : Position w h → Bool) (link : Bool) : Grid w h → Bool
  | .junction _ => true
  | .quadE p => ring p
  | .quadN p => ring p
  | .linkE _ => link
  | .linkN _ => link

/-- All cells of the grid. -/
def gridCells (ring : Position w h → Bool) (link : Bool) : List (Grid w h) :=
  (allSites w h).filter (present ring link)

theorem gridCells_nodup : (gridCells ring link).Nodup :=
  (allSites_nodup w h).sublist List.filter_sublist

theorem mem_gridCells {c : Grid w h} : c ∈ gridCells ring link ↔ present ring link c = true := by
  simp [gridCells, mem_allSites]

/-- The roundabout set, as a count. -/
def roundabouts (ring : Position w h → Bool) : Nat := ((positions w h).filter ring).length

private theorem sum_cells (l : List (Position w h)) :
    (l.map fun p => ((([Site.junction p, .quadE p, .quadN p, .linkE p, .linkN p] : List (Grid w h)).filter
        (present ring link)).length)).sum =
      l.length + 2 * (l.filter ring).length + (if link then 2 * l.length else 0) := by
  induction l with
  | nil => cases link <;> simp
  | cons p l ih =>
    rw [List.map_cons, List.sum_cons, ih]
    cases hr : ring p <;> cases link <;> simp [present, hr, List.filter_cons] <;> omega

/-- **The number of cells**: `(1 + 2ℓ)·w·h + 2·|R|`. -/
theorem gridCells_length :
    (gridCells ring link).length = w * h + 2 * roundabouts ring + (if link then 2 * (w * h) else 0) := by
  unfold gridCells allSites
  rw [List.filter_flatMap, List.length_flatMap, sum_cells, positions_length]
  rfl

variable {s : Config (Grid w h) Species}

/-- A stuck state occupies only cells that exist. -/
theorem stuck_present (hs : Stuck (mixed (torus hw hh ring link)) s) {c : Grid w h}
    (hc : (s c).isSome = true) : present ring link c = true := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hc
  cases c with
  | junction _ => rfl
  | quadE p => simpa [present, torus] using (stuck_quadE hs hk).2
  | quadN p => simpa [present, torus] using (stuck_quadN hs hk).2
  | linkE p => simpa [present, torus] using (stuck_linkE hs hk).2
  | linkN p => simpa [present, torus] using (stuck_linkN hs hk).2

/-- **Theorem MX-G, upper end.** A gridlock has at most as many cars as the grid has cells. -/
theorem stuck_carCount_le_cells (hs : Stuck (mixed (torus hw hh ring link)) s) :
    carCount s ≤ (gridCells ring link).length := by
  refine List.Nodup.length_le_of_subset ((allSites_nodup w h).filter _) fun c hc => ?_
  exact mem_gridCells.mpr (stuck_present hs (List.mem_filter.mp hc).2)

/-! ### Adding one car to a gridlock -/

section Generic

variable {Cell Class : Type} [DecidableEq Cell] [DecidableEq Class]

/-- Put a class-`k` car in cell `c`. -/
def place (s : Config Cell Class) (c : Cell) (k : Class) : Config Cell Class :=
  fun c' => if c' = c then some k else s c'

omit [DecidableEq Class] in
/-- A car queued behind an occupied cell keeps a stuck state stuck. -/
theorem stuck_place {net : Net Cell Class} {s : Config Cell Class} (hs : Stuck net s)
    {c d : Cell} {k : Class} (hn : net.next k c = some d) (hd : (s d).isSome = true) :
    Stuck net (place s c k) := by
  intro p j hp
  by_cases hpc : p = c
  · subst hpc
    have hj : j = k := by simpa [place] using hp.symm
    subst hj
    exact ⟨d, hn, by unfold place; split <;> simp_all⟩
  · have hp' : s p = some j := by simpa [place, hpc] using hp
    obtain ⟨e, he, ho⟩ := hs p j hp'
    exact ⟨e, he, by unfold place; split <;> simp_all⟩

omit [DecidableEq Class] in
theorem filter_place_length (l : List Cell) (hl : l.Nodup) (s : Config Cell Class) {c : Cell}
    {k : Class} (hc : s c = none) :
    (l.filter fun x => (place s c k x).isSome).length =
      (l.filter fun x => (s x).isSome).length + (if c ∈ l then 1 else 0) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl'⟩ := List.nodup_cons.mp hl
    by_cases hac : a = c
    · subst hac
      have hrest : (l.filter fun x => (place s a k x).isSome) = l.filter fun x => (s x).isSome := by
        apply List.filter_congr
        intro x hx
        have : x ≠ a := fun h => ha (h ▸ hx)
        simp [place, this]
      have h1 : (place s a k a).isSome = true := by simp [place]
      simp only [List.filter_cons, h1, ↓reduceIte, hc, Option.isSome_none, Bool.false_eq_true,
        List.length_cons, hrest, List.mem_cons, true_or]
    · have hmem : (c ∈ a :: l) = (c ∈ l) := by
        simp only [List.mem_cons, eq_iff_iff]
        exact ⟨fun h => h.resolve_left (fun h' => hac h'.symm), Or.inr⟩
      simp only [List.filter_cons, place, hac, ↓reduceIte, hmem]
      split <;> simp_all [place] <;> omega

end Generic

theorem carCount_place {c : Grid w h} {k : Species} (hc : s c = none) :
    carCount (place s c k) = carCount s + 1 := by
  have := filter_place_length (allSites w h) (allSites_nodup w h) s (k := k) hc
  simpa [carCount, mem_allSites] using this

/-! ### Every gridlock below full has room for one more car -/

/-- From an empty junction, everything along its east street to the next junction is empty. -/
theorem east_empty
    (H : ∀ c k d, present ring link c = true → s c = none →
      (mixed (torus hw hh ring link)).next k c = some d → s d = none)
    {q : Position w h} (hq : s (.junction q) = none) :
    s (.junction ((eastDirection w h hw).next q)) = none := by
  have into : s ((torus hw hh ring link).intoE ((eastDirection w h hw).next q)) = none →
      s (.junction ((eastDirection w h hw).next q)) = none := by
    intro hi
    cases hr : ring ((eastDirection w h hw).next q) with
    | false => simpa [Layout.intoE, torus, hr] using hi
    | true =>
      have hi' : s (.quadE ((eastDirection w h hw).next q)) = none := by
        simpa [Layout.intoE, torus, hr] using hi
      exact H _ .east _ (by simp [present, hr]) hi' (by simp [mixed, Layout.next, torus, hr])
  cases hl : link with
  | false =>
    exact into (H _ .east _ rfl hq (by simp [mixed, Layout.next, torus, hl]))
  | true =>
    have he := H _ .east (.linkE q) rfl hq (by simp [mixed, Layout.next, torus, hl])
    exact into (H _ .east _ (by simp [present, hl]) he (by simp [mixed, Layout.next, torus, hl]))

theorem north_empty
    (H : ∀ c k d, present ring link c = true → s c = none →
      (mixed (torus hw hh ring link)).next k c = some d → s d = none)
    {q : Position w h} (hq : s (.junction q) = none) :
    s (.junction ((northDirection w h hh).next q)) = none := by
  have out : s ((torus hw hh ring link).outN q) = none →
      s (.junction ((northDirection w h hh).next q)) = none := by
    intro ho
    cases hl : link with
    | false => simpa [Layout.outN, torus, hl] using ho
    | true =>
      have ho' : s (.linkN q) = none := by simpa [Layout.outN, torus, hl] using ho
      exact H _ .north _ (by simp [present, hl]) ho' (by simp [mixed, Layout.next, torus, hl])
  cases hr : ring q with
  | false => exact out (H _ .north _ rfl hq (by simp [mixed, Layout.next, torus, hr]))
  | true =>
    have hb := H _ .north (.quadN q) rfl hq (by simp [mixed, Layout.next, torus, hr])
    exact out (H _ .north _ (by simp [present, hr]) hb (by simp [mixed, Layout.next, torus, hr]))

/-- Stepping a coordinate forward reaches every residue. -/
theorem cyclic_reach {n : Nat} (hn : 0 < n) (P : Fin n → Prop)
    (hstep : ∀ i, P i → P (cyclicNext n hn i)) (i : Fin n) (hi : P i) : ∀ j, P j := by
  have hd : ∀ d, P ⟨(i.val + d) % n, Nat.mod_lt _ hn⟩ := by
    intro d
    induction d with
    | zero => simpa [Nat.mod_eq_of_lt i.isLt] using hi
    | succ d ih =>
      have := hstep _ ih
      have heq : cyclicNext n hn ⟨(i.val + d) % n, Nat.mod_lt _ hn⟩ =
          ⟨(i.val + (d + 1)) % n, Nat.mod_lt _ hn⟩ := by
        apply Fin.ext
        simp only [cyclicNext]
        split
        · rename_i hlt
          simp only
          rw [← Nat.add_assoc, Nat.add_mod (i.val + d) 1, Nat.mod_eq_of_lt (a := 1) (by omega)]
          · exact (Nat.mod_eq_of_lt hlt).symm
        · rename_i hge
          simp only
          have hlt := Nat.mod_lt (i.val + d) hn
          have heqn : (i.val + d) % n + 1 = n := by omega
          rw [← Nat.add_assoc, Nat.add_mod (i.val + d) 1]
          rcases Nat.lt_or_ge 1 n with h1 | h1
          · rw [Nat.mod_eq_of_lt h1, heqn, Nat.mod_self]
          · have : n = 1 := by omega
            subst this
            simp [Nat.mod_one]
      rwa [heq] at this
  intro j
  have := hd (j.val + n - i.val)
  have hj : (i.val + (j.val + n - i.val)) % n = j.val := by
    have := i.isLt
    rw [show i.val + (j.val + n - i.val) = j.val + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt j.isLt]
  have hfin : (⟨(i.val + (j.val + n - i.val)) % n, Nat.mod_lt _ hn⟩ : Fin n) = j := Fin.ext hj
  rwa [hfin] at this

/-- If every cell behind an empty cell is empty, the whole grid is empty. -/
theorem all_junctions_empty
    (H : ∀ c k d, present ring link c = true → s c = none →
      (mixed (torus hw hh ring link)).next k c = some d → s d = none)
    {q : Position w h} (hq : s (.junction q) = none) : ∀ p, s (.junction p) = none := by
  have row : ∀ y : Fin h, s (.junction (q.1, y)) = none → ∀ x : Fin w, s (.junction (x, y)) = none :=
    fun y hy => cyclic_reach hw (fun x => s (.junction (x, y)) = none)
      (fun x hx => by simpa [eastDirection] using east_empty H hx) q.1 hy
  have col : ∀ y : Fin h, s (.junction (q.1, y)) = none :=
    cyclic_reach hh (fun y => s (.junction (q.1, y)) = none)
      (fun y hy => by simpa [northDirection] using north_empty H hy) q.2 (by simpa using hq)
  intro p
  exact row p.2 (col p.2) p.1

/-- The cell after an existing private cell, on its route, also exists, and
an existing empty cell leads within two steps to an empty junction. -/
theorem reaches_empty_junction
    (H : ∀ c k d, present ring link c = true → s c = none →
      (mixed (torus hw hh ring link)).next k c = some d → s d = none)
    {c : Grid w h} (hp : present ring link c = true) (hc : s c = none) :
    ∃ q, s (.junction q) = none := by
  cases c with
  | junction q => exact ⟨q, hc⟩
  | quadE q =>
    exact ⟨q, H _ .east (.junction q) hp hc
      (by simp [present] at hp; simp [mixed, Layout.next, torus, hp])⟩
  | linkE q =>
    have hl : link = true := by simpa [present] using hp
    have hi := H _ .east ((torus hw hh ring link).intoE ((eastDirection w h hw).next q)) hp hc
      (by simp [mixed, Layout.next, torus, hl])
    cases hr : ring ((eastDirection w h hw).next q) with
    | false => exact ⟨_, by simpa [Layout.intoE, torus, hr] using hi⟩
    | true =>
      have hi' : s (.quadE ((eastDirection w h hw).next q)) = none := by
        simpa [Layout.intoE, torus, hr] using hi
      exact ⟨_, H _ .east (.junction ((eastDirection w h hw).next q)) (by simp [present, hr]) hi'
        (by simp [mixed, Layout.next, torus, hr])⟩
  | linkN q =>
    have hl : link = true := by simpa [present] using hp
    exact ⟨_, H _ .north (.junction ((northDirection w h hh).next q)) hp hc
      (by simp [mixed, Layout.next, torus, hl])⟩
  | quadN q =>
    have hr : ring q = true := by simpa [present] using hp
    have ho := H _ .north ((torus hw hh ring link).outN q) hp hc
      (by simp [mixed, Layout.next, torus, hr])
    cases hl : link with
    | false => exact ⟨_, by simpa [Layout.outN, torus, hl] using ho⟩
    | true =>
      have ho' : s (.linkN q) = none := by simpa [Layout.outN, torus, hl] using ho
      exact ⟨_, H _ .north (.junction ((northDirection w h hh).next q)) (by simp [present, hl]) ho'
        (by simp [mixed, Layout.next, torus, hl])⟩

/-- **Room for one more.** A gridlock with a car and an empty cell has an empty
cell whose next cell, for some species, is occupied. -/
theorem stuck_extendable (hs : Stuck (mixed (torus hw hh ring link)) s)
    (hne : ∃ c, (s c).isSome = true) {c0 : Grid w h} (hp0 : present ring link c0 = true)
    (hc0 : s c0 = none) :
    ∃ c k d, s c = none ∧ (mixed (torus hw hh ring link)).next k c = some d ∧ (s d).isSome = true := by
  apply Classical.byContradiction
  intro hno
  have H : ∀ c k d, present ring link c = true → s c = none →
      (mixed (torus hw hh ring link)).next k c = some d → s d = none := by
    intro c k d _ hc hn
    cases hd : s d with
    | none => rfl
    | some j => exact absurd ⟨c, k, d, hc, hn, by simp [hd]⟩ hno
  obtain ⟨q, hq⟩ := reaches_empty_junction H hp0 hc0
  obtain ⟨c, hc⟩ := hne
  obtain ⟨p, hpj⟩ := stuck_has_junction hs hc
  rw [all_junctions_empty H hq p] at hpj
  cases hpj

/-- **Theorem MX-G, every count.** For every street, and every `n` from its
number of cells up to the number of cells of the grid, some gridlock has
exactly `n` cars. -/
theorem gridlock_every_count (start : List (Grid w h)) (k0 : Species)
    (hstart : Stuck (mixed (torus hw hh ring link)) (fill start k0)) (hnd : start.Nodup)
    (hpos : 0 < start.length) :
    ∀ n, start.length ≤ n → n ≤ (gridCells ring link).length →
      ∃ s : Config (Grid w h) Species, Stuck (mixed (torus hw hh ring link)) s ∧ carCount s = n := by
  intro n hlo hhi
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases heq : start.length = n + 1
    · exact ⟨_, hstart, (fill_carCount start k0 hnd).trans heq⟩
    · obtain ⟨s, hs, hcount⟩ := ih (by omega) (by omega)
      -- some cell of the grid is empty
      have hroom : ∃ c, present ring link c = true ∧ s c = none := by
        apply Classical.byContradiction
        intro hfull
        have hsub : gridCells ring link ⊆ (allSites w h).filter fun c => (s c).isSome := by
          intro c hc
          refine List.mem_filter.mpr ⟨mem_allSites c, ?_⟩
          cases hsc : s c with
          | none => exact absurd ⟨c, mem_gridCells.mp hc, hsc⟩ hfull
          | some _ => rfl
        have := gridCells_nodup.length_le_of_subset hsub
        change _ ≤ carCount s at this
        omega
      obtain ⟨c0, hp0, hc0⟩ := hroom
      have hne : ∃ c, (s c).isSome = true := by
        apply Classical.byContradiction
        intro hnone
        have : carCount s = 0 := by
          simp only [carCount, List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro c _ hc
          exact hnone ⟨c, by simpa using hc⟩
        omega
      obtain ⟨c, k, d, hc, hn, hd⟩ := stuck_extendable hs hne hp0 hc0
      exact ⟨place s c k, stuck_place hs hn hd, by rw [carCount_place hc, hcount]⟩

/-- MX-G at every count, from a cheapest row street. -/
theorem row_gridlock_every_count (y : Fin h) (n : Nat)
    (hlo : (rowStreet ring link y).length ≤ n) (hhi : n ≤ (gridCells ring link).length) :
    ∃ s : Config (Grid w h) Species, Stuck (mixed (torus hw hh ring link)) s ∧ carCount s = n :=
  gridlock_every_count _ .east (row_gridlock (hw := hw) (hh := hh) y).1
    (rowStreet_nodup ring link y) (by rw [rowStreet_length]; omega) n hlo hhi

theorem col_gridlock_every_count (x : Fin w) (n : Nat)
    (hlo : (colStreet ring link x).length ≤ n) (hhi : n ≤ (gridCells ring link).length) :
    ∃ s : Config (Grid w h) Species, Stuck (mixed (torus hw hh ring link)) s ∧ carCount s = n :=
  gridlock_every_count _ .north (col_gridlock (hw := hw) (hh := hh) x).1
    (colStreet_nodup ring link x) (by rw [colStreet_length]; omega) n hlo hhi

/-- **Theorem MX-G.** On the `w × h` torus, for every roundabout set and with
or without links, a gridlock with exactly `n` cars exists iff some straight
street has at most `n` cells and the grid has at least `n`. -/
theorem gridlock_count_iff (n : Nat) :
    (∃ s : Config (Grid w h) Species,
      Stuck (mixed (torus hw hh ring link)) s ∧ (∃ c, (s c).isSome = true) ∧ carCount s = n) ↔
    ((∃ y, (rowStreet ring link y).length ≤ n) ∨ (∃ x, (colStreet ring link x).length ≤ n)) ∧
      n ≤ (gridCells ring link).length := by
  constructor
  · rintro ⟨s, hs, hne, rfl⟩
    exact ⟨stuck_carCount_ge_street hs hne, stuck_carCount_le_cells hs⟩
  · rintro ⟨hlo | hlo, hhi⟩
    · obtain ⟨y, hy⟩ := hlo
      obtain ⟨s, hs, hc⟩ := row_gridlock_every_count (hw := hw) (hh := hh) y n hy hhi
      refine ⟨s, hs, ?_, hc⟩
      apply Classical.byContradiction
      intro hnone
      have : carCount s = 0 := by
        simp only [carCount, List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro c _ hc'
        exact hnone ⟨c, by simpa using hc'⟩
      rw [rowStreet_length] at hy
      omega
    · obtain ⟨x, hx⟩ := hlo
      obtain ⟨s, hs, hc⟩ := col_gridlock_every_count (hw := hw) (hh := hh) x n hx hhi
      refine ⟨s, hs, ?_, hc⟩
      apply Classical.byContradiction
      intro hnone
      have : carCount s = 0 := by
        simp only [carCount, List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro c _ hc'
        exact hnone ⟨c, by simpa using hc'⟩
      rw [colStreet_length] at hx
      omega

end Torus

end BML.Net
