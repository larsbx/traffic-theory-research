import BML.ThinRigidity

/-!
Gap independence (blueprint B10.8).

A column's next state reads only that column and its two neighbours, and
full north columns never change. So a set `G` of columns whose outside
neighbours are full north evolves on its own: replacing every other column by
a full north column (`isolate G s`) leaves the orbit on `G` unchanged
(`iterate_isolate_agree`). With a full north column present, `s` eventually
jams iff each isolated member of a walled cover does (`eventuallyJammed_iff_cover`).

The gap after a full north column `x` is the run `x+1, …, x+g` of columns
that are not full north, ended by the full north column `x+g+1`. Its jam
status depends only on its `g` columns: it is the jam status of the *walled
gap* `gapConfig g word`, the torus of width `g + 1` whose last column is full
north (`isolate_gap_iff_gapJams`). On two rows this is the walled gap of
`bml/native/gap_jam.c`. Hence (`eventuallyJammed_iff_gaps`): a configuration
with a full north column jams iff every gap after a full north column jams as
a walled gap. This is the basis of the exact counts in `bml/thin_exact.py`.
All statements hold at every height.
-/
namespace BML

section GapIndependence

variable {w w' h : Nat} (hw : 0 < w) (hw' : 0 < w') (hh : 0 < h)

/-- Column `x` of `s` equals column `x'` of `u`; the tori may differ in width. -/
def AgreeAt (s : Config (Position w h)) (u : Config (Position w' h)) (x : Fin w) (x' : Fin w') :
    Prop :=
  ∀ y, s (x,y) = u (x',y)

theorem agreeAt_of_full (s : Config (Position w h)) (u : Config (Position w' h)) (x : Fin w)
    (x' : Fin w') (hs : FullNorthColumn s x) (hu : FullNorthColumn u x') : AgreeAt s u x x' :=
  fun y => (hs y).trans (hu y).symm

private theorem halfStep_eq_of_agree {α β : Type} (d₁ : Direction α) (d₂ : Direction β)
    (sp : Species) (s : Config α) (u : Config β) (p : α) (p' : β) (here : s p = u p')
    (ahead : s (d₁.next p) = u (d₂.next p')) (behind : s (d₁.prev p) = u (d₂.prev p')) :
    halfStep d₁ sp s p = halfStep d₂ sp u p' := by
  simp only [halfStep, here, ahead, behind]

/-- The column of a step reads only that column and its two neighbours. -/
theorem step_agreeAt (s : Config (Position w h)) (u : Config (Position w' h)) (x : Fin w)
    (x' : Fin w') (here : AgreeAt s u x x')
    (ahead : AgreeAt s u (cyclicNext w hw x) (cyclicNext w' hw' x'))
    (behind : AgreeAt s u (cyclicPrev w hw x) (cyclicPrev w' hw' x')) :
    AgreeAt (torusStep w h hw hh s) (torusStep w' h hw' hh u) x x' := by
  have heast : ∀ y, halfStep (eastDirection w h hw) .east s (x,y) =
      halfStep (eastDirection w' h hw') .east u (x',y) := fun y =>
    halfStep_eq_of_agree _ _ _ _ _ _ _ (here y) (ahead y) (behind y)
  exact fun y => halfStep_eq_of_agree _ _ _ _ _ _ _ (heast y) (heast _) (heast _)

theorem full_iterate (s : Config (Position w h)) (x : Fin w) (hx : FullNorthColumn s x) (t : Nat) :
    FullNorthColumn (iterate (torusStep w h hw hh) t s) x :=
  (fullNorthColumn_iterate_iff hw hh s x t).mpr hx

include hh in
theorem nonempty_of_full (s : Config (Position w h)) (x : Fin w) (hx : FullNorthColumn s x) :
    Nonempty s :=
  ⟨(x, ⟨0, hh⟩), by rw [hx]; decide⟩

/-- With a full north column, eventual gridlock is eventually being fixed. -/
theorem eventuallyJammed_iff_fixed (s : Config (Position w h)) (x : Fin w)
    (hx : FullNorthColumn s x) :
    EventuallyJammed (eastDirection w h hw) (northDirection w h hh) s ↔
      ∃ t, torusStep w h hw hh (iterate (torusStep w h hw hh) t s) =
        iterate (torusStep w h hw hh) t s :=
  ⟨fun ⟨t, ht⟩ => ⟨t, ((jam_iff_nonempty_fixed _ _ _).mp ht).2⟩,
    fun ⟨t, ht⟩ => ⟨t, (jam_iff_nonempty_fixed _ _ _).mpr
      ⟨nonempty_of_full hh _ x (full_iterate hw hh s x hx t), ht⟩⟩⟩

private theorem step_eq_of_columns (s : Config (Position w h))
    (hc : ∀ x, AgreeAt (torusStep w h hw hh s) s x x) : torusStep w h hw hh s = s :=
  funext fun p => hc p.1 p.2

private theorem full_step (s : Config (Position w h)) (x : Fin w) (hx : FullNorthColumn s x) :
    AgreeAt (torusStep w h hw hh s) s x x :=
  agreeAt_of_full _ _ x x (full_iterate hw hh s x hx 1) hx

private theorem fixed_later (s : Config (Position w h)) {t t' : Nat} (htt : t ≤ t')
    (hfix : torusStep w h hw hh (iterate (torusStep w h hw hh) t s) =
      iterate (torusStep w h hw hh) t s) :
    torusStep w h hw hh (iterate (torusStep w h hw hh) t' s) =
      iterate (torusStep w h hw hh) t' s := by
  unfold torusStep at *
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htt
  rw [reached_frozen_persists _ _ s t ((step_eq_iff_frozen _ _ _).mp hfix) k]
  exact hfix

private theorem exists_common_time {α : Type} (l : List α) (P : α → Nat → Prop)
    (mono : ∀ a t t', t ≤ t' → P a t → P a t') (h : ∀ a ∈ l, ∃ t, P a t) :
    ∃ T, ∀ a ∈ l, P a T := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a l ih =>
    obtain ⟨t, ht⟩ := h a (by simp)
    obtain ⟨T, hT⟩ := ih fun b hb => h b (by simp [hb])
    refine ⟨t + T, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact mono _ _ _ (by omega) ht
    · exact mono _ _ _ (by omega) (hT b hb)

/-! ### Walled column sets on one torus -/

/-- Every column outside `G` next to a column of `G` is full north. -/
def Walled (G : Fin w → Prop) (s : Config (Position w h)) : Prop :=
  ∀ x, G x → (G (cyclicNext w hw x) ∨ FullNorthColumn s (cyclicNext w hw x)) ∧
    (G (cyclicPrev w hw x) ∨ FullNorthColumn s (cyclicPrev w hw x))

/-- Agreement on `G`, with the outside neighbours of `G` full north in both. -/
def AgreeWalled (G : Fin w → Prop) (s u : Config (Position w h)) : Prop :=
  (∀ x, G x → AgreeAt s u x x) ∧ Walled hw G s ∧ Walled hw G u

theorem walled_step (G : Fin w → Prop) (s : Config (Position w h)) (hs : Walled hw G s) :
    Walled hw G (torusStep w h hw hh s) := fun x hx =>
  ⟨(hs x hx).1.imp_right (full_iterate hw hh s _ · 1),
    (hs x hx).2.imp_right (full_iterate hw hh s _ · 1)⟩

theorem agreeWalled_step (G : Fin w → Prop) (s u : Config (Position w h))
    (hsu : AgreeWalled hw G s u) :
    AgreeWalled hw G (torusStep w h hw hh s) (torusStep w h hw hh u) := by
  obtain ⟨hag, hs, hu⟩ := hsu
  have nbr : ∀ n, (G n ∨ FullNorthColumn s n) → (G n ∨ FullNorthColumn u n) →
      AgreeAt s u n n := by
    intro n h₁ h₂
    by_cases hg : G n
    · exact hag n hg
    · exact agreeAt_of_full s u n n (h₁.resolve_left hg) (h₂.resolve_left hg)
  exact ⟨fun x hx => step_agreeAt hw hw hh s u x x (hag x hx)
      (nbr _ (hs x hx).1 (hu x hx).1) (nbr _ (hs x hx).2 (hu x hx).2),
    walled_step hw hh G s hs, walled_step hw hh G u hu⟩

theorem agreeWalled_iterate (G : Fin w → Prop) (s u : Config (Position w h))
    (hsu : AgreeWalled hw G s u) (t : Nat) :
    AgreeWalled hw G (iterate (torusStep w h hw hh) t s) (iterate (torusStep w h hw hh) t u) := by
  induction t with
  | zero => exact hsu
  | succ t ih => exact agreeWalled_step hw hh G _ _ ih

/-- Every column outside `G` replaced by a full north column. -/
def isolate (G : Fin w → Prop) [DecidablePred G] (s : Config (Position w h)) :
    Config (Position w h) :=
  fun p => if G p.1 then s p else .north

theorem isolate_full (G : Fin w → Prop) [DecidablePred G] (s : Config (Position w h))
    (x : Fin w) (hx : ¬ G x) : FullNorthColumn (isolate G s) x := fun y => by
  simp [isolate, hx]

theorem isolate_full_of_full (G : Fin w → Prop) [DecidablePred G] (s : Config (Position w h))
    (x : Fin w) (hx : FullNorthColumn s x) : FullNorthColumn (isolate G s) x := fun y => by
  by_cases hg : G x <;> simp [isolate, hg, hx y]

theorem agreeWalled_isolate (G : Fin w → Prop) [DecidablePred G] (s : Config (Position w h))
    (hs : Walled hw G s) : AgreeWalled hw G s (isolate G s) := by
  refine ⟨fun x hx y => by simp [isolate, hx], hs, fun x hx => ?_⟩
  have side : ∀ n, G n ∨ FullNorthColumn s n → G n ∨ FullNorthColumn (isolate G s) n :=
    fun n hn => by
      by_cases hg : G n
      · exact Or.inl hg
      · exact Or.inr (isolate_full G s n hg)
  exact ⟨side _ (hs x hx).1, side _ (hs x hx).2⟩

/-- B10.8: on a walled column set the orbit of `s` is the orbit of its
isolated gap. -/
theorem iterate_isolate_agree (G : Fin w → Prop) [DecidablePred G] (s : Config (Position w h))
    (hs : Walled hw G s) (t : Nat) (x : Fin w) (hx : G x) :
    AgreeAt (iterate (torusStep w h hw hh) t s)
      (iterate (torusStep w h hw hh) t (isolate G s)) x x :=
  (agreeWalled_iterate hw hh G _ _ (agreeWalled_isolate hw G s hs) t).1 x hx

/-- A walled column set on which `s` and `u` agree is fixed in `u` once `s` is fixed. -/
private theorem fixed_on_walled (G : Fin w → Prop) (s u : Config (Position w h))
    (hsu : AgreeWalled hw G s u) (hs : torusStep w h hw hh s = s) (x : Fin w) (hx : G x) :
    AgreeAt (torusStep w h hw hh u) u x x := fun y => by
  have := (agreeWalled_step hw hh G s u hsu).1 x hx y
  rw [hs] at this
  exact this.symm.trans (hsu.1 x hx y)

/-- B10.8: with a full north column, `s` eventually jams iff each isolated
member of a walled cover of its other columns does. -/
theorem eventuallyJammed_iff_cover (s : Config (Position w h))
    (hplug : ∃ x, FullNorthColumn s x) {ι : Type} (l : List ι)
    (gap : ι → Fin w → Prop) [∀ i, DecidablePred (gap i)]
    (hcover : ∀ z, ¬ FullNorthColumn s z → ∃ i ∈ l, gap i z)
    (hwall : ∀ i ∈ l, Walled hw (gap i) s) :
    EventuallyJammed (eastDirection w h hw) (northDirection w h hh) s ↔
      ∀ i ∈ l, EventuallyJammed (eastDirection w h hw) (northDirection w h hh)
        (isolate (gap i) s) := by
  obtain ⟨x₀, hx₀⟩ := hplug
  have hwalled : ∀ i ∈ l, ∀ t, AgreeWalled hw (gap i)
      (iterate (torusStep w h hw hh) t s) (iterate (torusStep w h hw hh) t (isolate (gap i) s)) :=
    fun i hi t => agreeWalled_iterate hw hh _ _ _ (agreeWalled_isolate hw _ s (hwall i hi)) t
  have hiso : ∀ i, EventuallyJammed (eastDirection w h hw) (northDirection w h hh)
      (isolate (gap i) s) ↔ _ :=
    fun i => eventuallyJammed_iff_fixed hw hh _ x₀ (isolate_full_of_full (gap i) s x₀ hx₀)
  rw [eventuallyJammed_iff_fixed hw hh _ x₀ hx₀]
  simp only [hiso]
  constructor
  · rintro ⟨t, ht⟩ i hi
    refine ⟨t, step_eq_of_columns hw hh _ fun z => ?_⟩
    by_cases hz : gap i z
    · exact fixed_on_walled hw hh _ _ _ (hwalled i hi t) ht z hz
    · exact full_step hw hh _ z (full_iterate hw hh _ z (isolate_full _ s z hz) t)
  · intro hall
    obtain ⟨T, hT⟩ := exists_common_time l
      (fun i t => torusStep w h hw hh (iterate (torusStep w h hw hh) t (isolate (gap i) s)) =
          iterate (torusStep w h hw hh) t (isolate (gap i) s))
      (fun _ _ _ htt hP => fixed_later hw hh _ htt hP) hall
    refine ⟨T, step_eq_of_columns hw hh _ fun z => ?_⟩
    by_cases hz : FullNorthColumn s z
    · exact full_step hw hh _ z (full_iterate hw hh _ z hz T)
    · obtain ⟨i, hi, hgz⟩ := hcover z hz
      obtain ⟨a, b, c⟩ := hwalled i hi T
      exact fixed_on_walled hw hh _ _ _ ⟨fun x hx y => (a x hx y).symm, c, b⟩ (hT i hi) z hgz

/-! ### The walled gap on its own torus -/

/-- The `i`-th column east of `x`. -/
abbrev eastOf (x : Fin w) (i : Nat) : Fin w := iterate (cyclicNext w hw) i x

private theorem eastOf_succ (x : Fin w) (i : Nat) :
    eastOf hw x (i+1) = cyclicNext w hw (eastOf hw x i) := rfl

private theorem eastOf_prev (x : Fin w) (i : Nat) :
    cyclicPrev w hw (eastOf hw x (i+1)) = eastOf hw x i := cyclicPrev_next _ _ _

private theorem eastOf_val (x : Fin w) (i : Nat) : (eastOf hw x i).val = (x.val + i) % w :=
  iterate_cyclicNext_val w hw i x

/-- Simulation across tori: two configurations that agree along the runs
`x, x+1, …, x+g+1` and `x', …, x'+g+1`, with full north columns at both ends
and everywhere off the runs, jam together. -/
theorem eventuallyJammed_iff_of_simulation (s : Config (Position w h))
    (u : Config (Position w' h)) (x : Fin w) (x' : Fin w') (g : Nat)
    (hagree : ∀ i, i ≤ g + 1 → AgreeAt s u (eastOf hw x i) (eastOf hw' x' i))
    (hx : FullNorthColumn s x) (hend : FullNorthColumn s (eastOf hw x (g+1)))
    (hout : ∀ z, (∀ i, 1 ≤ i → i ≤ g → z ≠ eastOf hw x i) → FullNorthColumn s z)
    (hout' : ∀ z, (∀ i, 1 ≤ i → i ≤ g → z ≠ eastOf hw' x' i) → FullNorthColumn u z) :
    EventuallyJammed (eastDirection w h hw) (northDirection w h hh) s ↔
      EventuallyJammed (eastDirection w' h hw') (northDirection w' h hh) u := by
  have fullS : ∀ i, (i = 0 ∨ i = g + 1) → FullNorthColumn s (eastOf hw x i) := by
    rintro i (rfl | rfl)
    · exact hx
    · exact hend
  have fullU : ∀ i, (i = 0 ∨ i = g + 1) → FullNorthColumn u (eastOf hw' x' i) :=
    fun i hb y => by
      rw [← hagree i (by omega) y]
      exact fullS i hb y
  have rel : ∀ t, ∀ i, i ≤ g + 1 → AgreeAt (iterate (torusStep w h hw hh) t s)
      (iterate (torusStep w' h hw' hh) t u) (eastOf hw x i) (eastOf hw' x' i) := by
    intro t
    induction t with
    | zero => exact hagree
    | succ t ih =>
      intro i hi
      by_cases hb : i = 0 ∨ i = g + 1
      · exact agreeAt_of_full _ _ _ _ (full_iterate hw hh _ _ (fullS i hb) _)
          (full_iterate hw' hh _ _ (fullU i hb) _)
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        refine step_agreeAt hw hw' hh _ _ _ _ (ih _ hi) (ih (j+2) (by omega)) ?_
        rw [eastOf_prev, eastOf_prev]
        exact ih j (by omega)
  have onRun : ∀ {v : Nat} (hv : 0 < v) (c : Fin v) (r : Config (Position v h)),
      (∀ z, (∀ i, 1 ≤ i → i ≤ g → z ≠ eastOf hv c i) → FullNorthColumn r z) →
      (torusStep v h hv hh r = r ↔
        ∀ i, 1 ≤ i → i ≤ g → AgreeAt (torusStep v h hv hh r) r (eastOf hv c i) (eastOf hv c i)) := by
    intro v hv c r hr
    refine ⟨fun hfix i _ _ y => by rw [hfix], fun hall => step_eq_of_columns hv hh _ fun z => ?_⟩
    by_cases hz : ∃ i, 1 ≤ i ∧ i ≤ g ∧ z = eastOf hv c i
    · obtain ⟨i, h1, h2, rfl⟩ := hz
      exact hall i h1 h2
    · exact full_step hv hh _ z (hr z fun i h1 h2 he => hz ⟨i, h1, h2, he⟩)
  rw [eventuallyJammed_iff_fixed hw hh _ x hx,
    eventuallyJammed_iff_fixed hw' hh _ _ (fullU 0 (Or.inl rfl))]
  refine exists_congr fun t => ?_
  rw [onRun hw x _ fun z hz => full_iterate hw hh _ z (hout z hz) t,
    onRun hw' x' _ fun z hz => full_iterate hw' hh _ z (hout' z hz) t]
  refine forall_congr' fun i => forall_congr' fun h1 => forall_congr' fun h2 => ?_
  have hs := rel (t+1) i (by omega)
  have h0 := rel t i (by omega)
  exact ⟨fun ha y => (hs y).symm.trans ((ha y).trans (h0 y)),
    fun ha y => (hs y).trans ((ha y).trans (h0 y).symm)⟩

/-- The walled gap: `g` columns followed by one full north column, on the
torus of width `g + 1`. Its west wall is the same full north column. -/
def gapConfig (g : Nat) (word : Fin g → Fin h → Cell) : Config (Position (g+1) h) :=
  fun p => if hp : p.1.val < g then word ⟨p.1.val, hp⟩ p.2 else .north

/-- The walled gap eventually jams. -/
def GapJams (g : Nat) (word : Fin g → Fin h → Cell) : Prop :=
  EventuallyJammed (eastDirection (g+1) h (Nat.succ_pos g)) (northDirection (g+1) h hh)
    (gapConfig g word)

/-- `x` is full north, and the next full north column east of it is `x+g+1`. -/
def IsGapAfter (s : Config (Position w h)) (x : Fin w) (g : Nat) : Prop :=
  FullNorthColumn s x ∧ (∀ i, 1 ≤ i → i ≤ g → ¬ FullNorthColumn s (eastOf hw x i)) ∧
    FullNorthColumn s (eastOf hw x (g+1))

/-- The columns of the gap after `x`, west to east. -/
def gapWord (s : Config (Position w h)) (x : Fin w) (g : Nat) : Fin g → Fin h → Cell :=
  fun i y => s (eastOf hw x (i.val+1), y)

/-- The columns of the gap after `x` as a column set (empty unless it is a gap). -/
def gapSet (s : Config (Position w h)) (x : Fin w) (g : Nat) (z : Fin w) : Prop :=
  IsGapAfter hw s x g ∧ ∃ i, 1 ≤ i ∧ i ≤ g ∧ z = eastOf hw x i

theorem gapSet_walled (s : Config (Position w h)) (x : Fin w) (g : Nat) :
    Walled hw (gapSet hw s x g) s := by
  rintro z ⟨hgap, i, h1, h2, rfl⟩
  refine ⟨?_, ?_⟩
  · by_cases hi : i + 1 ≤ g
    · exact Or.inl ⟨hgap, i+1, by omega, hi, rfl⟩
    · rw [← eastOf_succ, show i + 1 = g + 1 by omega]
      exact Or.inr hgap.2.2
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [eastOf_prev]
    by_cases hj : j = 0
    · subst hj
      exact Or.inr hgap.1
    · exact Or.inl ⟨hgap, j, by omega, by omega, rfl⟩

open Classical in
/-- The isolated gap after `x` jams iff the walled gap of its columns does. -/
theorem isolate_gap_iff_gapJams (s : Config (Position w h)) (x : Fin w) (g : Nat)
    (hgap : IsGapAfter hw s x g) :
    EventuallyJammed (eastDirection w h hw) (northDirection w h hh)
        (isolate (gapSet hw s x g) s) ↔ GapJams hh g (gapWord hw s x g) := by
  let x' : Fin (g+1) := ⟨g, by omega⟩
  have inGap : ∀ i, 1 ≤ i → i ≤ g → (eastOf (Nat.succ_pos g) x' i).val = i - 1 := by
    intro i h1 h2
    rw [eastOf_val, show g + i = (i - 1) + 1 * (g + 1) by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have atWall : ∀ i, (i = 0 ∨ i = g + 1) → (eastOf (Nat.succ_pos g) x' i).val = g := by
    rintro i (rfl | rfl)
    · rw [eastOf_val, Nat.add_zero, Nat.mod_eq_of_lt (by simp [x'])]
    · rw [eastOf_val, show g + (g + 1) = g + 1 * (g + 1) by omega,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have wallNorth : ∀ z : Fin (g+1), z.val = g →
      FullNorthColumn (gapConfig g (gapWord hw s x g)) z :=
    fun z hz y => by simp [gapConfig, hz]
  refine eventuallyJammed_iff_of_simulation hw (Nat.succ_pos g) hh _ _ x x' g ?_
    (isolate_full_of_full _ s x hgap.1) (isolate_full_of_full _ s _ hgap.2.2) ?_ ?_
  · intro i hi
    by_cases hb : i = 0 ∨ i = g + 1
    · refine agreeAt_of_full _ _ _ _ ?_ (wallNorth _ (atWall i hb))
      rcases hb with rfl | rfl
      · exact isolate_full_of_full _ s x hgap.1
      · exact isolate_full_of_full _ s _ hgap.2.2
    · have h1 : 1 ≤ i := by omega
      have h2 : i ≤ g := by omega
      have hv := inGap i h1 h2
      have hlt : (eastOf (Nat.succ_pos g) x' i).val < g := by omega
      have hin : gapSet hw s x g (eastOf hw x i) := ⟨hgap, i, h1, h2, rfl⟩
      intro y
      have hlt' : i - 1 < g := by omega
      simp only [isolate, hin, ite_true, gapConfig, gapWord, hv, hlt', dite_true,
        show i - 1 + 1 = i by omega]
  · intro z hz
    exact isolate_full _ s z fun ⟨_, i, h1, h2, he⟩ => hz i h1 h2 he
  · intro z hz
    apply wallNorth
    have := z.isLt
    rcases Nat.lt_or_ge z.val g with hlt | hge
    · exact (hz (z.val + 1) (by omega) (by omega)
        (Fin.ext (by rw [inGap _ (by omega) (by omega)]; omega))).elim
    · omega

/-! ### Every gap of a configuration -/

private theorem exists_least (P : Nat → Prop) :
    ∀ n m, m ≤ n → P m → ∃ k, k ≤ m ∧ P k ∧ ∀ j, j < k → ¬ P j := by
  intro n
  induction n with
  | zero => intro m hm hp; exact ⟨m, Nat.le_refl _, hp, fun j hj => absurd hj (by omega)⟩
  | succ n ih =>
    intro m hm hp
    by_cases hq : ∃ j, j < m ∧ P j
    · obtain ⟨j, hj, hpj⟩ := hq
      obtain ⟨k, hk, hpk, hmin⟩ := ih j (by omega) hpj
      exact ⟨k, by omega, hpk, hmin⟩
    · exact ⟨m, Nat.le_refl _, hp, fun j hj hpj => hq ⟨j, hj, hpj⟩⟩

private theorem exists_greatest (P : Nat → Prop) (m : Nat) (h0 : P 0) :
    ∃ j, j ≤ m ∧ P j ∧ ∀ k, j < k → k ≤ m → ¬ P k := by
  induction m with
  | zero => exact ⟨0, Nat.le_refl _, h0, fun _ h1 h2 => absurd h1 (by omega)⟩
  | succ m ih =>
    by_cases hp : P (m + 1)
    · exact ⟨m + 1, Nat.le_refl _, hp, fun _ h1 h2 => absurd h1 (by omega)⟩
    · obtain ⟨j, hj, hpj, hmax⟩ := ih
      refine ⟨j, by omega, hpj, fun k h1 h2 hk => ?_⟩
      by_cases hk' : k = m + 1
      · exact hp (hk' ▸ hk)
      · exact hmax k h1 (by omega) hk

private theorem eastOf_add (x : Fin w) (a b : Nat) :
    eastOf hw (eastOf hw x a) b = eastOf hw x (a + b) :=
  (iterate_add _ x a b).symm

private theorem eastOf_full_circle (x : Fin w) : eastOf hw x w = x :=
  Fin.ext (by rw [eastOf_val, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt])

private theorem exists_eastOf (x z : Fin w) : ∃ m, m < w ∧ z = eastOf hw x m := by
  have hz := z.isLt
  have hx := x.isLt
  by_cases hle : x.val ≤ z.val
  · exact ⟨z.val - x.val, by omega, Fin.ext (by
      rw [eastOf_val, show x.val + (z.val - x.val) = z.val by omega, Nat.mod_eq_of_lt hz])⟩
  · exact ⟨z.val + w - x.val, by omega, Fin.ext (by
      rw [eastOf_val, show x.val + (z.val + w - x.val) = z.val + w by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hz])⟩

/-- Every column that is not full north lies in the gap after some full north
column. -/
theorem exists_gap (s : Config (Position w h)) (hplug : ∃ x, FullNorthColumn s x) (z : Fin w)
    (hz : ¬ FullNorthColumn s z) : ∃ x g, gapSet hw s x g z := by
  obtain ⟨x₀, hx₀⟩ := hplug
  obtain ⟨m, hm, rfl⟩ := exists_eastOf hw x₀ z
  obtain ⟨j, hj, hfj, hmax⟩ :=
    exists_greatest (fun j => FullNorthColumn s (eastOf hw x₀ j)) m hx₀
  have hjm : j < m := by
    rcases Nat.lt_or_ge j m with h | h
    · exact h
    · exact absurd (show m = j by omega ▸ hfj) hz
  obtain ⟨k, hk, hfk, hmin⟩ := exists_least
    (fun k => FullNorthColumn s (eastOf hw (eastOf hw x₀ j) (k+1))) (w - 1) (w - 1)
    (Nat.le_refl _) (by rw [show w - 1 + 1 = w by omega, eastOf_full_circle]; exact hfj)
  have hk' : m - j ≤ k := by
    rcases Nat.lt_or_ge k (m - j) with hlt | hge
    · have := hmax (j + (k+1)) (by omega) (by omega)
      rw [← eastOf_add] at this
      exact (this hfk).elim
    · exact hge
  refine ⟨eastOf hw x₀ j, k, ⟨hfj, fun i h1 h2 => ?_, hfk⟩, m - j, by omega, hk', ?_⟩
  · have := hmin (i - 1) (by omega)
    rwa [show i - 1 + 1 = i by omega] at this
  · rw [eastOf_add, show j + (m - j) = m by omega]

/-- A gap is shorter than the torus. -/
theorem IsGapAfter.lt {s : Config (Position w h)} {x : Fin w} {g : Nat}
    (hgap : IsGapAfter hw s x g) : g < w := by
  rcases Nat.lt_or_ge g w with hlt | hge
  · exact hlt
  · exact (hgap.2.1 w (by omega) hge ((eastOf_full_circle hw x).symm ▸ hgap.1)).elim

open Classical in
/-- B10.8, the form used for counting: a configuration with a full north
column eventually jams iff every gap after a full north column jams as a
walled gap. -/
theorem eventuallyJammed_iff_gaps (s : Config (Position w h))
    (hplug : ∃ x, FullNorthColumn s x) :
    EventuallyJammed (eastDirection w h hw) (northDirection w h hh) s ↔
      ∀ x g, IsGapAfter hw s x g → GapJams hh g (gapWord hw s x g) := by
  let l : List (Fin w × Nat) := (List.finRange w).flatMap fun x => (List.range w).map (x, ·)
  have hmem : ∀ x g, g < w → (x, g) ∈ l := fun x g hg =>
    List.mem_flatMap.mpr ⟨x, List.mem_finRange x, List.mem_map.mpr ⟨g, List.mem_range.mpr hg, rfl⟩⟩
  rw [eventuallyJammed_iff_cover hw hh s hplug l (fun i => gapSet hw s i.1 i.2)
    (fun z hz => by
      obtain ⟨x, g, hzg⟩ := exists_gap hw s hplug z hz
      exact ⟨(x, g), hmem x g hzg.1.lt, hzg⟩)
    (fun i _ => gapSet_walled hw s i.1 i.2)]
  constructor
  · intro hall x g hgap
    exact (isolate_gap_iff_gapJams hw hh s x g hgap).mp (hall (x, g) (hmem x g hgap.lt))
  · rintro hall ⟨x, g⟩ _
    by_cases hgap : IsGapAfter hw s x g
    · exact (isolate_gap_iff_gapJams hw hh s x g hgap).mpr (hall x g hgap)
    · obtain ⟨x₀, hx₀⟩ := hplug
      have hall' : ∀ z, FullNorthColumn (isolate (gapSet hw s x g) s) z :=
        fun z => isolate_full _ s z fun hz => hgap hz.1
      refine ⟨0, (jam_iff_nonempty_fixed _ _ _).mpr ⟨nonempty_of_full hh _ x₀ (hall' x₀), ?_⟩⟩
      exact step_eq_of_columns hw hh _ fun z => full_step hw hh _ z (hall' z)

end GapIndependence

end BML
