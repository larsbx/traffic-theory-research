import BML.NetInstances
import BML.Gridlock

/-!
# The least gridlock of a signal/roundabout grid (Theorem MX-G, lower bound)

The junction cells of a stuck state of the mixed grid form a BML jam, so the
torus winding theorem applies to them. A stuck state with a car therefore
contains a full east street, a full north street, or at least `w + h`
occupied junctions, and its car count is bounded below accordingly.
-/
namespace BML.Net

variable {α : Type} {L : Layout α} {s : Config (Site α) Species}

/-- Private cells hold only their own species, and only where they exist. -/
theorem stuck_linkE {p : α} {k : Species} (hs : Stuck (mixed L) s) (h : s (.linkE p) = some k) :
    k = .east ∧ L.link = true := by
  obtain ⟨c, hn, _⟩ := hs _ k h
  cases k <;> cases hl : L.link <;> simp_all [mixed, Layout.next]

theorem stuck_linkN {p : α} {k : Species} (hs : Stuck (mixed L) s) (h : s (.linkN p) = some k) :
    k = .north ∧ L.link = true := by
  obtain ⟨c, hn, _⟩ := hs _ k h
  cases k <;> cases hl : L.link <;> simp_all [mixed, Layout.next]

theorem stuck_quadE {p : α} {k : Species} (hs : Stuck (mixed L) s) (h : s (.quadE p) = some k) :
    k = .east ∧ L.ring p = true := by
  obtain ⟨c, hn, _⟩ := hs _ k h
  cases k <;> cases hl : L.ring p <;> simp_all [mixed, Layout.next]

theorem stuck_quadN {p : α} {k : Species} (hs : Stuck (mixed L) s) (h : s (.quadN p) = some k) :
    k = .north ∧ L.ring p = true := by
  obtain ⟨c, hn, _⟩ := hs _ k h
  cases k <;> cases hl : L.ring p <;> simp_all [mixed, Layout.next]

/-- An occupied cell of a stuck state, with the species it must hold. -/
private theorem occupied_as {c : Site α} (ho : (s c).isSome = true) : ∃ k, s c = some k := by
  cases hc : s c with
  | none => simp [hc] at ho
  | some k => exact ⟨k, rfl⟩

/-- Behind an east car in a junction, the whole segment to the next junction is full. -/
theorem east_segment {p : α} (hs : Stuck (mixed L) s) (hp : s (.junction p) = some .east) :
    (L.link = true → s (.linkE p) = some .east) ∧
    (L.ring (L.east.next p) = true → s (.quadE (L.east.next p)) = some .east) ∧
    (s (.junction (L.east.next p))).isSome = true := by
  have quad : L.ring (L.east.next p) = true → s (.quadE (L.east.next p)) = some .east →
      (s (.junction (L.east.next p))).isSome = true := by
    intro hr hq
    obtain ⟨c, hn, ho⟩ := hs _ _ hq
    simp only [mixed, Layout.next, hr, ↓reduceIte, Option.some.injEq] at hn
    exact hn ▸ ho
  have into : (s (L.intoE (L.east.next p))).isSome = true →
      (L.ring (L.east.next p) = true → s (.quadE (L.east.next p)) = some .east) ∧
      (s (.junction (L.east.next p))).isSome = true := by
    intro ho
    cases hr : L.ring (L.east.next p) with
    | false => exact ⟨by simp, by simpa [Layout.intoE, hr] using ho⟩
    | true =>
      obtain ⟨k, hk⟩ := occupied_as (by simpa [Layout.intoE, hr] using ho)
      have hq : s (.quadE (L.east.next p)) = some .east := (stuck_quadE hs hk).1 ▸ hk
      exact ⟨fun _ => hq, quad hr hq⟩
  obtain ⟨c, hn, ho⟩ := hs _ _ hp
  cases hl : L.link with
  | false =>
    simp only [mixed, Layout.next, hl, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn
    exact ⟨by simp, into (hn ▸ ho)⟩
  | true =>
    simp only [mixed, Layout.next, hl, ↓reduceIte, Option.some.injEq] at hn
    obtain ⟨k, hk⟩ := occupied_as (hn ▸ ho)
    have he : s (.linkE p) = some .east := (stuck_linkE hs hk).1 ▸ hk
    obtain ⟨c', hn', ho'⟩ := hs _ _ he
    simp only [mixed, Layout.next, hl, ↓reduceIte, Option.some.injEq] at hn'
    exact ⟨fun _ => he, into (hn' ▸ ho')⟩

/-- Ahead of a north car in a junction, the whole segment to the next junction is full. -/
theorem north_segment {p : α} (hs : Stuck (mixed L) s) (hp : s (.junction p) = some .north) :
    (L.ring p = true → s (.quadN p) = some .north) ∧
    (L.link = true → s (.linkN p) = some .north) ∧
    (s (.junction (L.north.next p))).isSome = true := by
  have link : L.link = true → s (.linkN p) = some .north →
      (s (.junction (L.north.next p))).isSome = true := by
    intro hl hq
    obtain ⟨c, hn, ho⟩ := hs _ _ hq
    simp only [mixed, Layout.next, hl, ↓reduceIte, Option.some.injEq] at hn
    exact hn ▸ ho
  have out : (s (L.outN p)).isSome = true →
      (L.link = true → s (.linkN p) = some .north) ∧
      (s (.junction (L.north.next p))).isSome = true := by
    intro ho
    cases hl : L.link with
    | false => exact ⟨by simp, by simpa [Layout.outN, hl] using ho⟩
    | true =>
      obtain ⟨k, hk⟩ := occupied_as (by simpa [Layout.outN, hl] using ho)
      have hq : s (.linkN p) = some .north := (stuck_linkN hs hk).1 ▸ hk
      exact ⟨fun _ => hq, link hl hq⟩
  obtain ⟨c, hn, ho⟩ := hs _ _ hp
  cases hr : L.ring p with
  | false =>
    simp only [mixed, Layout.next, hr, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn
    exact ⟨by simp, out (hn ▸ ho)⟩
  | true =>
    simp only [mixed, Layout.next, hr, ↓reduceIte, Option.some.injEq] at hn
    obtain ⟨k, hk⟩ := occupied_as (hn ▸ ho)
    have hq : s (.quadN p) = some .north := (stuck_quadN hs hk).1 ▸ hk
    obtain ⟨c', hn', ho'⟩ := hs _ _ hq
    simp only [mixed, Layout.next, hr, ↓reduceIte, Option.some.injEq] at hn'
    exact ⟨fun _ => hq, out (hn' ▸ ho')⟩

/-- The junction cells alone, as a BML board. -/
def junctions (s : Config (Site α) Species) : BML.Config α := fun p =>
  match s (.junction p) with
  | none => .empty
  | some k => k.cell

theorem junctions_east {p : α} : junctions s p = .east ↔ s (.junction p) = some .east := by
  unfold junctions
  cases h : s (.junction p) with
  | none => simp
  | some k => cases k <;> simp [Species.cell]

theorem junctions_north {p : α} : junctions s p = .north ↔ s (.junction p) = some .north := by
  unfold junctions
  cases h : s (.junction p) with
  | none => simp
  | some k => cases k <;> simp [Species.cell]

theorem junctions_occupied {p : α} :
    junctions s p ≠ .empty ↔ (s (.junction p)).isSome = true := by
  unfold junctions
  cases h : s (.junction p) with
  | none => simp
  | some k => cases k <;> simp [Species.cell]

/-- **Projection.** The junctions of a stuck state are a frozen BML board. -/
theorem junctions_frozen (hs : Stuck (mixed L) s) : Frozen L.east L.north (junctions s) :=
  ⟨fun _ hp => junctions_occupied.mpr (east_segment hs (junctions_east.mp hp)).2.2,
   fun _ hp => junctions_occupied.mpr (north_segment hs (junctions_north.mp hp)).2.2⟩

/-- Every car of a stuck state is queued behind an occupied junction. -/
theorem stuck_has_junction (hs : Stuck (mixed L) s) {c : Site α} (hc : (s c).isSome = true) :
    ∃ p, (s (.junction p)).isSome = true := by
  obtain ⟨k, hk⟩ := occupied_as hc
  have step : ∀ {c' : Site α} {k' : Species}, s c' = some k' →
      ∃ d, (mixed L).next k' c' = some d ∧ (s d).isSome = true := fun h => hs _ _ h
  cases c with
  | junction p => exact ⟨p, hc⟩
  | quadE p =>
    obtain ⟨hke, hr⟩ := stuck_quadE hs hk
    obtain ⟨d, hn, ho⟩ := step hk
    subst hke
    simp only [mixed, Layout.next, hr, ↓reduceIte, Option.some.injEq] at hn
    exact ⟨p, hn ▸ ho⟩
  | linkN p =>
    obtain ⟨hkn, hl⟩ := stuck_linkN hs hk
    obtain ⟨d, hn, ho⟩ := step hk
    subst hkn
    simp only [mixed, Layout.next, hl, ↓reduceIte, Option.some.injEq] at hn
    exact ⟨_, hn ▸ ho⟩
  | linkE p =>
    obtain ⟨hke, hl⟩ := stuck_linkE hs hk
    obtain ⟨d, hn, ho⟩ := step hk
    subst hke
    simp only [mixed, Layout.next, hl, ↓reduceIte, Option.some.injEq] at hn
    subst hn
    cases hr : L.ring (L.east.next p) with
    | false =>
      have hj : (s (.junction (L.east.next p))).isSome = true := by
        simpa [Layout.intoE, hr] using ho
      exact ⟨_, hj⟩
    | true =>
      have hq : (s (.quadE (L.east.next p))).isSome = true := by
        simpa [Layout.intoE, hr] using ho
      obtain ⟨k', hk'⟩ := occupied_as hq
      obtain ⟨hke', _⟩ := stuck_quadE hs hk'
      obtain ⟨d', hn', ho'⟩ := step hk'
      subst hke'
      simp only [mixed, Layout.next, hr, ↓reduceIte, Option.some.injEq] at hn'
      exact ⟨_, hn' ▸ ho'⟩
  | quadN p =>
    obtain ⟨hkn, hr⟩ := stuck_quadN hs hk
    obtain ⟨d, hn, ho⟩ := step hk
    subst hkn
    simp only [mixed, Layout.next, hr, ↓reduceIte, Option.some.injEq] at hn
    subst hn
    cases hl : L.link with
    | false =>
      have hj : (s (.junction (L.north.next p))).isSome = true := by
        simpa [Layout.outN, hl] using ho
      exact ⟨_, hj⟩
    | true =>
      have hq : (s (.linkN p)).isSome = true := by simpa [Layout.outN, hl] using ho
      obtain ⟨k', hk'⟩ := occupied_as hq
      obtain ⟨hkn', _⟩ := stuck_linkN hs hk'
      obtain ⟨d', hn', ho'⟩ := step hk'
      subst hkn'
      simp only [mixed, Layout.next, hl, ↓reduceIte, Option.some.injEq] at hn'
      exact ⟨_, hn' ▸ ho'⟩

/-! ## The torus -/

section Torus

variable {w h : Nat}

/-- The mixed grid on the `w × h` torus. -/
def torus (hw : 0 < w) (hh : 0 < h) (ring : Position w h → Bool) (link : Bool) :
    Layout (Position w h) :=
  ⟨eastDirection w h hw, northDirection w h hh, ring, link⟩

/-- `blocker_walk_lift` with the step counts tied to the species met on the walk. -/
theorem blocker_walk_lift_species (hw : 0 < w) (hh : 0 < h)
    (b : BML.Config (Position w h)) (p : Position w h) (k : Nat) :
    ∃ e n u v : Nat, e + n = k ∧
      p.1.val + e = (iterate (blocker w h hw hh b) k p).1.val + w * u ∧
      p.2.val + n = (iterate (blocker w h hw hh b) k p).2.val + h * v ∧
      (0 < e ↔ ∃ i, i < k ∧ b (iterate (blocker w h hw hh b) i p) = .east) ∧
      (0 < n ↔ ∃ i, i < k ∧ b (iterate (blocker w h hw hh b) i p) ≠ .east) := by
  induction k with
  | zero => exact ⟨0, 0, 0, 0, by simp [iterate]⟩
  | succ k ih =>
    obtain ⟨e, n, u, v, hen, hx, hy, hE, hN⟩ := ih
    let q := iterate (blocker w h hw hh b) k p
    have hqx : q.1.val < w := q.1.isLt
    have hqy : q.2.val < h := q.2.isLt
    change p.1.val + e = q.1.val + w * u at hx
    change p.2.val + n = q.2.val + h * v at hy
    by_cases he : b q = .east
    · have hE' : (0 < e + 1 ↔ ∃ i, i < k + 1 ∧ b (iterate (blocker w h hw hh b) i p) = .east) :=
        ⟨fun _ => ⟨k, by omega, he⟩, fun _ => by omega⟩
      have hN' : (0 < n ↔ ∃ i, i < k + 1 ∧ b (iterate (blocker w h hw hh b) i p) ≠ .east) := by
        rw [hN]
        constructor
        · rintro ⟨i, hi, hne⟩
          exact ⟨i, by omega, hne⟩
        · rintro ⟨i, hi, hne⟩
          by_cases hik : i = k
          · subst hik
            exact absurd he hne
          · exact ⟨i, by omega, hne⟩
      by_cases hwrap : q.1.val + 1 < w
      · refine ⟨e + 1, n, u, v, by omega, ?_, ?_, hE', hN'⟩
        · change p.1.val + (e + 1) = (blocker w h hw hh b q).1.val + w * u
          simp [blocker, he, eastDirection, cyclicNext, hwrap]
          omega
        · change p.2.val + n = (blocker w h hw hh b q).2.val + h * v
          simpa [blocker, he, eastDirection] using hy
      · refine ⟨e + 1, n, u + 1, v, by omega, ?_, ?_, hE', hN'⟩
        · change p.1.val + (e + 1) = (blocker w h hw hh b q).1.val + w * (u + 1)
          simp [blocker, he, eastDirection, cyclicNext, hwrap, Nat.mul_add]
          omega
        · change p.2.val + n = (blocker w h hw hh b q).2.val + h * v
          simpa [blocker, he, eastDirection] using hy
    · have hN' : (0 < n + 1 ↔ ∃ i, i < k + 1 ∧ b (iterate (blocker w h hw hh b) i p) ≠ .east) :=
        ⟨fun _ => ⟨k, by omega, he⟩, fun _ => by omega⟩
      have hE' : (0 < e ↔ ∃ i, i < k + 1 ∧ b (iterate (blocker w h hw hh b) i p) = .east) := by
        rw [hE]
        constructor
        · rintro ⟨i, hi, heq⟩
          exact ⟨i, by omega, heq⟩
        · rintro ⟨i, hi, heq⟩
          by_cases hik : i = k
          · subst hik
            exact absurd heq he
          · exact ⟨i, by omega, heq⟩
      by_cases hwrap : q.2.val + 1 < h
      · refine ⟨e, n + 1, u, v, by omega, ?_, ?_, hE', hN'⟩
        · change p.1.val + e = (blocker w h hw hh b q).1.val + w * u
          simpa [blocker, he, northDirection] using hx
        · change p.2.val + (n + 1) = (blocker w h hw hh b q).2.val + h * v
          simp [blocker, he, northDirection, cyclicNext, hwrap]
          omega
      · refine ⟨e, n + 1, u, v + 1, by omega, ?_, ?_, hE', hN'⟩
        · change p.1.val + e = (blocker w h hw hh b q).1.val + w * u
          simpa [blocker, he, northDirection] using hx
        · change p.2.val + (n + 1) = (blocker w h hw hh b q).2.val + h * (v + 1)
          simp [blocker, he, northDirection, cyclicNext, hwrap, Nat.mul_add]
          omega

/-- A coordinate that advanced by `t < m` steps round a cycle of length `m`
reaches every residue. -/
private theorem reach (m a c : Nat) (ha : a < m) (hc : c < m) :
    ∃ t, t < m ∧ ∀ q u, q < m → a + t = q + m * u → q = c := by
  by_cases hac : a ≤ c
  · refine ⟨c - a, by omega, fun q u hq heq => ?_⟩
    rcases Nat.eq_zero_or_pos u with rfl | hu
    · omega
    · have := Nat.le_mul_of_pos_right m hu
      omega
  · refine ⟨c + m - a, by omega, fun q u hq heq => ?_⟩
    rcases Nat.lt_or_ge u 1 with hu | hu
    · have : u = 0 := by omega
      subst this
      omega
    · rcases Nat.lt_or_ge u 2 with hu2 | hu2
      · have : u = 1 := by omega
        subst this
        omega
      · have := Nat.mul_le_mul_left m hu2
        omega

/-- A closed blocker walk of a frozen board that meets only east cars passes
through every cell of its row. -/
theorem east_cycle_fills_row (hw : 0 < w) (hh : 0 < h) (b : BML.Config (Position w h))
    (p : Position w h) (k : Nat) (hk : 0 < k)
    (hclose : iterate (blocker w h hw hh b) k p = p)
    (hall : ∀ i, i < k → b (iterate (blocker w h hw hh b) i p) = .east) (x : Fin w) :
    b (x, p.2) = .east := by
  -- the walk never leaves east cars, so it winds: k is a positive multiple of w
  obtain ⟨e, n, u, v, hen, hx, _, _, hN⟩ := blocker_walk_lift_species hw hh b p k
  have hn0 : n = 0 := by
    apply Classical.byContradiction
    intro hn
    obtain ⟨i, hi, hne⟩ := hN.mp (by omega)
    exact hne (hall i hi)
  rw [hclose] at hx
  have hkw : w ≤ k := by
    rcases Nat.eq_zero_or_pos u with rfl | hu
    · omega
    · have := Nat.le_mul_of_pos_right w hu
      omega
  obtain ⟨t, ht, hreach⟩ := reach w p.1.val x.val p.1.isLt x.isLt
  obtain ⟨e', n', u', v', hen', hx', hy', _, hN'⟩ := blocker_walk_lift_species hw hh b p t
  have hn0' : n' = 0 := by
    apply Classical.byContradiction
    intro hn
    obtain ⟨i, hi, hne⟩ := hN'.mp (by omega)
    exact hne (hall i (by omega))
  have he' : e' = t := by omega
  subst he' hn0'
  let q := iterate (blocker w h hw hh b) e' p
  have hq1 : q.1.val = x.val := hreach q.1.val u' q.1.isLt hx'
  have hq2 : q.2.val = p.2.val := by
    have hlt := q.2.isLt
    have hp := p.2.isLt
    rcases Nat.eq_zero_or_pos v' with rfl | hv
    · change p.2.val + 0 = q.2.val + h * 0 at hy'
      omega
    · have := Nat.le_mul_of_pos_right h hv
      change p.2.val + 0 = q.2.val + h * v' at hy'
      omega
  have hq : q = (x, p.2) := Prod.ext (Fin.ext hq1) (Fin.ext hq2)
  rw [← hq]
  exact hall e' (by omega)

/-- The mirror statement: a closed walk meeting only north cars fills its column. -/
theorem north_cycle_fills_column (hw : 0 < w) (hh : 0 < h) (b : BML.Config (Position w h))
    (p : Position w h) (k : Nat) (hk : 0 < k)
    (hclose : iterate (blocker w h hw hh b) k p = p)
    (hall : ∀ i, i < k → b (iterate (blocker w h hw hh b) i p) = .north) (y : Fin h) :
    b (p.1, y) = .north := by
  obtain ⟨e, n, u, v, hen, _, hy, hE, _⟩ := blocker_walk_lift_species hw hh b p k
  have he0 : e = 0 := by
    apply Classical.byContradiction
    intro he
    obtain ⟨i, hi, heq⟩ := hE.mp (by omega)
    rw [hall i hi] at heq
    cases heq
  rw [hclose] at hy
  have hkh : h ≤ k := by
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · omega
    · have := Nat.le_mul_of_pos_right h hv
      omega
  obtain ⟨t, ht, hreach⟩ := reach h p.2.val y.val p.2.isLt y.isLt
  obtain ⟨e', n', u', v', hen', hx', hy', hE', _⟩ := blocker_walk_lift_species hw hh b p t
  have he0' : e' = 0 := by
    apply Classical.byContradiction
    intro he
    obtain ⟨i, hi, heq⟩ := hE'.mp (by omega)
    rw [hall i (by omega)] at heq
    cases heq
  have hn' : n' = t := by omega
  subst hn' he0'
  let q := iterate (blocker w h hw hh b) n' p
  have hq2 : q.2.val = y.val := hreach q.2.val v' q.2.isLt hy'
  have hq1 : q.1.val = p.1.val := by
    have hlt := q.1.isLt
    have hp := p.1.isLt
    rcases Nat.eq_zero_or_pos u' with rfl | hu
    · change p.1.val + 0 = q.1.val + w * 0 at hx'
      omega
    · have := Nat.le_mul_of_pos_right w hu
      change p.1.val + 0 = q.1.val + w * u' at hx'
      omega
  have hq : q = (p.1, y) := Prod.ext (Fin.ext hq1) (Fin.ext hq2)
  rw [← hq]
  exact hall n' (by omega)

/-- A closed blocker walk that meets both an east car and a non-east cell winds
in both directions, so it has at least `w + h` steps. -/
theorem mixed_cycle_long (hw : 0 < w) (hh : 0 < h) (b : BML.Config (Position w h))
    (p : Position w h) (k : Nat)
    (hclose : iterate (blocker w h hw hh b) k p = p)
    (heast : ∃ i, i < k ∧ b (iterate (blocker w h hw hh b) i p) = .east)
    (hother : ∃ i, i < k ∧ b (iterate (blocker w h hw hh b) i p) ≠ .east) : w + h ≤ k := by
  obtain ⟨e, n, u, v, hen, hx, hy, hE, hN⟩ := blocker_walk_lift_species hw hh b p k
  rw [hclose] at hx hy
  have he : 0 < e := hE.mpr heast
  have hn : 0 < n := hN.mpr hother
  have hwe : w ≤ e := by
    rcases Nat.eq_zero_or_pos u with rfl | hu
    · omega
    · have := Nat.le_mul_of_pos_right w hu
      omega
  have hhn : h ≤ n := by
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · omega
    · have := Nat.le_mul_of_pos_right h hv
      omega
  omega

/-! ### Counting cars -/

/-- Every cell of the grid, existing or not. -/
def allSites (w h : Nat) : List (Site (Position w h)) :=
  (positions w h).flatMap fun p => [.junction p, .quadE p, .quadN p, .linkE p, .linkN p]

theorem mem_allSites (c : Site (Position w h)) : c ∈ allSites w h := by
  unfold allSites
  cases c with
  | _ p => exact List.mem_flatMap.mpr ⟨p, mem_positions w h p, by simp⟩

/-- The number of occupied cells. -/
def carCount (s : Config (Site (Position w h)) Species) : Nat :=
  ((allSites w h).filter fun c => (s c).isSome).length

/-- Distinct occupied cells are a lower bound for the car count. -/
theorem length_le_carCount {s : Config (Site (Position w h)) Species}
    (l : List (Site (Position w h))) (hl : l.Nodup) (ho : ∀ c, c ∈ l → (s c).isSome = true) :
    l.length ≤ carCount s :=
  hl.length_le_of_subset fun c hc => List.mem_filter.mpr ⟨mem_allSites c, ho c hc⟩

private theorem nodup_map {β γ : Type} (f : β → γ) (hf : ∀ a b, f a = f b → a = b)
    {l : List β} (hl : l.Nodup) : (l.map f).Nodup :=
  List.pairwise_map.mpr (List.Pairwise.imp (fun hne heq => hne (hf _ _ heq)) hl)

/-- The cells of the east street of row `y`: junctions, links, roundabout quadrants. -/
def rowStreet (ring : Position w h → Bool) (link : Bool) (y : Fin h) : List (Site (Position w h)) :=
  (List.finRange w).map (fun x => .junction (x, y)) ++
    ((if link then (List.finRange w).map (fun x => Site.linkE (x, y)) else []) ++
      ((List.finRange w).filter fun x => ring (x, y)).map (fun x => .quadE (x, y)))

/-- The cells of the north street of column `x`. -/
def colStreet (ring : Position w h → Bool) (link : Bool) (x : Fin w) : List (Site (Position w h)) :=
  (List.finRange h).map (fun y => .junction (x, y)) ++
    ((if link then (List.finRange h).map (fun y => Site.linkN (x, y)) else []) ++
      ((List.finRange h).filter fun y => ring (x, y)).map (fun y => .quadN (x, y)))

/-- A row street has `w` junctions, `w` links if there are links, and one cell
per roundabout: `(1 + ℓ)·w + r_y`. -/
theorem rowStreet_length (ring : Position w h → Bool) (link : Bool) (y : Fin h) :
    (rowStreet ring link y).length =
      w + (if link then w else 0) + ((List.finRange w).filter fun x => ring (x, y)).length := by
  cases link <;> simp [rowStreet, Nat.add_assoc]

theorem colStreet_length (ring : Position w h → Bool) (link : Bool) (x : Fin w) :
    (colStreet ring link x).length =
      h + (if link then h else 0) + ((List.finRange h).filter fun y => ring (x, y)).length := by
  cases link <;> simp [colStreet, Nat.add_assoc]

theorem rowStreet_nodup (ring : Position w h → Bool) (link : Bool) (y : Fin h) :
    (rowStreet ring link y).Nodup := by
  have hfin := List.nodup_finRange w
  have hj : ((List.finRange w).map fun x => Site.junction ((x, y) : Position w h)).Nodup :=
    nodup_map _ (fun a b hab => by simpa using hab) hfin
  have hl : ((List.finRange w).map fun x => Site.linkE ((x, y) : Position w h)).Nodup :=
    nodup_map _ (fun a b hab => by simpa using hab) hfin
  have hq : (((List.finRange w).filter fun x => ring (x, y)).map
      fun x => Site.quadE ((x, y) : Position w h)).Nodup :=
    nodup_map _ (fun a b hab => by simpa using hab) (List.Nodup.sublist List.filter_sublist hfin)
  unfold rowStreet
  cases link
  · refine List.nodup_append.mpr ⟨hj, ?_, ?_⟩
    · simpa using hq
    · intro a ha b hb
      simp only [List.mem_map, Bool.false_eq_true, ↓reduceIte, List.nil_append] at ha hb
      obtain ⟨_, _, rfl⟩ := ha
      obtain ⟨_, _, rfl⟩ := hb
      simp
  · refine List.nodup_append.mpr ⟨hj, List.nodup_append.mpr ⟨by simpa using hl, hq, ?_⟩, ?_⟩
    · intro a ha b hb
      simp only [↓reduceIte, List.mem_map] at ha hb
      obtain ⟨_, _, rfl⟩ := ha
      obtain ⟨_, _, rfl⟩ := hb
      simp
    · intro a ha b hb
      simp only [List.mem_map, ↓reduceIte, List.mem_append] at ha hb
      obtain ⟨_, _, rfl⟩ := ha
      rcases hb with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simp

theorem colStreet_nodup (ring : Position w h → Bool) (link : Bool) (x : Fin w) :
    (colStreet ring link x).Nodup := by
  have hfin := List.nodup_finRange h
  have hj : ((List.finRange h).map fun y => Site.junction ((x, y) : Position w h)).Nodup :=
    nodup_map _ (fun a b hab => by simpa using hab) hfin
  have hl : ((List.finRange h).map fun y => Site.linkN ((x, y) : Position w h)).Nodup :=
    nodup_map _ (fun a b hab => by simpa using hab) hfin
  have hq : (((List.finRange h).filter fun y => ring (x, y)).map
      fun y => Site.quadN ((x, y) : Position w h)).Nodup :=
    nodup_map _ (fun a b hab => by simpa using hab) (List.Nodup.sublist List.filter_sublist hfin)
  unfold colStreet
  cases link
  · refine List.nodup_append.mpr ⟨hj, ?_, ?_⟩
    · simpa using hq
    · intro a ha b hb
      simp only [List.mem_map, Bool.false_eq_true, ↓reduceIte, List.nil_append] at ha hb
      obtain ⟨_, _, rfl⟩ := ha
      obtain ⟨_, _, rfl⟩ := hb
      simp
  · refine List.nodup_append.mpr ⟨hj, List.nodup_append.mpr ⟨by simpa using hl, hq, ?_⟩, ?_⟩
    · intro a ha b hb
      simp only [↓reduceIte, List.mem_map] at ha hb
      obtain ⟨_, _, rfl⟩ := ha
      obtain ⟨_, _, rfl⟩ := hb
      simp
    · intro a ha b hb
      simp only [List.mem_map, ↓reduceIte, List.mem_append] at ha hb
      obtain ⟨_, _, rfl⟩ := ha
      rcases hb with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simp

/-! ### The least gridlock -/

variable {hw : 0 < w} {hh : 0 < h} {ring : Position w h → Bool} {link : Bool}
variable {s : Config (Site (Position w h)) Species}

/-- If every junction of a row holds an east car, the whole east street is full. -/
theorem row_full (hs : Stuck (mixed (torus hw hh ring link)) s) (y : Fin h)
    (hrow : ∀ x : Fin w, s (.junction (x, y)) = some .east) :
    ∀ c, c ∈ rowStreet ring link y → (s c).isSome = true := by
  intro c hc
  simp only [rowStreet, List.mem_append, List.mem_map, List.mem_filter] at hc
  rcases hc with ⟨x, _, rfl⟩ | hc | ⟨x, ⟨_, hr⟩, rfl⟩
  · simp [hrow x]
  · cases hl : link with
    | false => simp [hl] at hc
    | true =>
      simp only [hl, ↓reduceIte, List.mem_map] at hc
      obtain ⟨x, _, rfl⟩ := hc
      have := (east_segment hs (hrow x)).1 (by simpa [torus] using hl)
      simp [this]
  · have hseg := (east_segment hs (hrow (cyclicPrev w hw x))).2.1
    have hnext : (torus hw hh ring link).east.next (cyclicPrev w hw x, y) = (x, y) :=
      (eastDirection w h hw).next_prev (x, y)
    rw [hnext] at hseg
    simp [hseg (by simpa [torus] using hr)]

/-- If every junction of a column holds a north car, the whole north street is full. -/
theorem col_full (hs : Stuck (mixed (torus hw hh ring link)) s) (x : Fin w)
    (hcol : ∀ y : Fin h, s (.junction (x, y)) = some .north) :
    ∀ c, c ∈ colStreet ring link x → (s c).isSome = true := by
  intro c hc
  simp only [colStreet, List.mem_append, List.mem_map, List.mem_filter] at hc
  rcases hc with ⟨y, _, rfl⟩ | hc | ⟨y, ⟨_, hr⟩, rfl⟩
  · simp [hcol y]
  · cases hl : link with
    | false => simp [hl] at hc
    | true =>
      simp only [hl, ↓reduceIte, List.mem_map] at hc
      obtain ⟨y, _, rfl⟩ := hc
      have := (north_segment hs (hcol y)).2.1 (by simpa [torus] using hl)
      simp [this]
  · have := (north_segment hs (hcol y)).1 (by simpa [torus] using hr)
    simp [this]

/-- **Structure of a gridlock.** A stuck state with a car has a full east
street, or a full north street, or a simple blocker cycle through at least
`w + h` junctions together with the link cells behind them. -/
theorem stuck_carCount_cases (hs : Stuck (mixed (torus hw hh ring link)) s)
    (hne : ∃ c, (s c).isSome = true) :
    (∃ y, (rowStreet ring link y).length ≤ carCount s) ∨
    (∃ x, (colStreet ring link x).length ≤ carCount s) ∨
    (w + h) + (if link then w + h else 0) ≤ carCount s := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨p0, hp0⟩ := stuck_has_junction hs hc
  let J := junctions s
  have hfrozen : Frozen (eastDirection w h hw) (northDirection w h hh) J := junctions_frozen hs
  have hjam : Jam (eastDirection w h hw) (northDirection w h hh) J :=
    ⟨⟨p0, junctions_occupied.mpr hp0⟩, hfrozen⟩
  obtain ⟨p, k, hk, _, _, hret, hnodup, hocc⟩ := jam_has_simple_blocker_cycle w h hw hh J hjam
  by_cases hE : ∃ i, i < k ∧ J (iterate (blocker w h hw hh J) i p) = .east
  · by_cases hN : ∃ i, i < k ∧ J (iterate (blocker w h hw hh J) i p) ≠ .east
    · -- both species on the cycle: it is long
      right; right
      have hlong := mixed_cycle_long hw hh J p k hret hE hN
      let cyc := List.ofFn (fun i : Fin k => iterate (blocker w h hw hh J) i.val p)
      have hcyc : ∀ q, q ∈ cyc → J q ≠ .empty := by
        intro q hq
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hq
        exact hi ▸ hocc i
      let behind : Position w h → Site (Position w h) :=
        fun q => if J q = .east then .linkE q else .linkN q
      let cellsM := cyc.map Site.junction ++ (if link then cyc.map behind else [])
      have hbehind : ∀ a b, behind a = behind b → a = b := by
        intro a b hab
        by_cases ha : J a = .east <;> by_cases hb : J b = .east <;> simp_all [behind]
      have hnd : cellsM.Nodup := by
        refine List.nodup_append.mpr ⟨nodup_map _ (fun a b hab => by simpa using hab) hnodup, ?_, ?_⟩
        · cases link
          · simp
          · simp only [↓reduceIte]
            exact nodup_map behind hbehind hnodup
        · intro a ha b hb
          obtain ⟨qa, _, rfl⟩ := List.mem_map.mp ha
          cases link
          · simp at hb
          · simp only [↓reduceIte, List.mem_map] at hb
            obtain ⟨qb, _, rfl⟩ := hb
            by_cases hqb : J qb = .east <;> simp [behind, hqb]
      have hfull : ∀ c, c ∈ cellsM → (s c).isSome = true := by
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
          exact junctions_occupied.mp (hcyc q hq)
        · cases hl : link with
          | false => simp [hl] at hc
          | true =>
            simp only [hl, ↓reduceIte, List.mem_map] at hc
            obtain ⟨q, hq, rfl⟩ := hc
            by_cases hqe : J q = .east
            · have := (east_segment hs (junctions_east.mp hqe)).1 (by simpa [torus] using hl)
              simp [behind, hqe, this]
            · have hqn : J q = .north := by
                cases hJ : J q with
                | empty => exact absurd hJ (hcyc q hq)
                | east => exact absurd hJ hqe
                | north => rfl
              have := (north_segment hs (junctions_north.mp hqn)).2.1 (by simpa [torus] using hl)
              simp [behind, hqe, this]
      have hlen := length_le_carCount cellsM hnd hfull
      have hk' : cyc.length = k := by simp [cyc]
      cases link <;> simp [cellsM, hk'] at hlen ⊢ <;> omega
    · -- only east cars: a full row
      left
      have hall : ∀ i, i < k → J (iterate (blocker w h hw hh J) i p) = .east := by
        intro i hi
        apply Classical.byContradiction
        intro hne
        exact hN ⟨i, hi, hne⟩
      refine ⟨p.2, length_le_carCount _ (rowStreet_nodup ring link p.2) (row_full hs p.2 fun x => ?_)⟩
      exact junctions_east.mp (east_cycle_fills_row hw hh J p k hk hret hall x)
  · -- no east car: a full column
    right; left
    have hall : ∀ i, i < k → J (iterate (blocker w h hw hh J) i p) = .north := by
      intro i hi
      cases hJ : J (iterate (blocker w h hw hh J) i p) with
      | empty => exact absurd hJ (hocc ⟨i, hi⟩)
      | east => exact absurd ⟨i, hi, hJ⟩ hE
      | north => rfl
    refine ⟨p.1, length_le_carCount _ (colStreet_nodup ring link p.1) (col_full hs p.1 fun y => ?_)⟩
    exact junctions_north.mp (north_cycle_fills_column hw hh J p k hk hret hall y)

/-- **Theorem MX-G, lower bound.** On the `w × h` torus, for every roundabout
set and with or without links, a gridlock has at least as many cars as some
straight street has cells: `(1 + ℓ)·w + r_y` for a row, `(1 + ℓ)·h + c_x` for a
column (`rowStreet_length`, `colStreet_length`). -/
theorem stuck_carCount_ge_street (hs : Stuck (mixed (torus hw hh ring link)) s)
    (hne : ∃ c, (s c).isSome = true) :
    (∃ y, (rowStreet ring link y).length ≤ carCount s) ∨
    (∃ x, (colStreet ring link x).length ≤ carCount s) := by
  rcases stuck_carCount_cases hs hne with hrow | hcol | hmixed
  · exact Or.inl hrow
  · exact Or.inr hcol
  · by_cases hwh : w ≤ h
    · left
      refine ⟨⟨0, hh⟩, ?_⟩
      have hf : ((List.finRange w).filter fun x => ring (x, (⟨0, hh⟩ : Fin h))).length ≤ w := by
        simpa using List.length_filter_le (fun x => ring (x, (⟨0, hh⟩ : Fin h))) (List.finRange w)
      rw [rowStreet_length]
      cases link <;> simp at hmixed ⊢ <;> omega
    · right
      refine ⟨⟨0, hw⟩, ?_⟩
      have hf : ((List.finRange h).filter fun y => ring ((⟨0, hw⟩ : Fin w), y)).length ≤ h := by
        simpa using List.length_filter_le (fun y => ring ((⟨0, hw⟩ : Fin w), y)) (List.finRange h)
      rw [colStreet_length]
      cases link <;> simp at hmixed ⊢ <;> omega

/-! ### Attainment: a full street is a gridlock -/

theorem allSites_nodup (w h : Nat) : (allSites w h).Nodup := by
  unfold allSites
  refine List.pairwise_flatMap.mpr ⟨fun p _ => by simp, ?_⟩
  refine List.Pairwise.imp (fun {a b} hne x hx y hy => ?_) (positions_nodup w h)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl | rfl <;>
    simp [hne]

/-- The state whose cars are exactly the cells of `street`, all of one species. -/
def fill (street : List (Site (Position w h))) (k : Species) : Config (Site (Position w h)) Species :=
  fun c => if c ∈ street then some k else none

theorem fill_carCount (street : List (Site (Position w h))) (k : Species) (hnd : street.Nodup) :
    carCount (fill street k) = street.length := by
  apply Nat.le_antisymm
  · refine List.Nodup.length_le_of_subset ((allSites_nodup w h).filter _) fun c hc => ?_
    have := (List.mem_filter.mp hc).2
    by_cases hm : c ∈ street
    · exact hm
    · simp [fill, hm] at this
  · exact length_le_carCount street hnd fun c hc => by simp [fill, hc]

theorem fill_stuck (street : List (Site (Position w h))) (k : Species)
    (L : Layout (Position w h))
    (hclosed : ∀ c, c ∈ street → ∃ d, L.next k c = some d ∧ d ∈ street) :
    Stuck (mixed L) (fill street k) := by
  intro c j hj
  by_cases hm : c ∈ street
  · have hjk : j = k := by simpa [fill, hm] using hj.symm
    subst hjk
    obtain ⟨d, hn, hd⟩ := hclosed c hm
    exact ⟨d, hn, by simp [fill, hd]⟩
  · simp [fill, hm] at hj

theorem rowStreet_closed (y : Fin h) (c : Site (Position w h)) (hc : c ∈ rowStreet ring link y) :
    ∃ d, (torus hw hh ring link).next .east c = some d ∧ d ∈ rowStreet ring link y := by
  have into : ∀ x : Fin w, (torus hw hh ring link).intoE (x, y) ∈ rowStreet ring link y := by
    intro x
    cases hr : ring (x, y) <;> simp [Layout.intoE, torus, rowStreet, hr]
  have quad : ∀ x : Fin w, ring (x, y) = true →
      ∃ d, (torus hw hh ring link).next .east (.quadE (x, y)) = some d ∧
        d ∈ rowStreet ring link y :=
    fun x hr => ⟨.junction (x, y), by simp [Layout.next, torus, hr], by simp [rowStreet]⟩
  simp only [rowStreet, List.mem_append, List.mem_map, List.mem_filter] at hc
  cases link with
  | false =>
    rcases hc with ⟨x, _, rfl⟩ | hc | ⟨x, ⟨_, hr⟩, rfl⟩
    · exact ⟨_, rfl, into (cyclicNext w hw x)⟩
    · simp at hc
    · exact quad x hr
  | true =>
    rcases hc with ⟨x, _, rfl⟩ | hc | ⟨x, ⟨_, hr⟩, rfl⟩
    · exact ⟨.linkE (x, y), rfl, by simp [rowStreet]⟩
    · simp only [↓reduceIte, List.mem_map] at hc
      obtain ⟨x, _, rfl⟩ := hc
      exact ⟨_, rfl, into (cyclicNext w hw x)⟩
    · exact quad x hr

theorem colStreet_closed (x : Fin w) (c : Site (Position w h)) (hc : c ∈ colStreet ring link x) :
    ∃ d, (torus hw hh ring link).next .north c = some d ∧ d ∈ colStreet ring link x := by
  have out : ∀ y : Fin h, (torus hw hh ring link).outN (x, y) ∈ colStreet ring link x := by
    intro y
    cases hl : link <;> simp [Layout.outN, torus, colStreet, northDirection]
  have junction : ∀ y : Fin h,
      ∃ d, (torus hw hh ring link).next .north (.junction (x, y)) = some d ∧
        d ∈ colStreet ring link x := by
    intro y
    cases hr : ring (x, y) with
    | false => exact ⟨(torus hw hh ring link).outN (x, y), by simp [Layout.next, torus, hr], out y⟩
    | true => exact ⟨.quadN (x, y), by simp [Layout.next, torus, hr], by simp [colStreet, hr]⟩
  have quad : ∀ y : Fin h, ring (x, y) = true →
      ∃ d, (torus hw hh ring link).next .north (.quadN (x, y)) = some d ∧
        d ∈ colStreet ring link x :=
    fun y hr => ⟨(torus hw hh ring link).outN (x, y), by simp [Layout.next, torus, hr], out y⟩
  simp only [colStreet, List.mem_append, List.mem_map, List.mem_filter] at hc
  cases link with
  | false =>
    rcases hc with ⟨y, _, rfl⟩ | hc | ⟨y, ⟨_, hr⟩, rfl⟩
    · exact junction y
    · simp at hc
    · exact quad y hr
  | true =>
    rcases hc with ⟨y, _, rfl⟩ | hc | ⟨y, ⟨_, hr⟩, rfl⟩
    · exact junction y
    · simp only [↓reduceIte, List.mem_map] at hc
      obtain ⟨y, _, rfl⟩ := hc
      exact ⟨.junction (x, cyclicNext h hh y), rfl, by simp [colStreet]⟩
    · exact quad y hr

/-- **Theorem MX-G, attainment.** Filling one east street, or one north
street, is a gridlock with exactly as many cars as the street has cells. -/
theorem row_gridlock (y : Fin h) :
    Stuck (mixed (torus hw hh ring link)) (fill (rowStreet ring link y) .east) ∧
      carCount (fill (rowStreet ring link y) .east) = (rowStreet ring link y).length :=
  ⟨fill_stuck _ _ _ (rowStreet_closed y), fill_carCount _ _ (rowStreet_nodup ring link y)⟩

theorem col_gridlock (x : Fin w) :
    Stuck (mixed (torus hw hh ring link)) (fill (colStreet ring link x) .north) ∧
      carCount (fill (colStreet ring link x) .north) = (colStreet ring link x).length :=
  ⟨fill_stuck _ _ _ (colStreet_closed x), fill_carCount _ _ (colStreet_nodup ring link x)⟩

end Torus

end BML.Net
