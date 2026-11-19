import BML.FreeFlow
import BML.FreePacking
import BML.PhaseCounts
import BML.FreeConstruction
import BML.FreePureBound
import BML.FreeDeletion
import BML.Arithmetic

/-!
Theorem F: the exact maximum population admitting CLASSIC free flow on every
positive rectangular torus. The upper bound applies to actual configurations;
the executable construction attains every population from zero to the bound.
-/
namespace BML

/-- Exact free-flow capacity, with a separate coprime pure-species case. -/
def freeMax (w h : Nat) : Nat :=
  if Nat.gcd w h = 1 then max (h * (w / 2)) (w * (h / 2))
  else (w * h / Nat.gcd w h) * ((2 * Nat.gcd w h) / 3)

/-- Thin a maximizing configuration to the requested population. Requests
above the maximum retain the maximum; the exact-count theorem assumes n≤freeMax. -/
def freeWith (w h : Nat) (hw : 0 < w) (n : Nat) : Config (Position w h) :=
  thinConfig w h (maxFreeConfig w h hw) n

theorem staticFree_carCount_le_freeMax (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (hs : StaticFree w h hw hh s) :
    carCount w h s ≤ freeMax w h := by
  by_cases hg : Nat.gcd w h = 1
  · simpa only [freeMax, ite_eq_left hg] using
      staticFree_coprime_carCount_le w h hw hh s hg hs
  · have hpos := Nat.gcd_pos_of_pos_left h hw
    rw [freeMax, ite_eq_right hg, carCount_eq_sum_phaseSpeciesCount w h hw s]
    exact cyclic_weighted_packing_bound (Nat.gcd w h) hpos (by omega)
      (w * h / Nat.gcd w h)
      (phaseSpeciesCount w h hw .east s) (phaseSpeciesCount w h hw .north s)
      (phaseSpeciesCount_add_le w h hw s)
      (phaseEastCount_add_next_le w h hw hh s hs)
      (phaseNorthCount_add_next_le w h hw hh s hs)
      (phaseCounts_cross_same w h hw hh s hs)
      (phaseCounts_cross_next w h hw hh s hs)

theorem maxFreeConfig_carCount_eq_freeMax (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    carCount w h (maxFreeConfig w h hw) = freeMax w h :=
  maxFreeConfig_carCount w h hw hh

theorem freeMax_le_area (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    freeMax w h ≤ w * h := by
  rw [← maxFreeConfig_carCount_eq_freeMax w h hw hh]
  exact carCount_le_area w h _

theorem freeWith_staticFree (w h : Nat) (hw : 0 < w) (hh : 0 < h) (n : Nat) :
    StaticFree w h hw hh (freeWith w h hw n) :=
  thinConfig_staticFree w h hw hh _ (maxFreeConfig_staticFree w h hw hh) n

theorem freeWith_carCount (w h : Nat) (hw : 0 < w) (hh : 0 < h) (n : Nat) :
    carCount w h (freeWith w h hw n) = min n (freeMax w h) := by
  rw [freeWith, thinConfig_carCount, maxFreeConfig_carCount_eq_freeMax w h hw hh]

theorem freeWith_carCount_of_le (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (n : Nat) (hn : n ≤ freeMax w h) : carCount w h (freeWith w h hw n) = n := by
  rw [freeWith_carCount w h hw hh n, Nat.min_eq_left hn]

/-- Static formulation of the complete population spectrum, including zero. -/
theorem exists_staticFree_with_count_iff (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (n : Nat) :
    (∃ s : Config (Position w h), StaticFree w h hw hh s ∧ carCount w h s = n) ↔
      n ≤ freeMax w h := by
  constructor
  · rintro ⟨s, hs, hn⟩
    rw [← hn]
    exact staticFree_carCount_le_freeMax w h hw hh s hs
  · intro hn
    exact ⟨freeWith w h hw n, freeWith_staticFree w h hw hh n,
      freeWith_carCount_of_le w h hw hh n hn⟩

/-- Dynamic Theorem F: every car moves in every round from time zero. -/
theorem exists_perpetual_allMove_with_count_iff (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (n : Nat) :
    (∃ s : Config (Position w h), carCount w h s = n ∧
      ∀ t, AllMove (eastDirection w h hw) (northDirection w h hh)
        (iterate (torusStep w h hw hh) t s)) ↔ n ≤ freeMax w h := by
  constructor
  · rintro ⟨s, hn, hm⟩
    exact (exists_staticFree_with_count_iff w h hw hh n).mp
      ⟨s, (lemmaR w h hw hh s).mpr hm, hn⟩
  · intro hn
    obtain ⟨s, hs, hc⟩ := (exists_staticFree_with_count_iff w h hw hh n).mpr hn
    exact ⟨s, hc, (lemmaR w h hw hh s).mp hs⟩

/-- Conservation makes the same capacity necessary for eventual free flow. -/
theorem eventual_allMove_carCount_le_freeMax (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h))
    (hs : ∃ T, ∀ t, AllMove (eastDirection w h hw) (northDirection w h hh)
      (iterate (torusStep w h hw hh) (T + t) s)) :
    carCount w h s ≤ freeMax w h := by
  obtain ⟨T, hT⟩ := (eventually_allMove_iff_reaches_staticFree w h hw hh s).mp hs
  have hbound := staticFree_carCount_le_freeMax w h hw hh _ hT
  simpa only [iterate_torusStep_carCount] using hbound

/-- The exact attainable populations are unchanged if an initial transient is allowed. -/
theorem exists_eventual_allMove_with_count_iff (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (n : Nat) :
    (∃ s : Config (Position w h), carCount w h s = n ∧
      ∃ T, ∀ t, AllMove (eastDirection w h hw) (northDirection w h hh)
        (iterate (torusStep w h hw hh) (T + t) s)) ↔ n ≤ freeMax w h := by
  constructor
  · rintro ⟨s, hn, hs⟩
    rw [← hn]
    exact eventual_allMove_carCount_le_freeMax w h hw hh s hs
  · intro hn
    obtain ⟨s, hc, hm⟩ := (exists_perpetual_allMove_with_count_iff w h hw hh n).mpr hn
    exact ⟨s, hc, 0, by simpa only [Nat.zero_add] using hm⟩

/-- A population above the capacity can never enter a free-flow state. -/
theorem above_freeMax_never_staticFree (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (hn : freeMax w h < carCount w h s) (t : Nat) :
    ¬ StaticFree w h hw hh (iterate (torusStep w h hw hh) t s) := by
  intro hs
  have hbound := staticFree_carCount_le_freeMax w h hw hh _ hs
  rw [iterate_torusStep_carCount] at hbound
  omega

/-- On a square the two branches combine into the familiar two-thirds formula. -/
theorem freeMax_square (L : Nat) (hL : 0 < L) :
    freeMax L L = L * ((2 * L) / 3) := by
  by_cases h1 : L = 1
  · subst L
    decide
  · simp only [freeMax, Nat.gcd_self, ite_eq_right h1, Nat.mul_div_cancel_left L hL]

/-- Exact density two thirds occurs on every positive square divisible by three. -/
theorem freeMax_square_attains_two_thirds_iff (L : Nat) (hL : 0 < L) :
    3 * freeMax L L = 2 * (L * L) ↔ 3 ∣ L := by
  rw [freeMax_square L hL, ← freeClasses_eq_two_thirds L]
  have hleft : 3 * (L * freeClasses L) = L * (3 * freeClasses L) := by
    simp only [Nat.mul_assoc, Nat.mul_comm]
  have hright : 2 * (L * L) = L * (2 * L) := by
    simp only [Nat.mul_assoc, Nat.mul_comm]
  rw [hleft, hright, Nat.mul_left_cancel_iff hL]
  exact freeClasses_attains_two_thirds_iff L

end BML
