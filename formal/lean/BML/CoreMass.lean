import BML.Absorption
import BML.FiniteSums
import BML.StoppedCore

/-!
Exact finite initial-weight normalization of stopped-car and maximal-core counts.

The positive common denominator is constructed from the area. Every nonzero
population divides it, so natural-number division below is exact, not a floor
approximation. Empty boards contribute zero. Weights remain on the initial
boards throughout evolution. No size-uniform late-formation estimate or
exchange of infinite-volume and long-time limits is used.
-/
namespace BML

/-- A positive common multiple of all populations up to `capacity` (the
factorial, including value one at capacity zero). -/
def populationDenominator : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * populationDenominator n

theorem populationDenominator_pos (capacity : Nat) :
    0 < populationDenominator capacity := by
  induction capacity with
  | zero => exact Nat.zero_lt_one
  | succ n ih => exact Nat.mul_pos (by omega) ih

theorem population_dvd_denominator (capacity n : Nat) (hn : 0 < n)
    (hcap : n ≤ capacity) : n ∣ populationDenominator capacity := by
  induction capacity with
  | zero => omega
  | succ capacity ih =>
    by_cases heq : n = capacity+1
    · subst n
      exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_mul_left_of_dvd (ih (by omega)) _

/-- Cancellation holds exactly for every admissible nonempty population. -/
theorem population_scale_exact (capacity n : Nat) (hn : 0 < n)
    (hcap : n ≤ capacity) : populationDenominator capacity / n * n =
      populationDenominator capacity :=
  Nat.div_mul_cancel (population_dvd_denominator capacity n hn hcap)

/-- Finite initial mass of a per-car count, multiplied by the explicit common
population denominator. Repeated support entries retain their multiplicity;
zero weights and empty boards are allowed. -/
def normalizedCountMass (capacity : Nat) (states : List α) (weight : α → Nat)
    (population count : α → Nat) : Nat :=
  (states.map fun s => weight s * (populationDenominator capacity / population s * count s)).sum

private theorem scaled_count_bounds (capacity n z : Nat) (jam lane : Bool)
    (hn : n ≤ capacity) (hj : jam = true → 0 < n)
    (hz : (if jam then n else 0) ≤ z ∧
      z ≤ (if jam then n else 0) + (if lane then n else 0)) :
    (if jam then populationDenominator capacity else 0) ≤
        populationDenominator capacity / n * z ∧
    populationDenominator capacity / n * z ≤
      (if jam then populationDenominator capacity else 0) +
      (if lane then populationDenominator capacity else 0) := by
  by_cases hzero : n = 0
  · have hjfalse : jam = false := by
      cases h : jam with
      | false => rfl
      | true => have := hj h; omega
    simp [hzero, hjfalse]
  · have he := population_scale_exact capacity n (by omega) hn
    have hscale : ∀ b : Bool,
        populationDenominator capacity / n * (if b then n else 0) =
          if b then populationDenominator capacity else 0 := by
      intro b
      cases b <;> simp [he]
    constructor
    · have h := Nat.mul_le_mul_left (populationDenominator capacity / n) hz.1
      simpa only [hscale] using h
    · have h := Nat.mul_le_mul_left (populationDenominator capacity / n) hz.2
      simpa only [Nat.mul_add, hscale] using h

private theorem weighted_indicator_sum (states : List α) (weight : α → Nat)
    (scale : Nat) (event : α → Bool) :
    (states.map fun s => weight s * (if event s then scale else 0)).sum =
      scale * Absorption.mass states weight event := by
  induction states with
  | nil => simp [Absorption.mass]
  | cons s states ih =>
    cases he : event s <;>
      simp [Absorption.mass, he, Nat.mul_add, Nat.mul_comm] at ih ⊢ <;> exact ih

/-- Exact normalized count/event comparison for arbitrary finite initial Nat
weights. Dividing by the positive population scale and positive total weight
gives the corresponding rational probability bound. -/
theorem normalizedCountMass_event_bounds (capacity : Nat)
    (states : List α) (weight population count : α → Nat) (jam lane : α → Bool)
    (hpop : ∀ s ∈ states, population s ≤ capacity)
    (hjam : ∀ s ∈ states, jam s = true → 0 < population s)
    (hcount : ∀ s ∈ states,
      (if jam s then population s else 0) ≤ count s ∧
      count s ≤ (if jam s then population s else 0) +
        (if lane s then population s else 0)) :
    populationDenominator capacity * Absorption.mass states weight jam ≤
        normalizedCountMass capacity states weight population count ∧
    normalizedCountMass capacity states weight population count ≤
      populationDenominator capacity *
        (Absorption.mass states weight jam + Absorption.mass states weight lane) := by
  have hscaled := fun s hs => scaled_count_bounds capacity (population s) (count s)
    (jam s) (lane s) (hpop s hs) (hjam s hs) (hcount s hs)
  constructor
  · rw [← weighted_indicator_sum]
    exact list_sum_map_le states _ _ (fun s hs =>
      Nat.mul_le_mul_left (weight s) (hscaled s hs).1)
  · have h := list_sum_map_le states
      (fun s => weight s * (populationDenominator capacity / population s * count s))
      (fun s => weight s * ((if jam s then populationDenominator capacity else 0) +
        (if lane s then populationDenominator capacity else 0)))
      (fun s hs => Nat.mul_le_mul_left (weight s) (hscaled s hs).2)
    simpa only [normalizedCountMass, Nat.mul_add, list_sum_map_add,
      weighted_indicator_sum] using h

/-- Pointwise eventual equality becomes one uniform eventual equality on a
finite initial support. Initial weights and populations are unchanged. -/
theorem normalizedCountMass_eventually_eq (capacity : Nat)
    (states : List α) (weight population limit : α → Nat) (count : Nat → α → Nat)
    (heventual : ∀ s ∈ states, ∃ start, ∀ t, count (start+t) s = limit s) :
    ∃ start, ∀ t,
      normalizedCountMass capacity states weight population (count (start+t)) =
        normalizedCountMass capacity states weight population limit := by
  obtain ⟨start, hs⟩ := eventually_uniform_on_list states
    (fun t s => count t s = limit s) heventual
  refine ⟨start, ?_⟩
  intro t
  unfold normalizedCountMass
  congr 1
  apply List.map_congr_left
  intro s hmem
  rw [hs s hmem t]

section Torus

variable {w h : Nat} (hw : 0 < w) (hh : 0 < h)

/-- The semantic event is eventual *nonempty* CLASSIC gridlock. -/
noncomputable def eventualJamFlag (s : Config (Position w h)) : Bool := by
  classical
  exact decide (EventuallyJammed (eastDirection w h hw) (northDirection w h hh) s)

/-- This exception is measured in the initial board, not under a fresh law
on an evolved snapshot. -/
noncomputable def initialFullLaneFlag (s : Config (Position w h)) : Bool := by
  classical
  exact decide (HasFullMonochromaticLane s)

@[simp] theorem eventualJamFlag_eq_true (s : Config (Position w h)) :
    eventualJamFlag hw hh s = true ↔
      EventuallyJammed (eastDirection w h hw) (northDirection w h hh) s := by
  classical
  simp [eventualJamFlag]

@[simp] theorem initialFullLaneFlag_eq_true (s : Config (Position w h)) :
    initialFullLaneFlag s = true ↔ HasFullMonochromaticLane s := by
  classical
  simp [initialFullLaneFlag]

/-- Unnormalized finite initial mass of the eventual per-car frozen fraction,
scaled by the positive, exact common population denominator. -/
noncomputable def normalizedStoppedMass
    (states : List (Config (Position w h))) (weight : Config (Position w h) → Nat) : Nat :=
  normalizedCountMass (w*h) states weight (carCount w h)
    (stoppedCarCount (eastDirection w h hw) (northDirection w h hh))

/-- At time `t` only the core count evolves; every weight and population in
the normalization still belongs to the original input configuration. -/
def normalizedCoreMass (states : List (Config (Position w h)))
    (weight : Config (Position w h) → Nat) (t : Nat) : Nat :=
  normalizedCountMass (w*h) states weight (carCount w h)
    (fun s => pathCoreCount (eastDirection w h hw) (northDirection w h hh)
      (iterate (torusStep w h hw hh) t s))

/-- Formal finite-law version of `q ≤ E[Z/N; N>0] ≤ q + P(R)`. No iid,
independence, or finite-time stopping oracle is assumed. A probability law is
obtained by dividing by the positive total initial weight and population scale. -/
theorem normalizedStoppedMass_gridlock_bounds
    (states : List (Config (Position w h))) (weight : Config (Position w h) → Nat) :
    populationDenominator (w*h) * Absorption.mass states weight (eventualJamFlag hw hh) ≤
        normalizedStoppedMass hw hh states weight ∧
    normalizedStoppedMass hw hh states weight ≤ populationDenominator (w*h) *
      (Absorption.mass states weight (eventualJamFlag hw hh) +
        Absorption.mass states weight initialFullLaneFlag) := by
  classical
  apply normalizedCountMass_event_bounds
  · intro s _
    exact carCount_le_area w h s
  · intro s _ hs
    exact eventuallyJammed_carCount_pos _ _ s ((eventualJamFlag_eq_true hw hh s).mp hs)
  · intro s _
    simpa [eventualJamFlag, initialFullLaneFlag] using
      (stoppedCarCount_jam_bounds (hw := hw) (hh := hh) s)

/-- On every finite initial support there is a common time after which the
normalized core mass equals the stopped-tag mass exactly, for all later
rounds. This is a finite-support statement, not a size-uniform deadline. -/
theorem normalizedCoreMass_eventually_eq_stoppedMass
    (states : List (Config (Position w h))) (weight : Config (Position w h) → Nat) :
    ∃ start, ∀ t, normalizedCoreMass hw hh states weight (start+t) =
      normalizedStoppedMass hw hh states weight := by
  exact normalizedCountMass_eventually_eq (w*h) states weight (carCount w h)
    (stoppedCarCount (eastDirection w h hw) (northDirection w h hh))
    (fun t s => pathCoreCount (eastDirection w h hw) (northDirection w h hh)
      (iterate (torusStep w h hw hh) t s))
    (fun s _ => pathCoreCount_eventually_eq_stoppedCarCount
      (eastDirection w h hw) (northDirection w h hh) s)

/-- The same finite-law gridlock interval holds for every sufficiently late
actual core snapshot, with one common time for the whole finite support. -/
theorem normalizedCoreMass_eventual_gridlock_bounds
    (states : List (Config (Position w h))) (weight : Config (Position w h) → Nat) :
    ∃ start, ∀ t,
      populationDenominator (w*h) * Absorption.mass states weight (eventualJamFlag hw hh) ≤
          normalizedCoreMass hw hh states weight (start+t) ∧
      normalizedCoreMass hw hh states weight (start+t) ≤ populationDenominator (w*h) *
        (Absorption.mass states weight (eventualJamFlag hw hh) +
          Absorption.mass states weight initialFullLaneFlag) := by
  obtain ⟨start, hs⟩ := normalizedCoreMass_eventually_eq_stoppedMass hw hh states weight
  refine ⟨start, ?_⟩
  intro t
  rw [hs t]
  exact normalizedStoppedMass_gridlock_bounds hw hh states weight

end Torus

end BML
