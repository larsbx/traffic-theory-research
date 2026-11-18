import BML.Capture
import BML.Lanes

/-!
Explicit CLASSIC jams realizing prescribed east-row and north-column counts.

The construction is on a square torus. Its hypotheses are positivity of every
lane count and `r y + c x ≤ L` for every row and column, equivalently a bound
on the sum of the two maxima. Exact counts are proved for the executable
`eastRowCount` and `northColumnCount`; no count preservation is assumed.
-/
namespace BML

theorem profileDistance_zero_iff (n : Nat) (x target : Fin n) :
    cyclicDistance n x target = 0 ↔ x = target := by
  constructor
  · intro hz
    apply Fin.ext
    have hx := x.isLt
    have ht := target.isLt
    unfold cyclicDistance at hz
    split at hz <;> omega
  · rintro rfl
    simp [cyclicDistance]

theorem profileDistance_pos_iff (n : Nat) (x target : Fin n) :
    0 < cyclicDistance n x target ↔ x ≠ target := by
  have hz := profileDistance_zero_iff n x target
  constructor
  · intro hp he
    have hzero := hz.mpr he
    omega
  · intro hn
    have hzero : cyclicDistance n x target ≠ 0 := fun he => hn (hz.mp he)
    omega

theorem profileDistance_sum (n : Nat) (x y : Fin n) (hne : x ≠ y) :
    cyclicDistance n x y + cyclicDistance n y x = n := by
  have hx := x.isLt
  have hy := y.isLt
  have hv : x.val ≠ y.val := fun he => hne (Fin.ext he)
  unfold cyclicDistance
  split <;> split <;> omega

theorem profileDistance_to_next (n : Nat) (hn : 0 < n) (hlarge : 1 < n)
    (x : Fin n) : cyclicDistance n x (cyclicNext n hn x) = 1 := by
  have hx := x.isLt
  unfold cyclicNext cyclicDistance
  split <;> split <;> simp_all <;> omega

/-- Reflection `x ↦ target-x mod n`, represented using the existing distance. -/
def profileReflection (n : Nat) (hn : 0 < n) (target x : Fin n) : Fin n :=
  ⟨cyclicDistance n x target, by
    have hb := cyclicDistance_le n x target
    omega⟩

theorem profileReflection_involutive (n : Nat) (hn : 0 < n) (target x : Fin n) :
    profileReflection n hn target (profileReflection n hn target x) = x := by
  apply Fin.ext
  have hx := x.isLt
  have ht := target.isLt
  simp only [profileReflection, cyclicDistance]
  split <;> split <;> simp_all <;> omega

private theorem finRange_interval_count (n lower length : Nat)
    (hfit : lower+length ≤ n) :
    (List.finRange n).countP
      (fun x => decide (lower ≤ x.val ∧ x.val < lower+length)) = length := by
  let embed : Fin length → Fin n := fun i => ⟨lower+i.val, by have hi := i.isLt; omega⟩
  let xs := (List.finRange n).filter
    (fun x => decide (lower ≤ x.val ∧ x.val < lower+length))
  let ys := (List.finRange length).map embed
  have hinj : Function.Injective embed := by
    intro i j he
    apply Fin.ext
    have hv := congrArg Fin.val he
    change lower+i.val = lower+j.val at hv
    omega
  have hxnodup : xs.Nodup := (List.nodup_finRange n).filter _
  have hynodup : ys.Nodup := List.Pairwise.map embed
    (fun _ _ hne he => hne (hinj he)) (List.nodup_finRange length)
  have hmem : ∀ x, x ∈ xs ↔ x ∈ ys := by
    intro x
    simp only [xs, ys, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq, List.mem_map]
    constructor
    · intro hx
      refine ⟨⟨x.val-lower, by omega⟩, ?_⟩
      apply Fin.ext
      change lower+(x.val-lower) = x.val
      omega
    · rintro ⟨i, he⟩
      have hv := congrArg Fin.val he
      change lower+i.val = x.val at hv
      have hi := i.isLt
      omega
  have he := ((List.perm_ext_iff_of_nodup hxnodup hynodup).mpr hmem).length_eq
  simpa only [xs, ys, ← List.countP_eq_length_filter, List.length_map,
    List.length_finRange] using he

/-- Every cyclic interval has its specified length, proved by an explicit
involutive coordinate bijection and finite-list cardinality. -/
theorem profileDistance_interval_count (n : Nat) (hn : 0 < n) (target : Fin n)
    (lower length : Nat) (hfit : lower+length ≤ n) :
    (List.finRange n).countP (fun x => decide
      (lower ≤ cyclicDistance n x target ∧ cyclicDistance n x target < lower+length)) = length := by
  have he : ((List.finRange n).filter (fun x => decide
      (lower ≤ cyclicDistance n x target ∧ cyclicDistance n x target < lower+length))).length =
      ((List.finRange n).filter (fun x => decide
        (lower ≤ x.val ∧ x.val < lower+length))).length := by
    apply Train.Counting.filter_length_eq_of_bijection (List.finRange n)
      (List.nodup_finRange n) (fun x => List.mem_finRange x)
      (fun x => decide (lower ≤ cyclicDistance n x target ∧ cyclicDistance n x target < lower+length))
      (fun x => decide (lower ≤ x.val ∧ x.val < lower+length))
      (profileReflection n hn target)
    · intro x hx
      exact hx
    · intro x y _ _ heq
      have hh := congrArg (profileReflection n hn target) heq
      simpa only [profileReflection_involutive] using hh
    · intro y hy
      refine ⟨profileReflection n hn target y, ?_, profileReflection_involutive n hn target y⟩
      change decide (lower ≤ (profileReflection n hn target (profileReflection n hn target y)).val ∧
        (profileReflection n hn target (profileReflection n hn target y)).val < lower+length) = true
      rw [profileReflection_involutive]
      exact hy
  rw [List.countP_eq_length_filter, he, ← List.countP_eq_length_filter]
  exact finRange_interval_count n lower length hfit

/-- East queues end on the main diagonal; north queues end immediately below
it. This is the explicit modular placement `E(y-j,y)` and `N(x,x-i)`. -/
def laneProfileJam (L : Nat) (r c : Fin L → Nat) : Config (Position L L) := fun p =>
  if cyclicDistance L p.1 p.2 < r p.2 then .east
  else if 0 < cyclicDistance L p.2 p.1 ∧ cyclicDistance L p.2 p.1 ≤ c p.1
    then .north else .empty

theorem laneProfileJam_east_iff (L : Nat) (r c : Fin L → Nat) (p : Position L L) :
    laneProfileJam L r c p = .east ↔ cyclicDistance L p.1 p.2 < r p.2 := by
  by_cases he : cyclicDistance L p.1 p.2 < r p.2
  · simp [laneProfileJam, he]
  · by_cases hn : 0 < cyclicDistance L p.2 p.1 ∧ cyclicDistance L p.2 p.1 ≤ c p.1
    · simp [laneProfileJam, he, hn]
    · simp [laneProfileJam, he, hn]

theorem laneProfileJam_placements_disjoint (L : Nat) (r c : Fin L → Nat)
    (hsum : ∀ x y, r y+c x ≤ L) (p : Position L L)
    (he : cyclicDistance L p.1 p.2 < r p.2)
    (hn : 0 < cyclicDistance L p.2 p.1 ∧ cyclicDistance L p.2 p.1 ≤ c p.1) : False := by
  have hne := (profileDistance_pos_iff L p.2 p.1).mp hn.1
  have hd := profileDistance_sum L p.2 p.1 hne
  have hb := hsum p.1 p.2
  omega

theorem laneProfileJam_north_iff (L : Nat) (r c : Fin L → Nat)
    (hsum : ∀ x y, r y+c x ≤ L) (p : Position L L) :
    laneProfileJam L r c p = .north ↔
      0 < cyclicDistance L p.2 p.1 ∧ cyclicDistance L p.2 p.1 ≤ c p.1 := by
  constructor
  · intro hn
    by_cases he : cyclicDistance L p.1 p.2 < r p.2
    · simp [laneProfileJam, he] at hn
    · by_cases hc : 0 < cyclicDistance L p.2 p.1 ∧ cyclicDistance L p.2 p.1 ≤ c p.1
      · exact hc
      · simp [laneProfileJam, he, hc] at hn
  · intro hn
    have he : ¬ cyclicDistance L p.1 p.2 < r p.2 :=
      fun he => laneProfileJam_placements_disjoint L r c hsum p he hn
    simp [laneProfileJam, he, hn]

theorem laneProfileJam_eastRowCount (L : Nat) (hL : 0 < L)
    (r c : Fin L → Nat) (y : Fin L) (hfit : r y ≤ L) :
    eastRowCount (laneProfileJam L r c) y = r y := by
  have hp : (fun x : Fin L => decide (laneProfileJam L r c (x,y) = .east)) =
      (fun x => decide (0 ≤ cyclicDistance L x y ∧ cyclicDistance L x y < 0+r y)) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq, Nat.zero_le, true_and, Nat.zero_add] using
      laneProfileJam_east_iff L r c (x,y)
  unfold eastRowCount
  rw [hp]
  exact profileDistance_interval_count L hL y 0 (r y) (by omega)

theorem laneProfileJam_northColumnCount (L : Nat) (hL : 0 < L)
    (r c : Fin L → Nat) (hsum : ∀ x y, r y+c x ≤ L)
    (x : Fin L) (hfit : 1+c x ≤ L) :
    northColumnCount (laneProfileJam L r c) x = c x := by
  have hp : (fun y : Fin L => decide (laneProfileJam L r c (x,y) = .north)) =
      (fun y => decide (1 ≤ cyclicDistance L y x ∧ cyclicDistance L y x < 1+c x)) := by
    funext y
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    rw [laneProfileJam_north_iff L r c hsum (x,y)]
    change (0 < cyclicDistance L y x ∧ cyclicDistance L y x ≤ c x) ↔
      (1 ≤ cyclicDistance L y x ∧ cyclicDistance L y x < 1+c x)
    omega
  unfold northColumnCount
  rw [hp]
  exact profileDistance_interval_count L hL x 1 (c x) hfit

/-- Exact realization of both numerical lane profiles by the explicit state. -/
theorem laneProfileJam_counts (L : Nat) (hL : 0 < L) (r c : Fin L → Nat)
    (hr : ∀ y, 1 ≤ r y)
    (hsum : ∀ x y, r y+c x ≤ L) :
    (∀ y, eastRowCount (laneProfileJam L r c) y = r y) ∧
    (∀ x, northColumnCount (laneProfileJam L r c) x = c x) := by
  constructor
  · intro y
    apply laneProfileJam_eastRowCount L hL r c y
    have hb := hsum y y
    omega
  · intro x
    apply laneProfileJam_northColumnCount L hL r c hsum x
    have hb := hsum x x
    have hp := hr x
    omega

theorem laneProfileJam_diagonal_east (L : Nat) (r c : Fin L → Nat)
    (hr : ∀ y, 1 ≤ r y) (y : Fin L) : laneProfileJam L r c (y,y) = .east := by
  apply (laneProfileJam_east_iff L r c (y,y)).mpr
  have hp := hr y
  simp only [cyclicDistance, Nat.le_refl, ↓reduceIte, Nat.sub_self]
  omega

/-- Both CLASSIC blocking conditions hold: E queues end at the first N of the
next column, and N queues end at the diagonal E of their own column. -/
theorem laneProfileJam_frozen (L : Nat) (hL : 0 < L) (r c : Fin L → Nat)
    (hr : ∀ y, 1 ≤ r y) (hc : ∀ x, 1 ≤ c x)
    (hsum : ∀ x y, r y+c x ≤ L) :
    Frozen (eastDirection L L hL) (northDirection L L hL) (laneProfileJam L r c) := by
  have hlarge : 1 < L := by
    have he := hr ⟨0,hL⟩
    have hn := hc ⟨0,hL⟩
    have hb := hsum ⟨0,hL⟩ ⟨0,hL⟩
    omega
  constructor
  · rintro ⟨x,y⟩ he
    have hd := (laneProfileJam_east_iff L r c (x,y)).mp he
    change cyclicDistance L x y < r y at hd
    change laneProfileJam L r c (cyclicNext L hL x,y) ≠ .empty
    by_cases hxy : x = y
    · subst x
      have hn : laneProfileJam L r c (cyclicNext L hL y,y) = .north := by
        apply (laneProfileJam_north_iff L r c hsum (cyclicNext L hL y,y)).mpr
        rw [profileDistance_to_next L hL hlarge y]
        exact ⟨by decide, hc _⟩
      rw [hn]
      decide
    · have hstep := cyclicDistance_next L hL x y hxy
      have he' : laneProfileJam L r c (cyclicNext L hL x,y) = .east := by
        apply (laneProfileJam_east_iff L r c (cyclicNext L hL x,y)).mpr
        change cyclicDistance L (cyclicNext L hL x) y < r y
        omega
      rw [he']
      decide
  · rintro ⟨x,y⟩ hn
    have hd := (laneProfileJam_north_iff L r c hsum (x,y)).mp hn
    change 0 < cyclicDistance L y x ∧ cyclicDistance L y x ≤ c x at hd
    have hyx := (profileDistance_pos_iff L y x).mp hd.1
    change laneProfileJam L r c (x,cyclicNext L hL y) ≠ .empty
    by_cases hfront : cyclicNext L hL y = x
    · rw [hfront, laneProfileJam_diagonal_east L r c hr x]
      decide
    · have hstep := cyclicDistance_next L hL y x hyx
      have hn' : laneProfileJam L r c (x,cyclicNext L hL y) = .north := by
        apply (laneProfileJam_north_iff L r c hsum (x,cyclicNext L hL y)).mpr
        change 0 < cyclicDistance L (cyclicNext L hL y) x ∧
          cyclicDistance L (cyclicNext L hL y) x ≤ c x
        exact ⟨(profileDistance_pos_iff L _ x).mpr hfront, by omega⟩
      rw [hn']
      decide

theorem laneProfileJam_jam (L : Nat) (hL : 0 < L) (r c : Fin L → Nat)
    (hr : ∀ y, 1 ≤ r y) (hc : ∀ x, 1 ≤ c x)
    (hsum : ∀ x y, r y+c x ≤ L) :
    Jam (eastDirection L L hL) (northDirection L L hL) (laneProfileJam L r c) := by
  constructor
  · refine ⟨(⟨0,hL⟩,⟨0,hL⟩), ?_⟩
    rw [laneProfileJam_diagonal_east L r c hr ⟨0,hL⟩]
    decide
  · exact laneProfileJam_frozen L hL r c hr hc hsum

theorem laneProfileJam_no_moves (L : Nat) (hL : 0 < L) (r c : Fin L → Nat)
    (hr : ∀ y, 1 ≤ r y) (hc : ∀ x, 1 ≤ c x)
    (hsum : ∀ x y, r y+c x ≤ L) :
    NoMoves (eastDirection L L hL) (northDirection L L hL) (laneProfileJam L r c) :=
  (noMoves_iff_frozen _ _ _).mpr (laneProfileJam_frozen L hL r c hr hc hsum)

theorem laneProfileJam_fixed (L : Nat) (hL : 0 < L) (r c : Fin L → Nat)
    (hr : ∀ y, 1 ≤ r y) (hc : ∀ x, 1 ≤ c x)
    (hsum : ∀ x y, r y+c x ≤ L) :
    torusStep L L hL hL (laneProfileJam L r c) = laneProfileJam L r c :=
  (step_eq_iff_frozen _ _ _).mpr (laneProfileJam_frozen L hL r c hr hc hsum)

/-- These jam representatives have no full monochromatic lane; positivity of
the opposite species keeps every specified lane count strictly below `L`. -/
theorem laneProfileJam_no_full_lane (L : Nat) (hL : 0 < L) (r c : Fin L → Nat)
    (hr : ∀ y, 1 ≤ r y) (hc : ∀ x, 1 ≤ c x)
    (hsum : ∀ x y, r y+c x ≤ L) :
    ¬ HasFullMonochromaticLane (laneProfileJam L r c) := by
  have hcounts := laneProfileJam_counts L hL r c hr hsum
  rintro (⟨y, hy⟩ | ⟨x, hx⟩)
  · have he := (eastRowCount_eq_width_iff (laneProfileJam L r c) y).mpr hy
    rw [hcounts.1 y] at he
    have hb := hsum y y
    have hp := hc y
    omega
  · have hn := (northColumnCount_eq_height_iff (laneProfileJam L r c) x).mpr hx
    rw [hcounts.2 x] at hn
    have hb := hsum x x
    have hp := hr x
    omega

theorem exists_jam_with_lane_profile (L : Nat) (hL : 0 < L) (r c : Fin L → Nat)
    (hr : ∀ y, 1 ≤ r y) (hc : ∀ x, 1 ≤ c x)
    (hsum : ∀ x y, r y+c x ≤ L) :
    ∃ u : Config (Position L L),
      Jam (eastDirection L L hL) (northDirection L L hL) u ∧
      (∀ y, eastRowCount u y = r y) ∧ (∀ x, northColumnCount u x = c x) := by
  have hcounts := laneProfileJam_counts L hL r c hr hsum
  exact ⟨laneProfileJam L r c, laneProfileJam_jam L hL r c hr hc hsum, hcounts⟩

/-- An equivalent convenient interface uses any upper bounds on the two
profiles, in particular their finite maxima. -/
theorem exists_jam_with_lane_profile_of_caps (L : Nat) (hL : 0 < L)
    (r c : Fin L → Nat) (R C : Nat)
    (hr : ∀ y, 1 ≤ r y) (hc : ∀ x, 1 ≤ c x)
    (hrcap : ∀ y, r y ≤ R) (hccap : ∀ x, c x ≤ C) (hcap : R+C ≤ L) :
    ∃ u : Config (Position L L),
      Jam (eastDirection L L hL) (northDirection L L hL) u ∧
      (∀ y, eastRowCount u y = r y) ∧ (∀ x, northColumnCount u x = c x) := by
  apply exists_jam_with_lane_profile L hL r c hr hc
  intro x y
  have he := hrcap y
  have hn := hccap x
  omega

/-- Every configuration with an admissible invariant profile shares that exact
profile with an already jammed configuration. This does not assert attraction
of the supplied initial configuration to that jam. -/
theorem exists_jam_with_same_lane_profile (L : Nat) (hL : 0 < L)
    (s : Config (Position L L))
    (hr : ∀ y, 1 ≤ eastRowCount s y) (hc : ∀ x, 1 ≤ northColumnCount s x)
    (hsum : ∀ x y, eastRowCount s y+northColumnCount s x ≤ L) :
    ∃ u : Config (Position L L),
      Jam (eastDirection L L hL) (northDirection L L hL) u ∧
      (∀ y, eastRowCount u y = eastRowCount s y) ∧
      (∀ x, northColumnCount u x = northColumnCount s x) :=
  exists_jam_with_lane_profile L hL (eastRowCount s) (northColumnCount s) hr hc hsum

/-- A predicate of only the two lane-count vectors that soundly excludes jams
cannot accept any of these positive, separated profiles. -/
theorem admissible_profile_cannot_certify_no_jam (L : Nat) (hL : 0 < L)
    (r c : Fin L → Nat) (hr : ∀ y, 1 ≤ r y) (hc : ∀ x, 1 ≤ c x)
    (hsum : ∀ x y, r y+c x ≤ L)
    (certificate : (Fin L → Nat) → (Fin L → Nat) → Prop)
    (sound : ∀ u : Config (Position L L),
      certificate (eastRowCount u) (northColumnCount u) →
        ¬ Jam (eastDirection L L hL) (northDirection L L hL) u) :
    ¬ certificate r c := by
  intro hcert
  obtain ⟨u, hj, he, hn⟩ := exists_jam_with_lane_profile L hL r c hr hc hsum
  have her : eastRowCount u = r := funext he
  have hnc : northColumnCount u = c := funext hn
  apply sound u
  · simpa only [her, hnc] using hcert
  · exact hj

end BML
