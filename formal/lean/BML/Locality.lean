import BML.Capture

/-!
Locality and initial car origins for the CLASSIC east-then-north kernel.
The probability argument that uses these facts is in the diagonal-cuts note.
-/
namespace BML

theorem halfStep_eq_of_local_agreement (d : Direction α) (sp : Species)
    (s u : Config α) (z : α) (here : s z = u z)
    (ahead : s (d.next z) = u (d.next z)) (behind : s (d.prev z) = u (d.prev z)) :
    halfStep d sp s z = halfStep d sp u z := by
  simp only [halfStep, here, ahead, behind]

private theorem halfStep_pullback (domain : Direction α) (range : Direction β)
    (project : α → β) (next : ∀ z, project (domain.next z) = range.next (project z))
    (prev : ∀ z, project (domain.prev z) = range.prev (project z))
    (sp : Species) (s : Config β) :
    halfStep domain sp (s ∘ project) = (halfStep range sp s) ∘ project := by
  funext z
  simp only [halfStep, Function.comp_apply, next, prev]

abbrev LatticePosition := Int × Int

def latticeEast : Direction LatticePosition where
  next z := (z.1 + 1, z.2)
  prev z := (z.1 - 1, z.2)
  next_prev z := by apply Prod.ext <;> dsimp <;> omega
  prev_next z := by apply Prod.ext <;> dsimp <;> omega

def latticeNorth : Direction LatticePosition where
  next z := (z.1, z.2 + 1)
  prev z := (z.1, z.2 - 1)
  next_prev z := by apply Prod.ext <;> dsimp <;> omega
  prev_next z := by apply Prod.ext <;> dsimp <;> omega

def AgreesOnBox (radius : Nat) (z : LatticePosition) (s u : Config LatticePosition) : Prop :=
  ∀ q : LatticePosition, z.1 - radius ≤ q.1 → q.1 ≤ z.1 + radius →
    z.2 - radius ≤ q.2 → q.2 ≤ z.2 + radius → s q = u q

theorem lattice_step_eq_of_box (s u : Config LatticePosition) (z : LatticePosition)
    (agree : AgreesOnBox 1 z s u) : step latticeEast latticeNorth s z = step latticeEast latticeNorth u z := by
  unfold step
  apply halfStep_eq_of_local_agreement
  all_goals apply halfStep_eq_of_local_agreement
  all_goals apply agree <;> simp [latticeEast, latticeNorth] <;> omega

theorem lattice_iterate_eq_of_box (t : Nat) (s u : Config LatticePosition) (z : LatticePosition)
    (agree : AgreesOnBox t z s u) :
    iterate (step latticeEast latticeNorth) t s z = iterate (step latticeEast latticeNorth) t u z := by
  induction t generalizing z with
  | zero => exact agree z (by omega) (by omega) (by omega) (by omega)
  | succ t ih =>
    rw [iterate, iterate]
    apply lattice_step_eq_of_box
    intro q qx₁ qx₂ qy₁ qy₂
    apply ih q
    intro r rx₁ rx₂ ry₁ ry₂
    exact agree r (by omega) (by omega) (by omega) (by omega)

def reduceCoordinate (n : Nat) (hn : 0 < n) (x : Int) : Fin n :=
  ⟨(x % (n : Int)).toNat, by
    have hlow := Int.emod_nonneg x (show (n : Int) ≠ 0 by omega)
    have hhigh := Int.emod_lt_of_pos x (show 0 < (n : Int) by omega)
    omega⟩

private theorem reduceCoordinate_next (n : Nat) (hn : 0 < n) (x : Int) :
    reduceCoordinate n hn (x + 1) = cyclicNext n hn (reduceCoordinate n hn x) := by
  have hlow := Int.emod_nonneg x (show (n : Int) ≠ 0 by omega)
  have hhigh := Int.emod_lt_of_pos x (show 0 < (n : Int) by omega)
  have hr := Int.emod_add_emod x (n : Int) 1
  apply Fin.ext
  by_cases h : (x % (n : Int)).toNat + 1 < n
  · have hm : (x + 1) % (n : Int) = x % (n : Int) + 1 := by
      rw [← hr, Int.emod_eq_of_lt (by omega) (by omega)]
    simp only [cyclicNext, reduceCoordinate, h, ↓reduceDIte, hm]
    omega
  · have hm : x % (n : Int) + 1 = (n : Int) := by omega
    simp [cyclicNext, reduceCoordinate, h, ← hr, hm]

private theorem reduceCoordinate_prev (n : Nat) (hn : 0 < n) (x : Int) :
    reduceCoordinate n hn (x - 1) = cyclicPrev n hn (reduceCoordinate n hn x) := by
  have h := reduceCoordinate_next n hn (x - 1)
  rw [show x - 1 + 1 = x by omega] at h
  rw [h, cyclicPrev_next]

/-- Reduce a lifted lattice coordinate to the actual `Fin w × Fin h` torus. -/
def torusProject (w h : Nat) (hw : 0 < w) (hh : 0 < h) (z : LatticePosition) : Position w h :=
  (reduceCoordinate w hw z.1, reduceCoordinate h hh z.2)

private theorem eq_of_reduceCoordinate_eq_of_short_gap (n : Nat) (hn : 0 < n) (x y : Int)
    (lo : -(n : Int) < x-y) (hi : x-y < n)
    (equal : reduceCoordinate n hn x = reduceCoordinate n hn y) : x = y := by
  have npos : 0 < (n : Int) := by omega
  have h := congrArg Fin.val equal
  change (x % (n : Int)).toNat = (y % (n : Int)).toNat at h
  have hx := Int.emod_nonneg x (by omega : (n : Int) ≠ 0)
  have hy := Int.emod_nonneg y (by omega : (n : Int) ≠ 0)
  have residues : x % (n : Int) = y % (n : Int) := by omega
  by_cases hxy : y ≤ x
  · have zero := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp residues
    rw [Int.emod_eq_of_lt (by omega) hi] at zero
    omega
  · have zero := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp residues.symm
    rw [Int.emod_eq_of_lt (by omega) (by omega : y-x < (n : Int))] at zero
    omega

/-- In a lifted rectangle shorter than one period in each coordinate,
distinct lattice sites have distinct torus projections. -/
theorem torusProject_eq_lift_of_short_spans (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (q r : LatticePosition)
    (hx : -(w : Int) < q.1-r.1 ∧ q.1-r.1 < w)
    (hy : -(h : Int) < q.2-r.2 ∧ q.2-r.2 < h)
    (equal : torusProject w h hw hh q = torusProject w h hw hh r) : q = r := by
  apply Prod.ext
  · exact eq_of_reduceCoordinate_eq_of_short_gap w hw _ _ hx.1 hx.2 (congrArg Prod.fst equal)
  · exact eq_of_reduceCoordinate_eq_of_short_gap h hh _ _ hy.1 hy.2 (congrArg Prod.snd equal)

/-- Heights in a window shorter than L identify disjoint layers on a square torus. -/
theorem torusProject_ne_of_height_gap (L : Nat) (hL : 0 < L) (z q : LatticePosition)
    (positive : 0 < (q.1 + q.2) - (z.1 + z.2))
    (short : (q.1 + q.2) - (z.1 + z.2) < L) :
    torusProject L L hL hL z ≠ torusProject L L hL hL q := by
  intro equal
  have hne : (L : Int) ≠ 0 := by omega
  have hx := congrArg (fun p : Position L L => p.1.val) equal
  have hy := congrArg (fun p : Position L L => p.2.val) equal
  change (z.1 % (L : Int)).toNat = (q.1 % (L : Int)).toNat at hx
  change (z.2 % (L : Int)).toNat = (q.2 % (L : Int)).toNat at hy
  have x : q.1 % (L : Int) = z.1 % (L : Int) := by
    have hz := Int.emod_nonneg z.1 hne
    have hq := Int.emod_nonneg q.1 hne
    omega
  have y : q.2 % (L : Int) = z.2 % (L : Int) := by
    have hz := Int.emod_nonneg z.2 hne
    have hq := Int.emod_nonneg q.2 hne
    omega
  have heights : (q.1 + q.2) % (L : Int) = (z.1 + z.2) % (L : Int) := by
    rw [Int.add_emod q.1, Int.add_emod z.1, x, y]
  have zero := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp heights
  rw [Int.emod_eq_of_lt (by omega) short] at zero
  omega

theorem torusStep_pullback (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) :
    step latticeEast latticeNorth (s ∘ torusProject w h hw hh) =
      (torusStep w h hw hh s) ∘ torusProject w h hw hh := by
  simp only [step, torusStep]
  have heNext (z) : torusProject w h hw hh (latticeEast.next z) =
      (eastDirection w h hw).next (torusProject w h hw hh z) := by
    simp [torusProject, latticeEast, eastDirection, reduceCoordinate_next]
  have hePrev (z) : torusProject w h hw hh (latticeEast.prev z) =
      (eastDirection w h hw).prev (torusProject w h hw hh z) := by
    simp [torusProject, latticeEast, eastDirection, reduceCoordinate_prev]
  have hnNext (z) : torusProject w h hw hh (latticeNorth.next z) =
      (northDirection w h hh).next (torusProject w h hw hh z) := by
    simp [torusProject, latticeNorth, northDirection, reduceCoordinate_next]
  have hnPrev (z) : torusProject w h hw hh (latticeNorth.prev z) =
      (northDirection w h hh).prev (torusProject w h hw hh z) := by
    simp [torusProject, latticeNorth, northDirection, reduceCoordinate_prev]
  rw [halfStep_pullback _ _ _ heNext hePrev, halfStep_pullback _ _ _ hnNext hnPrev]

theorem torusIterate_pullback (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (t : Nat) (s : Config (Position w h)) :
    iterate (step latticeEast latticeNorth) t (s ∘ torusProject w h hw hh) =
      (iterate (torusStep w h hw hh) t s) ∘ torusProject w h hw hh := by
  induction t with
  | zero => rfl
  | succ t ih => rw [iterate, iterate, ih, torusStep_pullback]

theorem torus_iterate_eq_of_lifted_box (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (t : Nat) (s u : Config (Position w h)) (z : LatticePosition)
    (agree : AgreesOnBox t z (s ∘ torusProject w h hw hh) (u ∘ torusProject w h hw hh)) :
    iterate (torusStep w h hw hh) t s (torusProject w h hw hh z) =
      iterate (torusStep w h hw hh) t u (torusProject w h hw hh z) := by
  simpa only [torusIterate_pullback, Function.comp_apply] using
    lattice_iterate_eq_of_box t _ _ z agree

private def speciesDirection (east north : Direction α) : Species → Direction α
  | .east => east
  | .north => north

private theorem origin_of_transport (d : Direction α) (sp : Species) (s : Config α)
    (r q : α) (destination : transport d sp s r = q) : r = q ∨ r = d.prev q := by
  unfold transport at destination
  split at destination
  · exact Or.inr (by simpa only [d.prev_next] using congrArg d.prev destination)
  · exact Or.inl destination

private theorem round_origin (east north : Direction α) (sp : Species)
    (s : Config α) (q : α) (occupied : step east north s q = sp.cell) :
    s q = sp.cell ∨ s ((speciesDirection east north sp).prev q) = sp.cell := by
  obtain ⟨r, origin, destination⟩ := roundTransport_surjective_on_cars east north sp s q occupied
  have h : r = q ∨ r = (speciesDirection east north sp).prev q := by
    cases sp with
    | east => exact origin_of_transport east .east s r q destination
    | north => exact origin_of_transport north .north (halfStep east .east s) r q destination
  rcases h with stays | moves
  · exact Or.inl (stays ▸ origin)
  · exact Or.inr (moves ▸ origin)

private theorem iterate_origin (east north : Direction α) (sp : Species) (t : Nat)
    (s : Config α) (q : α) (occupied : iterate (step east north) t s q = sp.cell) :
    ∃ k ≤ t, s (iterate (speciesDirection east north sp).prev k q) = sp.cell := by
  induction t generalizing q with
  | zero => exact ⟨0, Nat.le_refl 0, occupied⟩
  | succ t ih =>
    rcases round_origin east north sp _ q occupied with h | h
    · obtain ⟨k, hk, origin⟩ := ih q h
      exact ⟨k, by omega, origin⟩
    · obtain ⟨k, hk, origin⟩ := ih ((speciesDirection east north sp).prev q) h
      exact ⟨1 + k, by omega, by simpa only [iterate_add, iterate] using origin⟩

theorem iterate_east_origin (east north : Direction α) (t : Nat) (s : Config α) (q : α)
    (occupied : iterate (step east north) t s q = .east) :
    ∃ k ≤ t, s (iterate east.prev k q) = .east :=
  iterate_origin east north .east t s q occupied

theorem iterate_north_origin (east north : Direction α) (t : Nat) (s : Config α) (q : α)
    (occupied : iterate (step east north) t s q = .north) :
    ∃ k ≤ t, s (iterate north.prev k q) = .north :=
  iterate_origin east north .north t s q occupied

/-- Time-t vacancy follows from excluding both species' compatible initial origins. -/
theorem iterate_empty_of_no_origins (east north : Direction α) (t : Nat) (s : Config α) (q : α)
    (noEast : ∀ k ≤ t, s (iterate east.prev k q) ≠ .east)
    (noNorth : ∀ k ≤ t, s (iterate north.prev k q) ≠ .north) :
    iterate (step east north) t s q = .empty := by
  cases h : iterate (step east north) t s q with
  | empty => rfl
  | east =>
    obtain ⟨k, hk, origin⟩ := iterate_east_origin east north t s q h
    exact False.elim (noEast k hk origin)
  | north =>
    obtain ⟨k, hk, origin⟩ := iterate_north_origin east north t s q h
    exact False.elim (noNorth k hk origin)

private theorem latticeWest_iterate (k : Nat) (z : LatticePosition) :
    iterate latticeEast.prev k z = (z.1 - k, z.2) := by
  induction k with
  | zero => simp [iterate]
  | succ k ih => rw [iterate, ih]; apply Prod.ext <;> simp [latticeEast] <;> omega

private theorem latticeSouth_iterate (k : Nat) (z : LatticePosition) :
    iterate latticeNorth.prev k z = (z.1, z.2 - k) := by
  induction k with
  | zero => simp [iterate]
  | succ k ih => rw [iterate, ih]; apply Prod.ext <;> simp [latticeNorth] <;> omega

theorem torus_iterate_empty_of_no_lifted_origins (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (t : Nat) (s : Config (Position w h)) (z : LatticePosition)
    (noEast : ∀ k : Nat, k ≤ t → s (torusProject w h hw hh (z.1 - k, z.2)) ≠ .east)
    (noNorth : ∀ k : Nat, k ≤ t → s (torusProject w h hw hh (z.1, z.2 - k)) ≠ .north) :
    iterate (torusStep w h hw hh) t s (torusProject w h hw hh z) = .empty := by
  have empty := iterate_empty_of_no_origins latticeEast latticeNorth t
    (s ∘ torusProject w h hw hh) z
    (fun k hk => by simpa only [latticeWest_iterate, Function.comp_apply] using noEast k hk)
    (fun k hk => by simpa only [latticeSouth_iterate, Function.comp_apply] using noNorth k hk)
  simpa only [torusIterate_pullback, Function.comp_apply] using empty

end BML
