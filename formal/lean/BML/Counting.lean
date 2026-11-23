import BML.Torus
import BML.Transport

/-!
Finite enumeration and exact numerical car counts. This connects the abstract
transport bijection to the executable species sums on every finite torus.
-/
namespace BML

/-- The row-major enumeration contains every torus position. -/
theorem mem_positions (w h : Nat) (p : Position w h) : p ∈ positions w h := by
  apply List.mem_flatMap.mpr
  refine ⟨p.2, List.mem_finRange p.2, ?_⟩
  exact List.mem_map.mpr ⟨p.1, List.mem_finRange p.1, rfl⟩

/-- The row-major enumeration counts each position once. -/
theorem positions_nodup (w h : Nat) : (positions w h).Nodup := by
  unfold positions
  apply List.pairwise_flatMap.mpr
  constructor
  · intro y _
    apply List.pairwise_map.mpr
    exact (List.nodup_finRange w).imp (fun hne heq => hne (congrArg Prod.fst heq))
  · apply (List.nodup_finRange h).imp
    intro y₁ y₂ hy p hp q hq heq
    obtain ⟨x₁, _, rfl⟩ := List.mem_map.mp hp
    obtain ⟨x₂, _, rfl⟩ := List.mem_map.mp hq
    exact hy (congrArg Prod.snd heq)

@[simp] theorem positions_length (w h : Nat) : (positions w h).length = w * h := by
  simp [positions, List.length_flatMap, List.map_const', List.sum_replicate_nat, Nat.mul_comm]

def speciesCells (w h : Nat) (sp : Species) (s : Config (Position w h)) :
    List (Position w h) :=
  (positions w h).filter (fun p => decide (s p = sp.cell))

def occupiedCells (w h : Nat) (s : Config (Position w h)) : List (Position w h) :=
  (positions w h).filter (fun p => decide (s p ≠ .empty))

def carCount (w h : Nat) (s : Config (Position w h)) : Nat :=
  (occupiedCells w h s).length

theorem carCount_le_area (w h : Nat) (s : Config (Position w h)) :
    carCount w h s ≤ w * h := by
  have hle := List.length_filter_le (fun p => decide (s p ≠ .empty)) (positions w h)
  simpa only [carCount, occupiedCells, positions_length] using hle

@[simp] theorem mem_speciesCells (w h : Nat) (sp : Species)
    (s : Config (Position w h)) (p : Position w h) :
    p ∈ speciesCells w h sp s ↔ s p = sp.cell := by
  simp [speciesCells, mem_positions]

@[simp] theorem mem_occupiedCells (w h : Nat) (s : Config (Position w h))
    (p : Position w h) : p ∈ occupiedCells w h s ↔ s p ≠ .empty := by
  simp [occupiedCells, mem_positions]

theorem speciesCells_nodup (w h : Nat) (sp : Species) (s : Config (Position w h)) :
    (speciesCells w h sp s).Nodup :=
  (positions_nodup w h).filter _

theorem occupiedCells_nodup (w h : Nat) (s : Config (Position w h)) :
    (occupiedCells w h s).Nodup :=
  (positions_nodup w h).filter _

theorem occupiedCells_nonempty_iff (w h : Nat) (s : Config (Position w h)) :
    occupiedCells w h s ≠ [] ↔ Nonempty s := by
  rw [List.ne_nil_iff_length_pos, List.length_pos_iff_exists_mem]
  simp only [mem_occupiedCells, Nonempty]

/-- List filtering and the executable 0/1 indicator sum compute the same count. -/
theorem length_filter_eq_indicator_sum (xs : List α) (P : α → Prop) [DecidablePred P] :
    (xs.filter (fun p => decide (P p))).length =
      (xs.map (fun p => if P p then 1 else 0)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : P x <;> simp [hx, ih, Nat.add_comm]

theorem speciesCount_eq_length_speciesCells (w h : Nat) (sp : Species)
    (s : Config (Position w h)) :
    speciesCount w h sp s = (speciesCells w h sp s).length := by
  exact (length_filter_eq_indicator_sum (positions w h) (fun p => s p = sp.cell)).symm

theorem occupied_length_eq_species_sums (xs : List α) (s : Config α) :
    (xs.filter (fun p => decide (s p ≠ .empty))).length =
      (xs.map (fun p => if s p = .east then 1 else 0)).sum +
      (xs.map (fun p => if s p = .north then 1 else 0)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hx : s x <;> simp [hx] at * <;> omega

theorem carCount_eq_speciesCount (w h : Nat) (s : Config (Position w h)) :
    carCount w h s = speciesCount w h .east s + speciesCount w h .north s := by
  exact occupied_length_eq_species_sums (positions w h) s

/-- Transport maps the old species list bijectively onto the new one. -/
theorem speciesCells_transport_perm (w h : Nat) (d : Direction (Position w h))
    (sp : Species) (s : Config (Position w h)) :
    (speciesCells w h sp (halfStep d sp s)).Perm
      ((speciesCells w h sp s).map (transport d sp s)) := by
  have hmap : ((speciesCells w h sp s).map (transport d sp s)).Nodup := by
    apply List.pairwise_map.mpr
    apply (speciesCells_nodup w h sp s).imp_of_mem
    intro p q hp hq hpq heq
    exact hpq (transport_injective_on_cars d sp s p q
      ((mem_speciesCells w h sp s p).mp hp) ((mem_speciesCells w h sp s q).mp hq) heq)
  apply (List.perm_ext_iff_of_nodup (speciesCells_nodup w h sp _) hmap).mpr
  intro q
  constructor
  · intro hq
    obtain ⟨p, hp, heq⟩ := transport_surjective_on_cars d sp s q
      ((mem_speciesCells w h sp _ q).mp hq)
    exact List.mem_map.mpr ⟨p, (mem_speciesCells w h sp s p).mpr hp, heq⟩
  · intro hq
    obtain ⟨p, hp, heq⟩ := List.mem_map.mp hq
    rw [← heq]
    apply (mem_speciesCells w h sp _ _).mpr
    exact transport_preserves_car d sp s p ((mem_speciesCells w h sp s p).mp hp)

theorem halfStep_moving_speciesCount (w h : Nat) (d : Direction (Position w h))
    (sp : Species) (s : Config (Position w h)) :
    speciesCount w h sp (halfStep d sp s) = speciesCount w h sp s := by
  rw [speciesCount_eq_length_speciesCells, speciesCount_eq_length_speciesCells]
  have heq := (speciesCells_transport_perm w h d sp s).length_eq
  simpa only [List.length_map] using heq

/-- Both the moving and the stationary species counts are conserved in each phase. -/
theorem halfStep_speciesCount (w h : Nat) (d : Direction (Position w h))
    (moving observed : Species) (s : Config (Position w h)) :
    speciesCount w h observed (halfStep d moving s) = speciesCount w h observed s := by
  by_cases hsame : moving = observed
  · subst observed
    exact halfStep_moving_speciesCount w h d moving s
  · have hcell : observed.cell ≠ moving.cell := by
      cases moving <;> cases observed <;> simp_all [Species.cell]
    unfold speciesCount
    apply congrArg List.sum
    apply List.map_congr_left
    intro p _
    simp only [other_species_unchanged d moving s p observed.cell observed.cell_ne_empty hcell]

theorem torusStep_speciesCount (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (sp : Species) (s : Config (Position w h)) :
    speciesCount w h sp (torusStep w h hw hh s) = speciesCount w h sp s := by
  simp only [torusStep, step, halfStep_speciesCount]

theorem torusStep_carCount (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) : carCount w h (torusStep w h hw hh s) = carCount w h s := by
  simp only [carCount_eq_speciesCount, torusStep_speciesCount]

theorem iterate_torusStep_speciesCount (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (sp : Species) (s : Config (Position w h)) (t : Nat) :
    speciesCount w h sp (iterate (torusStep w h hw hh) t s) = speciesCount w h sp s := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [iterate, torusStep_speciesCount] using ih

theorem iterate_torusStep_carCount (w h : Nat) (hw : 0 < w) (hh : 0 < h)
    (s : Config (Position w h)) (t : Nat) :
    carCount w h (iterate (torusStep w h hw hh) t s) = carCount w h s := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [iterate, torusStep_carCount] using ih

end BML
