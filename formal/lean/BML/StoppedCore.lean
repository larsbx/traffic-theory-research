import BML.PathCore

/-!
The eventual maximal-core cardinality counts stopped original CLASSIC cars.

Snapshot core membership is computed using the exact `carCount`-edge test.
The stopped-car count is semantic: it counts original tags whose actual car
traces eventually become constant. The equality uses the actual transport
bijection, so spatial persistence is not confused with replacement of labels.
The final torus comparison isolates the initial full-lane exceptional event.
-/
namespace BML

/-- A finite family of eventual assertions has one common starting time. -/
theorem eventually_uniform_on_list {α : Type u} (xs : List α)
    (P : Nat → α → Prop)
    (hp : ∀ p, p ∈ xs → ∃ start, ∀ t, P (start+t) p) :
    ∃ start, ∀ p, p ∈ xs → ∀ t, P (start+t) p := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons a xs ih =>
    obtain ⟨u, hu⟩ := hp a (by simp)
    obtain ⟨v, hv⟩ := ih (fun p hm => hp p (by simp [hm]))
    refine ⟨u+v, ?_⟩
    intro p hm t
    rcases List.mem_cons.mp hm with rfl | hm
    · simpa only [Nat.add_assoc] using hu (v+t)
    · simpa only [Nat.add_assoc, Nat.add_left_comm u v] using hv p hm (u+t)

section General

variable {α : Type} (east north : Direction α)

/-- Entry into a snapshot core freezes this very original tag from that
round, not merely some later round. -/
theorem carTrace_eq_of_pathCoreMember (sp : Species) (s : Config α)
    (p : α) (hc : s p = sp.cell) (start : Nat)
    (hp : PathCoreMember east north (iterate (step east north) start s)
      (carTrace east north sp s start p)) (t : Nat) :
    carTrace east north sp s (start+t) p = carTrace east north sp s start p := by
  have hperm : PermanentFrom east north s sp
      (carTrace east north sp s start p) start := by
    intro u
    rw [iterate_add, hp.persists east north u]
    exact carTrace_preserves_car east north sp s p hc start
  induction t with
  | zero => simp only [Nat.add_zero]
  | succ t ih =>
    rw [show start+(t+1) = start+t+1 by omega]
    change roundTransport east north sp (iterate (step east north) (start+t) s)
      (carTrace east north sp s (start+t) p) = carTrace east north sp s start p
    rw [ih]
    exact roundTransport_eq_of_no_round_move east north sp _ _
      (hperm.no_round_move east north t)

end General

section Finite

variable {w h : Nat} (east north : Direction (Position w h))

/-- Executable exact snapshot test: `carCount` edges, including both endpoints. -/
def pathCoreFlag (s : Config (Position w h)) (p : Position w h) : Bool :=
  (List.range (carCount w h s + 1)).all fun k =>
    decide (s (iterate (directBlocker east north s) k p) ≠ .empty)

@[simp] theorem pathCoreFlag_eq_true (s : Config (Position w h)) (p : Position w h) :
    pathCoreFlag east north s p = true ↔ PathCoreMember east north s p := by
  rw [pathCoreMember_iff_occupiedBlockerPath_carCount]
  simp only [pathCoreFlag, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Nat.lt_succ_iff, OccupiedBlockerPath]

/-- Number of current cars of one species in the maximal snapshot core. -/
def pathCoreSpeciesCount (sp : Species) (s : Config (Position w h)) : Nat :=
  ((speciesCells w h sp s).filter (pathCoreFlag east north s)).length

/-- Executable cardinality of the maximal occupied successor-closed core. -/
def pathCoreCount (s : Config (Position w h)) : Nat :=
  pathCoreSpeciesCount east north .east s + pathCoreSpeciesCount east north .north s

/-- Number of original tags of one species whose actual traces eventually stop. -/
noncomputable def stoppedSpeciesCount (sp : Species) (s : Config (Position w h)) : Nat := by
  classical
  exact ((speciesCells w h sp s).filter
    (fun p => decide (TagEventuallyStopped east north sp s p))).length

/-- Semantic count of eventually stopped original cars; empty sites are excluded. -/
noncomputable def stoppedCarCount (s : Config (Position w h)) : Nat :=
  stoppedSpeciesCount east north .east s + stoppedSpeciesCount east north .north s

theorem pathCoreCount_eq_length_filter (s : Config (Position w h)) :
    pathCoreCount east north s =
      ((positions w h).filter (pathCoreFlag east north s)).length := by
  have aux : ∀ xs : List (Position w h),
      ((xs.filter (fun p => decide (s p = .east))).filter
          (pathCoreFlag east north s)).length +
        ((xs.filter (fun p => decide (s p = .north))).filter
          (pathCoreFlag east north s)).length =
        (xs.filter (pathCoreFlag east north s)).length := by
    intro xs
    induction xs with
    | nil => rfl
    | cons p xs ih =>
      have he : s p = .empty → pathCoreFlag east north s p = false := by
        intro hp
        apply Bool.eq_false_iff.mpr
        intro hc
        exact ((pathCoreFlag_eq_true east north s p).mp hc).occupied east north hp
      cases hc : s p with
      | empty => simp [hc, he hc] at *; exact ih
      | east =>
        cases hf : pathCoreFlag east north s p <;> simp [hc, hf] at * <;> omega
      | north =>
        cases hf : pathCoreFlag east north s p <;> simp [hc, hf] at * <;> omega
  exact aux (positions w h)

theorem pathCoreCount_le_carCount (s : Config (Position w h)) :
    pathCoreCount east north s ≤ carCount w h s := by
  rw [pathCoreCount, carCount_eq_speciesCount,
    speciesCount_eq_length_speciesCells, speciesCount_eq_length_speciesCells]
  exact Nat.add_le_add (List.length_filter_le _ _) (List.length_filter_le _ _)

theorem stoppedCarCount_le_carCount (s : Config (Position w h)) :
    stoppedCarCount east north s ≤ carCount w h s := by
  classical
  rw [stoppedCarCount, carCount_eq_speciesCount,
    speciesCount_eq_length_speciesCells, speciesCount_eq_length_speciesCells]
  exact Nat.add_le_add (List.length_filter_le _ _) (List.length_filter_le _ _)

theorem carCount_pos_iff_nonempty (s : Config (Position w h)) :
    0 < carCount w h s ↔ Nonempty s := by
  change 0 < (occupiedCells w h s).length ↔ Nonempty s
  rw [← List.ne_nil_iff_length_pos, occupiedCells_nonempty_iff]

theorem eventuallyJammed_carCount_pos (s : Config (Position w h))
    (hj : EventuallyJammed east north s) : 0 < carCount w h s := by
  obtain ⟨t, hn, _⟩ := hj
  exact (carCount_pos_iff_nonempty s).mpr ((iterate_nonempty_iff east north s t).mp hn)

/-- Actual round-by-round tag transport permutes the initial and current
species lists. The statement preserves labels and not only total population. -/
theorem speciesCells_carTrace_perm (sp : Species) (s : Config (Position w h)) (t : Nat) :
    (speciesCells w h sp (iterate (step east north) t s)).Perm
      ((speciesCells w h sp s).map (carTrace east north sp s t)) := by
  have hmap : ((speciesCells w h sp s).map (carTrace east north sp s t)).Nodup := by
    apply List.pairwise_map.mpr
    apply (speciesCells_nodup w h sp s).imp_of_mem
    intro p q hp hq hpq heq
    exact hpq (carTrace_injective_on_cars east north sp s t p q
      ((mem_speciesCells w h sp s p).mp hp) ((mem_speciesCells w h sp s q).mp hq) heq)
  apply (List.perm_ext_iff_of_nodup (speciesCells_nodup w h sp _) hmap).mpr
  intro q
  constructor
  · intro hq
    obtain ⟨p, hp, heq⟩ := carTrace_surjective_on_cars east north sp s t q
      ((mem_speciesCells w h sp _ q).mp hq)
    exact List.mem_map.mpr ⟨p, (mem_speciesCells w h sp s p).mpr hp, heq⟩
  · intro hq
    obtain ⟨p, hp, heq⟩ := List.mem_map.mp hq
    rw [← heq]
    apply (mem_speciesCells w h sp _ _).mpr
    exact carTrace_preserves_car east north sp s p
      ((mem_speciesCells w h sp s p).mp hp) t

/-- Executable count of initial tags of one species whose current traces
are in the current core. No eventual-stop oracle is used. -/
def tracedCoreSpeciesCount (sp : Species) (s : Config (Position w h)) (t : Nat) : Nat :=
  ((speciesCells w h sp s).filter fun p =>
    pathCoreFlag east north (iterate (step east north) t s)
      (carTrace east north sp s t p)).length

/-- Executable count of original tags in the core at one specified round. -/
def tracedCoreCount (s : Config (Position w h)) (t : Nat) : Nat :=
  tracedCoreSpeciesCount east north .east s t + tracedCoreSpeciesCount east north .north s t

/-- The numeric tag/site bridge holds at every checkpoint, before or after
the core stabilizes. -/
theorem pathCoreSpeciesCount_eq_tracedCoreSpeciesCount (sp : Species)
    (s : Config (Position w h)) (t : Nat) :
    pathCoreSpeciesCount east north sp (iterate (step east north) t s) =
      tracedCoreSpeciesCount east north sp s t := by
  have hperm := (speciesCells_carTrace_perm east north sp s t).filter
    (pathCoreFlag east north (iterate (step east north) t s))
  simpa only [pathCoreSpeciesCount, tracedCoreSpeciesCount,
    List.filter_map, List.length_map, Function.comp_def] using hperm.length_eq

theorem pathCoreCount_eq_tracedCoreCount (s : Config (Position w h)) (t : Nat) :
    pathCoreCount east north (iterate (step east north) t s) =
      tracedCoreCount east north s t := by
  simp only [pathCoreCount, tracedCoreCount, pathCoreSpeciesCount_eq_tracedCoreSpeciesCount]

/-- Every original tag currently in the core is one of the tags that stop.
The converse is only eventually true, because the core can still grow. -/
theorem pathCoreSpeciesCount_le_stoppedSpeciesCount (sp : Species)
    (s : Config (Position w h)) (t : Nat) :
    pathCoreSpeciesCount east north sp (iterate (step east north) t s) ≤
      stoppedSpeciesCount east north sp s := by
  classical
  rw [pathCoreSpeciesCount_eq_tracedCoreSpeciesCount]
  unfold tracedCoreSpeciesCount stoppedSpeciesCount
  apply List.Nodup.length_le_of_subset ((speciesCells_nodup w h sp s).filter _)
  intro p hp
  obtain ⟨hp, hk⟩ := List.mem_filter.mp hp
  apply List.mem_filter.mpr
  refine ⟨hp, ?_⟩
  apply decide_eq_true
  exact tagEventuallyStopped_of_pathCoreMember east north sp s p
    ((mem_speciesCells w h sp s p).mp hp) t
    ((pathCoreFlag_eq_true east north _ _).mp hk)

/-- Snapshot core mass is a lower bound for the eventual stopped population
at every finite time. Later arrivals into the core are allowed. -/
theorem pathCoreCount_le_stoppedCarCount (s : Config (Position w h)) (t : Nat) :
    pathCoreCount east north (iterate (step east north) t s) ≤
      stoppedCarCount east north s := by
  unfold pathCoreCount stoppedCarCount
  exact Nat.add_le_add
    (pathCoreSpeciesCount_le_stoppedSpeciesCount east north .east s t)
    (pathCoreSpeciesCount_le_stoppedSpeciesCount east north .north s t)

/-- Uniformly over the original cars of a species, eventual stopping is
equivalent to current core membership after one common finite time. -/
theorem stoppedTag_eventually_iff_current_core (sp : Species)
    (s : Config (Position w h)) :
    ∃ start, ∀ t p, s p = sp.cell →
      (TagEventuallyStopped east north sp s p ↔
        PathCoreMember east north (iterate (step east north) (start+t) s)
          (carTrace east north sp s (start+t) p)) := by
  classical
  let P := fun t p => TagEventuallyStopped east north sp s p ↔
    PathCoreMember east north (iterate (step east north) t s)
      (carTrace east north sp s t p)
  have hp : ∀ p, p ∈ speciesCells w h sp s → ∃ start, ∀ t, P (start+t) p := by
    intro p hp
    have hc := (mem_speciesCells w h sp s p).mp hp
    by_cases hs : TagEventuallyStopped east north sp s p
    · obtain ⟨start, hk⟩ :=
        (tagEventuallyStopped_iff_eventual_pathCoreMember east north sp s p hc).mp hs
      refine ⟨start, ?_⟩
      intro t
      constructor
      · intro _
        rw [carTrace_eq_of_pathCoreMember east north sp s p hc start hk t, iterate_add]
        exact hk.iterate east north t
      · exact fun _ => hs
    · refine ⟨0, ?_⟩
      intro t
      constructor
      · exact fun ht => False.elim (hs ht)
      · intro hk
        exact tagEventuallyStopped_of_pathCoreMember east north sp s p hc (0+t) hk
  obtain ⟨start, hall⟩ := eventually_uniform_on_list (speciesCells w h sp s) P hp
  exact ⟨start, fun t p hc => hall p ((mem_speciesCells w h sp s p).mpr hc) t⟩

/-- The finite core count of one species eventually counts precisely its
stopped original tags. -/
theorem pathCoreSpeciesCount_eventually_eq_stoppedSpeciesCount (sp : Species)
    (s : Config (Position w h)) :
    ∃ start, ∀ t,
      pathCoreSpeciesCount east north sp (iterate (step east north) (start+t) s) =
        stoppedSpeciesCount east north sp s := by
  classical
  obtain ⟨start, hall⟩ := stoppedTag_eventually_iff_current_core east north sp s
  refine ⟨start, ?_⟩
  intro t
  have hperm := (speciesCells_carTrace_perm east north sp s (start+t)).filter
    (pathCoreFlag east north (iterate (step east north) (start+t) s))
  have heq := hperm.length_eq
  rw [List.filter_map, List.length_map] at heq
  change pathCoreSpeciesCount east north sp (iterate (step east north) (start+t) s) = _ at heq
  rw [heq]
  unfold stoppedSpeciesCount
  apply congrArg List.length
  apply List.filter_congr
  intro p hp
  apply Bool.eq_iff_iff.mpr
  change pathCoreFlag east north (iterate (step east north) (start+t) s)
      (carTrace east north sp s (start+t) p) = true ↔ _
  rw [pathCoreFlag_eq_true]
  simpa only [decide_eq_true_eq] using
    (hall t p ((mem_speciesCells w h sp s p).mp hp)).symm

/-- The maximal snapshot core eventually has exactly as many sites as there
are eventually stopped original cars, with equality at every later round.
No quantitative bound on this starting time is asserted. -/
theorem pathCoreCount_eventually_eq_stoppedCarCount (s : Config (Position w h)) :
    ∃ start, ∀ t,
      pathCoreCount east north (iterate (step east north) (start+t) s) =
        stoppedCarCount east north s := by
  obtain ⟨u, hu⟩ := pathCoreSpeciesCount_eventually_eq_stoppedSpeciesCount east north .east s
  obtain ⟨v, hv⟩ := pathCoreSpeciesCount_eventually_eq_stoppedSpeciesCount east north .north s
  refine ⟨u+v, ?_⟩
  intro t
  unfold pathCoreCount stoppedCarCount
  rw [show u+v+t = u+(v+t) by omega, hu]
  rw [show u+(v+t) = v+(u+t) by omega, hv]

theorem stoppedSpeciesCount_eq_speciesCount_of_all_stopped
    (sp : Species) (s : Config (Position w h))
    (ha : AllCarsEventuallyStopped east north s) :
    stoppedSpeciesCount east north sp s = speciesCount w h sp s := by
  classical
  rw [speciesCount_eq_length_speciesCells]
  unfold stoppedSpeciesCount
  apply congrArg List.length
  apply List.filter_eq_self.mpr
  intro p hp
  exact decide_eq_true (ha sp p ((mem_speciesCells w h sp s p).mp hp))

theorem stoppedCarCount_eq_carCount_of_all_stopped (s : Config (Position w h))
    (ha : AllCarsEventuallyStopped east north s) :
    stoppedCarCount east north s = carCount w h s := by
  rw [stoppedCarCount, stoppedSpeciesCount_eq_speciesCount_of_all_stopped east north _ s ha,
    stoppedSpeciesCount_eq_speciesCount_of_all_stopped east north _ s ha,
    carCount_eq_speciesCount]

theorem stoppedCarCount_eq_carCount_of_eventuallyJammed (s : Config (Position w h))
    (hj : EventuallyJammed east north s) :
    stoppedCarCount east north s = carCount w h s :=
  stoppedCarCount_eq_carCount_of_all_stopped east north s
    (fun sp p hp => eventuallyJammed_every_tag_stops east north s hj sp p hp)

theorem stoppedCarCount_eq_zero_of_no_stopped (s : Config (Position w h))
    (hn : ¬ HasEventuallyStoppedCar east north s) :
    stoppedCarCount east north s = 0 := by
  classical
  have hz : ∀ sp, stoppedSpeciesCount east north sp s = 0 := by
    intro sp
    unfold stoppedSpeciesCount
    have hf : (speciesCells w h sp s).filter
        (fun p => decide (TagEventuallyStopped east north sp s p)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro p hp
      simp only [decide_eq_true_eq]
      exact fun hs => hn ⟨sp, p, (mem_speciesCells w h sp s p).mp hp, hs⟩
    rw [hf]
    rfl
  rw [stoppedCarCount, hz, hz]

end Finite

section Torus

variable {w h : Nat} {hw : 0 < w} {hh : 0 < h}

attribute [local instance] Classical.propDecidable

/-- Away from eventual jam and initial full lanes, no original car stops. -/
theorem stoppedCarCount_eq_zero_of_no_jam_no_full_lane (s : Config (Position w h))
    (hj : ¬ EventuallyJammed (eastDirection w h hw) (northDirection w h hh) s)
    (hr : ¬ HasFullMonochromaticLane s) :
    stoppedCarCount (eastDirection w h hw) (northDirection w h hh) s = 0 := by
  apply stoppedCarCount_eq_zero_of_no_stopped
  intro hs
  exact (hasEventuallyStoppedCar_iff_jam_or_full_lane.mp hs).elim hj hr

/-- Pointwise count comparison for the actual CLASSIC torus. The exceptional
event refers to full monochromatic lanes in the original board. The empty
configuration is covered, and singleton dimensions are allowed. -/
theorem stoppedCarCount_jam_bounds (s : Config (Position w h)) :
    (if EventuallyJammed (eastDirection w h hw) (northDirection w h hh) s then
      carCount w h s else 0) ≤
        stoppedCarCount (eastDirection w h hw) (northDirection w h hh) s ∧
    stoppedCarCount (eastDirection w h hw) (northDirection w h hh) s ≤
      (if EventuallyJammed (eastDirection w h hw) (northDirection w h hh) s then
        carCount w h s else 0) +
      (if HasFullMonochromaticLane s then carCount w h s else 0) := by
  classical
  by_cases hj : EventuallyJammed (eastDirection w h hw) (northDirection w h hh) s
  · rw [stoppedCarCount_eq_carCount_of_eventuallyJammed _ _ s hj]
    simp [hj]
  · by_cases hr : HasFullMonochromaticLane s
    · simp only [ite_eq_right hj, ite_eq_left hr, Nat.zero_add]
      exact ⟨Nat.zero_le _, stoppedCarCount_le_carCount _ _ s⟩
    · rw [stoppedCarCount_eq_zero_of_no_jam_no_full_lane s hj hr]
      simp [hj, hr]

end Torus

end BML
