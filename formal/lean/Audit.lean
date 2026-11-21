-- Batch audits need the command and axiom APIs, not the server/shell umbrella.
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import BML
import G1Export

open Lean Elab Command

/-- Audit every declaration in this package, including transitive proof dependencies. -/
elab "audit_bml" : command => do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut used : Array Name := #[]
  let required : Array Name := #[
    ``BML.step_eq_iff_frozen, ``BML.step_eq_iff_noMoves,
    ``BML.phaseIndex_east, ``BML.phaseIndex_north, ``BML.correctedClass_roundTransport,
    ``BML.corrected_release, ``BML.corrected_survival,
    ``BML.corrected_emptyPair_backwards, ``BML.corrected_emptyPair_before,
    ``BML.corrected_emptyPair_of_sparse, ``BML.low_density_tag_block_bound,
    ``BML.low_density_block_bound, ``BML.low_density_speed_one,
    ``BML.staticFree_of_blockedRoundCount_bound,
    ``BML.low_density_staticFree_deadline, ``BML.low_density_speed_one_deadline,
    ``BML.low_density_square_speed_one_deadline,
    ``BML.transport_bijection, ``BML.iterate_nonempty_iff,
    ``BML.carCount_eq_speciesCount, ``BML.halfStep_speciesCount,
    ``BML.iterate_torusStep_speciesCount, ``BML.iterate_torusStep_carCount,
    ``BML.orbit_prefix_repeats, ``BML.finite_closed_cycle,
    ``BML.blocker_closed_winding, ``BML.jam_has_simple_blocker_cycle,
    ``BML.jam_carCount_lower_bound, ``BML.few_cars_never_jam,
    ``BML.exists_minimum_jam, ``BML.exists_jam_at_most_iff,
    ``BML.carCount_of_rank, ``BML.gridlockWith_is_jam,
    ``BML.gridlockWith_carCount, ``BML.exists_jam_with_count,
    ``BML.jam_carCount_iff, ``BML.exists_eventual_jam_with_count_iff,
    ``BML.cyclicNext_reaches_lt, ``BML.cyclicNext_reaches,
    ``BML.EastMixedRow.halfStep, ``BML.NorthMixedColumn.halfStep,
    ``BML.EastMixedRow.has_mover, ``BML.NorthMixedColumn.has_mover,
    ``BML.EastMixedRow.never_jam, ``BML.NorthMixedColumn.never_jam,
    ``BML.nonGridlockWith_carCount, ``BML.nonGridlockWith_never_jam,
    ``BML.exists_never_jam_with_count, ``BML.carCount_eq_area_iff,
    ``BML.full_carCount_is_jam, ``BML.forced_eventual_jam_iff,
    ``BML.nat_gcd_bezout, ``BML.coset_dvd_iff, ``BML.coset_int_iff, ``BML.coset_iff,
    ``BML.cyclicShift_add, ``BML.diagonalShift_add, ``BML.iterate_diagonalStep,
    ``BML.diagonalShift_exists_iff, ``BML.diagonal_kernel_iff,
    ``BML.phaseClass_east, ``BML.phaseClass_surjective,
    ``BML.east_diagonalShift_exists_iff,
    ``BML.diagonalShift_emod_lcm, ``BML.iterate_diagonalStep_eq_self_iff,
    ``BML.iterate_diagonalStep_lcm, ``BML.diagonalStep_reaches_lt_iff,
    ``BML.diagonalStep_reaches_iff, ``BML.diagonalStep_reaches_pos_iff,
    ``BML.east_diagonalStep_reaches_lt_iff, ``BML.east_diagonalStep_reaches_pos_iff,
    ``BML.halfStep_rigid, ``BML.allMove_step_east_iff, ``BML.allMove_step_north_iff,
    ``BML.allMove_iterate_east_iff, ``BML.allMove_iterate_north_iff,
    ``BML.allMove_iterate_east_at, ``BML.allMove_iterate_north_at,
    ``BML.diagonal_encounter_iff, ``BML.east_diagonal_encounter_iff,
    ``BML.same_phase_encounter_pos_iff, ``BML.next_phase_encounter_lt_iff,
    ``BML.staticFree_allMove, ``BML.staticFree_step, ``BML.staticFree_iterate,
    ``BML.staticFree_of_allMove_before_lcm, ``BML.lemmaR,
    ``BML.lemmaR_finite_lt, ``BML.lemmaR_finite, ``BML.lemmaR_window,
    ``BML.not_staticFree_iff_blocked_before_lcm,
    ``BML.freeFlow_returns_lcm, ``BML.freeFlow_periodic,
    ``BML.eventually_allMove_iff_reaches_staticFree,
    ``BML.sumFin_twice_le_of_adjacent, ``BML.sumFin_le_half_of_adjacent,
    ``BML.phaseFiber_length, ``BML.phaseSpeciesCount_sum,
    ``BML.carCount_eq_sum_phaseSpeciesCount, ``BML.carCount_phaseConfig,
    ``BML.phaseSpeciesCount_add_le, ``BML.phaseEastCount_add_next_le,
    ``BML.phaseNorthCount_add_next_le, ``BML.phaseCounts_cross_same,
    ``BML.phaseCounts_cross_next,
    ``BML.cyclic_weighted_packing_triple, ``BML.cyclic_weighted_packing_bound,
    ``BML.staticFree_coprime_pure, ``BML.staticFree_coprime_carCount_le,
    ``BML.freePattern_count, ``BML.maxFreeConfig_staticFree,
    ``BML.maxFreeConfig_carCount, ``BML.staticFree_of_subconfig,
    ``BML.thinConfig_carCount, ``BML.thinConfig_staticFree,
    ``BML.staticFree_carCount_le_freeMax, ``BML.freeMax_le_area,
    ``BML.freeWith_staticFree, ``BML.freeWith_carCount, ``BML.freeWith_carCount_of_le,
    ``BML.exists_staticFree_with_count_iff,
    ``BML.exists_perpetual_allMove_with_count_iff,
    ``BML.eventual_allMove_carCount_le_freeMax,
    ``BML.exists_eventual_allMove_with_count_iff,
    ``BML.above_freeMax_never_staticFree,
    ``BML.freeMax_square, ``BML.freeMax_square_attains_two_thirds_iff,
    ``BML.torus_fixed_iff_blocked, ``BML.winding_length_lower_bound,
    ``BML.freeClasses_attains_two_thirds_iff,
    ``BML.Gated.adds_one_north, ``BML.Gated.closed_gate,
    ``BML.Gated.freeCar_row, ``BML.Gated.freeCar_trace, ``BML.Gated.freeCar_canMove,
    ``BML.Gated.gatedY_never_jams, ``BML.Gated.eastPotential_step_balance,
    ``BML.Gated.gatedX_east_balance, ``BML.Gated.gatedX_eastMoves_le,
    ``BML.Gated.gatedX_eventually_east_blocked, ``BML.Gated.gatedX_terminal_obstacles,
    ``BML.Gated.gatedX_eventually_jams, ``BML.Gated.gated_genuine,
    ``BML.Gated.row_adds_one_east, ``BML.Gated.gatedRow_freeCar_trace,
    ``BML.Gated.gatedRowX_eventually_jams, ``BML.Gated.gatedRow_genuine,
    ``BML.Gated.exists_genuine_unjamming,
    ``BML.Witness.after_never_jams, ``BML.Witness.original_traced_car_moves_forever,
    ``BML.BlockingCore.persists, ``BML.BlockerCycle.persists,
    ``BML.carTrace_bijection, ``BML.RouteCover.distance_roundTransport,
    ``BML.RouteCover.rank_balance, ``BML.RouteCover.total_moves_le,
    ``BML.RouteCover.jammed_by_movementBudget,
    ``BML.speciesCount_halfStep, ``BML.speciesCount_iterate,
    ``BML.eastRowCount_iterate, ``BML.northColumnCount_iterate,
    ``BML.fullEastRow_no_moves, ``BML.fullNorthColumn_no_moves,
    ``BML.fullEastRow_iterate_iff, ``BML.fullNorthColumn_iterate_iff,
    ``BML.hasFullMonochromaticLane_iterate_iff,
    ``BML.fullEastRow_excludes_fullNorthColumn,
    ``BML.northFreeColumn_iterate_iff, ``BML.northFreeStrip_iterate_iff,
    ``BML.eastRowsBelow_iterate_iff,
    ``BML.staircase_pair_preimage_iff, ``BML.staircase_formed,
    ``BML.Absorption.safe_at_cutoff_avoids,
    ``BML.Absorption.repeated_endpoint_avoids,
    ``BML.Absorption.probe_hit_sound, ``BML.Absorption.probe_safe_sound,
    ``BML.Absorption.probe_hit_persists, ``BML.Absorption.probe_safe_persists,
    ``BML.Absorption.probe_unresolved_antitone,
    ``BML.Absorption.probe_mass_bounds, ``BML.Absorption.probe_mass_partition,
    ``BML.Absorption.probe_mass_intervals_nested,
    ``BML.Absorption.probe_zero_unresolved_exact,
    ``BML.configEqual_iff, ``BML.jamCheck_iff,
    ``BML.boardConfig_materialize, ``BML.boardConfig_step,
    ``BML.boardConfig_iterate, ``BML.absorptionProbe_eq,
    ``BML.absorptionProbe_hit_sound, ``BML.absorptionProbe_safe_sound,
    ``BML.absorptionProbe_mass_bounds,
    ``BML.eastRun_step, ``BML.eastRun_iterate, ``BML.eastRun_delay,
    ``BML.eastRun_rear_trace, ``BML.eastRun_settling_after,
    ``BML.torus_eastRun_delay,
    ``BML.DelayWitness.vacant_cycle_does_not_prevent_jam,
    ``BML.DelayWitness.after_has_no_vacant_cycle,
    ``BML.GuardedEastQueue.step, ``BML.GuardedEastQueue.iterate,
    ``BML.GuardedEastQueue.rear_blocked_before, ``BML.GuardedEastQueue.rear_trace,
    ``BML.GuardedEastQueue.rear_canMove, ``BML.GuardedEastQueue.rear_first_move,
    ``BML.GuardedEastQueue.jam_after, ``BML.GuardedEastQueue.no_jam_through,
    ``BML.torus_guardedEastQueue_first_move,
    ``BML.torus_guardedEastQueue_jam_after,
    ``BML.torus_guardedEastQueue_no_jam_through,
    ``BML.same_cell_no_round_move,
    ``BML.tagEventuallyStopped_iff_finitely_many_moves,
    ``BML.hasPermanentSite_iff_hasEventuallyStoppedCar,
    ``BML.occupied_forever_has_permanent_site,
    ``BML.eventuallyPermanent_east_successor,
    ``BML.eventuallyPermanent_north_successor,
    ``BML.future_blockingCore_of_permanent_site,
    ``BML.future_blockingCore_of_eventually_permanent_sites,
    ``BML.pathCoreMember_iff_all_paths, ``BML.pathCore_maximal,
    ``BML.BlockingCore.pathCoreMember,
    ``BML.PathCoreMember.persists, ``BML.PathCoreMember.iterate,
    ``BML.PathCoreMember.step, ``BML.pathCoreMember_iff_occupied_of_frozen,
    ``BML.PathCoreMember.repeats_by_carCount,
    ``BML.pathCoreMember_iff_occupiedBlockerPath_carCount,
    ``BML.pathCore_eventually_eq_permanent_sites,
    ``BML.eventual_pathCoreMember_iff_permanent_site,
    ``BML.tagEventuallyStopped_iff_eventual_pathCoreMember,
    ``BML.directBlocker_eq_blocker,
    ``BML.BlockingCore.full_east_row_of_missed_row,
    ``BML.BlockingCore.full_north_column_of_missed_column,
    ``BML.BlockingCore.routeCover_of_no_full_lane,
    ``BML.BlockingCore.routeCover_or_full_lane,
    ``BML.BlockingCore.jammed_by_budget_of_no_full_lane,
    ``BML.eventuallyJammed_every_tag_stops,
    ``BML.allCarsEventuallyStopped_iff_empty_or_jam,
    ``BML.hasPermanentSite_iff_jam_or_full_lane,
    ``BML.hasEventuallyStoppedCar_iff_jam_or_full_lane,
    ``BML.every_site_empty_arbitrarily_late,
    ``BML.every_tag_moves_arbitrarily_late,
    ``BML.successor_stays_for_half, ``BML.occupied_path_during_wait,
    ``BML.blocking_core_during_wait, ``BML.route_cover_during_wait,
    ``BML.tagged_wait_iff_stays_forever,
    ``BML.profileReflection_involutive, ``BML.profileDistance_interval_count,
    ``BML.laneProfileJam_placements_disjoint,
    ``BML.laneProfileJam_eastRowCount, ``BML.laneProfileJam_northColumnCount,
    ``BML.laneProfileJam_counts, ``BML.laneProfileJam_frozen,
    ``BML.laneProfileJam_jam, ``BML.laneProfileJam_no_moves,
    ``BML.laneProfileJam_fixed, ``BML.laneProfileJam_no_full_lane,
    ``BML.exists_jam_with_lane_profile,
    ``BML.exists_jam_with_lane_profile_of_caps,
    ``BML.exists_jam_with_same_lane_profile,
    ``BML.admissible_profile_cannot_certify_no_jam,
    ``BML.torus_iterate_eq_of_lifted_box, ``BML.torusProject_ne_of_height_gap,
    ``BML.torusProject_eq_lift_of_short_spans,
    ``BML.torus_iterate_empty_of_no_lifted_origins,
    ``BML.Barrier.northRun_mono, ``BML.Barrier.northRun_step,
    ``BML.Barrier.northRun_iterate,
    ``BML.Barrier.GuardedNorthHole.step, ``BML.Barrier.GuardedNorthHole.iterate,
    ``BML.Barrier.GuardedNorthHole.empty_at_deadline,
    ``BML.Barrier.eastWall_preserved, ``BML.Barrier.draining_l_barrier,
    ``BML.Barrier.torus_draining_l_barrier]
  for name in required do
    match env.find? name with
    | none => throwError "BML audit missing required theorem {name}"
    | some info =>
      unless info.isTheorem do
        throwError "BML audit required declaration is not a theorem: {name}"
  let requiredExecutables : Array Name := #[
    ``BML.G1Export.boardDigits, ``BML.G1Export.emitConstruction,
    ``BML.G1Export.exportThrough, ``main]
  for name in requiredExecutables do
    if (env.find? name).isNone then
      throwError "BML audit missing G1 exporter declaration {name}"
  let allowed : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]
  for (name, info) in env.constants.toList do
    if (`BML).isPrefixOf name || name == ``main then
      declarations := declarations + 1
      if info.isTheorem then theorems := theorems + 1
      let axioms ← collectAxioms name
      for axiomName in axioms do
        if !used.contains axiomName then used := used.push axiomName
        if !allowed.contains axiomName then
          throwError "BML axiom audit rejected {name}: {axiomName}"
  if theorems < 25 then
    throwError "BML audit found only {theorems} theorems; expected formal modules are missing"
  logInfo m!"BML axiom audit passed: {declarations} declarations, {theorems} theorems; transitive axioms: {used}"

audit_bml
