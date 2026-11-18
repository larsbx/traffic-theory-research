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
    ``BML.transport_bijection, ``BML.iterate_nonempty_iff,
    ``BML.carCount_eq_speciesCount, ``BML.halfStep_speciesCount,
    ``BML.iterate_torusStep_speciesCount, ``BML.iterate_torusStep_carCount,
    ``BML.finite_closed_cycle,
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
    ``BML.torus_fixed_iff_blocked, ``BML.winding_length_lower_bound,
    ``BML.freeClasses_attains_two_thirds_iff,
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
    ``BML.same_cell_no_round_move,
    ``BML.tagEventuallyStopped_iff_finitely_many_moves,
    ``BML.hasPermanentSite_iff_hasEventuallyStoppedCar,
    ``BML.occupied_forever_has_permanent_site,
    ``BML.eventuallyPermanent_east_successor,
    ``BML.eventuallyPermanent_north_successor,
    ``BML.future_blockingCore_of_permanent_site,
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
    ``BML.every_tag_moves_arbitrarily_late]
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
