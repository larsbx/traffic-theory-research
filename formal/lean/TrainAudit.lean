import Train
import Train.Export
import Lean

open Lean Elab Command

-- Audit all declarations originating in the TRAIN modules, including private
-- generated declarations and the executable's global `main`.
run_cmd do
  let env ← getEnv
  let required : Array Name := #[
    ``BML.Train.canMove_iff_queue_or_fullRing,
    ``BML.Train.canMove_iff_propagation,
    ``BML.Train.stopped_car_iff_blocker,
    ``BML.Train.canMove_local,
    ``BML.Train.moving_destination_filled,
    ``BML.Train.transport_bijection,
    ``BML.Train.other_species_unchanged,
    ``BML.Train.no_movers_iff_blocked_no_fullRing,
    ``BML.Train.noMoves_iff_stuck,
    ``BML.Train.stuck_iff_classic_no_fullRing,
    ``BML.Train.stuck_persists,
    ``BML.Train.cyclic_iterate_period,
    ``BML.Train.east_fullRing_iff_row,
    ``BML.Train.north_fullRing_iff_column,
    ``BML.Train.torus_stuck_iff,
    ``BML.Train.stuck_east_has_north,
    ``BML.Train.stuck_north_has_east,
    ``BML.Train.singleton_full_ring_counterexample,
    ``BML.Train.population_pos_iff,
    ``BML.Train.population_le_area,
    ``BML.Train.population_eq_listing,
    ``BML.Train.population_ge_rows_columns,
    ``BML.Train.Counting.filter_length_eq_of_bijection,
    ``BML.Train.Counting.speciesCount_eq_filter_length,
    ``BML.Train.speciesCount_halfStep,
    ``BML.Train.speciesCount_step,
    ``BML.Train.speciesCount_iterate,
    ``BML.Train.population_eq_speciesCounts,
    ``BML.Train.population_halfStep,
    ``BML.Train.population_step,
    ``BML.Train.population_iterate,
    ``BML.Train.moveCount_eq_zero_iff,
    ``BML.Train.totalMoveCount_eq_zero_iff_stuck,
    ``BML.Train.jam_iff_positive_zero_moves,
    ``BML.Train.full_species_moveCount,
    ``BML.Train.fixed_occupancy_with_movement,
    ``BML.Train.stuckConfig_population,
    ``BML.Train.stuckConfig_jam,
    ``BML.Train.jam_rows_columns,
    ``BML.Train.jam_population_lower,
    ``BML.Train.jam_population_iff_positive,
    ``BML.Train.no_jam_singleton,
    ``BML.Train.noMoves_population_iff,
    ``BML.Train.stuckCheck_eq_true_iff,
    ``BML.Train.moveCount_le_speciesCount,
    ``BML.Train.moveCount_eq_speciesCount_iff,
    ``BML.Train.totalMoveCount_le_population,
    ``BML.Train.fullSpeed_iff_all_phases_move,
    ``BML.Train.fullSpeed_iff_all_cars_move,
    ``BML.Train.fullSpeed_at_time_iff_tags,
    ``BML.Train.eventuallyFullSpeed_iff_moves_equal_initial_population,
    ``BML.Train.fullTransport_preserves_cell,
    ``BML.Train.fullTransport_injective,
    ``BML.Train.fullTransport_surjective,
    ``BML.Train.trace_cell,
    ``BML.Train.trace_injective,
    ``BML.Train.trace_coverage,
    ``BML.Train.corrected_trace_step_cases,
    ``BML.Train.corrected_trace_release,
    ``BML.Train.corrected_trace_stable_iff_move,
    ``BML.Train.Diagonals.sparse_eventual_stable,
    ``BML.Train.sparse_square_eventually_fullSpeed,
    ``BML.Train.sparse_square_moves_equal_population]
  for name in required do
    unless (env.find? name).any ConstantInfo.isTheorem do
      throwError "TRAIN audit missing required theorem {name}"
  let names := (env.constants.toList.map Prod.fst).filter fun name =>
    match env.getModuleIdxFor? name with
    | none => false
    | some idx =>
      let moduleName := env.header.moduleNames[idx.toNat]!.toString
      moduleName == "Train" || moduleName.startsWith "Train."
  if names.isEmpty then
    throwError "TRAIN audit found no originating project declarations"
  unless names.contains `main do
    throwError "TRAIN audit did not include the executable's global main"
  let allowed : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]
  let mut theorems := 0
  for name in names.toArray.qsort Name.lt do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "TRAIN axiom audit rejected {name}: {ax}"
    if (env.find? name).any ConstantInfo.isTheorem then
      theorems := theorems + 1
      liftIO <| IO.println s!"AUDIT_THEOREM\t{name}\t{String.intercalate "," (axioms.toList.map Name.toString)}"
  if theorems < required.size then
    throwError "TRAIN audit theorem inventory was unexpectedly small"
  liftIO <| IO.println s!"AUDIT_SUMMARY\t{names.length}\t{theorems}\t{required.size}"
