import Lean
import BML

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
  let allowed : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]
  for (name, info) in env.constants.toList do
    if (`BML).isPrefixOf name then
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
