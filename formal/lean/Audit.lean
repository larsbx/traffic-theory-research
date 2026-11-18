import Lean
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
    ``BML.torus_fixed_iff_blocked, ``BML.winding_length_lower_bound,
    ``BML.freeClasses_attains_two_thirds_iff,
    ``BML.Witness.after_never_jams, ``BML.Witness.original_traced_car_moves_forever,
    ``BML.BlockingCore.persists, ``BML.BlockerCycle.persists,
    ``BML.carTrace_bijection, ``BML.RouteCover.distance_roundTransport,
    ``BML.RouteCover.rank_balance, ``BML.RouteCover.total_moves_le,
    ``BML.RouteCover.jammed_by_movementBudget]
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
