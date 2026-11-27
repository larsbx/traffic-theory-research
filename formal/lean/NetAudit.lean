import Lean.Elab.Command
import Lean.Util.CollectAxioms
import NetExport
import BML.NetGridlock
import BML.NetFree
import BML.NetCount
import BML.NetMixed
import BML.NetPlacement
import BML.NetRoundabout

open Lean Elab Command

/-- Audit the traffic-net layer: the generic gridlock theorems, the BML and
mixed-grid instances, the least gridlock of the mixed torus, the free-flow layer,
conservation, the placement extremes, the roundabout capacity, and the
separately linked replay. -/
elab "audit_net" : command => do
  let env ← getEnv
  let required : Array Name := #[
    ``BML.Net.stuck_step, ``BML.Net.stuck_iff, ``BML.Net.stuck_iff_run_constant,
    ``BML.Net.stuck_blocker_cycle, ``BML.Net.bml_even, ``BML.Net.bml_odd, ``BML.Net.bml_round,
    ``BML.Net.Layout.prev_iff, ``BML.Net.mixed_complete, ``BML.Net.mixed_fair,
    ``BML.Net.mixed_stuck_iff, ``BML.Net.junctions_frozen, ``BML.Net.stuck_carCount_cases,
    ``BML.Net.stuck_carCount_ge_street, ``BML.Net.rowStreet_length, ``BML.Net.colStreet_length,
    ``BML.Net.row_gridlock, ``BML.Net.col_gridlock, ``BML.Net.step_undelayed,
    ``BML.Net.free_run_iff, ``BML.Net.Free.sub, ``BML.Net.Free.run_sub, ``BML.Net.free_iff_pairs,
    ``BML.Net.free_of_recurrence, ``BML.Net.mixed_periodic, ``BML.Net.count_step,
    ``BML.Net.count_run, ``BML.Net.mixed_routeClosed, ``BML.Net.mixed_count_run,
    ``BML.Net.gridCells_length, ``BML.Net.stuck_carCount_le_cells, ``BML.Net.stuck_extendable,
    ``BML.Net.gridlock_count_iff, ``BML.Net.best_bound, ``BML.Net.worst_bound,
    ``BML.Net.worst_attained, ``BML.Net.best_attained, ``BML.Net.undelayed_carCount_le,
    ``BML.Net.free_carCount_le, ``BML.Net.capacity_attained,
    ``BML.NetExport.emit, ``main]
  for name in required do
    if (env.find? name).isNone then
      throwError "Net audit missing {name}"
  let allowed : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]
  let mut declarations : Nat := 0
  for (name, _) in env.constants.toList do
    if (`BML.Net).isPrefixOf name || (`BML.NetExport).isPrefixOf name || name == ``main then
      declarations := declarations + 1
      for axiomName in (← collectAxioms name) do
        if !allowed.contains axiomName then
          throwError "Net audit rejected {name}: {axiomName}"
  logInfo m!"Traffic-net axiom audit passed: {declarations} declarations"

audit_net
