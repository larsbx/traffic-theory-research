import Lean.Elab.Command
import Lean.Util.CollectAxioms
import NetExport

open Lean Elab Command

/-- Audit the traffic-net layer: the generic gridlock theorems, the BML and
mixed-grid instances, and the separately linked replay. -/
elab "audit_net" : command => do
  let env ← getEnv
  let required : Array Name := #[
    ``BML.Net.stuck_step, ``BML.Net.stuck_iff, ``BML.Net.stuck_iff_run_constant,
    ``BML.Net.stuck_blocker_cycle, ``BML.Net.bml_even, ``BML.Net.bml_odd, ``BML.Net.bml_round,
    ``BML.Net.Layout.prev_iff, ``BML.Net.mixed_complete, ``BML.Net.mixed_fair,
    ``BML.Net.mixed_stuck_iff, ``BML.NetExport.emit, ``main]
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
