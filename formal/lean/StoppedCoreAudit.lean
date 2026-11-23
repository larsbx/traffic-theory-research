import Lean.Elab.Command
import Lean.Util.CollectAxioms
import StoppedCoreExport

open Lean Elab Command

/-- Audit the separately linked finite replay, including the universal
refinement of its cached board and original-tag lists to the actual kernel. -/
elab "audit_stopped_core_export" : command => do
  let env ← getEnv
  let required : Array Name := #[
    ``BML.StoppedCoreExport.eval_board,
    ``BML.StoppedCoreExport.eval_eastTags,
    ``BML.StoppedCoreExport.eval_northTags,
    ``BML.StoppedCoreExport.coreTagCount_eq_tracedCoreCount,
    ``BML.StoppedCoreExport.fullLaneCheck_iff,
    ``BML.StoppedCoreExport.row, ``main]
  for name in required do
    if (env.find? name).isNone then
      throwError "Stopped-core replay audit missing {name}"
  let allowed : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]
  let mut declarations : Nat := 0
  for (name, _) in env.constants.toList do
    if (`BML.StoppedCoreExport).isPrefixOf name || name == ``main then
      declarations := declarations + 1
      for axiomName in (← collectAxioms name) do
        if !allowed.contains axiomName then
          throwError "Stopped-core replay audit rejected {name}: {axiomName}"
  logInfo m!"Stopped-core replay axiom audit passed: {declarations} exporter declarations"

audit_stopped_core_export
