-- Batch audits need only the command and axiom-collection APIs.
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import FreeFlowExport

open Lean Elab Command

/-- Separate executable audit because all exporters define a global `main`.
The universal B3 theorem declarations are covered by the main BML audit. -/
elab "audit_freeflow_export" : command => do
  let env ← getEnv
  let required : Array Name := #[
    ``BML.StaticFree, ``BML.AllMove, ``BML.halfStep, ``BML.torusStep,
    ``BML.FreeFlowExport.positionForall,
    ``BML.FreeFlowExport.staticFreeDecidable,
    ``BML.FreeFlowExport.allMoveDecidable,
    ``BML.FreeFlowExport.staticFreeFlag, ``BML.FreeFlowExport.allMoveFlag,
    ``BML.FreeFlowExport.materialize, ``BML.FreeFlowExport.arrayConfig,
    ``BML.FreeFlowExport.traceState, ``BML.FreeFlowExport.exportThrough, ``main]
  for name in required do
    if (env.find? name).isNone then
      throwError "free-flow exporter audit missing declaration {name}"
  let allowed : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]
  let mut declarations : Nat := 0
  let mut used : Array Name := #[]
  for (name, _) in env.constants.toList do
    if (`BML.FreeFlowExport).isPrefixOf name || name == ``main then
      declarations := declarations + 1
      let axioms ← collectAxioms name
      for axiomName in axioms do
        if !used.contains axiomName then used := used.push axiomName
        if !allowed.contains axiomName then
          throwError "free-flow exporter audit rejected {name}: {axiomName}"
  logInfo m!"Free-flow exporter audit passed: {declarations} declarations; transitive axioms: {used}"

audit_freeflow_export
