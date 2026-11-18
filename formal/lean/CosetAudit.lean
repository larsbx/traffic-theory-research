-- Batch audits need the command and axiom APIs, not the server/shell umbrella.
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import CosetExport

open Lean Elab Command

/-- Separate executable audit: the other exporters also have a global `main`.
The universal coset theorems belong to the main BML proof audit. -/
elab "audit_coset_export" : command => do
  let env ← getEnv
  let required : Array Name := #[
    ``BML.diagonalStep, ``BML.phaseClass,
    ``BML.CosetExport.emitPosition, ``BML.CosetExport.exportThrough, ``main]
  for name in required do
    if (env.find? name).isNone then
      throwError "coset exporter audit missing declaration {name}"
  let allowed : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]
  let mut declarations : Nat := 0
  let mut used : Array Name := #[]
  for (name, _) in env.constants.toList do
    if (`BML.CosetExport).isPrefixOf name || name == ``main then
      declarations := declarations + 1
      let axioms ← collectAxioms name
      for axiomName in axioms do
        if !used.contains axiomName then used := used.push axiomName
        if !allowed.contains axiomName then
          throwError "coset exporter audit rejected {name}: {axiomName}"
  logInfo m!"Coset exporter audit passed: {declarations} declarations; transitive axioms: {used}"

audit_coset_export
