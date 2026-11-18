import Lean.Elab.Command
import Lean.Util.CollectAxioms
import BML.AbsorptionExport

open Lean Elab Command

elab "audit_absorption_export" : command => do
  let env ← getEnv
  let required : Array Name := #[``BML.AbsorptionExport.verdictDigit,
    ``BML.AbsorptionExport.row, ``BML.AbsorptionExport.run, ``main]
  let allowed : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]
  for name in required do
    unless env.contains name do
      throwError "Absorption exporter audit missing {name}"
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Absorption exporter audit rejected {name}: {axiomName}"
  logInfo m!"Absorption exporter audit passed: {required.size} declarations"

audit_absorption_export
