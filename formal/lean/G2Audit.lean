import Lean
import G2Export

open Lean Elab Command

/-- Kept separate from the G1 exporter audit because each executable has a
global `main`. The universal G2 theorems belong to the main BML proof audit. -/
elab "audit_g2_export" : command => do
  let env ← getEnv
  let required : Array Name := #[
    ``BML.G2Export.materialize, ``BML.G2Export.arrayConfig, ``BML.G2Export.boardDigits,
    ``BML.G2Export.observedJam, ``BML.G2Export.emitTransition,
    ``BML.G2Export.traceConstruction, ``BML.G2Export.exportThrough, ``main]
  for name in required do
    if (env.find? name).isNone then
      throwError "G2 exporter audit missing declaration {name}"
  let allowed : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]
  let mut declarations : Nat := 0
  let mut used : Array Name := #[]
  for (name, _) in env.constants.toList do
    if (`BML.G2Export).isPrefixOf name || name == ``main then
      declarations := declarations + 1
      let axioms ← collectAxioms name
      for axiomName in axioms do
        if !used.contains axiomName then used := used.push axiomName
        if !allowed.contains axiomName then
          throwError "G2 exporter audit rejected {name}: {axiomName}"
  logInfo m!"G2 exporter audit passed: {declarations} declarations; transitive axioms: {used}"

audit_g2_export
