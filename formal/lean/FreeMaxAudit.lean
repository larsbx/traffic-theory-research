import Lean.Elab.Command
import Lean.Util.CollectAxioms
import FreeMaxExport

open Lean Elab Command

/-- Separate executable audit because exporter modules each define `main`.
The universal Theorem F declarations are also checked by the main BML audit. -/
elab "audit_free_max_export" : command => do
  let env ← getEnv
  let required : Array Name := #[
    ``BML.freeMax, ``BML.freeWith, ``BML.StaticFree,
    ``BML.staticFree_carCount_le_freeMax,
    ``BML.freeWith_staticFree, ``BML.freeWith_carCount_of_le,
    ``BML.exists_staticFree_with_count_iff,
    ``BML.exists_perpetual_allMove_with_count_iff,
    ``BML.exists_eventual_allMove_with_count_iff,
    ``BML.above_freeMax_never_staticFree,
    ``BML.FreeMaxExport.positionForall, ``BML.FreeMaxExport.staticFreeDecidable,
    ``BML.FreeMaxExport.staticFreeFlag, ``BML.FreeMaxExport.materialize,
    ``BML.FreeMaxExport.arrayConfig, ``BML.FreeMaxExport.boardDigits,
    ``BML.FreeMaxExport.sequenceField, ``BML.FreeMaxExport.traceConstruction,
    ``BML.FreeMaxExport.exportThrough, ``main]
  let allowed : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]
  let mut used : Array Name := #[]
  for name in required do
    if (env.find? name).isNone then
      throwError "free-max audit missing declaration {name}"
    for axiomName in (← collectAxioms name) do
      if !used.contains axiomName then used := used.push axiomName
      if !allowed.contains axiomName then
        throwError "free-max audit rejected {name}: {axiomName}"
  let mut declarations : Nat := 0
  for (name, _) in env.constants.toList do
    if (`BML.FreeMaxExport).isPrefixOf name || name == ``main then
      declarations := declarations + 1
      for axiomName in (← collectAxioms name) do
        if !used.contains axiomName then used := used.push axiomName
        if !allowed.contains axiomName then
          throwError "free-max exporter audit rejected {name}: {axiomName}"
  logInfo m!"Free-max audit passed: {required.size} required declarations; {declarations} exporter declarations; transitive axioms: {used}"

audit_free_max_export
