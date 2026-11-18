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
    ``BML.carCount_eq_speciesCount, ``BML.halfStep_speciesCount,
    ``BML.iterate_torusStep_speciesCount, ``BML.iterate_torusStep_carCount,
    ``BML.finite_closed_cycle,
    ``BML.blocker_closed_winding, ``BML.jam_has_simple_blocker_cycle,
    ``BML.jam_carCount_lower_bound, ``BML.few_cars_never_jam,
    ``BML.exists_minimum_jam, ``BML.exists_jam_at_most_iff,
    ``BML.torus_fixed_iff_blocked, ``BML.winding_length_lower_bound,
    ``BML.freeClasses_attains_two_thirds_iff,
    ``BML.Witness.after_never_jams, ``BML.Witness.original_traced_car_moves_forever]
  for name in required do
    if (env.find? name).isNone then
      throwError "BML audit missing required theorem {name}"
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
