import Traffic
import Traffic.Export
-- Batch audits need the command and axiom APIs, not the server/shell umbrella.
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command

-- Audit every imported project declaration, including generated private declarations.
run_cmd do
  let env ← getEnv
  let names := (env.constants.toList.map Prod.fst).filter fun n =>
    let inProjectModule := match env.getModuleIdxFor? n with
      | none => false
      | some idx =>
        let moduleName := env.header.moduleNames[idx.toNat]!.toString
        moduleName == "Traffic" || moduleName.startsWith "Traffic."
    inProjectModule || n.toString.startsWith "Traffic." ||
      n.toString.startsWith "_private.Traffic."
  if names.isEmpty then
    throwError "axiom audit found no Traffic declarations"
  let mut theorems := 0
  for name in names.toArray.qsort Name.lt do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #["propext", "Quot.sound", "Classical.choice"].contains ax.toString do
        throwError "disallowed axiom {ax} in {name}"
    if (env.find? name).any ConstantInfo.isTheorem then
      theorems := theorems + 1
      liftIO <| IO.println s!"AUDIT_THEOREM\t{name}\t{String.intercalate "," (axioms.toList.map Name.toString)}"
  if theorems == 0 then
    throwError "axiom audit found no project theorems"
  liftIO <| IO.println s!"AUDIT_SUMMARY\t{names.length}\t{theorems}"
