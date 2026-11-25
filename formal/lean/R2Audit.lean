import BML.RouteTrap
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut theorems := 0
  for (name, decl) in env.constants.toList do
    let inScope := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]! == `BML.RouteTrap
      | none => false
    if inScope then
      for ax in ← collectAxioms name do
        unless #[`propext, `Quot.sound, `Classical.choice].contains ax do
          throwError "disallowed axiom {ax} in {name}"
      if decl.isTheorem then
        theorems := theorems + 1
  if theorems == 0 then
    throwError "R2 axiom audit found no theorems"
  liftIO <| IO.println s!"R2 axiom audit checked {theorems} theorems"
