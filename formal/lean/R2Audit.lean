import BML.RouteProgress
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut trapTheorems := 0
  let mut progressTheorems := 0
  for (name, decl) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      unless mod == `BML.RouteTrap || mod == `BML.RouteProgress do continue
      for ax in ← collectAxioms name do
        unless #[`propext, `Quot.sound, `Classical.choice].contains ax do
          throwError "disallowed axiom {ax} in {name}"
      if decl.isTheorem then
        if mod == `BML.RouteTrap then trapTheorems := trapTheorems + 1
        else progressTheorems := progressTheorems + 1
  if trapTheorems == 0 || progressTheorems == 0 then
    throwError "R2 axiom audit found an empty module"
  liftIO <| IO.println s!"R2 axiom audit checked {trapTheorems} trap and {progressTheorems} progress theorems"
