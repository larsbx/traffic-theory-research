import BML.RouteService
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut trapTheorems := 0
  let mut progressTheorems := 0
  let mut serviceTheorems := 0
  for (name, decl) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      unless mod == `BML.RouteTrap || mod == `BML.RouteProgress || mod == `BML.RouteService do continue
      for ax in ← collectAxioms name do
        unless #[`propext, `Quot.sound, `Classical.choice].contains ax do
          throwError "disallowed axiom {ax} in {name}"
      if decl.isTheorem then
        if mod == `BML.RouteTrap then trapTheorems := trapTheorems + 1
        else if mod == `BML.RouteProgress then progressTheorems := progressTheorems + 1
        else serviceTheorems := serviceTheorems + 1
  if trapTheorems == 0 || progressTheorems == 0 || serviceTheorems == 0 then
    throwError "R2 axiom audit found an empty module"
  liftIO <| IO.println s!"R2 axiom audit checked {trapTheorems} trap, {progressTheorems} progress, and {serviceTheorems} service theorems"
