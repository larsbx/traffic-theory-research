import Lean.Elab.Command
import Lean.Util.CollectAxioms
import BMLProb

open Lean Elab Command

-- The probability layer may use Mathlib, but only the three standard axioms.
run_cmd do
  let env ← getEnv
  let required : Array Name := #[
    ``BML.Prob.prob_forall, ``BML.Prob.prob_true, ``BML.Prob.prob_mono,
    ``BML.Prob.prob_forall_column, ``BML.Prob.prob_plug_no_lone,
    ``BML.Prob.jamProb_lower_bound, ``BML.Prob.thin_lower_bound,
    ``BML.Prob.prob_exists_fullNorthColumn, ``BML.Prob.jamProb_upper_bound,
    ``BML.Prob.eventuallyJammed_runGapCondition, ``BML.Prob.jamProb_runGap_upper,
    ``BML.Prob.renewal_weight_transport, ``BML.Prob.marked_block_factor,
    ``BML.Prob.marked_renewal_identity, ``BML.Prob.marked_sum_le,
    ``BML.Prob.noJam_isolated_north]
  let allowed : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]
  for name in required do
    unless (env.find? name).any ConstantInfo.isTheorem do
      throwError "probability audit missing required theorem {name}"
    for ax in ← collectAxioms name do
      unless allowed.contains ax do
        throwError "probability audit rejected {name}: {ax}"
  liftIO <| IO.println s!"BML probability audit passed: {required.size} theorems; axioms within [propext, Quot.sound, Classical.choice]"
