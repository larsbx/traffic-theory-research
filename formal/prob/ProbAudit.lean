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
    ``BML.Prob.sum_weight_mul_pow_eastCount, ``BML.Prob.prob_eastCount_ge,
    ``BML.Prob.speciesCount_eq_card, ``BML.Prob.prob_speciesCount_east_ge,
    ``BML.Prob.prob_speciesCount_east_ge_thin, ``BML.Prob.thin_upper_bound_chernoff]
  let allowed : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]
  for name in required do
    unless (env.find? name).any ConstantInfo.isTheorem do
      throwError "probability audit missing required theorem {name}"
    for ax in ← collectAxioms name do
      unless allowed.contains ax do
        throwError "probability audit rejected {name}: {ax}"
  liftIO <| IO.println s!"BML probability audit passed: {required.size} theorems; axioms within [propext, Quot.sound, Classical.choice]"
