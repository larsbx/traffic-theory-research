import BML.TrafficEvents
import BML.TrafficWork
import BML.TrafficPolicy
import BML.TrafficHistory
import BML.TrafficServiceBridge
import BML.TrafficObstruction
import BML.FieldObservation
import TrafficEvidenceCheck
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command

/-! Audit the proof modules, wire decoders and executable entry point together.
Native execution supplies finite correspondence evidence, not new proof axioms.
-/
run_cmd do
  let env ← getEnv
  let modules := #[`BML.TrafficEvents, `BML.TrafficWork, `BML.TrafficPolicy,
    `BML.TrafficHistory, `BML.TrafficServiceBridge, `BML.TrafficObstruction, `BML.FieldObservation,
    `FieldEvidenceCheck, `TrafficEventsCheck, `TrafficWorkCheck, `TrafficEvidenceCheck]
  let required := #[
    `BML.TrafficEvents.checkState_sound,
    `BML.TrafficEvents.checkState_complete,
    `BML.TrafficEvents.endpoints_do_not_determine_admissions,
    `BML.TrafficEvents.replay?_iff,
    `BML.TrafficEvents.AcceptedHistory.prefix,
    `BML.TrafficEvents.departure_leaves_vacancy,
    `BML.TrafficEvents.Run.toRouteTrace_leaves_vacancy,
    `BML.TrafficEvents.Run.movement_correspondence,
    `BML.TrafficWork.checkDAG_sound,
    `BML.TrafficWork.checked_batch_accounting,
    `BML.TrafficWork.checked_run_work_allowed,
    `BML.TrafficWork.Ledger.prefix_accounting,
    `BML.TrafficWork.finite_event_contradiction,
    `BML.TrafficWork.Focal.quota_wait_of_budget,
    `BML.TrafficWork.checked_closed_DAG_evacuation,
    `BML.TrafficPolicy.checkOwnerTable_exists,
    `BML.TrafficPolicy.checkOwnerConservingFrame_sound,
    `BML.TrafficPolicy.checkSignalPermission_sound,
    `BML.TrafficPolicy.ProtectedPolicy.quiet_owner_stable,
    `BML.TrafficPolicy.ProtectedPolicy.block_progress,
    `BML.TrafficPolicy.ProtectedPolicy.quota_wait_of_budget,
    `BML.TrafficPolicy.ProtectedPolicy.closed_DAG_evacuation,
    `BML.TrafficPolicy.checkProtectedPrefix_sound,
    `BML.TrafficPolicy.ProtectedPrefix.block_progress,
    `BML.TrafficPolicy.ProtectedPrefix.quota_wait_of_budget,
    `BML.TrafficPolicy.ProtectedPrefix.closed_DAG_evacuation,
    `BML.TrafficHistory.extend_accepted,
    `BML.TrafficHistory.extend_replay,
    `BML.TrafficHistory.extend_checked_policy,
    `BML.TrafficServiceBridge.protected_bounded_service,
    `BML.TrafficServiceBridge.protected_joint_guarantee,
    `BML.TrafficServiceBridge.protected_moves_before_rank_bound,
    `BML.TrafficObstruction.replay_prefix,
    `BML.TrafficObstruction.empty_structural_trap,
    `BML.TrafficObstruction.vacancy_every_two,
    `BML.TrafficObstruction.no_joint_vacancy_and_phase,
    `BML.TrafficObstruction.no_bounded_service,
    `BML.TrafficObstruction.requestAge_step,
    `BML.FieldObservation.crossing_iff,
    `BML.FieldObservation.gap_candidate_not_crossing,
    `BML.FieldObservation.no_immediate_double_crossing,
    `BML.FieldObservation.robustPhase_iff,
    `BML.FieldObservation.robustSpatial_sound,
    `BML.FieldObservation.phase_comparable_requires_registrations,
    `BML.FieldObservation.vacancy_of_complete_observation,
    `BML.FieldObservation.missing_sample_is_nonidentifying]
  for name in required do
    unless (env.find? name).any ConstantInfo.isTheorem do
      throwError "missing required evidence theorem {name}"
  let mut declarations := 0
  let mut theorems := 0
  for mod in modules do
    let mut moduleDecls := 0
    let mut moduleTheorems := 0
    for (name, decl) in env.constants.toList do
      if let some index := env.getModuleIdxFor? name then
        unless env.header.moduleNames[index.toNat]! == mod do continue
        moduleDecls := moduleDecls + 1
        let axioms ← collectAxioms name
        for ax in axioms do
          unless #[`propext, `Quot.sound, `Classical.choice].contains ax do
            throwError "disallowed axiom {ax} in {name}"
        if decl.isTheorem then
          moduleTheorems := moduleTheorems + 1
          liftIO <| IO.println s!"EVIDENCE_THEOREM\t{mod}\t{name}\t{String.intercalate "," (axioms.toList.map Name.toString)}"
    if moduleDecls == 0 then throwError "empty or unaudited evidence module {mod}"
    declarations := declarations + moduleDecls
    theorems := theorems + moduleTheorems
    liftIO <| IO.println s!"EVIDENCE_MODULE\t{mod}\t{moduleDecls}\t{moduleTheorems}"
  liftIO <| IO.println s!"EVIDENCE_SUMMARY\t{declarations}\t{theorems}\t{required.size}"
