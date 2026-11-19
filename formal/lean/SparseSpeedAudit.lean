import Lean.Elab.Command
import Lean.Util.CollectAxioms
import SparseSpeedExport

open Lean Elab Command

/-- The main audit checks the whole B7 proof. Audit the separately linked
replay executable and its entry point here. -/
elab "audit_sparse_speed_export" : command => do
  let env ← getEnv
  let required : Array Name := #[``BML.SparseSpeedExport.row, ``BML.SparseSpeedExport.run, ``main]
  for name in required do
    if (env.find? name).isNone then
      throwError "B7 replay audit missing {name}"
  let allowed : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]
  let mut declarations : Nat := 0
  for (name, _) in env.constants.toList do
    if (`BML.SparseSpeedExport).isPrefixOf name || name == ``main then
      declarations := declarations + 1
      for axiomName in (← collectAxioms name) do
        if !allowed.contains axiomName then
          throwError "B7 replay audit rejected {name}: {axiomName}"
  logInfo m!"B7 replay axiom audit passed: {declarations} exporter declarations"

audit_sparse_speed_export

-- The direct counting definitions include exactly one blocked round from
-- the wrap-around CLASSIC east queue. The front car moves both rounds.
#guard BML.blockedRoundCount (by decide) (by decide) (BML.decode 5 5 82) 2 == 1
#guard BML.blockedTagCount (by decide) (by decide) (BML.decode 5 5 82) .east (4, 0) 2 == 1
#guard BML.blockedTagCount (by decide) (by decide) (BML.decode 5 5 82) .east (0, 0) 2 == 0

-- The strict inequality excludes equality, and a 3×3 full east row
-- keeps blocking outside the sparse range.
#guard !(decide (2 * BML.carCount 4 4 (BML.decode 4 4 19) < Nat.gcd 4 4))
#guard BML.blockedRoundCount (by decide) (by decide) (BML.decode 3 3 13) 4 == 4

-- Deadlines use elapsed time, including the zero deadline on empty boards.
#guard BML.sparseSpeedDeadline 1 1 (BML.decode 1 1 0) == 0
#guard BML.sparseSpeedDeadline 5 10 (BML.decode 5 10 487) == 60
