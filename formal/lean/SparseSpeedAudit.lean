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

-- Equality is admitted. Alternating singleton classes move immediately,
-- whereas an adjacent equality queue blocks once before permanent flow.
#guard decide (2 * BML.carCount 4 4 (BML.decode 4 4 19) ≤ Nat.gcd 4 4)
#guard BML.blockedRoundCount (by decide) (by decide) (BML.decode 4 4 19) 8 == 0
#guard BML.blockedRoundCount (by decide) (by decide) (BML.decode 4 4 4) 8 == 1
#guard BML.blockedTagCount (by decide) (by decide) (BML.decode 4 4 4) .east (0, 0) 8 == 1

-- One car above the inclusive threshold is outside the guarantee: a full
-- 2×2 east row freezes, and three east cars in a 4×4 row block indefinitely.
#guard !(decide (2 * BML.carCount 2 2 (BML.decode 2 2 4) ≤ Nat.gcd 2 2))
#guard BML.blockedRoundCount (by decide) (by decide) (BML.decode 2 2 4) 2 == 2
#guard !(decide (2 * BML.carCount 4 4 (BML.decode 4 4 13) ≤ Nat.gcd 4 4))
#guard BML.blockedRoundCount (by decide) (by decide) (BML.decode 4 4 13) 8 == 8
#guard BML.blockedRoundCount (by decide) (by decide) (BML.decode 3 3 13) 4 == 4

-- Deadlines use elapsed time, including the zero deadline on empty boards.
#guard BML.sparseSpeedDeadline 1 1 (BML.decode 1 1 0) == 0
#guard BML.sparseSpeedDeadline 5 10 (BML.decode 5 10 487) == 60

-- These proof terms instantiate the inclusive theorem, including g=2,m=1,
-- where both the blockage budget and elapsed deadline are zero.
example (t : Nat) :
    BML.AllMove (BML.eastDirection 2 2 (by decide)) (BML.northDirection 2 2 (by decide))
      (BML.iterate (BML.torusStep 2 2 (by decide) (by decide)) t (BML.decode 2 2 1)) := by
  apply BML.low_density_speed_one_deadline (by decide) (by decide) _ (by decide) t
  change 0 ≤ t
  exact Nat.zero_le t

example (T : Nat) :
    BML.blockedTagCount (by decide) (by decide) (BML.decode 2 2 1) .east (0, 0) T = 0 := by
  exact Nat.eq_zero_of_le_zero (BML.low_density_tag_block_bound
    (by decide) (by decide) (BML.decode 2 2 1) (by decide) .east (0, 0) (by decide) T)

example :
    BML.AllMove (BML.eastDirection 4 4 (by decide)) (BML.northDirection 4 4 (by decide))
      (BML.iterate (BML.torusStep 4 4 (by decide) (by decide)) 16 (BML.decode 4 4 4)) := by
  exact BML.low_density_speed_one_deadline (by decide) (by decide)
    (BML.decode 4 4 4) (by decide) 16 (by decide)
