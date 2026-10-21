import Imscribing.Vox.ProofLift
import Imscribing.Millennium.Erdos.CollatzDepthSplit
open Lean Elab Meta in
elab "#liftTab " ids:ident+ : command => Elab.Command.liftTermElabM do
  for i in ids do
    let n ← realizeGlobalConstNoOverload i
    let w ← ProofLift.wordOf n
    IO.println s!"{n}\t{w}"
#liftTab CollatzDepthSplit.col_shift CollatzDepthSplit.survives_succ_of_odd CollatzDepthSplit.exists_survivor_lift CollatzDepthSplit.survivors_nonempty CollatzDepthSplit.not_contracts_pred_two_pow CollatzDepthSplit.both_lifts_survive CollatzDepthSplit.col_lt_of_gap CollatzDepthSplit.oddSteps_mod
