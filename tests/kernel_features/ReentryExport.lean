import Init.Paraconsistent
open Lean
run_cmd do
  unless (← getEnv).isTrilattice do
    throwError "SIXTEEN_3 must be active in a fresh module"
reentry exportedFixedPoint (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i f (Sixteen3.ofBelnap true true false true)
def exportedRuntime : Bool := exportedFixedPoint.hasN && exportedFixedPoint.hasT && exportedFixedPoint.hasB
