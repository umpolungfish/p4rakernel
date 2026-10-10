import Init.Paraconsistent
open Lean
enable_trilattice
reentry exportedFixedPoint (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i f (Sixteen3.ofBelnap true true false true)
def exportedRuntime : Bool := exportedFixedPoint.hasN && exportedFixedPoint.hasT && exportedFixedPoint.hasB
