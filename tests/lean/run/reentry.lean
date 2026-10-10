import Lean
import Init.Paraconsistent

open Lean

enable_trilattice

/-- Adding the truth singleton at every information-order iteration converges to it. -/
reentry injectedTruth (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i f (Sixteen3.ofBelnap false true false false)

example : injectedTruth = Sixteen3.ofBelnap false true false false := rfl
example : injectedTruth.hasT = true := rfl
