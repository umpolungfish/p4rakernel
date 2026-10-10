import Init.Paraconsistent
import Imscribing.Paraconsistent.CombinatoryFixedPointBounds
import Imscribing.Paraconsistent.CombinatoryDynamics
open Lean

enable_trilattice

reentry injectedTruth (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i f (Sixteen3.ofBelnap false true false false)

example : injectedTruth = Sixteen3.ofBelnap false true false false := rfl
example : injectedTruth.hasT = true := rfl

open Imscribing.Paraconsistent.CombinatoryFixedPointBounds
open Imscribing.Paraconsistent.TrilatticePrograms

#eval (solveBounds 4 (retainAfterInject
  (Lean.Sixteen3.ofMask 6) (Lean.Sixteen3.ofMask 8))).map
  fun bounds => (bounds.lower.point, bounds.upper.point)

#eval (solveBounds 4 (injectAfterRetain
  (Lean.Sixteen3.ofMask 6) (Lean.Sixteen3.ofMask 8))).map
  fun bounds => (bounds.lower.point, bounds.upper.point)

open Imscribing.Paraconsistent.CombinatoryDynamics
open Imscribing.Paraconsistent.CombinatoryReentry
open Imscribing.Paraconsistent.Temporal.Semantics

#eval (analyzeOrbit 1 .negation (FDE.singleton .T)).map
  fun cycle => (cycle.entry, cycle.period, cycle.loop)

#eval (analyzeOrbit 32 (seededOperator (FDE.singleton .N)) (FDE.singleton .T)).map
  fun cycle => (cycle.entry, cycle.period, cycle.loop)

enable_paraconsistent
#is_paraconsistent
-- A direct h.rec with h : False is rejected while this mode is enabled.
disable_paraconsistent
