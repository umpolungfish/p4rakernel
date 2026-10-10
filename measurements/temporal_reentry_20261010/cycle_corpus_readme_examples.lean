import Imscribing.Paraconsistent.CombinatoryFixedPointBounds
import Imscribing.Paraconsistent.CombinatoryDynamics

open Imscribing.Paraconsistent.CombinatoryReentry
open Imscribing.Paraconsistent.CombinatoryFixedPoint
open Imscribing.Paraconsistent.CombinatoryFixedPointBounds
open Imscribing.Paraconsistent.TrilatticePrograms
open Imscribing.Paraconsistent.Temporal.Semantics

-- Retained singleton T settles at the subset containing T and F.
#eval (solveProgram 32 (seededOperator (FDE.singleton .T))).map (·.point)

-- Retention after injection: endpoints are empty and the T/F frame.
#eval (solveBounds 4 (retainAfterInject
  (Lean.Sixteen3.ofMask 6) (FDE.singleton .B))).map
  fun bounds => (bounds.lower.point, bounds.upper.point)

-- Injection after retention: endpoints are B and the T/F/B subset.
#eval (solveBounds 4 (injectAfterRetain
  (Lean.Sixteen3.ofMask 6) (FDE.singleton .B))).map
  fun bounds => (bounds.lower.point, bounds.upper.point)

open Imscribing.Paraconsistent.CombinatoryDynamics
open Imscribing.Paraconsistent.CombinatoryReentry
open Imscribing.Paraconsistent.Temporal.Semantics

#eval (analyzeOrbit 1 .negation (FDE.singleton .T)).map
  fun cycle => (cycle.entry, cycle.period, cycle.transient, cycle.loop)

#eval (analyzeOrbit 3 hold (FDE.singleton .T)).map
  fun cycle => (cycle.entry, cycle.period, cycle.transient, cycle.loop)

#eval (analyzeOrbit 32 (seededOperator (FDE.singleton .N)) (FDE.singleton .T)).map
  fun cycle => (cycle.entry, cycle.period, cycle.transient, cycle.loop)
