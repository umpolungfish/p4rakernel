import Imscribing.Paraconsistent.CombinatoryFixedPointBounds

open Imscribing.Paraconsistent.CombinatoryReentry
open Imscribing.Paraconsistent.CombinatoryFixedPoint
open Imscribing.Paraconsistent.CombinatoryFixedPointBounds
open Imscribing.Paraconsistent.TrilatticePrograms
open Imscribing.Paraconsistent.Temporal.Semantics

local infixl:70 " @@ " => Term.app

#print axioms informationComplement_involutive
#print axioms informationComplement_order
#print axioms dual_involutive
#print axioms dual_monotone
#print axioms dual_fixed_iff
#print axioms GreatestCertificate.program_fixed
#print axioms GreatestCertificate.orbit_settled
#print axioms Bounds.ordered
#print axioms Bounds.encloses_fixed
#print axioms Bounds.unique_of_equal
#print axioms seedCeiling_fixed
#print axioms seedCeiling_greatest

private def values : Array Lean.Sixteen3 :=
  (List.range 16).toArray.map Lean.Sixteen3.ofMask

private def operations : List LatticeOp :=
  [.joinInformation, .meetInformation, .joinTruth, .meetTruth, .joinFalsity, .meetFalsity]

private def requireBounds {program : Term} (label : String)
    (lower upper : Lean.Sixteen3) (result : Option (Bounds program)) : IO Unit := do
  let some bounds := result
    | throw <| IO.userError s!"{label}: no bounds"
  unless bounds.lower.point == lower && bounds.upper.point == upper do
    throw <| IO.userError s!"{label}: endpoint mismatch"
  for x in values do
    if bounds.isFixed x then
      unless bounds.contains x do
        throw <| IO.userError s!"{label}: fixed state outside bounds"
      if lower == upper && x != lower then
        throw <| IO.userError s!"{label}: non-unique state between equal endpoints"
  for tick in [4:7] do
    unless bounds.lower.orbit tick == lower && bounds.upper.orbit tick == upper do
      throw <| IO.userError s!"{label}: unsettled feedback"

#eval show IO Unit from do
  for op in operations do
    for seed in values do
      requireBounds s!"seeded {repr op}" (seedPoint op seed) (seedCeiling op seed)
        (solveBounds 1 (withSeed op seed))
    requireBounds s!"diagonal {repr op}" Lean.Sixteen3.none Lean.Sixteen3.all
      (solveBounds 3 (diagonal op))
  IO.println "endpoint checks passed: 96 seeded lattice maps and 6 diagonal maps"

#eval show IO Unit from do
  requireBounds "identity" Lean.Sixteen3.none Lean.Sixteen3.all (solveBounds 1 .i)
  requireBounds "negation" Lean.Sixteen3.none Lean.Sixteen3.all (solveBounds 1 .negation)
  requireBounds "hold" Lean.Sixteen3.none Lean.Sixteen3.all (solveBounds 3 hold)
  for seed in values do
    requireBounds "constant" seed seed (solveBounds 1 (.k @@ .datum seed))
    requireBounds "Y constant" seed seed
      (solveBounds 100 (Y @@ (.k @@ (.k @@ .datum seed))))
    requireBounds "seeded negation" (FDE.negationClosure seed) Lean.Sixteen3.all
      (solveBounds 32 (seededOperator seed))
  IO.println "recursive endpoint checks passed: 3 base maps, 16 constants, 16 Y maps, 16 retained seeds"

#eval show IO Unit from do
  for frame in values do
    for seed in values do
      requireBounds "retain after inject" (Lean.Sixteen3.meet_i frame seed) frame
        (solveBounds 4 (retainAfterInject frame seed))
      requireBounds "inject after retain" seed (Lean.Sixteen3.join_i seed frame)
        (solveBounds 4 (injectAfterRetain frame seed))
  IO.println "composed endpoint checks passed: 512 maps with all fixed states enclosed"

#eval show IO Unit from do
  let some identityTable := tabulate 1 .i
    | throw <| IO.userError "identity table"
  for mask in [0:16] do
    unless (certifyGreatest identityTable (Lean.Sixteen3.ofMask mask)).isSome == (mask == 15) do
      throw <| IO.userError s!"non-greatest identity candidate accepted at {mask}"
  let some constantTable := tabulate 1 (.k @@ .datum (FDE.singleton .B))
    | throw <| IO.userError "constant table"
  unless (certifyGreatest constantTable Lean.Sixteen3.all).isNone do
    throw <| IO.userError "non-fixed greatest candidate accepted"
  unless (solveBounds 0 .i).isNone && (solveGreatest 0 .i).isNone do
    throw <| IO.userError "insufficient fuel accepted"
  let some negation := solveBounds 1 .negation
    | throw <| IO.userError "negation bounds"
  unless negation.contains (FDE.singleton .T) && !negation.isFixed (FDE.singleton .T) do
    throw <| IO.userError "interval membership mistaken for fixedness"
  unless (values.filter negation.isFixed).size == 8 do
    throw <| IO.userError "negation fixed-state count"
  IO.println "controls passed: 15 non-greatest candidates rejected, non-fixed and low-fuel rejection, non-fixed interior state"

#eval (solveBounds 4 (retainAfterInject (Lean.Sixteen3.ofMask 6) (FDE.singleton .B))).map
  fun bounds => (bounds.lower.point, bounds.upper.point)
#eval (solveBounds 4 (injectAfterRetain (Lean.Sixteen3.ofMask 6) (FDE.singleton .B))).map
  fun bounds => (bounds.lower.point, bounds.upper.point)
#eval (solveBounds 1 (withSeed .meetInformation (Lean.Sixteen3.ofMask 6))).map
  fun bounds => ((List.range 6).map bounds.lower.orbit, (List.range 6).map bounds.upper.orbit)

example : informationComplement (FDE.singleton .T) ≠ FDE.liftNegation (FDE.singleton .T) :=
  by decide
