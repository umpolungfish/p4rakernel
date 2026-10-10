import Imscribing.Paraconsistent.TrilatticePrograms

open Imscribing.Paraconsistent.CombinatoryReentry
open Imscribing.Paraconsistent.CombinatoryFixedPoint
open Imscribing.Paraconsistent.TrilatticePrograms
open Imscribing.Paraconsistent.Temporal.Semantics

local infixl:70 " @@ " => Term.app

#print axioms lattice_apply
#print axioms after_unfold
#print axioms after_apply
#print axioms lattice_idempotent
#print axioms seedPoint_fixed
#print axioms seedPoint_least
#print axioms diagonal_apply
#print axioms retainAfterInject_apply
#print axioms injectAfterRetain_apply

private def operations : List LatticeOp :=
  [.joinInformation, .meetInformation, .joinTruth, .meetTruth, .joinFalsity, .meetFalsity]

private def values : Array Lean.Sixteen3 :=
  (List.range 16).toArray.map Lean.Sixteen3.ofMask

private def requirePoint {program : Term} (label : String) (expected : Lean.Sixteen3)
    (result : Option (Certificate program)) : IO Unit := do
  unless result.map (·.point) == some expected do
    throw <| IO.userError s!"{label}: expected {repr expected}, got {repr (result.map (·.point))}"

-- Every binary native operation contracts correctly on every pair of inputs.
#eval show IO Unit from do
  for op in operations do
    for x in values do
      unless run 3 (diagonal op @@ .datum x) == .datum x do
        throw <| IO.userError s!"diagonal failure: {repr op}, {repr x}"
      for y in values do
        unless run 1 (.lattice op @@ .datum x @@ .datum y) == .datum (op.apply x y) do
          throw <| IO.userError s!"binary contraction failure: {repr op}"
      requirePoint s!"seeded {repr op}" (seedPoint op x) (solveProgram 1 (withSeed op x))
    requirePoint s!"diagonal {repr op}" Lean.Sixteen3.none (solveProgram 3 (diagonal op))
  IO.println "trilattice checks passed: 1536 binary inputs, 96 diagonal inputs, 96 seeded maps, 6 diagonal maps"

-- Composition is tested in both orders over every frame, seed, and input.
#eval show IO Unit from do
  for frame in values do
    for seed in values do
      for x in values do
        unless run 4 (retainAfterInject frame seed @@ .datum x) ==
            .datum (Lean.Sixteen3.meet_i frame (Lean.Sixteen3.join_i seed x)) do
          throw <| IO.userError "retain-after-inject contraction"
        unless run 4 (injectAfterRetain frame seed @@ .datum x) ==
            .datum (Lean.Sixteen3.join_i seed (Lean.Sixteen3.meet_i frame x)) do
          throw <| IO.userError "inject-after-retain contraction"
      requirePoint "retain after inject" (Lean.Sixteen3.meet_i frame seed)
        (solveProgram 4 (retainAfterInject frame seed))
      requirePoint "inject after retain" seed
        (solveProgram 4 (injectAfterRetain frame seed))
  IO.println "composition checks passed: 8192 data inputs and 512 native fixed-point maps"

-- A frame containing T and F distinguishes the two orders on a singleton B seed.
private def tfFrame : Lean.Sixteen3 := Lean.Sixteen3.ofMask 6
private def bSeed : Lean.Sixteen3 := FDE.singleton .B

example : run 4 (retainAfterInject tfFrame bSeed @@ .datum Lean.Sixteen3.none) =
    .datum Lean.Sixteen3.none := by decide
example : run 4 (injectAfterRetain tfFrame bSeed @@ .datum Lean.Sixteen3.none) =
    .datum bSeed := by decide
example : run 4 (retainAfterInject tfFrame bSeed @@ .datum Lean.Sixteen3.none) ≠
    run 4 (injectAfterRetain tfFrame bSeed @@ .datum Lean.Sixteen3.none) := by decide

#eval (solveProgram 4 (retainAfterInject tfFrame bSeed)).map (·.point)
#eval (solveProgram 4 (injectAfterRetain tfFrame bSeed)).map (·.point)

-- Changing the native order changes the seeded map's least information point.
example : seedPoint .joinInformation (FDE.singleton .F) = FDE.singleton .F := by decide
example : seedPoint .joinTruth (FDE.singleton .F) = Lean.Sixteen3.none := by decide
example : seedPoint .joinFalsity (FDE.singleton .F) = FDE.singleton .F := by decide
