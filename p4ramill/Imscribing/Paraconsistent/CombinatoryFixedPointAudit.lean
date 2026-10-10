import Imscribing.Paraconsistent.CombinatoryFixedPoint

open Imscribing.Paraconsistent.CombinatoryReentry
open Imscribing.Paraconsistent.CombinatoryFixedPoint
open Imscribing.Paraconsistent.Temporal.Semantics

local infixl:70 " @@ " => Term.app

#print axioms ofMask_maskIndex
#print axioms maskIndex_ofMask
#print axioms ProgramTable.toArray_size
#print axioms ProgramTable.reduces_at
#print axioms ProgramTable.interpret_ofMask
#print axioms Certificate.program_fixed
#print axioms Certificate.least_of_table_fixed
#print axioms Certificate.orbit_settled

private def requirePoint {program : Term} (label : String) (expected : Lean.Sixteen3)
    (result : Option (Certificate program)) : IO Unit := do
  unless result.map (·.point) == some expected do
    throw <| IO.userError s!"{label}: expected {repr expected}, got {repr (result.map (·.point))}"

-- Kernel solving follows the certified table produced by combinator execution.
#eval show IO Unit from do
  requirePoint "identity" Lean.Sixteen3.none (solveProgram 1 .i)
  requirePoint "negation" Lean.Sixteen3.none (solveProgram 1 .negation)
  requirePoint "hold" Lean.Sixteen3.none (solveProgram 3 hold)
  for mask in [0:16] do
    let seed := Lean.Sixteen3.ofMask mask
    requirePoint s!"seed {mask}" (FDE.negationClosure seed)
      (solveProgram 32 (seededOperator seed))
    requirePoint s!"constant {mask}" seed
      (solveProgram 1 (.k @@ .datum seed))
    -- Y computes a constant map; that map then enters the native finite solver.
    requirePoint s!"Y constant map {mask}" seed
      (solveProgram 100 (Y @@ (.k @@ (.k @@ .datum seed))))
  IO.println "native solver checks passed: identity, negation, hold, 16 seeds, 16 constants, 16 Y maps"

-- A fixed point of identity can still fail the leastness check.
#eval show IO Unit from do
  let some table := tabulate 1 .i
    | throw <| IO.userError "identity table did not compile"
  unless table.toArray.size == 16 do
    throw <| IO.userError "table cardinality"
  for mask in [0:16] do
    let candidate := Lean.Sixteen3.ofMask mask
    unless (certify table candidate).isSome == (mask == 0) do
      throw <| IO.userError s!"identity accepted the wrong least point at mask {mask}"
  let some seeded := tabulate 32 (seededOperator (FDE.singleton .T))
    | throw <| IO.userError "seeded table did not compile"
  unless (certify seeded Lean.Sixteen3.none).isNone do
    throw <| IO.userError "non-fixed candidate accepted"
  unless (certify seeded KernelReentry.truthNegationReentry).isSome do
    throw <| IO.userError "least seeded point rejected"
  IO.println "candidate controls passed: 15 fixed but non-least candidates rejected, non-fixed candidate rejected"

-- Table compilation requires a native data result for every input.
#eval show IO Unit from do
  unless (tabulate 0 .i).isNone && (tabulate 2 hold).isNone &&
      (tabulate 10 (.var 37)).isNone && (tabulate 10 duplicate).isNone do
    throw <| IO.userError "incomplete or non-data computation accepted"
  unless (tabulate 1 .i).isSome && (tabulate 3 hold).isSome do
    throw <| IO.userError "sufficient fuel rejected"
  IO.println "compilation controls passed: insufficient fuel and non-data results rejected"

-- These raw ABI controls deliberately change the map away from its bottom orbit.
#eval show IO Unit from do
  let identityTable := (List.range 16).toArray.map Lean.Sixteen3.ofMask
  unless (Lean.Sixteen3.fixedPoint #[]).isNone do
    throw <| IO.userError "malformed native table accepted"
  unless (Lean.Sixteen3.fixedPoint (identityTable.set! 15 Lean.Sixteen3.none)).isNone do
    throw <| IO.userError "off-path nonmonotone native table accepted"
  let complement := identityTable.map fun x =>
    Lean.Sixteen3.mk (!x.hasN) (!x.hasT) (!x.hasF) (!x.hasB)
  unless (Lean.Sixteen3.fixedPoint complement).isNone do
    throw <| IO.userError "complement table accepted"
  IO.println "native ABI controls passed: malformed, off-path nonmonotone, and complement tables rejected"

#eval (solveProgram 32 (seededOperator (FDE.singleton .T))).map (·.point)
#eval (solveProgram 32 (seededOperator (FDE.singleton .B))).map (·.point)

#eval (solveProgram 32 (seededOperator (FDE.singleton .T))).map fun certificate =>
  (List.range 6).map certificate.orbit
