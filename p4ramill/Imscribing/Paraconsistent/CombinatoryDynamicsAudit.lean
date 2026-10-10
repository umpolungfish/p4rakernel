import Imscribing.Paraconsistent.CombinatoryDynamics
import Imscribing.Paraconsistent.CombinatoryFixedPointBounds

open Imscribing.Paraconsistent.CombinatoryReentry
open Imscribing.Paraconsistent.CombinatoryFixedPoint
open Imscribing.Paraconsistent.CombinatoryFixedPointBounds
open Imscribing.Paraconsistent.CombinatoryDynamics
open Imscribing.Paraconsistent.TrilatticePrograms
open Imscribing.Paraconsistent.Temporal.Semantics

local infixl:70 " @@ " => Term.app

#print axioms feedback_restart
#print axioms feedback_equal_future
#print axioms Cycle.program_tick
#print axioms Cycle.periodic
#print axioms Cycle.no_earlier_return
#print axioms Cycle.fixed_of_period_one
#print axioms Cycle.moves_of_period_gt_one

private def values : Array Lean.Sixteen3 :=
  (List.range 16).toArray.map Lean.Sixteen3.ofMask

private def operations : List LatticeOp :=
  [.joinInformation, .meetInformation, .joinTruth, .meetTruth, .joinFalsity, .meetFalsity]

private def requireCycle {program : Term} {seed : Lean.Sixteen3} (label : String)
    (entry period : Nat) (loop : List Lean.Sixteen3)
    (reference : Lean.Sixteen3 → Lean.Sixteen3)
    (result : Option (Cycle program seed)) : IO Unit := do
  let some cycle := result
    | throw <| IO.userError s!"{label}: no cycle"
  unless cycle.entry == entry && cycle.period == period && cycle.loop == loop do
    throw <| IO.userError s!"{label}: incorrect transient or primitive period"
  unless cycle.transient == (List.range entry).map (feedback reference seed) do
    throw <| IO.userError s!"{label}: transient mismatch"
  unless cycle.isStationary == (period == 1) do
    throw <| IO.userError s!"{label}: stationary flag"
  for tick in [0:32] do
    unless cycle.orbit tick == feedback reference seed tick do
      throw <| IO.userError s!"{label}: reference feedback mismatch at {tick}"
    unless cycle.orbit (entry + tick + period) == cycle.orbit (entry + tick) do
      throw <| IO.userError s!"{label}: periodic continuation at {tick}"
  for start in [0:4] do
    for tick in [0:4] do
      unless feedback cycle.table.interpret (cycle.orbit start) tick ==
          cycle.orbit (start + tick) do
        throw <| IO.userError s!"{label}: restart mismatch"

private def requireIdempotent (label : String) (fuel : Nat) (program : Term)
    (reference : Lean.Sixteen3 → Lean.Sixteen3) : IO Unit := do
  let some table := tabulate fuel program
    | throw <| IO.userError s!"{label}: table did not compile"
  for seed in values do
    let point := reference seed
    unless reference point == point do
      throw <| IO.userError s!"{label}: reference is not idempotent"
    requireCycle label (if point == seed then 0 else 1) 1 [point] reference
      (findCycle table seed)

#eval show IO Unit from do
  requireIdempotent "identity" 1 .i id
  requireIdempotent "hold" 3 hold FDE.negationClosure
  let some table := tabulate 1 .negation
    | throw <| IO.userError "negation table"
  for seed in values do
    let opposite := FDE.liftNegation seed
    requireCycle "negation" 0 (if opposite == seed then 1 else 2)
      (if opposite == seed then [seed] else [seed, opposite]) FDE.liftNegation
      (findCycle table seed)
  IO.println "base feedback passed: all native seeds for identity, hold, and negation"

#eval show IO Unit from do
  for op in operations do
    for seed in values do
      requireIdempotent s!"seeded {repr op}" 1 (withSeed op seed) (op.apply seed)
    requireIdempotent s!"diagonal {repr op}" 3 (diagonal op) id
  for frame in values do
    for seed in values do
      requireIdempotent "retain after inject" 4 (retainAfterInject frame seed)
        (fun x => Lean.Sixteen3.meet_i frame (Lean.Sixteen3.join_i seed x))
      requireIdempotent "inject after retain" 4 (injectAfterRetain frame seed)
        (fun x => Lean.Sixteen3.join_i seed (Lean.Sixteen3.meet_i frame x))
  IO.println "lattice feedback passed: all native seeds for 96 seeded maps, 6 diagonals, and 512 compositions"

#eval show IO Unit from do
  for retained in values do
    requireIdempotent "constant" 1 (.k @@ .datum retained) (fun _ => retained)
    requireIdempotent "Y constant" 100 (Y @@ (.k @@ (.k @@ .datum retained)))
      (fun _ => retained)
    let some table := tabulate 32 (seededOperator retained)
      | throw <| IO.userError "retained-negation table"
    let reference := fun x => Lean.Sixteen3.join_i (FDE.liftNegation x) retained
    for seed in values do
      -- Negation with retained support repeats by tick four. Compute the
      -- expected first repeat from the FOUR operation, independently of AST reduction.
      let mut expected : Option (Nat × Nat) := none
      for stop in [1:5] do
        for entry in [0:stop] do
          if expected.isNone && feedback reference seed stop == feedback reference seed entry then
            expected := some (entry, stop - entry)
      let some (entry, period) := expected
        | throw <| IO.userError "retained-negation reference did not repeat"
      let loop := (List.range period).map fun phase => feedback reference seed (entry + phase)
      requireCycle "retained negation" entry period loop reference (findCycle table seed)
  IO.println "recursive feedback passed: all native seeds for 16 constants, 16 Y maps, and 16 retained-negation maps"

#eval show IO Unit from do
  let truth := FDE.singleton .T
  let falsity := FDE.singleton .F
  let unknown := FDE.singleton .N
  let both := FDE.singleton .B
  requireCycle "retained N oscillator" 1 2
    [Lean.Sixteen3.join_i falsity unknown, Lean.Sixteen3.join_i truth unknown]
    (fun x => Lean.Sixteen3.join_i (FDE.liftNegation x) unknown)
    (analyzeOrbit 32 (seededOperator unknown) truth)
  requireCycle "retained T settles from B" 2 1 [Lean.Sixteen3.ofMask 14]
    (fun x => Lean.Sixteen3.join_i (FDE.liftNegation x) truth)
    (analyzeOrbit 32 (seededOperator truth) both)
  let some bounds := solveBounds 1 .negation
    | throw <| IO.userError "negation bounds"
  requireCycle "shared bounds table" 0 2 [truth, falsity] FDE.liftNegation
    (findCycle bounds.lower.table truth)
  let table := bounds.lower.table
  unless (certifyCycle table truth 0 0).isNone &&
      (certifyCycle table truth 0 1).isNone &&
      (certifyCycle table truth 0 4).isNone &&
      (certifyCycle table truth 2 2).isNone &&
      (certifyCycle table truth 0 17).isNone do
    throw <| IO.userError "invalid cycle certificate accepted"
  unless (analyzeOrbit 0 .i truth).isNone &&
      (analyzeOrbit 1 (.datum both) truth).isNone do
    throw <| IO.userError "unfinished program accepted"
  IO.println "controls passed: retained-seed oscillator, delayed settlement, shared endpoint table, zero/nonclosing/nonprimitive/late/oversized cycles, fuel and residual rejection"

#eval (analyzeOrbit 1 .negation (FDE.singleton .T)).map
  fun cycle => (cycle.entry, cycle.period, cycle.transient, cycle.loop)
#eval (analyzeOrbit 3 hold (FDE.singleton .T)).map
  fun cycle => (cycle.entry, cycle.period, cycle.transient, cycle.loop)
#eval (analyzeOrbit 32 (seededOperator (FDE.singleton .N)) (FDE.singleton .T)).map
  fun cycle => (cycle.entry, cycle.period, cycle.transient, cycle.loop)
