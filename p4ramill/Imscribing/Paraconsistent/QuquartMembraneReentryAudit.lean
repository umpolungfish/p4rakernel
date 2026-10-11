import Imscribing.Paraconsistent.QuquartMembraneReentry
import Imscribing.Paraconsistent.CertifiedModularResidue

open Imscribing.Paraconsistent.QuquartMembraneReentry
open Imscribing.Paraconsistent.CombinatoryFixedPoint

#print axioms runtime_native_roundtrip
#print axioms native_runtime_roundtrip
#print axioms runtime_tick_agrees
#print axioms runtime_program_tick
#print axioms observation_coordinates
#print axioms observation_control
#print axioms retained_runtime_program
#print axioms retained_runtime_bits
#print axioms Imscribing.Paraconsistent.CertifiedModularResidue.step_correct
#print axioms Imscribing.Paraconsistent.CertifiedModularResidue.residue_index_bound
#print axioms Imscribing.Paraconsistent.CertifiedModularResidue.same_residue_same_step
#print axioms Imscribing.Paraconsistent.CertifiedModularResidue.period_multiple_preserves_step

#eval (List.finRange 16).map (fun i => (maskIndex (nativeOutcome i)).val)

/- Export actual certified tables and clocks for every runtime seed and retained
evidence value. Consumers check the integer leaf and orbit against these tables. -/
#eval show IO Unit from do
  let mut records : Array Lean.Json := #[]
  for retained in List.finRange 16 do
    let program := Imscribing.Paraconsistent.CombinatoryReentry.seededOperator (nativeOutcome retained)
    for seed in List.finRange 16 do
      let some cycle := Imscribing.Paraconsistent.CombinatoryDynamics.analyzeOrbit 32 program (nativeOutcome seed)
        | throw <| IO.userError "retained runtime cycle missing"
      let clock := cycle.clock
      let table := (List.finRange 16).map fun i =>
        Lean.toJson (retainedRuntimeStep retained i).val
      let ticks := (List.range 16).map fun tick => Lean.toJson (runtimeTick clock tick).val
      records := records.push <| Lean.Json.mkObj
        [("retained", Lean.toJson retained.val), ("seed", Lean.toJson seed.val),
         ("entry", Lean.toJson cycle.entry), ("period", Lean.toJson cycle.period),
         ("table", Lean.toJson table), ("ticks", Lean.toJson ticks)]
  IO.println <| "QUQUART_CLOCKS=" ++ (Lean.Json.mkObj
    [("schema", Lean.toJson "retained-runtime-clock-v1"),
     ("clocks", Lean.toJson records)]).compress
