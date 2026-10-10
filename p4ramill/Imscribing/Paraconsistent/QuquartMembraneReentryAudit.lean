import Imscribing.Paraconsistent.QuquartMembraneReentry

open Imscribing.Paraconsistent.QuquartMembraneReentry
open Imscribing.Paraconsistent.CombinatoryFixedPoint

#print axioms runtime_native_roundtrip
#print axioms native_runtime_roundtrip
#print axioms runtime_tick_agrees
#print axioms runtime_program_tick
#print axioms observation_coordinates
#print axioms observation_control

#eval (List.finRange 16).map (fun i => (maskIndex (nativeOutcome i)).val)
