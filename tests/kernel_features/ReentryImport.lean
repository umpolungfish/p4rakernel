import ReentryExport
open Lean
run_cmd do
  unless (← getEnv).isTrilattice do
    throwError "SIXTEEN_3 must remain active after importing a re-entry module"
example : exportedFixedPoint = Sixteen3.ofBelnap true true false true := rfl
#eval show IO Unit from do
  unless exportedRuntime && exportedFixedPoint.hasB do
    throw <| IO.userError "imported re-entry runtime mismatch"
def main : IO Unit := do
  unless exportedRuntime && exportedFixedPoint.hasB do
    throw <| IO.userError "compiled imported re-entry runtime mismatch"
