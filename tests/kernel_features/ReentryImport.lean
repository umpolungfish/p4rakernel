import ReentryExport
open Lean
example : exportedFixedPoint = Sixteen3.ofBelnap true true false true := rfl
#eval show IO Unit from do
  unless exportedRuntime && exportedFixedPoint.hasB do
    throw <| IO.userError "imported re-entry runtime mismatch"
def main : IO Unit := do
  unless exportedRuntime && exportedFixedPoint.hasB do
    throw <| IO.userError "compiled imported re-entry runtime mismatch"
