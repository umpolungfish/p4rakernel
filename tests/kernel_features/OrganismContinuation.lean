import NativeDialetheicOrganism

open Lean Lean.DialetheicOrganism

def main (args : List String) : IO Unit := do
  let [library] := args
    | throw <| IO.userError "supply the VGI organism adapter"
  let left ← create (Sixteen3.ofMask 8)
  let right ← create (Sixteen3.ofMask 8)
  attachVGI left library
  attachVGI right library
  for _ in [:4] do step left
  let middle ← snapshot left
  for _ in [:4] do step left
  for _ in [:8] do step right
  let after ← snapshot left
  unless after == (← snapshot right) do
    throw <| IO.userError "snapshot-interleaved continuation differs from uninterrupted execution"
  if middle == after then
    throw <| IO.userError "continued body did not change"
  let alias := left
  step alias
  step right
  unless (← snapshot left) == (← snapshot right) do
    throw <| IO.userError "alias failed to continue the same native body"
  IO.println "{\"status\":\"passed\",\"split_steps\":[4,4],\"uninterrupted_steps\":8,\"alias_step\":true,\"complete_state_equal\":true}"
