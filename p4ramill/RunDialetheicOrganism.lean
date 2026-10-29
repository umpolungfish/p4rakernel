import NativeDialetheicOrganism

open Lean Lean.DialetheicOrganism

def main (args : List String) : IO Unit := do
  if args.length > 3 then
    throw <| IO.userError "usage: organism [steps] [source-mask 0..15] [VGI-adapter.so]"
  let steps ← match args[0]? with
    | none => pure 12
    | some s => match s.toNat? with
      | some n => pure n
      | none => throw <| IO.userError "steps must be a natural number"
  let source ← match args[1]? with
    | none => pure 8
    | some s => match s.toNat? with
      | some n => if n < 16 then pure n else throw <| IO.userError "source-mask must be 0..15"
      | none => throw <| IO.userError "source-mask must be 0..15"
  let body ← create (Sixteen3.ofMask source)
  if let some library := args[2]? then attachVGI body library
  for _ in [:steps] do
    step body
  IO.println (← snapshot body)
