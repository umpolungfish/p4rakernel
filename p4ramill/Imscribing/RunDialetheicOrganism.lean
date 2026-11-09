import Imscribing.NativeDialetheicOrganism
import Lean.Sixteen3

open Lean Lean.DialetheicOrganism

/-! RunDialetheicOrganism: drives a dialetheic organism body through a fixed
number of steps, starting from a Sixteen3 source mask, optionally attaching a
VGI adapter library, and printing the final snapshot. -/

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
  if let some library := args[2]? then _ ← attachVGI body library
  for _ in List.range steps do
    step body
  IO.println (← snapshot body)

def runWithMask (mask : Nat) (steps : Nat) (library : Option String) : IO String := do
  let body ← create (Sixteen3.ofMask mask)
  if let some lib := library then _ ← attachVGI body lib
  for _ in List.range steps do
    step body
  snapshot body

def runUntilClosedOrLimit (mask : Nat) (stepLimit : Nat) : IO String := do
  let body ← create (Sixteen3.ofMask mask)
  runToClosure body stepLimit

def runNStepsFromMask (mask : Nat) (steps : Nat) : IO String := do
  let body ← create (Sixteen3.ofMask mask)
  runNSteps body steps

def classifyState (s : Lean.Sixteen3) : String :=
  if s.hasB then "DIALETHEIC"
  else if s.hasT then "TRUE"
  else if s.hasF then "FALSE"
  else if s.hasN then "VOID"
  else "MIXED"

def runAndDiff (mask : Nat) (steps : Nat) (library : Option String) : IO String := do
  let body ← create (Sixteen3.ofMask mask)
  if let some lib := library then _ ← attachVGI body lib
  let before ← snapshot body
  for _ in List.range steps do
    step body
  let after ← snapshot body
  pure <| if before == after then s!"UNCHANGED:{after}" else s!"CHANGED:{after}"

def composeRuns (mask1 : Nat) (steps1 : Nat) (mask2 : Nat) (steps2 : Nat) (library : Option String) : IO String := do
  let snap1 ← runWithMask mask1 steps1 library
  let snap2 ← runWithMask mask2 steps2 library
  pure s!"{snap1}||{snap2}"
