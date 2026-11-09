import NativeDialetheicOrganism
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
  if let some library := args[2]? then attachVGI body library
  for _ in [:steps] do
    step body
  IO.println (← snapshot body)

-- Derived: run an organism from a mask with VGI attachment and report closure
def runWithMask (mask : Nat) (steps : ℕ) (library : Option String) : IO String := do
  let body ← create (Sixteen3.ofMask mask)
  match library with
  | some lib => attachVGI body lib
  | none => pure ()
  for _ in Finset.range steps do
    step body
  ← snapshot body

-- Derived: run until closure with a step limit
def runUntilClosedOrLimit (mask : Nat) (stepLimit : ℕ) : IO String := do
  let body ← create (Sixteen3.ofMask mask)
  runToClosure body stepLimit

-- Derived: run exactly N steps from a mask
def runNStepsFromMask (mask : Nat) (steps : ℕ) : IO String := do
  let body ← create (Sixteen3.ofMask mask)
  runNSteps body steps

-- Derived: classify a Sixteen3 state into one of 5 Belnap classes
def classifyState (s : Lean.Sixteen3) : String :=
  if s.hasB then "DIALETHEIC"
  else if s.hasT then "TRUE"
  else if s.hasF then "FALSE"
  else if s.hasN then "VOID"
  else "MIXED"

-- Derived: run N steps and report whether state changed across snapshots
def runAndDiff (mask : Nat) (steps : ℕ) (library : Option String) : IO String := do
  let body ← create (Sixteen3.ofMask mask)
  match library with
  | some lib => attachVGI body lib
  | none => pure ()
  let before ← ← snapshot body
  for _ in Finset.range steps do
    step body
  let after ← ← snapshot body
  pure if snapshotChanged before after then s!"CHANGED:{after}" else s!"UNCHANGED:{after}"

-- Derived: compose two organism runs (first result seeds second)
def composeRuns (mask1 : Nat) (steps1 : ℕ) (mask2 : Nat) (steps2 : ℕ) (library : Option String) : IO String := do
  let snap1 ← runWithMask mask1 steps1 library
  let snap2 ← runWithMask mask2 steps2 library
  pure s!"{snap1}||{snap2}"

end RunDialetheicOrganism
