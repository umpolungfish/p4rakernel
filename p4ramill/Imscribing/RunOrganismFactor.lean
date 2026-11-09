import NativeDialetheicOrganism
import Lean.Sixteen3

open Lean Lean.DialetheicOrganism

/-! RunOrganismFactor: drives an organism body through factorization, reading
a source file, attaching a VGI neural library and a factor bridge library,
running until closure or timeout, then printing the final snapshot. -/

def main (args : List String) : IO Unit := do
  let [sourceFile, neuralLibrary, factorLibrary, seconds] := args
    | throw <| IO.userError "organism-factor N-only-file VGI-adapter.so factor-bridge.so seconds"
  let some limit := seconds.toNat? | throw <| IO.userError "invalid execution boundary"
  let source ← IO.FS.readFile sourceFile
  let body ← create (Sixteen3.ofMask 8)
  attachVGI body neuralLibrary
  attachFactor body source factorLibrary
  let rec loop (remaining : ℕ) : IO Unit :=
    if remaining = 0 then pure ()
    else do
      closed ← taskClosed body
      if closed then pure ()
      else do
        step body
        loop (remaining - 1)
  loop limit
  IO.eprintln s!"ORGANISM_RETURN_DONE {limit * 1000}"
  IO.println (← snapshot body)

-- Derived: factor a source file through the organism with given libraries and timeout
def factorFile (sourceFile : String) (neuralLib : String) (factorLib : String) (timeoutSeconds : ℕ) : IO String := do
  let source ← IO.FS.readFile sourceFile
  let body ← create (Sixteen3.ofMask 8)
  attachVGI body neuralLib
  attachFactor body source factorLib
  let rec loop (remaining : ℕ) : IO Unit :=
    if remaining = 0 then pure ()
    else do
      closed ← taskClosed body
      if closed then pure ()
      else do
        step body
        loop (remaining - 1)
  loop timeoutSeconds
  ← snapshot body

-- Derived: run factorization from a Sixteen3 mask directly
def factorMask (mask : Nat) (neuralLib : String) (factorLib : String) (timeoutSeconds : ℕ) : IO String := do
  let body ← create (Sixteen3.ofMask mask)
  attachVGI body neuralLib
  attachFactor body "" factorLib
  let rec loop (remaining : ℕ) : IO Unit :=
    if remaining = 0 then pure ()
    else do
      closed ← taskClosed body
      if closed then pure ()
      else do
        step body
        loop (remaining - 1)
  loop timeoutSeconds
  ← snapshot body

-- Derived: factor a source file using runToClosure combinator
def factorFileClosure (sourceFile : String) (neuralLib : String) (factorLib : String) (stepLimit : ℕ) : IO String := do
  let source ← IO.FS.readFile sourceFile
  let body ← createWithBoth (Sixteen3.ofMask 8) neuralLib factorLib
  runToClosure body stepLimit

-- Derived: factor with VGI-only attachment until closure
def factorFileVGIOOnly (sourceFile : String) (neuralLib : String) (stepLimit : ℕ) : IO String := do
  let source ← IO.FS.readFile sourceFile
  let body ← createWithVGI (Sixteen3.ofMask 8) neuralLib
  runToClosure body stepLimit

-- Derived: factor with factor-lib-only attachment until closure
def factorFileFactorOnly (sourceFile : String) (factorLib : String) (stepLimit : ℕ) : IO String := do
  let source ← IO.FS.readFile sourceFile
  let body ← create (Sixteen3.ofMask 8)
  attachFactor body source factorLib
  runToClosure body stepLimit

-- Derived: factor multiple source files sequentially, collecting snapshots
def factorFiles (sourceFiles : List String) (neuralLib : String) (factorLib : String) (timeoutSeconds : ℕ) : IO (List String) := do
  let rec go (files : List String) (acc : List String) : IO (List String) :=
    match files with
    | [] => pure (List.reverse acc)
    | f :: fs => do
      let snap ← factorFile f neuralLib factorLib timeoutSeconds
      go fs (snap :: acc)
  go sourceFiles []

-- Derived: factor a file and report whether closure was reached within the timeout
def factorFileWithVerdict (sourceFile : String) (neuralLib : String) (factorLib : String) (timeoutSeconds : ℕ) : IO String := do
  let snap ← factorFile sourceFile neuralLib factorLib timeoutSeconds
  pure if snap = "" then "OPEN:" else s!"CLOSED:{snap}"

end RunOrganismFactor
