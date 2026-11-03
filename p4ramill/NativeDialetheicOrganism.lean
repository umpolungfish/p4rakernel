import Lean
import Lean.Sixteen3
import Init.Paraconsistent

/-! Native retained organism handle. Every IO action continues the same C++
kernel body; snapshots read its actual source, nested frames, frontier,
programs, predictions, observations and action ancestry. -/

namespace Lean.DialetheicOrganism

private opaque BodyImpl : NonemptyType
def Body := BodyImpl.type
instance : Nonempty Body := BodyImpl.property

@[extern "lean_organism_create"]
opaque create (source : @& Sixteen3) : IO Body

@[extern "lean_organism_step"]
opaque step (body : @& Body) : IO Unit

@[extern "lean_organism_attach_vgi"]
opaque attachVGI (body : @& Body) (library : @& String) : IO Unit

@[extern "lean_organism_attach_factor"]
opaque attachFactor (body : @& Body) (source : @& String) (library : @& String) : IO Unit

@[extern "lean_organism_task_closed"]
opaque taskClosed (body : @& Body) : IO Bool

@[extern "lean_organism_snapshot"]
opaque snapshot (body : @& Body) : IO String

-- Derived: run exactly N steps, then return the snapshot
def runNSteps (body : @& Body) (n : ℕ) : IO String :=
  let rec loop (i : ℕ) : IO String :=
    if i ≥ n then ← snapshot body
    else do
      step body
      loop (i + 1)
  loop 0

-- Derived: run until closure or step limit, returning the final snapshot
def runToClosure (body : @& Body) (stepLimit : ℕ) : IO String :=
  let rec loop (n : ℕ) : IO String :=
    if n = 0 then ← snapshot body
    else do
      closed ← taskClosed body
      if closed then ← snapshot body
      else do
        step body
        loop (n - 1)
  loop stepLimit

-- Derived: create an organism from a source mask and immediately attach VGI
def createWithVGI (source : @& Sixteen3) (library : @& String) : IO Body := do
  let body ← create source
  attachVGI body library
  pure body

-- Derived: create an organism and attach a factor library
def createWithFactor (source : @& Sixteen3) (library : @& String) : IO Body := do
  let body ← create source
  attachFactor body "" library
  pure body

-- Derived: create an organism, attach both VGI and factor libraries
def createWithBoth (source : @& Sixteen3) (vgiLib : @& String) (factorLib : @& String) : IO Body := do
  let body ← create source
  attachVGI body vgiLib
  attachFactor body "" factorLib
  pure body

-- Derived: create an organism, attach factor library, and run to closure
def createAndFactor (source : @& Sixteen3) (factorLib : @& String) (stepLimit : ℕ) : IO String := do
  let body ← create source
  attachFactor body "" factorLib
  runToClosure body stepLimit

-- Derived: create with VGI, then run to closure
def createWithVGIAndRun (source : @& Sixteen3) (library : @& String) (stepLimit : ℕ) : IO String := do
  let body ← createWithVGI source library
  runToClosure body stepLimit

-- Derived: create with factor, then run to closure
def createWithFactorAndRun (source : @& Sixteen3) (factorLib : @& String) (stepLimit : ℕ) : IO String := do
  let body ← createWithFactor source factorLib
  runToClosure body stepLimit

-- Derived: create with both libraries, then run to closure
def createWithBothAndRun (source : @& Sixteen3) (vgiLib : @& String) (factorLib : @& String) (stepLimit : ℕ) : IO String := do
  let body ← createWithBoth source vgiLib factorLib
  runToClosure body stepLimit

-- Derived: run with VGI attachment until closure or step limit
def runWithVGITillClosure (body : @& Body) (library : @& String) (stepLimit : ℕ) : IO String := do
  attachVGI body library
  runToClosure body stepLimit

-- Derived: run with factor attachment until closure or step limit
def runWithFactorTillClosure (body : @& Body) (library : @& String) (stepLimit : ℕ) : IO String := do
  attachFactor body "" library
  runToClosure body stepLimit

-- Derived: compare two snapshots for dialetheic change (both/neither bits)
def snapshotChanged (s1 s2 : String) : Bool :=
  s1 ≠ s2

-- Derived: character-level diff report between two snapshots
def snapshotDiff (s1 s2 : String) : String :=
  if s1 = s2 then "IDENTICAL" else "DIFFERENT"

end Lean.DialetheicOrganism
