import Imscribing.Paraconsistent.CombinatoryReentry

/-!
Compile a combinator program into the native SIXTEEN_3 solver's full table.
Each table entry carries a reduction proof. A returned fixed point carries
checked information monotonicity, fixedness, and leastness for the program.
Insufficient reduction fuel and non-data results produce no table.
-/

namespace Imscribing.Paraconsistent.CombinatoryFixedPoint

open CombinatoryReentry
open Temporal.Semantics
local infixl:70 " @@ " => Term.app

/-- Encode all four native memberships in the kernel's mask order. -/
def maskIndex (x : Lean.Sixteen3) : Fin 16 :=
  ⟨(if x.hasN then 1 else 0) + (if x.hasT then 2 else 0) +
    (if x.hasF then 4 else 0) + (if x.hasB then 8 else 0), by
    rcases x with ⟨n, t, f, b⟩
    cases n <;> cases t <;> cases f <;> cases b <;> decide⟩

theorem ofMask_maskIndex (x : Lean.Sixteen3) :
    Lean.Sixteen3.ofMask (maskIndex x).val = x := by
  rcases x with ⟨n, t, f, b⟩
  cases n <;> cases t <;> cases f <;> cases b <;> decide

theorem maskIndex_ofMask : ∀ i : Fin 16,
    maskIndex (Lean.Sixteen3.ofMask i.val) = i := by decide

/-- A completed data computation with its combinatory reduction witness. -/
structure DataResult (program : Term) (input : Lean.Sixteen3) where
  value : Lean.Sixteen3
  reduced : Steps (program @@ .datum input) (.datum value)

def evaluate (fuel : Nat) (program : Term) (input : Lean.Sixteen3) :
    Option (DataResult program input) :=
  match h : run fuel (program @@ .datum input) with
  | .datum value => some ⟨value, by rw [← h]; exact run_reduces fuel _⟩
  | _ => none

/-- Exactly sixteen inputs; every output is certified against the program. -/
structure ProgramTable (program : Term) where
  entry : Fin 16 → Lean.Sixteen3
  reduced : ∀ i, Steps (program @@ .datum (Lean.Sixteen3.ofMask i.val))
    (.datum (entry i))

def tabulate (fuel : Nat) (program : Term) : Option (ProgramTable program) :=
  let results := fun i : Fin 16 => evaluate fuel program (Lean.Sixteen3.ofMask i.val)
  if h : ∀ i, (results i).isSome = true then
    some {
      entry := fun i => ((results i).get (h i)).value
      reduced := fun i => ((results i).get (h i)).reduced
    }
  else none

def ProgramTable.toArray {program : Term} (table : ProgramTable program) :
    Array Lean.Sixteen3 := Array.ofFn table.entry

theorem ProgramTable.toArray_size {program : Term} (table : ProgramTable program) :
    table.toArray.size = 16 := by simp [ProgramTable.toArray]

def ProgramTable.interpret {program : Term} (table : ProgramTable program)
    (x : Lean.Sixteen3) : Lean.Sixteen3 := table.entry (maskIndex x)

theorem ProgramTable.reduces_at {program : Term} (table : ProgramTable program)
    (x : Lean.Sixteen3) : Steps (program @@ .datum x) (.datum (table.interpret x)) := by
  simpa only [ofMask_maskIndex] using table.reduced (maskIndex x)

theorem ProgramTable.interpret_ofMask {program : Term} (table : ProgramTable program)
    (i : Fin 16) : table.interpret (Lean.Sixteen3.ofMask i.val) = table.entry i := by
  unfold ProgramTable.interpret
  rw [maskIndex_ofMask]

def MonotoneTable {program : Term} (table : ProgramTable program) : Prop :=
  ∀ i j : Fin 16, Lean.Sixteen3.le_i (Lean.Sixteen3.ofMask i.val)
    (Lean.Sixteen3.ofMask j.val) = true →
    Lean.Sixteen3.le_i (table.entry i) (table.entry j) = true

theorem ProgramTable.monotone_of_table {program : Term} (table : ProgramTable program)
    (hmono : MonotoneTable table) (x y : Lean.Sixteen3)
    (hxy : Lean.Sixteen3.le_i x y = true) :
    Lean.Sixteen3.le_i (table.interpret x) (table.interpret y) = true := by
  have horder : Lean.Sixteen3.le_i
      (Lean.Sixteen3.ofMask (maskIndex x).val)
      (Lean.Sixteen3.ofMask (maskIndex y).val) = true := by
    rw [ofMask_maskIndex, ofMask_maskIndex]
    exact hxy
  exact hmono (maskIndex x) (maskIndex y) horder

theorem ProgramTable.fixed_at_mask {program : Term} (table : ProgramTable program)
    (x : Lean.Sixteen3) (hx : table.interpret x = x) :
    table.entry (maskIndex x) = Lean.Sixteen3.ofMask (maskIndex x).val := by
  rw [ofMask_maskIndex]
  exact hx

def LeastTable {program : Term} (table : ProgramTable program)
    (point : Lean.Sixteen3) : Prop :=
  ∀ i : Fin 16, table.entry i = Lean.Sixteen3.ofMask i.val →
    Lean.Sixteen3.le_i point (Lean.Sixteen3.ofMask i.val) = true

instance {program : Term} (table : ProgramTable program) : Decidable (MonotoneTable table) :=
  inferInstanceAs (Decidable (∀ i j : Fin 16,
    Lean.Sixteen3.le_i (Lean.Sixteen3.ofMask i.val) (Lean.Sixteen3.ofMask j.val) = true →
    Lean.Sixteen3.le_i (table.entry i) (table.entry j) = true))

instance {program : Term} (table : ProgramTable program) (point : Lean.Sixteen3) :
    Decidable (LeastTable table point) :=
  inferInstanceAs (Decidable (∀ i : Fin 16,
    table.entry i = Lean.Sixteen3.ofMask i.val →
    Lean.Sixteen3.le_i point (Lean.Sixteen3.ofMask i.val) = true))

/-- Native solving produces this certificate after all finite checks pass. -/
structure Certificate (program : Term) where
  table : ProgramTable program
  point : Lean.Sixteen3
  monotone : ∀ x y, Lean.Sixteen3.le_i x y = true →
    Lean.Sixteen3.le_i (table.interpret x) (table.interpret y) = true
  fixed : table.interpret point = point
  least : ∀ x, table.interpret x = x → Lean.Sixteen3.le_i point x = true
  reached : feedback table.interpret Lean.Sixteen3.none 4 = point

/-- Validate a solver candidate against the entire certified value table. -/
def certify {program : Term} (table : ProgramTable program) (point : Lean.Sixteen3) :
    Option (Certificate program) :=
  if hmono : MonotoneTable table then
    if hfixed : table.interpret point = point then
      if hfinal : LeastTable table point ∧
          feedback table.interpret Lean.Sixteen3.none 4 = point then
        some {
          table := table
          point := point
          monotone := table.monotone_of_table hmono
          fixed := hfixed
          least := by
            intro x hx
            simpa only [ofMask_maskIndex] using
              hfinal.1 (maskIndex x) (table.fixed_at_mask x hx)
          reached := hfinal.2
        }
      else none
    else none
  else none

/-- Evaluate all inputs, call the C++ solver, and retain the checked certificate. -/
def solveProgram (fuel : Nat) (program : Term) : Option (Certificate program) := do
  let table ← tabulate fuel program
  let point ← Lean.Sixteen3.fixedPoint table.toArray
  certify table point

theorem Certificate.program_fixed {program : Term} (certificate : Certificate program) :
    Steps (program @@ .datum certificate.point) (.datum certificate.point) := by
  have h := certificate.table.reduces_at certificate.point
  rw [certificate.fixed] at h
  exact h

theorem Certificate.least_of_table_fixed {program : Term} (certificate : Certificate program)
    (x : Lean.Sixteen3) (h : certificate.table.interpret x = x) :
    Lean.Sixteen3.le_i certificate.point x = true := certificate.least x h

/-- The full certified map unfolds into an executable carrier-valued signal. -/
def Certificate.orbit {program : Term} (certificate : Certificate program) :
    Signal Lean.Sixteen3 := feedback certificate.table.interpret Lean.Sixteen3.none

theorem Certificate.orbit_settled {program : Term} (certificate : Certificate program)
    (tick : Nat) : certificate.orbit (tick + 4) = certificate.point := by
  induction tick with
  | zero => exact certificate.reached
  | succ tick ih =>
      change certificate.table.interpret (certificate.orbit (tick + 4)) = certificate.point
      rw [ih]
      exact certificate.fixed

end Imscribing.Paraconsistent.CombinatoryFixedPoint
