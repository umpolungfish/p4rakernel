import Imscribing.Paraconsistent.TrilatticePrograms

/-!
Greatest fixed points are computed through information-order duality and
checked against the original certified table. Bounds enclose every fixed
state; coincident endpoints certify uniqueness. Both feedback directions
settle by tick four and retain reduction evidence for the original program.
-/

namespace Imscribing.Paraconsistent.CombinatoryFixedPointBounds

open CombinatoryReentry CombinatoryFixedPoint
open Temporal.Semantics
local infixl:70 " @@ " => Term.app

/-- Boolean complement of the native information powerset: toggle all memberships. -/
def informationComplement (x : Lean.Sixteen3) : Lean.Sixteen3 :=
  ⟨!x.hasN, !x.hasT, !x.hasF, !x.hasB⟩

theorem informationComplement_involutive (x : Lean.Sixteen3) :
    informationComplement (informationComplement x) = x := by
  rcases x with ⟨n, t, f, b⟩
  cases n <;> cases t <;> cases f <;> cases b <;> decide

theorem informationComplement_order (x y : Lean.Sixteen3) :
    Lean.Sixteen3.le_i (informationComplement x) (informationComplement y) =
      Lean.Sixteen3.le_i y x := by
  rcases x with ⟨n, t, f, b⟩
  rcases y with ⟨yn, yt, yf, yb⟩
  cases n <;> cases t <;> cases f <;> cases b <;>
    cases yn <;> cases yt <;> cases yf <;> cases yb <;> decide

def dual (f : Lean.Sixteen3 → Lean.Sixteen3) (x : Lean.Sixteen3) : Lean.Sixteen3 :=
  informationComplement (f (informationComplement x))

theorem dual_involutive (f : Lean.Sixteen3 → Lean.Sixteen3) (x : Lean.Sixteen3) :
    dual (dual f) x = f x := by simp only [dual, informationComplement_involutive]

theorem dual_monotone (f : Lean.Sixteen3 → Lean.Sixteen3)
    (hf : ∀ x y, Lean.Sixteen3.le_i x y = true → Lean.Sixteen3.le_i (f x) (f y) = true)
    (x y : Lean.Sixteen3) (hxy : Lean.Sixteen3.le_i x y = true) :
    Lean.Sixteen3.le_i (dual f x) (dual f y) = true := by
  have hreverse : Lean.Sixteen3.le_i (informationComplement y)
      (informationComplement x) = true := by
    rw [informationComplement_order]
    exact hxy
  change Lean.Sixteen3.le_i (informationComplement (f (informationComplement x)))
    (informationComplement (f (informationComplement y))) = true
  rw [informationComplement_order]
  exact hf _ _ hreverse

theorem dual_fixed_iff (f : Lean.Sixteen3 → Lean.Sixteen3) (x : Lean.Sixteen3) :
    dual f (informationComplement x) = informationComplement x ↔ f x = x := by
  constructor
  · intro h
    have hc := congrArg informationComplement h
    simpa only [dual, informationComplement_involutive] using hc
  · intro h
    simp only [dual, informationComplement_involutive, h]

def dualArray {program : Term} (table : ProgramTable program) : Array Lean.Sixteen3 :=
  Array.ofFn fun i : Fin 16 => dual table.interpret (Lean.Sixteen3.ofMask i.val)

def GreatestTable {program : Term} (table : ProgramTable program)
    (point : Lean.Sixteen3) : Prop :=
  ∀ i : Fin 16, table.entry i = Lean.Sixteen3.ofMask i.val →
    Lean.Sixteen3.le_i (Lean.Sixteen3.ofMask i.val) point = true

instance {program : Term} (table : ProgramTable program) (point : Lean.Sixteen3) :
    Decidable (GreatestTable table point) :=
  inferInstanceAs (Decidable (∀ i : Fin 16,
    table.entry i = Lean.Sixteen3.ofMask i.val →
    Lean.Sixteen3.le_i (Lean.Sixteen3.ofMask i.val) point = true))

structure GreatestCertificate (program : Term) where
  table : ProgramTable program
  point : Lean.Sixteen3
  monotone : ∀ x y, Lean.Sixteen3.le_i x y = true →
    Lean.Sixteen3.le_i (table.interpret x) (table.interpret y) = true
  fixed : table.interpret point = point
  greatest : ∀ x, table.interpret x = x → Lean.Sixteen3.le_i x point = true
  reached : feedback table.interpret Lean.Sixteen3.all 4 = point

def certifyGreatest {program : Term} (table : ProgramTable program) (point : Lean.Sixteen3) :
    Option (GreatestCertificate program) :=
  if hmono : MonotoneTable table then
    if hfixed : table.interpret point = point then
      if hfinal : GreatestTable table point ∧
          feedback table.interpret Lean.Sixteen3.all 4 = point then
        some {
          table := table
          point := point
          monotone := table.monotone_of_table hmono
          fixed := hfixed
          greatest := by
            intro x hx
            simpa only [ofMask_maskIndex] using
              hfinal.1 (maskIndex x) (table.fixed_at_mask x hx)
          reached := hfinal.2
        }
      else none
    else none
  else none

def solveGreatest (fuel : Nat) (program : Term) : Option (GreatestCertificate program) := do
  let table ← tabulate fuel program
  let dualPoint ← Lean.Sixteen3.fixedPoint (dualArray table)
  certifyGreatest table (informationComplement dualPoint)

theorem GreatestCertificate.program_fixed {program : Term}
    (certificate : GreatestCertificate program) :
    Steps (program @@ .datum certificate.point) (.datum certificate.point) := by
  have h := certificate.table.reduces_at certificate.point
  rw [certificate.fixed] at h
  exact h

def GreatestCertificate.orbit {program : Term} (certificate : GreatestCertificate program) :
    Signal Lean.Sixteen3 := feedback certificate.table.interpret Lean.Sixteen3.all

theorem GreatestCertificate.orbit_settled {program : Term}
    (certificate : GreatestCertificate program) (tick : Nat) :
    certificate.orbit (tick + 4) = certificate.point := by
  induction tick with
  | zero => exact certificate.reached
  | succ tick ih =>
      change certificate.table.interpret (certificate.orbit (tick + 4)) = certificate.point
      rw [ih]
      exact certificate.fixed

structure Bounds (program : Term) where
  lower : Certificate program
  upper : GreatestCertificate program
  sameMap : ∀ x, lower.table.interpret x = upper.table.interpret x

def certifyBounds {program : Term} (lower : Certificate program)
    (upper : GreatestCertificate program) : Option (Bounds program) :=
  if h : ∀ i : Fin 16, lower.table.entry i = upper.table.entry i then
    some { lower := lower, upper := upper, sameMap := fun x => h (maskIndex x) }
  else none

/-- Compile once and compute both endpoints through the native solver. -/
def solveBounds (fuel : Nat) (program : Term) : Option (Bounds program) := do
  let table ← tabulate fuel program
  let lowerPoint ← Lean.Sixteen3.fixedPoint table.toArray
  let upperDualPoint ← Lean.Sixteen3.fixedPoint (dualArray table)
  let lower ← certify table lowerPoint
  let upper ← certifyGreatest table (informationComplement upperDualPoint)
  certifyBounds lower upper

theorem Bounds.ordered {program : Term} (bounds : Bounds program) :
    Lean.Sixteen3.le_i bounds.lower.point bounds.upper.point = true := by
  apply bounds.upper.greatest
  rw [← bounds.sameMap]
  exact bounds.lower.fixed

theorem Bounds.encloses_fixed {program : Term} (bounds : Bounds program)
    (x : Lean.Sixteen3) (hx : bounds.lower.table.interpret x = x) :
    Lean.Sixteen3.le_i bounds.lower.point x = true ∧
      Lean.Sixteen3.le_i x bounds.upper.point = true := by
  refine ⟨bounds.lower.least x hx, bounds.upper.greatest x ?_⟩
  rw [← bounds.sameMap]
  exact hx

theorem information_antisymm (x y : Lean.Sixteen3) :
    Lean.Sixteen3.le_i x y = true → Lean.Sixteen3.le_i y x = true → x = y := by
  rcases x with ⟨n, t, f, b⟩
  rcases y with ⟨yn, yt, yf, yb⟩
  cases n <;> cases t <;> cases f <;> cases b <;>
    cases yn <;> cases yt <;> cases yf <;> cases yb <;> decide

theorem Bounds.unique_of_equal {program : Term} (bounds : Bounds program)
    (heq : bounds.lower.point = bounds.upper.point) (x : Lean.Sixteen3)
    (hx : bounds.lower.table.interpret x = x) : x = bounds.lower.point := by
  have h := bounds.encloses_fixed x hx
  rw [← heq] at h
  exact information_antisymm x bounds.lower.point h.2 h.1

def Bounds.contains {program : Term} (bounds : Bounds program) (x : Lean.Sixteen3) : Bool :=
  Lean.Sixteen3.le_i bounds.lower.point x && Lean.Sixteen3.le_i x bounds.upper.point

def Bounds.isFixed {program : Term} (bounds : Bounds program) (x : Lean.Sixteen3) : Bool :=
  bounds.lower.table.interpret x == x

end Imscribing.Paraconsistent.CombinatoryFixedPointBounds
