import Mathlib

/-!
# The IUT paper's carrier, kept *distinct* from native `Lean.Sixteen3`

The paper's power set on {T,F,t,f} and the fork's native power set on
{N,T,F,B} each have 16 elements, but do not identify those atom labels.
This module formalizes paper-style three-arm split/recombination by union.
-/

namespace Imscribing.PrimeWhorl.Paper

inductive Atom where
  | T | F | t | f
  deriving Repr, DecidableEq

abbrev Carrier := Set Atom

def truthArm (X : Carrier) : Carrier := X ∩ {Atom.T}
def informationArm (X : Carrier) : Carrier := X ∩ {Atom.t, Atom.f}
def falsityArm (X : Carrier) : Carrier := X ∩ {Atom.F}

/-- Asymmetric three-arm decomposition (the middle arm is not discarded). -/
def delta3 (X : Carrier) : Carrier × Carrier × Carrier :=
  (truthArm X, informationArm X, falsityArm X)

/-- Recombination is union; no classical resolution is imposed. -/
def mu3 (parts : Carrier × Carrier × Carrier) : Carrier :=
  parts.1 ∪ parts.2.1 ∪ parts.2.2

/-- Exact self-fusion/recovery BEFORE branchwise deformation. -/
theorem mu3_delta3 (X : Carrier) : mu3 (delta3 X) = X := by
  ext a
  cases a <;> simp [mu3, delta3, truthArm, informationArm, falsityArm]

/-- Classical support is a lossy four-valued slice, not a Boolean choice. -/
def classicalSlice (X : Carrier) : Carrier := X ∩ {Atom.T, Atom.F}

/-- A full information-bearing glut is lost under the classical slice. -/
def full : Carrier := Set.univ

theorem full_t_survives : Atom.t ∈ full := by simp [full]
theorem full_f_survives : Atom.f ∈ full := by simp [full]
theorem classicalSlice_loses_t (X : Carrier) : Atom.t ∉ classicalSlice X := by
  simp [classicalSlice]
theorem classicalSlice_loses_f (X : Carrier) : Atom.f ∉ classicalSlice X := by
  simp [classicalSlice]

end Imscribing.PrimeWhorl.Paper
