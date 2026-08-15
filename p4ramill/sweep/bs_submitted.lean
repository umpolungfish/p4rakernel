import Mathlib
open BigOperators
open scoped BigOperators ComplexConjugate
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G] [Fintype G] [DecidableEq G]

def indicator (A : Set G) (x : G) : ℂ := if x ∈ A then 1 else 0

def density (A : Set G) : ℝ := (Fintype.card A : ℝ) / (Fintype.card G : ℝ)

def convolution (f g : G → ℂ) (x : G) : ℂ := ∑ y : G, f y * g (x - y)

def additive_energy (A : Set G) : ℝ :=
  ∑ x : G, ‖convolution (indicator A) (indicator A) x‖ ^ 2
