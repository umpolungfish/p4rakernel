import Mathlib
import Imscribing.Millennium.SIC_D2048_Moduli
import Imscribing.Millennium.StarkRungFiveDualLimit

/-!
# StarkClassNumberField — the number field of the analytic last rung

Direct attack on K4 (the Dirichlet class-number relation).  This module puts
`F = ℚ(√4190205)` into Mathlib's `NumberField` machinery: the defining
polynomial `X² − 4190205` is irreducible over ℚ, so `AdjoinRoot` carries the
`Field` and `NumberField` instances.  Everything downstream of the general
`NumberField.dedekindZeta_residue` (the Dirichlet class number formula) can
therefore be stated for this exact field.

The two arithmetic inputs that Mathlib does not compute — the class number
`64` and the regulator `log ε` of this field, together with the factorization
`ζ_F = ζ · L(χ)` — are the remaining wall; see the module notes in
`stark-ladder-state.md`.
-/


open Polynomial
open Complex Real
open Imscribing.Millennium.StarkCharacterD2048
open Imscribing.Millennium.StarkRungOne
open Imscribing.Millennium.StarkRungFour
open Imscribing.Millennium.ClinkStarkBridge
open Imscribing.Millennium.StarkDualLimit

namespace Imscribing.Millennium.StarkClassNumberField

/-- `4190205` is not a square in ℚ.  Reduced to the integer non-square receipt
    `SIC.D2048.Moduli.m2048_not_square` through `Rat.sqrt`. -/
theorem not_sq_rat : ∀ b : ℚ, b ^ 2 ≠ (4190205 : ℚ) := by
  intro b hb
  have hb2 : b * b = (4190205 : ℚ) := by simpa [pow_two] using hb
  have hRat : Rat.sqrt (4190205 : ℚ) * Rat.sqrt (4190205 : ℚ) = (4190205 : ℚ) :=
    (Rat.exists_mul_self (4190205 : ℚ)).1 ⟨b, hb2⟩
  have hcast : (4190205 : ℚ) = ((4190205 : ℤ) : ℚ) := by norm_num
  rw [hcast, Rat.sqrt_intCast] at hRat
  have hsqrt_sq : Int.sqrt 4190205 * Int.sqrt 4190205 ≠ (4190205 : ℤ) := by
    intro h
    have hnot : ¬ ∃ n : ℤ, (4190205 : ℤ) = n * n := by
      simpa [IsSquare] using SIC.D2048.Moduli.m2048_not_square
    rcases (Int.exists_mul_self (4190205 : ℤ)).2 h with ⟨n, hn⟩
    exact hnot ⟨n, hn.symm⟩
  apply hsqrt_sq
  exact_mod_cast hRat

/-- The defining polynomial of `F = ℚ(√4190205)`. -/
theorem irreducible_quadratic :
    Irreducible ((X ^ 2 - C (4190205 : ℚ)) : Polynomial ℚ) := by
  apply X_pow_sub_C_irreducible_of_prime (by norm_num : Nat.Prime 2)
  exact not_sq_rat

/-- The number field `F = ℚ[X]/(X² − 4190205)`. -/
abbrev F := AdjoinRoot ((X ^ 2 - C (4190205 : ℚ)) : Polynomial ℚ)

instance : Fact (Irreducible ((X ^ 2 - C (4190205 : ℚ)) : Polynomial ℚ)) :=
  ⟨irreducible_quadratic⟩

/-- `F` really is a number field, so the general Dirichlet class number formula
    applies to it. -/
instance : NumberField F := by infer_instance

/-- The residue of `ζ_F` at `s = 1` is positive — Mathlib's Dirichlet class
    number formula, instantiated at the Stark field. -/
theorem residue_pos : 0 < NumberField.dedekindZeta_residue F :=
  NumberField.dedekindZeta_residue_pos F

/-- The exact form of the class number formula at this field: the residue is
    `2^2 · regulator · classNumber / (2 · √4190205)`, since `F` has two real
    places and no complex places. -/
theorem residue_def :
    NumberField.dedekindZeta_residue F =
      (2 ^ NumberField.InfinitePlace.nrRealPlaces F *
        (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces F *
        NumberField.Units.regulator F * NumberField.classNumber F) /
      (NumberField.Units.torsionOrder F * Real.sqrt |NumberField.discr F|) :=
  NumberField.dedekindZeta_residue_def F


/-! ### The standard inputs Mathlib does not compute for this field

These are the ordinary invariants of `F = ℚ(√4190205)`, verified by PARI/GP
in `SIC_D2048_Moduli` and standard for real quadratic fields.  Mathlib has the
general Dirichlet class number formula but no quadratic specialization, no
`ζ_F = ζ · L(χ)` factorization, and no class-number or regulator computation
for a concrete field.  They are therefore recorded here as named receipts, in
the same style as the other PARI data in the tree, so that the derivation below
is fully auditable. -/

/-- The class number of `F` is 64 (PARI `bnfinit(x²−4190205).clgp`). -/
axiom classNumber_F : NumberField.classNumber F = 64

/-- The regulator of `F` is `log ε`, `ε = (2047+√4190205)/2` the fundamental unit. -/
axiom regulator_F : NumberField.Units.regulator F = Real.log ((2047 + Real.sqrt 4190205) / 2)

/-- The only roots of unity in a real quadratic field are ±1. -/
axiom torsionOrder_F : NumberField.Units.torsionOrder F = 2

/-- `F` has two real places and no complex places. -/
axiom nrReal_F : NumberField.InfinitePlace.nrRealPlaces F = 2
axiom nrComplex_F : NumberField.InfinitePlace.nrComplexPlaces F = 0

/-- The (absolute) field discriminant is 4190205. -/
axiom discr_abs_F : |NumberField.discr F| = (4190205 : ℤ)

/-- The quadratic Dedekind zeta factorization `ζ_F = ζ · L(χ)` together with
    the residue `res₁ ζ = 1` gives `res₁ ζ_F = L(1, χ)`. -/
axiom residue_eq_L_one_re : NumberField.dedekindZeta_residue F = (ZMod.LFunction qchar 1).re

/-- **K4 closed modulo the standard receipts above.** Mathlib's Dirichlet class
    number formula, specialized to `F = ℚ(√4190205)`, is exactly the analytic
    class number relation `√con · L(1, χ) = 2 h · log ε`.  Combined with the
    unconditional K3b, this closes the Stark ladder (`stark_ladder_closed`). -/
theorem cnf_of_class_number_formula :
    ((Real.sqrt (con : ℝ) : ℝ) : ℂ) * ZMod.LFunction qchar 1
      = (2 : ℂ) * ((((hField : ℕ) : ℝ) * Real.log (epsilonReal 2048) : ℝ) : ℂ) := by
  have hres := residue_def
  have hdisc : |((NumberField.discr F : ℤ) : ℝ)| = (4190205 : ℝ) := by
    rw [← Int.cast_abs, discr_abs_F]
    norm_num
  rw [nrReal_F, nrComplex_F, torsionOrder_F, regulator_F, classNumber_F, hdisc] at hres
  norm_num at hres
  rw [residue_eq_L_one_re] at hres
  have him : (ZMod.LFunction qchar 1).im = 0 := im_LFunction_one_eq_zero
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hcon : (con : ℝ) = 4190205 := by norm_num [con]
    rw [hcon]
    have hsqrt_pos : 0 < Real.sqrt (4190205 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    rw [hres]
    field_simp [ne_of_gt hsqrt_pos]
    norm_num [SIC.D2048.Moduli.hilbert_class_degree, epsilonReal]
    ring
  · simp [Complex.mul_im, him]


/-- **The Stark ladder is closed** modulo the standard receipts: the algebraic
    Stark theorem and the analytic derivative identity at d = 2048. -/
theorem stark_ladder_closed_of_class_number_formula :
    (epsilonReal 2048 * epsilonConjReal 2048 = 1 ∧
    epsilonReal 2048 + epsilonConjReal 2048 = (2047 : ℝ) ∧
    (2046 : ℝ) < epsilonReal 2048 ∧ epsilonReal 2048 < (2047 : ℝ) ∧
    (1/2047 : ℝ) < epsilonConjReal 2048 ∧ epsilonConjReal 2048 < (1/2046 : ℝ) ∧
    epsilonReal 2048 ≠ 0 ∧ epsilonConjReal 2048 ≠ 0 ∧
    2 * Real.cosh (Real.log (epsilonReal 2048)) = (2047 : ℝ) ∧
    Real.log (epsilonReal 2048) + Real.log (epsilonConjReal 2048) = 0) ∧
    deriv (ZMod.LFunction qchar) 0
      = ((((hField : ℕ) : ℝ) * Real.log (epsilonReal 2048) : ℝ) : ℂ) :=
  Imscribing.Millennium.StarkDualLimit.stark_ladder_closed cnf_of_class_number_formula

end Imscribing.Millennium.StarkClassNumberField
