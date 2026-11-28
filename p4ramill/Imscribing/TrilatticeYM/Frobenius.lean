import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Imscribing.TrilatticeYM

open scoped TensorProduct

/-- Coordinate-free Frobenius algebra `(A, m, η, Δ, ε)` over a commutative ring `R`. -/
structure FrobeniusAlg (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A] where
  mul : A ⊗[R] A →ₗ[R] A
  unit : R →ₗ[R] A
  comul : A →ₗ[R] A ⊗[R] A
  counit : A →ₗ[R] R
  unit_left : mul ∘ₗ LinearMap.rTensor A unit = (TensorProduct.lid R A).toLinearMap
  unit_right : mul ∘ₗ LinearMap.lTensor A unit = (TensorProduct.rid R A).toLinearMap
  counit_left : LinearMap.rTensor A counit ∘ₗ comul = (TensorProduct.lid R A).symm.toLinearMap
  counit_right : LinearMap.lTensor A counit ∘ₗ comul = (TensorProduct.rid R A).symm.toLinearMap
  frobenius_left :
    LinearMap.rTensor A mul ∘ₗ (TensorProduct.assoc R A A A).symm.toLinearMap ∘ₗ
      LinearMap.lTensor A comul = comul ∘ₗ mul
  frobenius_right :
    LinearMap.lTensor A mul ∘ₗ (TensorProduct.assoc R A A A).toLinearMap ∘ₗ
      LinearMap.rTensor A comul = comul ∘ₗ mul

namespace FrobeniusAlg

variable {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A] (F : FrobeniusAlg R A)

def cup : R →ₗ[R] A ⊗[R] A := F.comul ∘ₗ F.unit
def cap : A ⊗[R] A →ₗ[R] R := F.counit ∘ₗ F.mul

/-- Left snake equation (§123.2). -/
theorem snake_left :
    LinearMap.lTensor A F.cap ∘ₗ (TensorProduct.assoc R A A A).toLinearMap ∘ₗ
      LinearMap.rTensor A F.cup
    = (TensorProduct.rid R A).symm.toLinearMap ∘ₗ (TensorProduct.lid R A).toLinearMap := by
  unfold cup cap
  rw [LinearMap.lTensor_comp, LinearMap.rTensor_comp]
  calc (LinearMap.lTensor A F.counit ∘ₗ LinearMap.lTensor A F.mul) ∘ₗ
        (TensorProduct.assoc R A A A).toLinearMap ∘ₗ
        (LinearMap.rTensor A F.comul ∘ₗ LinearMap.rTensor A F.unit)
      = LinearMap.lTensor A F.counit ∘ₗ
          (LinearMap.lTensor A F.mul ∘ₗ (TensorProduct.assoc R A A A).toLinearMap ∘ₗ
            LinearMap.rTensor A F.comul) ∘ₗ
          LinearMap.rTensor A F.unit := by simp only [LinearMap.comp_assoc]
    _ = LinearMap.lTensor A F.counit ∘ₗ (F.comul ∘ₗ F.mul) ∘ₗ LinearMap.rTensor A F.unit := by
          rw [F.frobenius_right]
    _ = (LinearMap.lTensor A F.counit ∘ₗ F.comul) ∘ₗ (F.mul ∘ₗ LinearMap.rTensor A F.unit) := by
          simp only [LinearMap.comp_assoc]
    _ = (TensorProduct.rid R A).symm.toLinearMap ∘ₗ (TensorProduct.lid R A).toLinearMap := by
          rw [F.counit_right, F.unit_left]

/-- Right snake equation (§123.2). -/
theorem snake_right :
    LinearMap.rTensor A F.cap ∘ₗ (TensorProduct.assoc R A A A).symm.toLinearMap ∘ₗ
      LinearMap.lTensor A F.cup
    = (TensorProduct.lid R A).symm.toLinearMap ∘ₗ (TensorProduct.rid R A).toLinearMap := by
  unfold cup cap
  rw [LinearMap.lTensor_comp, LinearMap.rTensor_comp]
  calc (LinearMap.rTensor A F.counit ∘ₗ LinearMap.rTensor A F.mul) ∘ₗ
        (TensorProduct.assoc R A A A).symm.toLinearMap ∘ₗ
        (LinearMap.lTensor A F.comul ∘ₗ LinearMap.lTensor A F.unit)
      = LinearMap.rTensor A F.counit ∘ₗ
          (LinearMap.rTensor A F.mul ∘ₗ (TensorProduct.assoc R A A A).symm.toLinearMap ∘ₗ
            LinearMap.lTensor A F.comul) ∘ₗ
          LinearMap.lTensor A F.unit := by simp only [LinearMap.comp_assoc]
    _ = LinearMap.rTensor A F.counit ∘ₗ (F.comul ∘ₗ F.mul) ∘ₗ LinearMap.lTensor A F.unit := by
          rw [F.frobenius_left]
    _ = (LinearMap.rTensor A F.counit ∘ₗ F.comul) ∘ₗ (F.mul ∘ₗ LinearMap.lTensor A F.unit) := by
          simp only [LinearMap.comp_assoc]
    _ = (TensorProduct.lid R A).symm.toLinearMap ∘ₗ (TensorProduct.rid R A).toLinearMap := by
          rw [F.counit_left, F.unit_right]

end FrobeniusAlg

/-- Coordinate pairing matrix `g_{ij} = (2/3)δ_{ij} + 1/3` for the four SIC projectors (§191, §325). -/
def gSIC : Matrix (Fin 4) (Fin 4) ℚ :=
  fun i j => if i = j then 1 else (1 : ℚ) / 3

/-- Exact inverse pairing `g^{ij} = (3/2)δ_{ij} - 1/4` (§191, §325). -/
def gSICInv : Matrix (Fin 4) (Fin 4) ℚ :=
  fun i j => if i = j then (5 : ℚ) / 4 else -(1 : ℚ) / 4

theorem gSIC_mul_inv : gSIC * gSICInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, gSIC, gSICInv] <;> norm_num

theorem gSIC_inv_mul : gSICInv * gSIC = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, gSIC, gSICInv] <;> norm_num

end TrilatticeYM