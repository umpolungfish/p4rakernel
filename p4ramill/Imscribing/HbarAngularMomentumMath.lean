-- ħ Angular Momentum — exact matrix computation in Lean 4.
-- Spin-1/2 representation with physical ħ.
-- Verified: J² = (3/4)ħ²I, [Ja, Jb] = iħ ε_{abc} Jc, Jz = diag(±ħ/2).

import Mathlib

open Matrix

section HbarAngularMomentumMath

-- Pauli matrices (dimensionless)
def σx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def σy : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def σz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

-- Pauli matrix identities
theorem σx_sq : σx * σx = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σx, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem σy_sq : σy * σy = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σy, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;>
    ring_nf <;>
    simp [Complex.I_sq]

theorem σz_sq : σz * σz = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σz, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem σx_σy : σx * σy = Complex.I • σz := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σx, σy, σz, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply]

theorem σy_σx : σy * σx = -(Complex.I • σz) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σx, σy, σz, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply]

theorem σy_σz : σy * σz = Complex.I • σx := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σx, σy, σz, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply]

theorem σz_σy : σz * σy = -(Complex.I • σx) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σx, σy, σz, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply]

theorem σz_σx : σz * σx = Complex.I • σy := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σx, σy, σz, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply] <;>
    ring_nf <;>
    simp [Complex.I_sq]

theorem σx_σz : σx * σz = -(Complex.I • σy) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σx, σy, σz, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply] <;>
    ring_nf <;>
    simp [Complex.I_sq]

-- Angular momentum operators: J = (ħ/2) σ
noncomputable def Jx (ħ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := ((ħ / 2 : ℝ) : ℂ) • σx
noncomputable def Jy (ħ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := ((ħ / 2 : ℝ) : ℂ) • σy
noncomputable def Jz (ħ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := ((ħ / 2 : ℝ) : ℂ) • σz

-- Operator form: J² = Jx² + Jy² + Jz² = (3/4)ħ² I
theorem J2_half_op (ħ : ℝ) :
    Jx ħ * Jx ħ + Jy ħ * Jy ħ + Jz ħ * Jz ħ =
      ((3 / 4 : ℂ) * (ħ : ℂ) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp only [Jx, Jy, Jz, Matrix.smul_mul, Matrix.mul_smul, smul_smul, σx_sq, σy_sq, σz_sq]
  rw [← add_smul, ← add_smul]
  congr 1
  push_cast
  ring

-- Operator form: [Ja, Jb] = iħ Jc
theorem comm_half_op (ħ : ℝ) :
    Jx ħ * Jy ħ - Jy ħ * Jx ħ = (Complex.I * (ħ : ℂ)) • Jz ħ := by
  simp only [Jx, Jy, Jz, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    σx_σy, σy_σx, smul_neg, sub_neg_eq_add]
  rw [← add_smul]
  congr 1
  push_cast
  ring

theorem comm_yz_op (ħ : ℝ) :
    Jy ħ * Jz ħ - Jz ħ * Jy ħ = (Complex.I * (ħ : ℂ)) • Jx ħ := by
  simp only [Jx, Jy, Jz, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    σy_σz, σz_σy, smul_neg, sub_neg_eq_add]
  rw [← add_smul]
  congr 1
  push_cast
  ring

theorem comm_zx_op (ħ : ℝ) :
    Jz ħ * Jx ħ - Jx ħ * Jz ħ = (Complex.I * (ħ : ℂ)) • Jy ħ := by
  simp only [Jx, Jy, Jz, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    σz_σx, σx_σz, smul_neg, sub_neg_eq_add]
  rw [← add_smul]
  congr 1
  push_cast
  ring

-- Explicit matrix forms (compatible with original signatures)
theorem J2_half (ħ : ℝ) : Jx ħ * Jx ħ + Jy ħ * Jy ħ + Jz ħ * Jz ħ =
    !![(3 / 4 * (ħ : ℂ) * (ħ : ℂ) : ℂ), (0 : ℂ);
       (0 : ℂ), (3 / 4 * (ħ : ℂ) * (ħ : ℂ) : ℂ)] := by
  rw [J2_half_op]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.one_apply] <;>
    ring

theorem comm_half (ħ : ℝ) : Jx ħ * Jy ħ - Jy ħ * Jx ħ =
    !![(Complex.I * (ħ : ℂ) * (ħ : ℂ) / 2 : ℂ), (0 : ℂ);
       (0 : ℂ), (-Complex.I * (ħ : ℂ) * (ħ : ℂ) / 2 : ℂ)] := by
  rw [comm_half_op]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jz, σz, Matrix.smul_apply] <;>
    push_cast <;>
    ring

theorem Jz_form (ħ : ℝ) : Jz ħ = !![(ħ / 2 : ℂ), 0; 0, (-ħ / 2 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jz, σz, Matrix.smul_apply] <;>
    push_cast <;>
    ring

-- Eigenvalue and eigenvector verification
theorem Jz_eigen_up (ħ : ℝ) :
    Matrix.mulVec (Jz ħ) ![1, 0] = ((ħ / 2 : ℝ) : ℂ) • ![1, 0] := by
  ext i
  fin_cases i <;>
    simp [Jz, σz, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem Jz_eigen_down (ħ : ℝ) :
    Matrix.mulVec (Jz ħ) ![0, 1] = ((-ħ / 2 : ℝ) : ℂ) • ![0, 1] := by
  ext i
  fin_cases i <;>
    simp [Jz, σz, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    push_cast <;>
    ring

theorem J2_eigen (ħ : ℝ) (v : Fin 2 → ℂ) :
    Matrix.mulVec (Jx ħ * Jx ħ + Jy ħ * Jy ħ + Jz ħ * Jz ħ) v =
      ((3 / 4 : ℂ) * (ħ : ℂ) ^ 2) • v := by
  rw [J2_half_op, Matrix.smul_mulVec, Matrix.one_mulVec]

-- J² eigenvalue coefficient for spin-1/2: j(j+1) = 3/4
theorem j2_eigenvalue_half : (3 / 4 : ℝ) = (1 / 2 : ℝ) * ((1 / 2 : ℝ) + 1) := by norm_num

end HbarAngularMomentumMath