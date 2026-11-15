-- ħ Angular Momentum — exact matrix computation in Lean 4.
-- Spin-1/2 representation with physical ħ.
-- Verified: J² = (3/4)ħ²I, [Jx,Jy] = iħJz, Jz = diag(±ħ/2).

import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open Matrix

section HbarAngularMomentumMath

variable (ħ : ℝ)

-- Pauli matrices (dimensionless)
def σx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def σy : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def σz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, (-1 : ℂ)]

-- Angular momentum operators: J = (ħ/2) σ — direct matrix entries
noncomputable def Jx (ħ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), (ħ / 2 : ℂ); (ħ / 2 : ℂ), (0 : ℂ)]
noncomputable def Jy (ħ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), (-Complex.I * (ħ / 2 : ℂ)); (Complex.I * (ħ / 2 : ℂ)), (0 : ℂ)]
noncomputable def Jz (ħ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(ħ / 2 : ℂ), (0 : ℂ); (0 : ℂ), (-ħ / 2 : ℂ)]

-- Pauli matrix identities (concrete 2×2 matrix computation)
theorem σx_sq : σx * σx = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
  simp [σx, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
    Complex.ext_iff, pow_two]
  <;> norm_num [Complex.ext_iff, Complex.I]
  <;> ring_nf at *
  <;> norm_num at *
  <;>
  (try { simp_all [Complex.ext_iff] })
  <;>
  (try { norm_num })
  <;>
  (try { rfl })
  <;>
  (try { linarith })

theorem σy_sq : σy * σy = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
  simp [σy, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
    Complex.ext_iff, pow_two]
  <;> norm_num [Complex.ext_iff, Complex.I]
  <;> ring_nf at *
  <;> norm_num at *
  <;>
  (try { simp_all [Complex.ext_iff] })
  <;>
  (try { norm_num })
  <;>
  (try { rfl })
  <;>
  (try { linarith })

theorem σz_sq : σz * σz = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
  simp [σz, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
    Complex.ext_iff, pow_two]
  <;> norm_num [Complex.ext_iff, Complex.I]
  <;> ring_nf at *
  <;> norm_num at *
  <;>
  (try { simp_all [Complex.ext_iff] })
  <;>
  (try { norm_num })
  <;>
  (try { rfl })
  <;>
  (try { linarith })

theorem σx_σy : σx * σy = Complex.I • σz := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
  simp [σx, σy, σz, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
    Complex.ext_iff, pow_two, Matrix.smul_apply]
  <;> norm_num [Complex.ext_iff, Complex.I]
  <;> ring_nf at *
  <;> norm_num at *
  <;>
  (try { simp_all [Complex.ext_iff] })
  <;>
  (try { norm_num })
  <;>
  (try { rfl })
  <;>
  (try { linarith })

theorem σy_σx : σy * σx = -(Complex.I • σz) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
  simp [σx, σy, σz, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
    Complex.ext_iff, pow_two, Matrix.smul_apply]
  <;> norm_num [Complex.ext_iff, Complex.I]
  <;> ring_nf at *
  <;> norm_num at *
  <;>
  (try { simp_all [Complex.ext_iff] })
  <;>
  (try { norm_num })
  <;>
  (try { rfl })
  <;>
  (try { linarith })

-- J² = Jx² + Jy² + Jz² = (3/4)ħ² I  (entry-wise verification)
theorem J2_half (ħ : ℝ) : Jx ħ * Jx ħ + Jy ħ * Jy ħ + Jz ħ * Jz ħ =
    !![(3 / 4 * (ħ : ℂ) * (ħ : ℂ) : ℂ), (0 : ℂ); (0 : ℂ), (3 / 4 * (ħ : ℂ) * (ħ : ℂ) : ℂ)] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
  simp [Jx, Jy, Jz, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_succ, Matrix.one_apply,
    Complex.ext_iff, pow_two]
  <;> norm_num [Complex.ext_iff, Complex.I]
  <;> ring_nf at *
  <;> norm_num at *
  <;>
  (try { simp_all [Complex.ext_iff] })
  <;>
  (try { norm_num })
  <;>
  (try { rfl })
  <;>
  (try { linarith })

-- [Jx, Jy] = JxJy − JyJx = iħ Jz  (entry-wise verification)
theorem comm_half (ħ : ℝ) : Jx ħ * Jy ħ - Jy ħ * Jx ħ =
    !![(Complex.I * (ħ : ℂ) * (ħ : ℂ) / 2 : ℂ), (0 : ℂ); (0 : ℂ), (-Complex.I * (ħ : ℂ) * (ħ : ℂ) / 2 : ℂ)] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
  simp [Jx, Jy, Jz, Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_succ, Matrix.one_apply,
    Complex.ext_iff, pow_two]
  <;> norm_num [Complex.ext_iff, Complex.I]
  <;> ring_nf at *
  <;> norm_num at *
  <;>
  (try { simp_all [Complex.ext_iff] })
  <;>
  (try { norm_num })
  <;>
  (try { rfl })
  <;>
  (try { linarith })

-- Jz = diag(ħ/2, -ħ/2), eigenvalues ±ħ/2
theorem Jz_form (ħ : ℝ) : Jz ħ = !![(ħ / 2 : ℂ), 0; 0, (-ħ / 2 : ℂ)] := by rfl

-- J² eigenvalue for spin-1/2: j(j+1)ħ² = (3/4)ħ²
theorem j2_eigenvalue_half : (3 / 4 : ℝ) = (1 / 2 : ℝ) * ((1 / 2 : ℝ) + 1) := by norm_num

end HbarAngularMomentumMath
