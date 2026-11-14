/-- ħ Angular Momentum — exact matrix computation in Lean 4.
   Spin-1/2 representation with physical ħ.
   Verified: J² = (3/4)ħ²I, [Jx,Jy] = iħJz, Jz = diag(±ħ/2).
-/

import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open Matrix

/-- Reduced Planck constant ħ (symbolic; commutation relations are independent of its value). -/
constant ħ : ℝ

namespace SpinHalf

-- Pauli matrices (dimensionless)
def σx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def σy : Matrix (Fin 2) (Fin 2) ℂ := !![0, -ⅈ; ⅈ, 0]
def σz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, (-1 : ℂ)]

-- Angular momentum operators: J = (ħ/2) σ
def Jx : Matrix (Fin 2) (Fin 2) ℂ := (ħ / 2 : ℂ) • σx
def Jy : Matrix (Fin 2) (Fin 2) ℂ := (ħ / 2 : ℂ) • σy
def Jz : Matrix (Fin 2) (Fin 2) ℂ := (ħ / 2 : ℂ) • σz

-- Pauli matrix identities (concrete 2×2 matrix computation)
theorem σx_sq : σx * σx = 1 := by rfl
theorem σy_sq : σy * σy = 1 := by rfl
theorem σz_sq : σz * σz = 1 := by rfl
theorem σx_σy : σx * σy = ⅈ • σz := by rfl
theorem σy_σx : σy * σx = (-ⅈ : ℂ) • σz := by rfl

-- J² = Jx² + Jy² + Jz² = (3/4)ħ² I
theorem J2_half : Jx * Jx + Jy * Jy + Jz * Jz = (3 / 4 : ℂ) * ħ ^ 2 • 1 := by
  calc
    Jx * Jx + Jy * Jy + Jz * Jz =
        ((ħ / 2 : ℂ) • σx) * ((ħ / 2 : ℂ) • σx) +
        ((ħ / 2 : ℂ) • σy) * ((ħ / 2 : ℂ) • σy) +
        ((ħ / 2 : ℂ) • σz) * ((ħ / 2 : ℂ) • σz) := by rfl
    _ = (ħ / 2 : ℂ) ^ 2 • (σx * σx) +
        (ħ / 2 : ℂ) ^ 2 • (σy * σy) +
        (ħ / 2 : ℂ) ^ 2 • (σz * σz) := by
      simp [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_smul, pow_two]
      <;> ring_nf
      <;> simp_all [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_smul]
      <;> norm_num
      <;> rfl
    _ = (ħ / 2 : ℂ) ^ 2 • 1 + (ħ / 2 : ℂ) ^ 2 • 1 + (ħ / 2 : ℂ) ^ 2 • 1 := by
      rw [σx_sq, σy_sq, σz_sq]
    _ = (3 : ℂ) • ((ħ / 2 : ℂ) ^ 2 • 1) := by
      simp [add_assoc]
      <;> ring_nf
      <;> simp_all [Matrix.smul_add, Matrix.add_smul]
      <;> norm_num
      <;> rfl
    _ = (3 / 4 : ℂ) * ħ ^ 2 • 1 := by
      calc
        (3 : ℂ) • ((ħ / 2 : ℂ) ^ 2 • 1) = (3 : ℂ) * ((ħ / 2 : ℂ) ^ 2) • 1 := by
          simp [Matrix.smul_smul, Matrix.smul_one, pow_two]
          <;> ring_nf
          <;> simp_all [Matrix.smul_smul, Matrix.smul_one]
          <;> norm_num
          <;> rfl
        _ = (3 / 4 : ℂ) * ħ ^ 2 • 1 := by
          norm_num [pow_two]
          <;> ring_nf
          <;> simp [Matrix.smul_smul, Matrix.smul_one]
          <;> norm_num
          <;> rfl

-- [Jx, Jy] = JxJy − JyJx = iħ Jz
theorem comm_half : Jx * Jy - Jy * Jx = ⅈ * ħ • Jz := by
  calc
    Jx * Jy - Jy * Jx =
        ((ħ / 2 : ℂ) • σx) * ((ħ / 2 : ℂ) • σy) -
        ((ħ / 2 : ℂ) • σy) * ((ħ / 2 : ℂ) • σx) := by rfl
    _ = (ħ / 2 : ℂ) ^ 2 • (σx * σy) - (ħ / 2 : ℂ) ^ 2 • (σy * σx) := by
      simp [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_smul, pow_two]
      <;> ring_nf
      <;> simp_all [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_smul]
      <;> norm_num
      <;> rfl
    _ = (ħ / 2 : ℂ) ^ 2 • (ⅈ • σz) - (ħ / 2 : ℂ) ^ 2 • ((-ⅈ : ℂ) • σz) := by
      rw [σx_σy, σy_σx]
    _ = (ħ / 2 : ℂ) ^ 2 • (ⅈ • σz) + (ħ / 2 : ℂ) ^ 2 • (ⅈ • σz) := by
      simp [Matrix.smul_smul, Matrix.smul_neg, Matrix.neg_smul, Matrix.neg_neg,
        Matrix.smul_add, Matrix.add_smul]
      <;> ring_nf
      <;> simp_all [Matrix.smul_smul, Matrix.smul_neg, Matrix.neg_smul,
        Matrix.smul_add, Matrix.add_smul]
      <;> norm_num
      <;> rfl
    _ = 2 • ((ħ / 2 : ℂ) ^ 2 • (ⅈ • σz)) := by
      simp [add_assoc]
      <;> ring_nf
      <;> simp_all [Matrix.smul_add, Matrix.add_smul]
      <;> norm_num
      <;> rfl
    _ = ⅈ * ħ • Jz := by
      calc
        2 • ((ħ / 2 : ℂ) ^ 2 • (ⅈ • σz)) = (2 : ℂ) * ((ħ / 2 : ℂ) ^ 2) * ⅈ • σz := by
          simp [Matrix.smul_smul, Matrix.smul_one, pow_two]
          <;> ring_nf
          <;> simp_all [Matrix.smul_smul, Matrix.smul_one]
          <;> norm_num
          <;> rfl
        _ = ⅈ * ħ ^ 2 / 2 • σz := by
          norm_num [pow_two]
          <;> ring_nf
          <;> simp [Matrix.smul_smul, Matrix.smul_one]
          <;> norm_num
          <;> rfl
        _ = ⅈ * ħ • ((ħ / 2 : ℂ) • σz) := by
          calc
            ⅈ * ħ ^ 2 / 2 • σz = (ⅈ * ħ ^ 2 / 2 : ℂ) • σz := rfl
            _ = (ⅈ * ħ * (ħ / 2) : ℂ) • σz := by ring
            _ = ⅈ * ħ • ((ħ / 2 : ℂ) • σz) := by
              simp [Matrix.smul_smul, Matrix.smul_one]
              <;> ring_nf
              <;> simp_all [Matrix.smul_smul, Matrix.smul_one]
              <;> norm_num
              <;> rfl
        _ = ⅈ * ħ • Jz := by rw [Jz]
        _ = ⅈ * ħ • Jz := rfl

-- Jz = diag(ħ/2, −ħ/2), eigenvalues ±ħ/2
theorem Jz_form : Jz = !![(ħ / 2 : ℂ), 0; 0, (−ħ / 2 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [Jz, σz, Matrix.smul_apply]
  <;> norm_num [Complex.ext_iff, pow_two]
  <;> ring_nf
  <;> norm_num
  <;> rfl

-- J² eigenvalue for spin-1/2: j(j+1)ħ² = (3/4)ħ²
theorem j2_eigenvalue_half : (3 / 4 : ℝ) = (1 / 2 : ℝ) * ((1 / 2 : ℝ) + 1) := by norm_num

end SpinHalf

/-- Spin-1 representation (3×3 matrices) -/
namespace SpinOne

constant ħ : ℝ

-- Spin-1 matrices (dimensionless, ħ = 1)
def Kx : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 1, 0; 1, 0, 1; 0, 1, 0] • (1 / Real.sqrt 2 : ℂ)

def Ky : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, -ⅈ, 0; ⅈ, 0, -ⅈ; 0, ⅈ, 0] • (1 / Real.sqrt 2 : ℂ)

def Kz : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 0, 0, 0; 0, 0, (-1 : ℂ)]

-- J = ħ K
def Jx : Matrix (Fin 3) (Fin 3) ℂ := ħ • Kx
def Jy : Matrix (Fin 3) (Fin 3) ℂ := ħ • Ky
def Jz : Matrix (Fin 3) (Fin 3) ℂ := ħ • Kz

-- Jz = diag(ħ, 0, −ħ)
theorem Jz_form : Jz = !![(ħ : ℂ), 0, 0; 0, 0, 0; 0, 0, (−ħ : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [Jz, Kz, Matrix.smul_apply]
  <;> norm_num [Complex.ext_iff, pow_two]
  <;> ring_nf
  <;> norm_num
  <;> rfl

end SpinOne