import Mathlib
namespace Imscribing.Millennium.UgandaSeed
noncomputable section

def ugandaPsi : Fin 2 → ℂ := fun k =>
  if k = 0 then (1 / Real.sqrt 2 : ℂ) else
    Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ)

lemma exp_normSq (x : ℝ) : Complex.normSq (Complex.exp ((x : ℂ) * Complex.I)) = 1 := by
  rw [Complex.normSq_apply]
  rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  nlinarith [Real.sin_sq_add_cos_sq x]

lemma uganda_norm_sq0 : Complex.normSq (ugandaPsi 0) = 1/2 := by
  simp [ugandaPsi, Complex.normSq_ofReal]

lemma uganda_norm_sq1 : Complex.normSq (ugandaPsi 1) = 1/2 := by
  rw [ugandaPsi]
  norm_num
  convert exp_normSq (2 * Real.pi / 3) using 1
  push_cast
  ring

/-- The Uganda seed carries unit norm: the two squared moduli sum to 1. -/
theorem uganda_unit_norm : Complex.normSq (ugandaPsi 0) + Complex.normSq (ugandaPsi 1) = 1 := by
  rw [uganda_norm_sq0, uganda_norm_sq1]
  norm_num

