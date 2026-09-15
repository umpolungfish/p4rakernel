import Mathlib

open Real

abbrev TangentVector := ℝ × ℝ

noncomputable def rotate (θ : ℝ) (v : TangentVector) : TangentVector :=
  (v.1 * cos θ - v.2 * sin θ, v.1 * sin θ + v.2 * cos θ)

theorem rotate_add (θ₁ θ₂ : ℝ) (v : TangentVector) :
    rotate (θ₁ + θ₂) v = rotate θ₂ (rotate θ₁ v) := by
  apply Prod.ext
  · simp [rotate, cos_add, sin_add]; ring
  · simp [rotate, cos_add, sin_add]; ring
