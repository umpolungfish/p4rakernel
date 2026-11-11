import Imscribing.Paraconsistent.Monism

namespace Imscribing.Paraconsistent.SpindleGeometry

open Imscribing.Paraconsistent.Monism

/-!
# Spindle Geometry
Embedding, induced metric, determinant, Christoffel symbols,
Gaussian curvature, and throat degeneracy.

Major radius R, minor radius 1.
Coordinates: poloidal φ, toroidal θ.
-/

/-! ## 1. Embedding -/

abbrev Vec3 := ℝ × ℝ × ℝ

noncomputable def profile (R φ : ℝ) : ℝ :=
  spindleA R φ

noncomputable def embedding
    (R φ θ : ℝ) : Vec3 :=
  let A := profile R φ
  let u := 2 * Real.pi * θ
  let v := 2 * Real.pi * φ
  (A * Real.cos u,
   A * Real.sin u,
   Real.sin v)

/-! ## 2. Coordinate Tangent Vectors -/

/-- Poloidal coordinate tangent vector. -/
noncomputable def tangentPhi
    (R φ θ : ℝ) : Vec3 :=
  let u := 2 * Real.pi * θ
  let v := 2 * Real.pi * φ
  (-(2 * Real.pi) * Real.sin v * Real.cos u,
   -(2 * Real.pi) * Real.sin v * Real.sin u,
    (2 * Real.pi) * Real.cos v)

/-- Toroidal coordinate tangent vector. -/
noncomputable def tangentTheta
    (R φ θ : ℝ) : Vec3 :=
  let A := profile R φ
  let u := 2 * Real.pi * θ
  (-(2 * Real.pi) * A * Real.sin u,
    (2 * Real.pi) * A * Real.cos u,
    0)

/-- Euclidean inner product in R³. -/
def dot3 (u v : Vec3) : ℝ :=
  u.1 * v.1 +
  u.2.1 * v.2.1 +
  u.2.2 * v.2.2

/-! ## 3. Induced Metric Components -/

noncomputable def gPhiPhi
    (R φ θ : ℝ) : ℝ :=
  dot3 (tangentPhi R φ θ)
       (tangentPhi R φ θ)

noncomputable def gPhiTheta
    (R φ θ : ℝ) : ℝ :=
  dot3 (tangentPhi R φ θ)
       (tangentTheta R φ θ)

noncomputable def gThetaTheta
    (R φ θ : ℝ) : ℝ :=
  dot3 (tangentTheta R φ θ)
       (tangentTheta R φ θ)

/-- The poloidal metric component is constant. -/
theorem gPhiPhi_formula
    (R φ θ : ℝ) :
    gPhiPhi R φ θ = 4 * Real.pi ^ 2 := by
  have hu :
      Real.cos (2 * Real.pi * θ) ^ 2 +
      Real.sin (2 * Real.pi * θ) ^ 2 = 1 := by
    nlinarith [
      Real.sin_sq_add_cos_sq (2 * Real.pi * θ)
    ]
  have hv :
      Real.sin (2 * Real.pi * φ) ^ 2 +
      Real.cos (2 * Real.pi * φ) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (2 * Real.pi * φ)

  simp only [gPhiPhi, dot3, tangentPhi]
  calc
    _ =
      (2 * Real.pi) ^ 2 *
        (Real.sin (2 * Real.pi * φ) ^ 2 *
          (Real.cos (2 * Real.pi * θ) ^ 2 +
           Real.sin (2 * Real.pi * θ) ^ 2) +
         Real.cos (2 * Real.pi * φ) ^ 2) := by
          ring
    _ = 4 * Real.pi ^ 2 := by
          simp [hu, hv]
          ring

/-- The induced metric has zero mixed component. -/
theorem gPhiTheta_formula
    (R φ θ : ℝ) :
    gPhiTheta R φ θ = 0 := by
  simp only [gPhiTheta, dot3, tangentPhi, tangentTheta]
  ring

/-- The toroidal metric component. -/
theorem gThetaTheta_formula
    (R φ θ : ℝ) :
    gThetaTheta R φ θ =
      4 * Real.pi ^ 2 * (profile R φ) ^ 2 := by
  simp only [gThetaTheta, dot3, tangentTheta]
  calc
    _ =
      (2 * Real.pi * profile R φ) ^ 2 *
        (Real.sin (2 * Real.pi * θ) ^ 2 +
         Real.cos (2 * Real.pi * θ) ^ 2) := by
          ring
    _ = 4 * Real.pi ^ 2 * (profile R φ) ^ 2 := by
          rw [Real.sin_sq_add_cos_sq]
          ring

/-! ## 4. Metric Tensor and Determinant -/

/-- Induced metric in coordinate order (φ, θ). -/
noncomputable def metricMatrix
    (R φ θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![gPhiPhi R φ θ, gPhiTheta R φ θ;
     gPhiTheta R φ θ, gThetaTheta R φ θ]

/-- Determinant of the induced metric. -/
noncomputable def metricDet
    (R φ θ : ℝ) : ℝ :=
  gPhiPhi R φ θ * gThetaTheta R φ θ -
    (gPhiTheta R φ θ) ^ 2

/-- Exact determinant formula. -/
theorem metricDet_formula
    (R φ θ : ℝ) :
    metricDet R φ θ =
      16 * Real.pi ^ 4 * (profile R φ) ^ 2 := by
  rw [metricDet, gPhiPhi_formula,
      gPhiTheta_formula, gThetaTheta_formula]
  ring

/-- The toroidal metric vanishes precisely at the throat. -/
theorem gThetaTheta_zero_iff
    (R φ θ : ℝ) :
    gThetaTheta R φ θ = 0 ↔
      profile R φ = 0 := by
  rw [gThetaTheta_formula]
  constructor
  · intro h

    have hc :
        (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by
      positivity

    have hs :
        (profile R φ) ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_left hc

    have hm :
        profile R φ * profile R φ = 0 := by
      simpa [pow_two] using hs

    rcases mul_eq_zero.mp hm with h | h
    · exact h
    · exact h

  · intro h
    rw [h]
    ring

/-- The full determinant vanishes when the profile vanishes. -/
theorem metricDet_zero_of_profile_zero
    (R φ θ : ℝ)
    (h : profile R φ = 0) :
    metricDet R φ θ = 0 := by
  rw [metricDet_formula, h]
  ring

/-! ## 5. Metric Derivative -/

/-- Poloidal derivative of the toroidal metric component. -/
noncomputable def dPhiGThetaTheta
    (R φ : ℝ) : ℝ :=
  -16 * Real.pi ^ 3 *
    profile R φ *
    Real.sin (2 * Real.pi * φ)

/-! ## 6. Christoffel Symbols -/

/-- Γᵠₜₜ: poloidal acceleration from toroidal velocity. -/
noncomputable def christoffelPhiThetaTheta
    (R φ : ℝ) : ℝ :=
  2 * Real.pi *
    profile R φ *
    Real.sin (2 * Real.pi * φ)

/-- Γᵗᵠₜ = Γᵗₜᵠ: toroidal Coriolis deflection. -/
noncomputable def christoffelThetaPhiTheta
    (R φ : ℝ) : ℝ :=
  -2 * Real.pi *
    Real.sin (2 * Real.pi * φ) /
    profile R φ

/-- First Christoffel identity. -/
theorem christoffel_phi_identity
    (R φ : ℝ) :
    christoffelPhiThetaTheta R φ *
      (2 * (4 * Real.pi ^ 2)) =
      -dPhiGThetaTheta R φ := by
  simp [christoffelPhiThetaTheta,
        dPhiGThetaTheta]
  ring

/-- Second Christoffel identity on the regular locus. -/
theorem christoffel_theta_identity
    (R φ : ℝ)
    (hA : profile R φ ≠ 0) :
    (2 * (4 * Real.pi ^ 2 *
      (profile R φ) ^ 2)) *
        christoffelThetaPhiTheta R φ =
      dPhiGThetaTheta R φ := by
  simp only [christoffelThetaPhiTheta,
    dPhiGThetaTheta]
  field_simp
  <;> ring

/-! ## 7. Gaussian Curvature -/

/-- Gaussian curvature on the regular spindle surface. -/
noncomputable def gaussianCurvature
    (R φ : ℝ) : ℝ :=
  Real.cos (2 * Real.pi * φ) /
    profile R φ

/-- Curvature-profile identity. -/
theorem gaussianCurvature_profile_identity
    (R φ : ℝ)
    (hA : profile R φ ≠ 0) :
    gaussianCurvature R φ *
      profile R φ =
      Real.cos (2 * Real.pi * φ) := by
  unfold gaussianCurvature
  field_simp

/-- Positive curvature on the positive-profile,
positive-cosine region. -/
theorem gaussianCurvature_pos
    (R φ : ℝ)
    (hcos : 0 < Real.cos (2 * Real.pi * φ))
    (hA : 0 < profile R φ) :
    0 < gaussianCurvature R φ := by
  unfold gaussianCurvature
  positivity

/-- Negative curvature on the positive-profile,
negative-cosine region. -/
theorem gaussianCurvature_neg
    (R φ : ℝ)
    (hcos : Real.cos (2 * Real.pi * φ) < 0)
    (hA : 0 < profile R φ) :
    gaussianCurvature R φ < 0 := by
  unfold gaussianCurvature
  exact div_neg_of_neg_of_pos hcos hA

/-! ## 8. Regular Locus -/

/-- Regular coordinate domain. -/
def regularLocus
    (R φ : ℝ) : Prop :=
  profile R φ ≠ 0

/-- The determinant is strictly positive on the regular locus. -/
theorem metricDet_pos_on_regular_locus
    (R φ θ : ℝ)
    (h : regularLocus R φ) :
    0 < metricDet R φ θ := by
  rw [metricDet_formula]
  unfold regularLocus at h
  positivity

/-! ## 9. Throat Degeneracy -/

/-- The spindle throat forces degeneration of the induced metric. -/
theorem throat_metric_degeneracy
    (R φ θ : ℝ)
    (h : profile R φ = 0) :
    gThetaTheta R φ θ = 0 ∧
    metricDet R φ θ = 0 := by
  constructor
  · rw [gThetaTheta_formula, h]
    ring
  · exact metricDet_zero_of_profile_zero R φ θ h

end Imscribing.Paraconsistent.SpindleGeometry

