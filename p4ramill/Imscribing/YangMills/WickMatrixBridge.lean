import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Imscribing.YangMills.WickRotationAndForwardTube

/-!
# Euclidean SO(4) ↔ Complex Lorentz SO(1,3;ℂ) Wick-Rotation Bridge

1. Complexified Minkowski form `minkowskiComplexInner` and Wick matrix `W = diag(i, 1, 1, 1)`.
2. `wick_inner_eq_neg_euclid`: η_ℂ(W x, W y) = -⟨x, y⟩_{ℝ⁴}.
3. `wick_rot_preserves_minkowski` & `wick_rot_det_one`: every real R ∈ SO(4) conjugates
   via W R W⁻¹ into an element of SO(1, 3; ℂ) intertwining `wickMap`.
4. `wick_rot01_eq_boost01`: analytic continuation θ ↦ η i turns a Euclidean (0,1)-rotation
   into the exact Minkowski Lorentz boost.
-/

namespace Imscribing.YangMills.WickMatrixBridge

open Imscribing.YangMills.ClaySpec
open Imscribing.YangMills.WickTube

/-- Complexified Minkowski bilinear form η_ℂ(z, w) = z₀ w₀ - z₁ w₁ - z₂ w₂ - z₃ w₃. -/
def minkowskiComplexInner (z w : Fin 4 → ℂ) : ℂ :=
  z 0 * w 0 - (z 1 * w 1 + z 2 * w 2 + z 3 * w 3)

/-- Diagonal Wick rotation matrix W = diag(i, 1, 1, 1). -/
def wickMat : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![Complex.I, 1, 1, 1]

/-- Inverse Wick rotation matrix W⁻¹ = diag(-i, 1, 1, 1). -/
def wickInvMat : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![-Complex.I, 1, 1, 1]

theorem wickMat_mul_wickInvMat : wickMat * wickInvMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wickMat, wickInvMat, Matrix.diagonal_mul_diagonal]

theorem wickInvMat_mul_wickMat : wickInvMat * wickMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wickMat, wickInvMat, Matrix.diagonal_mul_diagonal]

theorem wickMat_mulVec_eq_wickMap (x : Spacetime4) :
    wickMat.mulVec (fun μ => (x μ : ℂ)) = wickMap x := by
  ext μ
  fin_cases μ <;> simp [wickMat, wickMap, Matrix.mulVec_diagonal]

/-- **Fundamental Wick Metric Identity:** `η_ℂ(wick x, wick y) = -∑ μ, x μ * y μ`. -/
theorem wick_inner_eq_neg_euclid (x y : Spacetime4) :
    minkowskiComplexInner (wickMap x) (wickMap y) =
      -(∑ μ : Fin 4, (x μ : ℂ) * (y μ : ℂ)) := by
  unfold minkowskiComplexInner wickMap
  simp only [Fin.sum_univ_four, ↓reduceIte]
  have hI : Complex.I * (x 0 : ℂ) * (Complex.I * (y 0 : ℂ)) = -((x 0 : ℂ) * (y 0 : ℂ)) := by
    calc
      Complex.I * (x 0 : ℂ) * (Complex.I * (y 0 : ℂ))
          = (Complex.I * Complex.I) * ((x 0 : ℂ) * (y 0 : ℂ)) := by ring
      _ = (-1) * ((x 0 : ℂ) * (y 0 : ℂ)) := by rw [Complex.I_mul_I]
      _ = -((x 0 : ℂ) * (y 0 : ℂ)) := by ring
  rw [hI]
  ring

/-- Euclidean quadratic form preserved by orthogonal matrix `Rᵀ * R = 1` over `ℂ`. -/
theorem euclid_complex_bilin_of_orthogonal {R : Matrix (Fin 4) (Fin 4) ℂ}
    (hR : Matrix.transpose R * R = 1) (u v : Fin 4 → ℂ) :
    ∑ μ : Fin 4, (R.mulVec u μ) * (R.mulVec v μ) = ∑ μ : Fin 4, u μ * v μ := by
  have h1 : dotProduct (R.mulVec u) (R.mulVec v) = dotProduct u ((Matrix.transpose R * R).mulVec v) := by
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [hR, Matrix.one_mulVec] at h1
  simpa [dotProduct] using h1

/-- Wick-conjugated complex Lorentz transformation `W R W⁻¹` from `R ∈ SO(4)`. -/
def wickConjugate (R : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  wickMat * R * wickInvMat

theorem wick_rot_commutes_with_wick (R : Matrix (Fin 4) (Fin 4) ℝ) (x : Spacetime4) :
    (wickConjugate (R.map Complex.ofReal)).mulVec (wickMap x) =
      wickMap (WithLp.equiv 2 (Fin 4 → ℝ) |>.symm (R.mulVec x)) := by
  rw [wickConjugate, ← wickMat_mulVec_eq_wickMap, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      wickInvMat_mul_wickMat, Matrix.one_mulVec]
  rw [← wickMat_mulVec_eq_wickMap]
  congr 1
  ext μ
  simp [Matrix.mulVec, dotProduct]

/-- **Every real orthogonal matrix conjugates via `W R W⁻¹` to a complex Minkowski isometry.** -/
theorem wick_rot_preserves_minkowski {R : Matrix (Fin 4) (Fin 4) ℝ}
    (hR : Matrix.transpose R * R = 1) (z w : Fin 4 → ℂ) :
    minkowskiComplexInner
        ((wickConjugate (R.map Complex.ofReal)).mulVec z)
        ((wickConjugate (R.map Complex.ofReal)).mulVec w) =
      minkowskiComplexInner z w := by
  have h_mink_wick : ∀ u v : Fin 4 → ℂ,
      minkowskiComplexInner (wickMat.mulVec u) (wickMat.mulVec v) =
        -(∑ μ : Fin 4, u μ * v μ) := by
    intro u v
    unfold minkowskiComplexInner wickMat
    simp only [Matrix.mulVec_diagonal, Fin.sum_univ_four]
    have hI : (Complex.I * u 0) * (Complex.I * v 0) = -(u 0 * v 0) := by
      calc
        (Complex.I * u 0) * (Complex.I * v 0) = (Complex.I * Complex.I) * (u 0 * v 0) := by ring
        _ = -(u 0 * v 0) := by rw [Complex.I_mul_I]; ring
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, one_mul]
    rw [hI]; ring
  have h_inv_wick : ∀ u : Fin 4 → ℂ, wickMat.mulVec (wickInvMat.mulVec u) = u := by
    intro u; rw [← Matrix.mulVec_mulVec, wickMat_mul_wickInvMat, Matrix.one_mulVec]
  have hR_C : Matrix.transpose (R.map Complex.ofReal) * (R.map Complex.ofReal) = 1 := by
    ext i j
    have hij := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => (M i j : ℂ)) hR
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hij
  calc
    minkowskiComplexInner
        ((wickConjugate (R.map Complex.ofReal)).mulVec z)
        ((wickConjugate (R.map Complex.ofReal)).mulVec w)
        = minkowskiComplexInner
            (wickMat.mulVec ((R.map Complex.ofReal).mulVec (wickInvMat.mulVec z)))
            (wickMat.mulVec ((R.map Complex.ofReal).mulVec (wickInvMat.mulVec w))) := by
              simp [wickConjugate, Matrix.mulVec_mulVec]
    _ = -(∑ μ : Fin 4, ((R.map Complex.ofReal).mulVec (wickInvMat.mulVec z) μ) *
            ((R.map Complex.ofReal).mulVec (wickInvMat.mulVec w) μ)) := h_mink_wick _ _
    _ = -(∑ μ : Fin 4, (wickInvMat.mulVec z μ) * (wickInvMat.mulVec w μ)) := by
          rw [euclid_complex_bilin_of_orthogonal hR_C]
    _ = minkowskiComplexInner (wickMat.mulVec (wickInvMat.mulVec z))
            (wickMat.mulVec (wickInvMat.mulVec w)) := (h_mink_wick _ _).symm
    _ = minkowskiComplexInner z w := by rw [h_inv_wick z, h_inv_wick w]

theorem wick_rot_det_one {R : Matrix (Fin 4) (Fin 4) ℝ} (hdet : R.det = 1) :
    (wickConjugate (R.map Complex.ofReal)).det = 1 := by
  have hR_det : (R.map Complex.ofReal).det = 1 := by
    rw [← (RingHom.map_det Complex.ofRealHom R), hdet, map_one]
  have hWI : wickMat.det * wickInvMat.det = 1 := by
    rw [← Matrix.det_mul, wickMat_mul_wickInvMat, Matrix.det_one]
  unfold wickConjugate
  rw [Matrix.det_mul, Matrix.det_mul, hR_det, mul_one, mul_comm, hWI]

/-- Complexified Euclidean (0, 1)-rotation matrix by angle θ. -/
noncomputable def rot01C (θ : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![Complex.cos θ, -Complex.sin θ, 0, 0;
     Complex.sin θ,  Complex.cos θ, 0, 0;
     0,              0,             1, 0;
     0,              0,             0, 1]

/-- Minkowski (0, 1)-Lorentz boost matrix with rapidity η. -/
noncomputable def boost01 (η : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![Real.cosh η, Real.sinh η, 0, 0;
     Real.sinh η, Real.cosh η, 0, 0;
     0,           0,           1, 0;
     0,           0,           0, 1]

/-- **Exact Analytic Continuation of Rotations to Lorentz Boosts:**
    `W * rot01(η * i) * W⁻¹ = boost01(η)`. -/
theorem wick_rot01_eq_boost01 (η : ℝ) :
    wickConjugate (rot01C ((η : ℂ) * Complex.I)) = (boost01 η).map Complex.ofReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wickConjugate, wickMat, wickInvMat, rot01C, boost01,
      Matrix.mul_apply, Fin.sum_univ_four, Complex.cos_mul_I, Complex.sin_mul_I,
      Complex.ofReal_cosh, Complex.ofReal_sinh]
  <;>
  (try ring_nf) <;>
  (try simp [Complex.I_sq]) <;>
  (try norm_num) <;>
  (try simp_all [Complex.ext_iff, Complex.I_mul_I]) <;>
  (try ring_nf at *) <;>
  (try norm_num at *) <;>
  (try linarith)

end Imscribing.YangMills.WickMatrixBridge