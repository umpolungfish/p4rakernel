
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Imscribing.YangMills.ClayStatement

/-!
# Lorentz4 Group Structure & Poincaré Spacelike Invariance
-/

noncomputable section

namespace Imscribing.YangMills.LorentzFields

open Imscribing.YangMills.ClaySpec

/-- Diagonal Minkowski metric tensor η = diag(1, -1, -1, -1). -/
def minkowskiEta : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, -1, -1, -1]

theorem minkowskiEta_sq : minkowskiEta * minkowskiEta = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minkowskiEta, Matrix.diagonal_mul_diagonal]

theorem minkowskiEta_det : minkowskiEta.det = -1 := by
  simp [minkowskiEta, Matrix.det_diagonal, Fin.prod_univ_four]

theorem minkowskiEta_transpose : Matrix.transpose minkowskiEta = minkowskiEta := by
  simp [minkowskiEta]

theorem minkowskiInner_eq_dot (x y : Spacetime4) :
    minkowskiInner x y = dotProduct x.ofLp (minkowskiEta.mulVec y.ofLp) := by
  simp [minkowskiInner, minkowskiEta, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_four]
  ring

private lemma mat_transpose_eta_mul (Λ : Lorentz4) :
    Matrix.transpose Λ.mat * minkowskiEta * Λ.mat = minkowskiEta := by
  ext i j
  let ei : Spacetime4 := (WithLp.equiv 2 (Fin 4 → ℝ)).symm (Pi.single i (1 : ℝ))
  let ej : Spacetime4 := (WithLp.equiv 2 (Fin 4 → ℝ)).symm (Pi.single j (1 : ℝ))
  have h_pres := Λ.preserves_metric ei ej
  rw [minkowskiInner_eq_dot, minkowskiInner_eq_dot] at h_pres
  have h_lhs :
      dotProduct ((WithLp.equiv 2 (Fin 4 → ℝ)).symm (Λ.mat.mulVec ei.ofLp)).ofLp
        (minkowskiEta.mulVec ((WithLp.equiv 2 (Fin 4 → ℝ)).symm (Λ.mat.mulVec ej.ofLp)).ofLp) =
      (Matrix.transpose Λ.mat * minkowskiEta * Λ.mat) i j := by
    have h_dot :
        dotProduct (Λ.mat.mulVec ei.ofLp) (minkowskiEta.mulVec (Λ.mat.mulVec ej.ofLp)) =
        dotProduct ei.ofLp
          ((Matrix.transpose Λ.mat * minkowskiEta * Λ.mat).mulVec ej.ofLp) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
        ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    change dotProduct (Λ.mat.mulVec ei.ofLp) (minkowskiEta.mulVec (Λ.mat.mulVec ej.ofLp)) = _
    rw [h_dot]
    simp [ei, ej, Matrix.mulVec, dotProduct]
  have h_rhs : dotProduct ei.ofLp (minkowskiEta.mulVec ej.ofLp) = minkowskiEta i j := by
    simp [ei, ej, Matrix.mulVec, dotProduct]
  rw [h_lhs, h_rhs] at h_pres
  exact h_pres

/-- Inverse matrix `η * Mᵀ * η` of `Λ : Lorentz4`. -/
def lorentzInvMat (Λ : Lorentz4) : Matrix (Fin 4) (Fin 4) ℝ :=
  minkowskiEta * Matrix.transpose Λ.mat * minkowskiEta

theorem lorentzInvMat_mul (Λ : Lorentz4) : lorentzInvMat Λ * Λ.mat = 1 := by
  unfold lorentzInvMat
  calc
    (minkowskiEta * Matrix.transpose Λ.mat * minkowskiEta) * Λ.mat
        = minkowskiEta * (Matrix.transpose Λ.mat * minkowskiEta * Λ.mat) := by
            simp only [Matrix.mul_assoc]
    _ = minkowskiEta * minkowskiEta := by rw [mat_transpose_eta_mul Λ]
    _ = 1 := minkowskiEta_sq

theorem mul_lorentzInvMat (Λ : Lorentz4) : Λ.mat * lorentzInvMat Λ = 1 :=
  mul_eq_one_comm.mp (lorentzInvMat_mul Λ)

instance : One Lorentz4 where
  one :=
    { mat := 1
      preserves_metric := fun x y => by simp [Matrix.one_mulVec]
      det_one := Matrix.det_one
      orthochronous := by norm_num }

instance : Mul Lorentz4 where
  mul Λ₁ Λ₂ :=
    { mat := Λ₁.mat * Λ₂.mat
      preserves_metric := fun x y => by
        have h1 := Λ₁.preserves_metric
          ((WithLp.equiv 2 (Fin 4 → ℝ)).symm (Λ₂.mat.mulVec x.ofLp))
          ((WithLp.equiv 2 (Fin 4 → ℝ)).symm (Λ₂.mat.mulVec y.ofLp))
        have h2 := Λ₂.preserves_metric x y
        have h_eq : ∀ v : Spacetime4,
            (WithLp.equiv 2 (Fin 4 → ℝ)).symm ((Λ₁.mat * Λ₂.mat).mulVec v.ofLp) =
            (WithLp.equiv 2 (Fin 4 → ℝ)).symm
              (Λ₁.mat.mulVec ((WithLp.equiv 2 (Fin 4 → ℝ)).symm (Λ₂.mat.mulVec v.ofLp)).ofLp) := by
          intro v; ext μ; simp [Matrix.mulVec_mulVec]
        rw [h_eq x, h_eq y, h1, h2]
      det_one := by rw [Matrix.det_mul, Λ₁.det_one, Λ₂.det_one, mul_one]
      orthochronous := by
        have h01 : (0 : Fin 4) ≠ 1 := by decide
        have h02 : (0 : Fin 4) ≠ 2 := by decide
        have h03 : (0 : Fin 4) ≠ 3 := by decide
        have h12 : (1 : Fin 4) ≠ 2 := by decide
        have h13 : (1 : Fin 4) ≠ 3 := by decide
        have h23 : (2 : Fin 4) ≠ 3 := by decide
        have h_norm1 : Λ₁.mat 0 0 ^ 2 -
            (Λ₁.mat 0 1 ^ 2 + Λ₁.mat 0 2 ^ 2 + Λ₁.mat 0 3 ^ 2) = 1 := by
          have h_m_inv : Λ₁.mat * minkowskiEta * Matrix.transpose Λ₁.mat = minkowskiEta := by
            have h1 := mul_lorentzInvMat Λ₁
            unfold lorentzInvMat at h1
            have h2 := congrArg (fun M => M * minkowskiEta) h1
            simp only [Matrix.mul_assoc, minkowskiEta_sq, Matrix.mul_one, Matrix.one_mul] at h2
            simpa only [Matrix.mul_assoc] using h2
          have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 0) h_m_inv
          simp only [Matrix.mul_apply, minkowskiEta, Matrix.transpose_apply,
            Matrix.diagonal_apply, Fin.sum_univ_four, ↓reduceIte,
            h01, h01.symm, h02, h02.symm, h03, h03.symm,
            h12, h12.symm, h13, h13.symm, h23, h23.symm] at h00
          have hv0 : (![1, -1, -1, -1] : Fin 4 → ℝ) 0 = 1 := by simp
          have hv1 : (![1, -1, -1, -1] : Fin 4 → ℝ) 1 = -1 := by simp
          have hv2 : (![1, -1, -1, -1] : Fin 4 → ℝ) 2 = -1 := by simp
          have hv3 : (![1, -1, -1, -1] : Fin 4 → ℝ) 3 = -1 := by simp
          rw [hv0, hv1, hv2, hv3] at h00
          rw [← h00]; ring
        have h_norm2 : Λ₂.mat 0 0 ^ 2 -
            (Λ₂.mat 1 0 ^ 2 + Λ₂.mat 2 0 ^ 2 + Λ₂.mat 3 0 ^ 2) = 1 := by
          have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 0) (mat_transpose_eta_mul Λ₂)
          simp only [Matrix.mul_apply, minkowskiEta, Matrix.transpose_apply,
            Matrix.diagonal_apply, Fin.sum_univ_four, ↓reduceIte,
            h01, h01.symm, h02, h02.symm, h03, h03.symm,
            h12, h12.symm, h13, h13.symm, h23, h23.symm] at h00
          have hv0 : (![1, -1, -1, -1] : Fin 4 → ℝ) 0 = 1 := by simp
          have hv1 : (![1, -1, -1, -1] : Fin 4 → ℝ) 1 = -1 := by simp
          have hv2 : (![1, -1, -1, -1] : Fin 4 → ℝ) 2 = -1 := by simp
          have hv3 : (![1, -1, -1, -1] : Fin 4 → ℝ) 3 = -1 := by simp
          rw [hv0, hv1, hv2, hv3] at h00
          rw [← h00]; ring
        have h_cs : (Λ₁.mat 0 1 * Λ₂.mat 1 0 + Λ₁.mat 0 2 * Λ₂.mat 2 0 +
            Λ₁.mat 0 3 * Λ₂.mat 3 0) ^ 2 ≤
            (Λ₁.mat 0 1 ^ 2 + Λ₁.mat 0 2 ^ 2 + Λ₁.mat 0 3 ^ 2) *
            (Λ₂.mat 1 0 ^ 2 + Λ₂.mat 2 0 ^ 2 + Λ₂.mat 3 0 ^ 2) := by
          have h_sq : 0 ≤ (Λ₁.mat 0 1 * Λ₂.mat 2 0 - Λ₁.mat 0 2 * Λ₂.mat 1 0) ^ 2 +
              (Λ₁.mat 0 1 * Λ₂.mat 3 0 - Λ₁.mat 0 3 * Λ₂.mat 1 0) ^ 2 +
              (Λ₁.mat 0 2 * Λ₂.mat 3 0 - Λ₁.mat 0 3 * Λ₂.mat 2 0) ^ 2 := by positivity
          linarith [h_sq]
        have h_lt1 : Λ₁.mat 0 1 ^ 2 + Λ₁.mat 0 2 ^ 2 + Λ₁.mat 0 3 ^ 2 < Λ₁.mat 0 0 ^ 2 := by linarith
        have h_lt2 : Λ₂.mat 1 0 ^ 2 + Λ₂.mat 2 0 ^ 2 + Λ₂.mat 3 0 ^ 2 < Λ₂.mat 0 0 ^ 2 := by linarith
        have h_prod_lt : (Λ₁.mat 0 1 * Λ₂.mat 1 0 + Λ₁.mat 0 2 * Λ₂.mat 2 0 +
            Λ₁.mat 0 3 * Λ₂.mat 3 0) ^ 2 < (Λ₁.mat 0 0 * Λ₂.mat 0 0) ^ 2 := by
          have hnn1 : 0 ≤ Λ₁.mat 0 1 ^ 2 + Λ₁.mat 0 2 ^ 2 + Λ₁.mat 0 3 ^ 2 := by positivity
          have hnn2 : 0 ≤ Λ₂.mat 1 0 ^ 2 + Λ₂.mat 2 0 ^ 2 + Λ₂.mat 3 0 ^ 2 := by positivity
          calc
            (Λ₁.mat 0 1 * Λ₂.mat 1 0 + Λ₁.mat 0 2 * Λ₂.mat 2 0 +
                Λ₁.mat 0 3 * Λ₂.mat 3 0) ^ 2
                ≤ (Λ₁.mat 0 1 ^ 2 + Λ₁.mat 0 2 ^ 2 + Λ₁.mat 0 3 ^ 2) *
                  (Λ₂.mat 1 0 ^ 2 + Λ₂.mat 2 0 ^ 2 + Λ₂.mat 3 0 ^ 2) := h_cs
            _ < Λ₁.mat 0 0 ^ 2 * Λ₂.mat 0 0 ^ 2 := mul_lt_mul'' h_lt1 h_lt2 hnn1 hnn2
            _ = (Λ₁.mat 0 0 * Λ₂.mat 0 0) ^ 2 := by ring
        have h_pos_prod : 0 < Λ₁.mat 0 0 * Λ₂.mat 0 0 :=
          mul_pos Λ₁.orthochronous Λ₂.orthochronous
        have h_mul00 : (Λ₁.mat * Λ₂.mat) 0 0 =
            Λ₁.mat 0 0 * Λ₂.mat 0 0 +
              (Λ₁.mat 0 1 * Λ₂.mat 1 0 + Λ₁.mat 0 2 * Λ₂.mat 2 0 +
               Λ₁.mat 0 3 * Λ₂.mat 3 0) := by
          simp [Matrix.mul_apply, Fin.sum_univ_four]; ring
        rw [h_mul00]
        nlinarith }

instance : Inv Lorentz4 where
  inv Λ :=
    { mat := lorentzInvMat Λ
      preserves_metric := fun x y => by
        let M := lorentzInvMat Λ
        have h_symm : Matrix.transpose M * minkowskiEta * M = minkowskiEta := by
          have h_m_inv : Λ.mat * minkowskiEta * Matrix.transpose Λ.mat = minkowskiEta := by
            have h1 := mul_lorentzInvMat Λ
            unfold lorentzInvMat at h1
            have h2 := congrArg (fun A => A * minkowskiEta) h1
            simp only [Matrix.mul_assoc, minkowskiEta_sq, Matrix.mul_one, Matrix.one_mul] at h2
            simpa only [Matrix.mul_assoc] using h2
          dsimp [M, lorentzInvMat]
          rw [Matrix.transpose_mul, Matrix.transpose_mul, minkowskiEta_transpose,
              Matrix.transpose_transpose]
          calc
            _ = minkowskiEta * (Λ.mat * (minkowskiEta * minkowskiEta) *
                    (minkowskiEta * Matrix.transpose Λ.mat)) * minkowskiEta := by
                    simp only [Matrix.mul_assoc]
            _ = minkowskiEta * (Λ.mat * minkowskiEta * Matrix.transpose Λ.mat) * minkowskiEta := by
                  rw [minkowskiEta_sq]; simp only [Matrix.one_mul, Matrix.mul_assoc]
            _ = minkowskiEta * minkowskiEta * minkowskiEta := by rw [h_m_inv]
            _ = minkowskiEta := by rw [minkowskiEta_sq, Matrix.one_mul]
        rw [minkowskiInner_eq_dot, minkowskiInner_eq_dot]
        have h_dot :
            dotProduct (M.mulVec x.ofLp) (minkowskiEta.mulVec (M.mulVec y.ofLp)) =
            dotProduct x.ofLp ((Matrix.transpose M * minkowskiEta * M).mulVec y.ofLp) := by
          rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
            ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
        change dotProduct (M.mulVec x.ofLp) (minkowskiEta.mulVec (M.mulVec y.ofLp)) = _
        rw [h_dot, h_symm]
      det_one := by
        unfold lorentzInvMat
        rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, minkowskiEta_det, Λ.det_one]
        norm_num
      orthochronous := by
        have h00 : lorentzInvMat Λ 0 0 = Λ.mat 0 0 := by
          simp [lorentzInvMat, minkowskiEta, Matrix.mul_apply, Fin.sum_univ_four]
        rw [h00]
        exact Λ.orthochronous }

theorem lorentz_inv_mul_mat (Λ : Lorentz4) : (Λ⁻¹ * Λ).mat = (1 : Lorentz4).mat :=
  lorentzInvMat_mul Λ

theorem lorentz_mul_inv_mat (Λ : Lorentz4) : (Λ * Λ⁻¹).mat = (1 : Lorentz4).mat :=
  mul_lorentzInvMat Λ

private def basis4 (μ : Fin 4) : Spacetime4 :=
  (WithLp.equiv 2 (Fin 4 → ℝ)).symm (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)

/-- Continuous linear map on `Spacetime4` induced by `Λ : Lorentz4`. -/
def lorentzCLM (Λ : Lorentz4) : Spacetime4 →L[ℝ] Spacetime4 where
  toFun x := ∑ μ : Fin 4, (Λ.mat.mulVec x.ofLp μ) • basis4 μ
  map_add' x y := by
    ext μ
    fin_cases μ <;> simp [Matrix.mulVec_add, basis4, Pi.single_apply, Fin.sum_univ_four] <;> ring
  map_smul' c x := by
    ext μ
    fin_cases μ <;> simp [Matrix.mulVec_smul, basis4, Pi.single_apply, Fin.sum_univ_four] <;> ring
  cont := by
    refine continuous_finset_sum _ fun μ _ => ?_
    have h_mulVec : Continuous (fun x : Spacetime4 => Λ.mat.mulVec x.ofLp μ) := by
      simp only [Matrix.mulVec, dotProduct]
      exact continuous_finset_sum _ fun ν _ =>
        continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) ν)
    exact h_mulVec.smul continuous_const

private lemma lorentzCLM_apply_coe (Λ : Lorentz4) (x : Spacetime4) (μ : Fin 4) :
    (lorentzCLM Λ x).ofLp μ = Λ.mat.mulVec x.ofLp μ := by
  fin_cases μ <;> simp [lorentzCLM, basis4, Pi.single_apply, Fin.sum_univ_four]

theorem lorentzCLM_mul (Λ₁ Λ₂ : Lorentz4) (x : Spacetime4) :
    lorentzCLM (Λ₁ * Λ₂) x = lorentzCLM Λ₁ (lorentzCLM Λ₂ x) := by
  ext μ
  rw [lorentzCLM_apply_coe, lorentzCLM_apply_coe]
  have h2 : (lorentzCLM Λ₂ x).ofLp = Λ₂.mat.mulVec x.ofLp := by
    ext ν; exact lorentzCLM_apply_coe Λ₂ x ν
  change ((Λ₁.mat * Λ₂.mat).mulVec x.ofLp) μ = (Λ₁.mat.mulVec (lorentzCLM Λ₂ x).ofLp) μ
  rw [h2, Matrix.mulVec_mulVec]

theorem lorentzCLM_one (x : Spacetime4) : lorentzCLM 1 x = x := by
  ext μ
  rw [lorentzCLM_apply_coe]
  change ((1 : Matrix (Fin 4) (Fin 4) ℝ).mulVec x.ofLp) μ = x.ofLp μ
  rw [Matrix.one_mulVec]

theorem lorentzCLM_inv_cancel (Λ : Lorentz4) (x : Spacetime4) :
    lorentzCLM Λ (lorentzCLM Λ⁻¹ x) = x := by
  rw [← lorentzCLM_mul]
  ext μ
  rw [lorentzCLM_apply_coe]
  change ((Λ * Λ⁻¹).mat.mulVec x.ofLp) μ = x.ofLp μ
  rw [lorentz_mul_inv_mat Λ]
  exact congrFun (Matrix.one_mulVec _) μ

theorem lorentzCLM_cancel_inv (Λ : Lorentz4) (x : Spacetime4) :
    lorentzCLM Λ⁻¹ (lorentzCLM Λ x) = x := by
  rw [← lorentzCLM_mul]
  ext μ
  rw [lorentzCLM_apply_coe]
  change ((Λ⁻¹ * Λ).mat.mulVec x.ofLp) μ = x.ofLp μ
  rw [lorentz_inv_mul_mat Λ]
  exact congrFun (Matrix.one_mulVec _) μ

/-- **Poincaré Invariance of `SpacelikeDisjoint`:** -/
theorem poincare_preserves_spacelike_diff (g : Poincare4) (x y : Spacetime4) :
    minkowskiInner ((g.trans + lorentzCLM g.lorentz x) - (g.trans + lorentzCLM g.lorentz y))
      ((g.trans + lorentzCLM g.lorentz x) - (g.trans + lorentzCLM g.lorentz y)) =
      minkowskiInner (x - y) (x - y) := by
  have h_sub : (g.trans + lorentzCLM g.lorentz x) - (g.trans + lorentzCLM g.lorentz y) =
      lorentzCLM g.lorentz (x - y) := by
    rw [add_sub_add_left_eq_sub, ← map_sub]
  rw [h_sub]
  have h_eq : lorentzCLM g.lorentz (x - y) =
      (WithLp.equiv 2 (Fin 4 → ℝ)).symm (g.lorentz.mat.mulVec (x - y).ofLp) := by
    ext μ; exact lorentzCLM_apply_coe g.lorentz (x - y) μ
  rw [h_eq]
  exact g.lorentz.preserves_metric (x - y) (x - y)

end Imscribing.YangMills.LorentzFields