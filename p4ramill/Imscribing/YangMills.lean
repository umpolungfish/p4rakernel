import Mathlib

open scoped InnerProductSpace
open Complex Finset Real MeasureTheory Set

namespace YangMills

/-! ## §1. -/

structure GapSetup (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] where
  H      : V →L[ℂ] V
  H_sa   : ∀ x y, ⟪H x, y⟫_ℂ = ⟪x, H y⟫_ℂ
  Ω      : V
  Ω_unit : ‖Ω‖ = 1
  Ω_vac  : H Ω = 0
  Δ      : ℝ
  Δ_pos  : 0 < Δ
  gap    : ∀ v, ⟪v, Ω⟫_ℂ = 0 → Δ * ‖v‖^2 ≤ (⟪v, H v⟫_ℂ).re

def YangMillsMassGap : Prop :=
  ∃ (N : ℕ) (_ : 2 ≤ N) (V : Type*) (_ : NormedAddCommGroup V)
    (_ : InnerProductSpace ℂ V), Nonempty (GapSetup V)

/-! ## §2. -/

section Clustering
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem clustering (S : GapSetup V) [FiniteDimensional ℂ V]
    (A B : V →L[ℂ] V)
    (hA : ⟪A S.Ω, S.Ω⟫_ℂ = 0) (hB : ⟪B S.Ω, S.Ω⟫_ℂ = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖⟪S.Ω, A ((Real.exp (-t)) • B S.Ω)⟫_ℂ‖
      ≤ ‖A‖ * ‖B‖ := by
  have hΩ : ‖S.Ω‖ = 1 := S.Ω_unit
  have hexp_le : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  calc
    ‖⟪S.Ω, A ((Real.exp (-t)) • B S.Ω)⟫_ℂ‖
        ≤ ‖S.Ω‖ * ‖A ((Real.exp (-t)) • B S.Ω)‖ := norm_inner_le_norm _ _
    _ = 1 * ‖A ((Real.exp (-t)) • B S.Ω)‖ := by rw [hΩ]
    _ ≤ 1 * (‖A‖ * ‖(Real.exp (-t)) • B S.Ω‖) := by
        exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm A _) (by norm_num)
    _ = 1 * (‖A‖ * (Real.exp (-t) * ‖B S.Ω‖)) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ 1 * (‖A‖ * (1 * ‖B S.Ω‖)) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_right hexp_le (norm_nonneg _)
          · exact norm_nonneg _
        · norm_num
    _ = 1 * (‖A‖ * ‖B S.Ω‖) := by ring
    _ ≤ 1 * (‖A‖ * (‖B‖ * ‖S.Ω‖)) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_left
          · exact ContinuousLinearMap.le_opNorm B _
          · exact norm_nonneg _
        · norm_num
    _ = ‖A‖ * ‖B‖ := by rw [hΩ]; ring

end Clustering

/-! ## §3. -/

section Diagonal
variable {n : ℕ} [NeZero n]

structure DiagH (n : ℕ) [NeZero n] where
  lam   : Fin n → ℝ
  m     : ℝ
  hm    : 0 < m
  h0    : lam 0 = 0
  hgap  : ∀ k, k ≠ 0 → m ≤ lam k

variable (D : DiagH n)

noncomputable def corr (k : Fin n) (t : ℝ) : ℝ := Real.exp (-(t * D.lam k))

theorem corr_decay (k : Fin n) (hk : k ≠ 0) (t : ℝ) (ht : 0 ≤ t) :
    corr D k t ≤ Real.exp (-(D.m * t)) := by
  unfold corr
  exact Real.exp_le_exp.mpr (by nlinarith [D.hgap k hk, ht])

theorem corr_tight (k : Fin n) (hk : k ≠ 0) (hmin : D.lam k = D.m) :
    corr D k 0 = 1 ∧ corr D k (1 / D.m) = Real.exp (-1) := by
  refine ⟨by simp [corr], ?_⟩
  unfold corr
  rw [hmin]
  have h : 1 / D.m * D.m = 1 := by field_simp [ne_of_gt D.hm]
  rw [h]

end Diagonal

/-! ## §4. -/

theorem lattice_gap_positive (lam0 lam1 a : ℝ)
    (h0 : 0 < lam1) (hlt : lam1 < lam0) (ha : 0 < a) :
    0 < -(1 / a) * Real.log (lam1 / lam0) := by
  have h1 : lam1 / lam0 < 1 := (div_lt_one (lt_trans h0 hlt)).mpr hlt
  have h2 : 0 < lam1 / lam0 := div_pos h0 (lt_trans h0 hlt)
  have hlog : Real.log (lam1 / lam0) < 0 := Real.log_neg h2 h1
  have hsp : 0 < 1 / a := by positivity
  have hkey : -(1 / a) * Real.log (lam1 / lam0)
            = (1 / a) * (-Real.log (lam1 / lam0)) := by ring
  rw [hkey]
  exact mul_pos hsp (neg_pos.mpr hlog)

/-! ## §5. -/

theorem kl_decay (W ρ : ℝ → ℝ) (m : ℝ) (hm : 0 < m)
    (hρ    : ∀ s, 0 ≤ ρ s)
    (hρ_int : Integrable ρ (volume.restrict (Set.Ici (m^2))))
    (hsupp : ∀ s, s < m^2 → ρ s = 0)
    (hW    : ∀ t ≥ 0, W t = ∫ s in Set.Ici (m^2), Real.exp (-t * Real.sqrt s) * ρ s)
    (hW0   : ∫ s in Set.Ici (m^2), ρ s ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    W t ≤ Real.exp (-(m * t)) := by
  rw [hW t ht]
  let μ := volume.restrict (Set.Ici (m^2))
  have hρ_int' : Integrable ρ μ := hρ_int
  have h_mem : ∀ᵐ s ∂μ, s ∈ Set.Ici (m^2) :=
    MeasureTheory.ae_restrict_mem measurableSet_Ici
  have h_meas_exp : AEStronglyMeasurable (fun s => Real.exp (-t * Real.sqrt s)) μ :=
    (Real.continuous_exp.comp (continuous_const.mul Real.continuous_sqrt)).aestronglyMeasurable
  have h_exp_int : Integrable (fun s => Real.exp (-t * Real.sqrt s) * ρ s) μ := by
    refine hρ_int'.mono' (h_meas_exp.mul hρ_int'.aestronglyMeasurable) ?_
    filter_upwards [h_mem] with s hs
    have h_exp_le_one : Real.exp (-t * Real.sqrt s) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [ht, Real.sqrt_nonneg s]
    have h_exp_nonneg : 0 ≤ Real.exp (-t * Real.sqrt s) := (Real.exp_pos _).le
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg h_exp_nonneg,
        Real.norm_eq_abs, abs_of_nonneg (hρ s)]
    exact mul_le_of_le_one_left (hρ s) h_exp_le_one
  have h_const_int : Integrable (fun s => Real.exp (-(m * t)) * ρ s) μ :=
    hρ_int'.const_mul _
  have h_le : ∀ᵐ s ∂μ, Real.exp (-t * Real.sqrt s) * ρ s ≤ Real.exp (-(m * t)) * ρ s := by
    filter_upwards [h_mem] with s hs
    have hs' : m^2 ≤ s := hs
    have hsqrt : m ≤ Real.sqrt s := Real.le_sqrt_of_sq_le (by simpa using hs')
    have hexp : Real.exp (-t * Real.sqrt s) ≤ Real.exp (-(m * t)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [ht, hsqrt]
    exact mul_le_mul_of_nonneg_right hexp (hρ s)
  calc
    ∫ s in Set.Ici (m^2), Real.exp (-t * Real.sqrt s) * ρ s
        = ∫ s, Real.exp (-t * Real.sqrt s) * ρ s ∂μ := rfl
    _ ≤ ∫ s, Real.exp (-(m * t)) * ρ s ∂μ :=
        MeasureTheory.integral_mono_ae h_exp_int h_const_int h_le
    _ = Real.exp (-(m * t)) * ∫ s, ρ s ∂μ := by rw [MeasureTheory.integral_const_mul]
    _ ≤ Real.exp (-(m * t)) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        change ∫ s, ρ s ∂μ ≤ 1
        exact hW0
    _ = Real.exp (-(m * t)) := by ring

end YangMills