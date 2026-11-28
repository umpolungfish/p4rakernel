import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Topology.Compactness.Compact
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Imscribing.YangMills.WilsonActionBounds4D

/-!
# Compactness of SU(N) & Normalized Finite-Volume Wilson Expectations
-/

namespace Imscribing.YangMills.WilsonMeasure4D

open MeasureTheory
open Imscribing.YangMills.WilsonLattice4D
open Imscribing.YangMills.WilsonBounds4D

/-- `SU(N)` is a compact subset of `Matrix (Fin N) (Fin N) ℂ`. -/
theorem isCompact_specialUnitaryGroup (N : ℕ) :
    IsCompact { M : Matrix (Fin N) (Fin N) ℂ | M ∈ Matrix.specialUnitaryGroup (Fin N) ℂ } := by
  let K : Set (Matrix (Fin N) (Fin N) ℂ) :=
    Set.pi Set.univ (fun _ : Fin N => Set.pi Set.univ (fun _ : Fin N => Metric.closedBall (0 : ℂ) 1))
  have hK : IsCompact K :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) 1
  have hS_sub : { M : Matrix (Fin N) (Fin N) ℂ | M ∈ Matrix.specialUnitaryGroup (Fin N) ℂ } ⊆ K := by
    intro M hM i _ j _
    rw [Metric.mem_closedBall, dist_zero_right]
    exact gaugeGroup_entry_norm_le_one ⟨M, hM⟩ i j
  have h_eq : { M : Matrix (Fin N) (Fin N) ℂ | M ∈ Matrix.specialUnitaryGroup (Fin N) ℂ } =
      { M : Matrix (Fin N) (Fin N) ℂ | M * star M = 1 ∧ M.det = 1 } := by
    ext M
    simp only [Set.mem_setOf_eq, Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  have h_cont_det : Continuous (fun M : Matrix (Fin N) (Fin N) ℂ => M.det) := by
    have hdet_eq : (fun M : Matrix (Fin N) (Fin N) ℂ => M.det) =
        fun M => ∑ σ : Equiv.Perm (Fin N), (Equiv.Perm.sign σ : ℂ) * ∏ i : Fin N, M (σ i) i := by
      ext M
      rw [Matrix.det_apply]
      refine Finset.sum_congr rfl fun σ _ => ?_
      change ((Equiv.Perm.sign σ : ℤ) • ∏ i, M (σ i) i) = _
      rw [zsmul_eq_mul]
    rw [hdet_eq]
    refine continuous_finset_sum _ fun σ _ => continuous_const.mul
      (continuous_finset_prod _ fun i _ => (continuous_apply i).comp (continuous_apply (σ i)))
  have h_closed1 : IsClosed { M : Matrix (Fin N) (Fin N) ℂ | M * star M = 1 } := by
    have h_mul : Continuous (fun M : Matrix (Fin N) (Fin N) ℂ => M * star M) := by
      refine Continuous.mul ?_ continuous_star
      exact continuous_pi (fun _ => continuous_pi (fun _ => (continuous_apply _).comp (continuous_apply _)))
    exact isClosed_eq h_mul continuous_const
  have h_closed2 : IsClosed { M : Matrix (Fin N) (Fin N) ℂ | M.det = 1 } :=
    isClosed_eq h_cont_det continuous_const
  have h_closed : IsClosed { M : Matrix (Fin N) (Fin N) ℂ | M ∈ Matrix.specialUnitaryGroup (Fin N) ℂ } := by
    rw [h_eq]; exact h_closed1.inter h_closed2
  exact hK.of_isClosed_subset h_closed hS_sub

/-- `GaugeGroup N = Matrix.specialUnitaryGroup (Fin N) ℂ` is a `CompactSpace`. -/
theorem compactSpace_gaugeGroup (N : ℕ) : CompactSpace (GaugeGroup N) :=
  isCompact_iff_compactSpace.mp (isCompact_specialUnitaryGroup N)

/-- Finite-volume 4D SU(N) Wilson partition function `Z = ∫ exp(-S_W(β, U)) dμ(U)`. -/
noncomputable def wilsonPartitionFn (N L : ℕ) [NeZero N] [NeZero L] (β : ℝ)
    [MeasurableSpace (LinkConfig N L)] (μ : Measure (LinkConfig N L)) : ℝ :=
  ∫ U : LinkConfig N L, Real.exp (-wilsonAction N L β U) ∂μ

/-- Normalized Wilson expectation `⟨F⟩ = Z⁻¹ ∫ F(U) exp(-S_W(β, U)) dμ(U)`. -/
noncomputable def wilsonExpectation (N L : ℕ) [NeZero N] [NeZero L] (β : ℝ)
    [MeasurableSpace (LinkConfig N L)] (μ : Measure (LinkConfig N L))
    (F : LinkConfig N L → ℂ) : ℂ :=
  ((wilsonPartitionFn N L β μ)⁻¹ : ℂ) *
    ∫ U : LinkConfig N L, F U * (Real.exp (-wilsonAction N L β U) : ℂ) ∂μ

/-- Uniform strictly positive lower bound and unit upper bound on `Z_{N, L}(β)`. -/
theorem wilsonPartitionFn_bounds {N L : ℕ} [NeZero N] [NeZero L] {β : ℝ} (hβ : 0 ≤ β)
    [MeasurableSpace (LinkConfig N L)] (μ : Measure (LinkConfig N L)) [IsProbabilityMeasure μ]
    (h_meas : Measurable (fun U : LinkConfig N L => wilsonAction N L β U)) :
    0 < Real.exp (-(32 * β * ((Fintype.card (Lat4 L) : ℕ) : ℝ))) ∧
    Real.exp (-(32 * β * ((Fintype.card (Lat4 L) : ℕ) : ℝ))) ≤ wilsonPartitionFn N L β μ ∧
    wilsonPartitionFn N L β μ ≤ 1 := by
  have h_exp_meas : Measurable (fun U : LinkConfig N L => Real.exp (-wilsonAction N L β U)) :=
    Real.continuous_exp.measurable.comp h_meas.neg
  have h_int : Integrable (fun U : LinkConfig N L => Real.exp (-wilsonAction N L β U)) μ :=
    Integrable.of_bound h_exp_meas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun U => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact (gibbsWeight_pos_le_one hβ U).2)
  have h_lower :
      Real.exp (-(32 * β * ((Fintype.card (Lat4 L) : ℕ) : ℝ))) ≤ wilsonPartitionFn N L β μ := by
    have h_const : Real.exp (-(32 * β * ((Fintype.card (Lat4 L) : ℕ) : ℝ))) =
        ∫ _U : LinkConfig N L, Real.exp (-(32 * β * ((Fintype.card (Lat4 L) : ℕ) : ℝ))) ∂μ := by
      simp [integral_const]
    rw [h_const]
    refine integral_mono (integrable_const _) h_int fun U => ?_
    exact Real.exp_le_exp.mpr (neg_le_neg (wilsonAction_le hβ U))
  have h_upper : wilsonPartitionFn N L β μ ≤ 1 := by
    have h_one : (1 : ℝ) = ∫ _U : LinkConfig N L, (1 : ℝ) ∂μ := by simp [integral_const]
    rw [h_one]
    refine integral_mono h_int (integrable_const _) fun U => (gibbsWeight_pos_le_one hβ U).2
  exact ⟨Real.exp_pos _, h_lower, h_upper⟩

/-- Uniform norm bound `‖⟨F⟩‖ ≤ BF` for any bounded measurable observable `‖F U‖ ≤ BF`. -/
theorem wilsonExpectation_norm_le {N L : ℕ} [NeZero N] [NeZero L] {β : ℝ} (hβ : 0 ≤ β)
    [MeasurableSpace (LinkConfig N L)] (μ : Measure (LinkConfig N L)) [IsProbabilityMeasure μ]
    (h_meas : Measurable (fun U : LinkConfig N L => wilsonAction N L β U))
    (F : LinkConfig N L → ℂ) (hF_meas : Measurable F) (BF : ℝ) (hBF : 0 ≤ BF)
    (hF_bound : ∀ U, ‖F U‖ ≤ BF) :
    ‖wilsonExpectation N L β μ F‖ ≤ BF := by
  obtain ⟨hpos_lb, hZ_lb, _⟩ := wilsonPartitionFn_bounds hβ μ h_meas
  have hZ_pos : 0 < wilsonPartitionFn N L β μ := lt_of_lt_of_le hpos_lb hZ_lb
  unfold wilsonExpectation
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hZ_pos.le]
  have h_int_norm :
      ‖∫ U : LinkConfig N L, F U * (Real.exp (-wilsonAction N L β U) : ℂ) ∂μ‖ ≤
        BF * wilsonPartitionFn N L β μ := by
    have h_exp_meas : Measurable (fun U : LinkConfig N L => Real.exp (-wilsonAction N L β U)) :=
      Real.continuous_exp.measurable.comp h_meas.neg
    have h_int_exp : Integrable (fun U : LinkConfig N L => Real.exp (-wilsonAction N L β U)) μ :=
      Integrable.of_bound h_exp_meas.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun U => by
          rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact (gibbsWeight_pos_le_one hβ U).2)
    calc
      ‖∫ U, F U * (Real.exp (-wilsonAction N L β U) : ℂ) ∂μ‖
          ≤ ∫ U, ‖F U * (Real.exp (-wilsonAction N L β U) : ℂ)‖ ∂μ :=
              norm_integral_le_integral_norm _
      _ ≤ ∫ U, BF * Real.exp (-wilsonAction N L β U) ∂μ := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
              (h_int_exp.const_mul BF) (Filter.Eventually.of_forall fun U => ?_)
            dsimp only
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
            exact mul_le_mul_of_nonneg_right (hF_bound U) (Real.exp_pos _).le
      _ = BF * wilsonPartitionFn N L β μ := integral_const_mul BF _
  calc
    (wilsonPartitionFn N L β μ)⁻¹ *
        ‖∫ U, F U * (Real.exp (-wilsonAction N L β U) : ℂ) ∂μ‖
        ≤ (wilsonPartitionFn N L β μ)⁻¹ * (BF * wilsonPartitionFn N L β μ) :=
            mul_le_mul_of_nonneg_left h_int_norm (inv_nonneg.mpr hZ_pos.le)
    _ = BF := by field_simp [hZ_pos.ne']

/-- **Gauge invariance of normalized Wilson loop expectations** under any
    gauge-transformation-preserving measure `μ`. -/
theorem wilsonExpectation_gaugeInvariant
    {N L k : ℕ} [NeZero N] [NeZero L] (hk : 0 < k) (β : ℝ)
    [MeasurableSpace (LinkConfig N L)] (μ : Measure (LinkConfig N L))
    (g : GaugeTransform N L)
    (hg_mp : Measure.map (applyGauge g) μ = μ)
    (hg_meas : Measurable (applyGauge g))
    (γ : Fin k → Lat4 L × Fin 4) (hcontig : IsContiguousPath γ)
    (hclosed : (γ ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩).1 +
        stepDir L (γ ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩).2 = (γ ⟨0, hk⟩).1)
    (h_int : Integrable (fun U : LinkConfig N L =>
      (realTrace (pathHolonomy U γ) : ℂ) * (Real.exp (-wilsonAction N L β U) : ℂ)) μ) :
    wilsonExpectation N L β μ (fun U => (realTrace (pathHolonomy (applyGauge g U) γ) : ℂ)) =
      wilsonExpectation N L β μ (fun U => (realTrace (pathHolonomy U γ) : ℂ)) := by
  unfold wilsonExpectation
  congr 1
  have h_eq : (fun U : LinkConfig N L =>
      (realTrace (pathHolonomy (applyGauge g U) γ) : ℂ) * (Real.exp (-wilsonAction N L β U) : ℂ)) =
      (fun U : LinkConfig N L =>
        (realTrace (pathHolonomy U γ) : ℂ) * (Real.exp (-wilsonAction N L β U) : ℂ)) := by
    ext U
    rw [wilsonLoop_gaugeInvariant hk g U γ hcontig hclosed]
  rw [h_eq]

end Imscribing.YangMills.WilsonMeasure4D