import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Quantitative Doeblin–Perron–Frobenius L² Spectral Gap

Proves unconditionally (`0 sorry`):
If `K : α → α → ℝ` is a bounded jointly-measurable symmetric Markov kernel on a
probability space `(α, π)` satisfying the minorization `0 < ε ≤ K x y`, then for
every bounded measurable mean-zero observable `φ : α → ℂ` (`∫ φ dπ = 0`),
`∫ ‖(T_K φ) x‖² dπ ≤ (1 - ε)² ∫ ‖φ‖² dπ ≤ exp(-2ε) ∫ ‖φ‖² dπ`.
-/

namespace Imscribing.YangMills.DoeblinGap

open MeasureTheory

/-- Quadratic Jensen inequality `(∫ R y * ‖φ y‖ dπ)² ≤ c * ∫ R y * ‖φ y‖² dπ`
    for any nonnegative bounded kernel `R ≥ 0` with `∫ R dπ = c`. -/
theorem unnormalized_jensen_sq_le {α : Type*} [MeasurableSpace α]
    (π : Measure α) [IsProbabilityMeasure π]
    (R : α → ℝ) (hR_nn : ∀ y, 0 ≤ R y) (hR_meas : Measurable R)
    (BR : ℝ) (hR_bound : ∀ y, R y ≤ BR)
    {c : ℝ} (hc_nn : 0 ≤ c) (hR_mass : ∫ y, R y ∂π = c)
    (φ : α → ℂ) (hφ_meas : Measurable φ) (Bφ : ℝ) (hφ_bound : ∀ y, ‖φ y‖ ≤ Bφ) :
    (∫ y, R y * ‖φ y‖ ∂π) ^ 2 ≤ c * ∫ y, R y * ‖φ y‖ ^ 2 ∂π := by
  haveI : Nonempty α := by
    by_contra h
    have hU : (Set.univ : Set α) = ∅ := Set.ext fun x => ⟨fun _ => h ⟨x⟩, False.elim⟩
    have h1 : π Set.univ = 1 := measure_univ
    rw [hU, measure_empty] at h1
    exact zero_ne_one h1
  have hBφ_nn : 0 ≤ Bφ := le_trans (norm_nonneg _) (hφ_bound (Classical.arbitrary α))
  have hBR_nn : 0 ≤ BR := le_trans (hR_nn _) (hR_bound (Classical.arbitrary α))
  have hR_int : Integrable R π :=
    Integrable.of_bound hR_meas.aestronglyMeasurable BR
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_of_nonneg (hR_nn y)]; exact hR_bound y)
  have hR1_int : Integrable (fun y => R y * ‖φ y‖) π :=
    Integrable.of_bound (hR_meas.mul (continuous_norm.measurable.comp hφ_meas)).aestronglyMeasurable
      (BR * Bφ) (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (mul_nonneg (hR_nn y) (norm_nonneg _))]
        exact mul_le_mul (hR_bound y) (hφ_bound y) (norm_nonneg _) hBR_nn)
  have hR2_int : Integrable (fun y => R y * ‖φ y‖ ^ 2) π :=
    Integrable.of_bound
      (hR_meas.mul ((continuous_norm.measurable.comp hφ_meas).pow_const 2)).aestronglyMeasurable
      (BR * Bφ ^ 2) (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (mul_nonneg (hR_nn y) (sq_nonneg _))]
        exact mul_le_mul (hR_bound y) (pow_le_pow_left₀ (norm_nonneg _) (hφ_bound y) 2)
          (sq_nonneg _) hBR_nn)
  by_cases hc0 : c = 0
  · subst hc0
    have h_le : ∫ y, R y * ‖φ y‖ ∂π ≤ Bφ * ∫ y, R y ∂π := by
      rw [← integral_const_mul]
      exact integral_mono hR1_int (hR_int.const_mul Bφ) fun y => by
        rw [mul_comm Bφ]; exact mul_le_mul_of_nonneg_left (hφ_bound y) (hR_nn y)
    have h_ge : 0 ≤ ∫ y, R y * ‖φ y‖ ∂π := integral_nonneg fun y => mul_nonneg (hR_nn y) (norm_nonneg _)
    rw [hR_mass, mul_zero] at h_le
    have h0 : ∫ y, R y * ‖φ y‖ ∂π = 0 := le_antisymm h_le h_ge
    rw [h0, zero_pow (by norm_num), zero_mul]
  · have hc_pos : 0 < c := lt_of_le_of_ne hc_nn (Ne.symm hc0)
    set s : ℝ := ∫ y, R y * ‖φ y‖ ∂π
    have h_quad_nn : 0 ≤ ∫ y, (s ^ 2 * R y - 2 * s * c * (R y * ‖φ y‖) + c ^ 2 * (R y * ‖φ y‖ ^ 2)) ∂π := by
      refine integral_nonneg fun y => ?_
      have h_sq : s ^ 2 * R y - 2 * s * c * (R y * ‖φ y‖) + c ^ 2 * (R y * ‖φ y‖ ^ 2) =
          R y * (s - c * ‖φ y‖) ^ 2 := by ring
      rw [h_sq]
      exact mul_nonneg (hR_nn y) (sq_nonneg _)
    have h_expand :
        (∫ y, (s ^ 2 * R y - 2 * s * c * (R y * ‖φ y‖) + c ^ 2 * (R y * ‖φ y‖ ^ 2)) ∂π) =
          s ^ 2 * (∫ y, R y ∂π) - 2 * s * c * (∫ y, R y * ‖φ y‖ ∂π) +
            c ^ 2 * (∫ y, R y * ‖φ y‖ ^ 2 ∂π) := by
      have h1 := integral_add ((hR_int.const_mul (s ^ 2)).sub (hR1_int.const_mul (2 * s * c))) (hR2_int.const_mul (c ^ 2))
      have h2 := integral_sub (hR_int.const_mul (s ^ 2)) (hR1_int.const_mul (2 * s * c))
      simp only [Pi.sub_apply] at h1 h2
      rw [h1, h2,
          integral_const_mul, integral_const_mul, integral_const_mul]
    rw [h_expand, hR_mass] at h_quad_nn
    change 0 ≤ s ^ 2 * c - 2 * s * c * s + c ^ 2 * ∫ y, R y * ‖φ y‖ ^ 2 ∂π at h_quad_nn
    have h_fac : c * (c * (∫ y, R y * ‖φ y‖ ^ 2 ∂π) - s ^ 2) =
        s ^ 2 * c - 2 * s * c * s + c ^ 2 * ∫ y, R y * ‖φ y‖ ^ 2 ∂π := by ring
    rw [← h_fac] at h_quad_nn
    have h_sub_nn : 0 ≤ c * (∫ y, R y * ‖φ y‖ ^ 2 ∂π) - s ^ 2 :=
      nonneg_of_mul_nonneg_right h_quad_nn hc_pos
    linarith

/-- **Doeblin–Perron–Frobenius L² Contraction Theorem:**
    For a symmetric Markov kernel `K` with `0 < ε ≤ K x y`, every mean-zero
    bounded measurable `φ` satisfies
    `∫ ‖∫ K x y • φ y dπ(y)‖² dπ(x) ≤ (1 - ε)² ∫ ‖φ‖² dπ ≤ exp(-2ε) ∫ ‖φ‖² dπ`. -/
theorem doeblin_markov_l2_contraction
    {α : Type*} [MeasurableSpace α] (π : Measure α) [IsProbabilityMeasure π]
    (K : α → α → ℝ) (hK_meas : Measurable (Function.uncurry K))
    (BK : ℝ) (hK_bound : ∀ x y, K x y ≤ BK)
    (hK_symm : ∀ x y, K x y = K y x)
    (hK_markov : ∀ x, ∫ y, K x y ∂π = 1)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_le : ε ≤ 1) (hK_lb : ∀ x y, ε ≤ K x y)
    (φ : α → ℂ) (hφ_meas : Measurable φ) (Bφ : ℝ) (hφ_bound : ∀ y, ‖φ y‖ ≤ Bφ)
    (h_mean_zero : ∫ y, φ y ∂π = 0) :
    (∫ x, ‖∫ y, (K x y : ℂ) * φ y ∂π‖ ^ 2 ∂π) ≤
      (1 - ε) ^ 2 * ∫ y, ‖φ y‖ ^ 2 ∂π ∧
    (1 - ε) ^ 2 * ∫ y, ‖φ y‖ ^ 2 ∂π ≤
      Real.exp (-2 * ε) * ∫ y, ‖φ y‖ ^ 2 ∂π := by
  haveI : Nonempty α := by
    by_contra h
    have hU : (Set.univ : Set α) = ∅ := Set.ext fun x => ⟨fun _ => h ⟨x⟩, False.elim⟩
    have h1 : π Set.univ = 1 := measure_univ
    rw [hU, measure_empty] at h1
    exact zero_ne_one h1
  have hBφ_nn : 0 ≤ Bφ := le_trans (norm_nonneg _) (hφ_bound (Classical.arbitrary α))
  have hBK_nn : 0 ≤ BK :=
    le_trans hε_pos.le (le_trans (hK_lb (Classical.arbitrary α) (Classical.arbitrary α)) (hK_bound _ _))
  have hφ_int : Integrable φ π :=
    Integrable.of_bound hφ_meas.aestronglyMeasurable Bφ (Filter.Eventually.of_forall hφ_bound)
  have hφ2_int : Integrable (fun y => ‖φ y‖ ^ 2) π :=
    Integrable.of_bound ((continuous_norm.measurable.comp hφ_meas).pow_const 2).aestronglyMeasurable
      (Bφ ^ 2) (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hφ_bound y) 2)
  have h_phi2_nn : 0 ≤ ∫ y, ‖φ y‖ ^ 2 ∂π := integral_nonneg fun _ => sq_nonneg _
  have h_exp_bd : (1 - ε) ^ 2 * ∫ y, ‖φ y‖ ^ 2 ∂π ≤ Real.exp (-2 * ε) * ∫ y, ‖φ y‖ ^ 2 ∂π := by
    have h1 : 1 - ε ≤ Real.exp (-ε) := by linarith [Real.add_one_le_exp (-ε)]
    have h2 : (1 - ε) ^ 2 ≤ (Real.exp (-ε)) ^ 2 :=
      pow_le_pow_left₀ (sub_nonneg.mpr hε_le) h1 2
    have h3 : (Real.exp (-ε)) ^ 2 = Real.exp (-2 * ε) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h3] at h2
    exact mul_le_mul_of_nonneg_right h2 h_phi2_nn
  refine ⟨?_, h_exp_bd⟩
  let R : α → α → ℝ := fun x y => K x y - ε
  have hR_nn : ∀ x y, 0 ≤ R x y := fun x y => sub_nonneg.mpr (hK_lb x y)
  have hR_bound : ∀ x y, R x y ≤ BK := fun x y => by dsimp [R]; linarith [hK_bound x y]
  have hR_meas : Measurable (Function.uncurry R) := hK_meas.sub measurable_const
  have hR_meas_y : ∀ x, Measurable (R x) := fun x =>
    hR_meas.comp (measurable_const.prodMk measurable_id)
  have hR_mass : ∀ x, ∫ y, R x y ∂π = 1 - ε := by
    intro x
    have hK_int_x : Integrable (K x) π :=
      Integrable.of_bound ((hK_meas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
        BK (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_of_nonneg (le_trans hε_pos.le (hK_lb x y))]; exact hK_bound x y)
    dsimp [R]
    rw [integral_sub hK_int_x (integrable_const ε), hK_markov x, integral_const]
    simp
  have h_sub_eq : ∀ x, (∫ y, (K x y : ℂ) * φ y ∂π) = ∫ y, (R x y : ℂ) * φ y ∂π := by
    intro x
    have hR_int_phi : Integrable (fun y => (R x y : ℂ) * φ y) π :=
      Integrable.of_bound
        ((Complex.continuous_ofReal.measurable.comp (hR_meas_y x)).mul hφ_meas).aestronglyMeasurable
        (BK * Bφ) (Filter.Eventually.of_forall fun y => by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hR_nn x y)]
          exact mul_le_mul (hR_bound x y) (hφ_bound y) (norm_nonneg _) hBK_nn)
    have h_eq_fn : (fun y => (K x y : ℂ) * φ y) =
        (fun y => (ε : ℂ) * φ y + (R x y : ℂ) * φ y) := by
      ext y; dsimp [R]; push_cast; ring
    rw [h_eq_fn, integral_add (hφ_int.const_mul (ε : ℂ)) hR_int_phi,
        integral_const_mul, h_mean_zero, mul_zero, zero_add]
  have h_pt_le : ∀ x,
      ‖∫ y, (K x y : ℂ) * φ y ∂π‖ ^ 2 ≤ (1 - ε) * ∫ y, R x y * ‖φ y‖ ^ 2 ∂π := by
    intro x
    rw [h_sub_eq x]
    have hR_int_norm : Integrable (fun y => R x y * ‖φ y‖) π :=
      Integrable.of_bound ((hR_meas_y x).mul (continuous_norm.measurable.comp hφ_meas)).aestronglyMeasurable
        (BK * Bφ) (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_of_nonneg (mul_nonneg (hR_nn x y) (norm_nonneg _))]
          exact mul_le_mul (hR_bound x y) (hφ_bound y) (norm_nonneg _) hBK_nn)
    have h_norm_le : ‖∫ y, (R x y : ℂ) * φ y ∂π‖ ≤ ∫ y, R x y * ‖φ y‖ ∂π := by
      calc
        ‖∫ y, (R x y : ℂ) * φ y ∂π‖ ≤ ∫ y, ‖(R x y : ℂ) * φ y‖ ∂π :=
            norm_integral_le_integral_norm _
        _ = ∫ y, R x y * ‖φ y‖ ∂π := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
            dsimp only; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hR_nn x y)]
    have h_sq_le : ‖∫ y, (R x y : ℂ) * φ y ∂π‖ ^ 2 ≤ (∫ y, R x y * ‖φ y‖ ∂π) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h_norm_le 2
    exact le_trans h_sq_le (unnormalized_jensen_sq_le π (R x) (hR_nn x) (hR_meas_y x)
      BK (hR_bound x) (sub_nonneg.mpr hε_le) (hR_mass x) φ hφ_meas Bφ hφ_bound)
  have h_prod_int : Integrable (Function.uncurry fun x y => R x y * ‖φ y‖ ^ 2) (π.prod π) := by
    have hm : Measurable (Function.uncurry fun x y => R x y * ‖φ y‖ ^ 2) :=
      hR_meas.mul (((continuous_norm.measurable.comp hφ_meas).pow_const 2).comp measurable_snd)
    refine Integrable.of_bound hm.aestronglyMeasurable (BK * Bφ ^ 2)
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Function.uncurry_apply_pair, Real.norm_of_nonneg (mul_nonneg (hR_nn p.1 p.2) (sq_nonneg _))]
    exact mul_le_mul (hR_bound p.1 p.2) (pow_le_pow_left₀ (norm_nonneg _) (hφ_bound p.2) 2)
      (sq_nonneg _) hBK_nn
  have h_lhs_int : Integrable (fun x => ‖∫ y, (K x y : ℂ) * φ y ∂π‖ ^ 2) π := by
    have hm_in : Measurable (fun x => ∫ y, (K x y : ℂ) * φ y ∂π) :=
      (MeasureTheory.StronglyMeasurable.integral_prod_right' (ν := π) ((Complex.continuous_ofReal.measurable.comp hK_meas).mul (hφ_meas.comp measurable_snd)).stronglyMeasurable).measurable
    refine Integrable.of_bound ((continuous_norm.measurable.comp hm_in).pow_const 2).aestronglyMeasurable
      ((BK * Bφ) ^ 2) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h_in_le : ‖∫ y, (K x y : ℂ) * φ y ∂π‖ ≤ BK * Bφ := by
      calc
        ‖∫ y, (K x y : ℂ) * φ y ∂π‖ ≤ ∫ y, ‖(K x y : ℂ) * φ y‖ ∂π :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ _y, (BK * Bφ) ∂π := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
              (integrable_const _) (Filter.Eventually.of_forall fun y => ?_)
            dsimp only; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_trans hε_pos.le (hK_lb x y))]
            exact mul_le_mul (hK_bound x y) (hφ_bound y) (norm_nonneg _) hBK_nn
        _ = BK * Bφ := by simp [integral_const]
    exact pow_le_pow_left₀ (norm_nonneg _) h_in_le 2
  have h_rhs_int : Integrable (fun x => (1 - ε) * ∫ y, R x y * ‖φ y‖ ^ 2 ∂π) π :=
    (h_prod_int.integral_prod_left).const_mul (1 - ε)
  calc
    (∫ x, ‖∫ y, (K x y : ℂ) * φ y ∂π‖ ^ 2 ∂π)
        ≤ ∫ x, (1 - ε) * ∫ y, R x y * ‖φ y‖ ^ 2 ∂π ∂π :=
            integral_mono h_lhs_int h_rhs_int h_pt_le
    _ = (1 - ε) * ∫ x, ∫ y, R x y * ‖φ y‖ ^ 2 ∂π ∂π := integral_const_mul _ _
    _ = (1 - ε) * ∫ y, ∫ x, R x y * ‖φ y‖ ^ 2 ∂π ∂π := by rw [integral_integral_swap h_prod_int]
    _ = (1 - ε) * ∫ y, (∫ x, R x y ∂π) * ‖φ y‖ ^ 2 ∂π := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          exact integral_mul_const _ _
    _ = (1 - ε) * ∫ y, (1 - ε) * ‖φ y‖ ^ 2 ∂π := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          dsimp only
          have h_symm_R : (fun x => R x y) = R y := by
            ext x; simp [R, hK_symm x y]
          rw [h_symm_R, hR_mass y]
    _ = (1 - ε) ^ 2 * ∫ y, ‖φ y‖ ^ 2 ∂π := by
          rw [integral_const_mul]; ring

end Imscribing.YangMills.DoeblinGap