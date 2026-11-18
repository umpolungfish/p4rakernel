import Mathlib

open scoped InnerProductSpace
open Real Set

private theorem norm_eq_iSup_rayleighQuotient
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    {T : V →L[ℂ] V} (hT : IsSelfAdjoint T) :
    ‖T‖ = ⨆ x : V, |T.rayleighQuotient x| := by
  have hT_sa : ∀ x y : V, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  set s : ℝ := ⨆ x : V, |T.rayleighQuotient x|
  have hbdd : BddAbove (Set.range fun x : V => |T.rayleighQuotient x|) :=
    ContinuousLinearMap.bddAbove_rayleighQuotient T
  have hs_le : s ≤ ‖T‖ := ciSup_le fun x => T.rayleighQuotient_le_norm x
  have hs_nonneg : 0 ≤ s := le_trans (abs_nonneg _) (le_ciSup hbdd 0)
  have hQ : ∀ z : V, |(⟪T z, z⟫_ℂ).re| ≤ s * ‖z‖ ^ 2 := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · have hq : |T.rayleighQuotient z| ≤ s := le_ciSup hbdd z
      have hz_sq_pos : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
      unfold ContinuousLinearMap.rayleighQuotient at hq
      simp only [ContinuousLinearMap.reApplyInnerSelf_apply] at hq
      rwa [abs_div, abs_of_pos hz_sq_pos, div_le_iff₀ hz_sq_pos] at hq
  have h_pol : ∀ u v : V,
      (⟪T (u + v), u + v⟫_ℂ).re - (⟪T (u - v), u - v⟫_ℂ).re = 4 * (⟪T u, v⟫_ℂ).re := by
    intro u v
    have h1 : ⟪T (u + v), u + v⟫_ℂ =
        ⟪T u, u⟫_ℂ + ⟪T u, v⟫_ℂ + ⟪T v, u⟫_ℂ + ⟪T v, v⟫_ℂ := by
      simp only [map_add, inner_add_left, inner_add_right]
      ring
    have h2 : ⟪T (u - v), u - v⟫_ℂ =
        ⟪T u, u⟫_ℂ - ⟪T u, v⟫_ℂ - ⟪T v, u⟫_ℂ + ⟪T v, v⟫_ℂ := by
      simp only [map_sub, inner_sub_left, inner_sub_right]
      ring
    have hsym : (⟪T v, u⟫_ℂ).re = (⟪T u, v⟫_ℂ).re := by
      rw [hT_sa v u]
      exact congrArg Complex.re (inner_conj_symm (T u) v).symm
    rw [h1, h2]
    simp only [Complex.add_re, Complex.sub_re, hsym]
    ring
  have h_para : ∀ u v : V, ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
    intro u v
    rw [norm_add_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ)]
    ring
  have h_cross : ∀ u v : V,
      4 * |(⟪T u, v⟫_ℂ).re| ≤ s * (2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2) := by
    intro u v
    have h4 : 4 * |(⟪T u, v⟫_ℂ).re| =
        |(⟪T (u + v), u + v⟫_ℂ).re - (⟪T (u - v), u - v⟫_ℂ).re| := by
      rw [h_pol u v, abs_mul]
      norm_num
    rw [h4]
    calc |(⟪T (u + v), u + v⟫_ℂ).re - (⟪T (u - v), u - v⟫_ℂ).re|
        ≤ |(⟪T (u + v), u + v⟫_ℂ).re| + |(⟪T (u - v), u - v⟫_ℂ).re| := abs_sub _ _
      _ ≤ s * ‖u + v‖ ^ 2 + s * ‖u - v‖ ^ 2 := add_le_add (hQ (u + v)) (hQ (u - v))
      _ = s * (‖u + v‖ ^ 2 + ‖u - v‖ ^ 2) := by ring
      _ = s * (2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2) := by rw [h_para]
  have h_le : ‖T‖ ≤ s := by
    refine ContinuousLinearMap.opNorm_le_bound T hs_nonneg fun x => ?_
    by_cases hx : x = 0
    · simp [hx]
    · by_cases hTx : T x = 0
      · simp [hTx]; positivity
      · have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
        have hTx_pos : 0 < ‖T x‖ := norm_pos_iff.mpr hTx
        let v : V := ((‖x‖ / ‖T x‖ : ℝ) : ℂ) • T x
        have hv_norm : ‖v‖ = ‖x‖ := by
          simp only [v, norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (div_pos hx_pos hTx_pos)]
          exact div_mul_cancel₀ _ hTx_pos.ne'
        have h_inner_val : (⟪T x, v⟫_ℂ).re = ‖x‖ * ‖T x‖ := by
          simp only [v, inner_smul_right, inner_self_eq_norm_sq_to_K]
          have hpow : (((‖T x‖ : ℂ) ^ 2).re) = ‖T x‖ ^ 2 := by
            rw [← Complex.ofReal_pow, Complex.ofReal_re]
          have him : (((‖T x‖ : ℂ) ^ 2).im) = 0 := by
            rw [← Complex.ofReal_pow, Complex.ofReal_im]
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hpow, him,
            zero_mul, sub_zero]
          field_simp [hTx_pos.ne']
        have hc := h_cross x v
        rw [hv_norm, h_inner_val, abs_of_nonneg (mul_nonneg hx_pos.le hTx_pos.le)] at hc
        have hmul : ‖x‖ * ‖T x‖ ≤ ‖x‖ * (s * ‖x‖) := by linarith
        exact le_of_mul_le_mul_left hmul hx_pos
  exact le_antisymm h_le hs_le
