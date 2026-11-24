import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.MetricSpace.Basic

/-!
# Semigroup Decay → Global Spectral Gap, Vacuum Uniqueness & Non-Triviality

Unconditional proofs upgrading Euclidean contraction semigroup decay on Ω⊥ to:
1. Uniqueness of the vacuum (fixed vectors of T(t) lie in ℂ ∙ Ω),
2. Full-Hilbert-space generator gap
   (Δ ‖ψ‖² ≤ Re ⟨ψ, Hψ⟩ for all ψ ∈ D(H) ∩ Ω⊥),
3. Hilbert space non-triviality (H ⊋ ℂ ∙ Ω)
   from positive connected variance,
4. Disjoint-support collapse of diagonal/equality-class kernels
   (formalizing why iidSchwinger vanishes on separated smeared test
   functions).
-/

namespace Imscribing.YangMills.SemigroupGapBridge

open scoped InnerProductSpace Topology

section HilbertGap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Vacuum uniqueness from semigroup decay on Ω⊥.**
    If `T t` fixes `Ω`, contracts `Ω⊥` by `exp (-Δ t)`, and fixes `ψ` at some `t > 0`,
    then `ψ ∈ ℂ ∙ Ω`. -/
theorem vacuum_unique_of_semigroup_decay
    (T : ℝ → H →L[ℂ] H) (Ω : H) (hΩ : ‖Ω‖ = 1) (Δ : ℝ) (hΔ : 0 < Δ)
    (hT_vac : ∀ t : ℝ, 0 ≤ t → T t Ω = Ω)
    (hT_decay : ∀ t : ℝ, 0 ≤ t → ∀ φ : H, ⟪Ω, φ⟫_ℂ = 0 →
      ‖T t φ‖ ≤ Real.exp (-Δ * t) * ‖φ‖)
    {t : ℝ} (ht : 0 < t) {ψ : H} (hfix : T t ψ = ψ) :
    ψ = ⟪Ω, ψ⟫_ℂ • Ω := by
  set c : ℂ := ⟪Ω, ψ⟫_ℂ
  set φ : H := ψ - c • Ω
  have h_orth : ⟪Ω, φ⟫_ℂ = 0 := by
    simp only [φ, inner_sub_right, inner_smul_right, c]
    have h1 : ⟪Ω, Ω⟫_ℂ = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, hΩ]
      norm_num
    rw [h1]
    ring
  have h_fix_perp : T t φ = φ := by
    simp only [φ, map_sub, map_smul, hfix, hT_vac t ht.le]
  have h_bound := hT_decay t ht.le φ h_orth
  rw [h_fix_perp] at h_bound
  have hexp_lt : Real.exp (-Δ * t) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hnorm_zero : ‖φ‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖φ‖ := lt_of_le_of_ne (norm_nonneg φ) (Ne.symm hne)
    nlinarith
  have hφ0 : φ = 0 := norm_eq_zero.mp hnorm_zero
  exact sub_eq_zero.mp hφ0

/-- **Full-space generator spectral gap from exponential semigroup decay.**
    For any `ψ ⊥ Ω` in the domain of the semigroup generator `H_op ψ = lim_{t→0⁺} (ψ - T t ψ)/t`,
    `Δ * ‖ψ‖² ≤ Re ⟨ψ, H_op ψ⟩`. -/
theorem generator_gap_of_semigroup_decay
    (T : ℝ → H →L[ℂ] H) (Ω : H) (Δ : ℝ)
    (hT_decay : ∀ t : ℝ, 0 ≤ t → ∀ ψ : H, ⟪Ω, ψ⟫_ℂ = 0 →
      ‖T t ψ‖ ≤ Real.exp (-Δ * t) * ‖ψ‖)
    {ψ Hψ : H} (h_orth : ⟪Ω, ψ⟫_ℂ = 0)
    (h_gen : Filter.Tendsto (fun t : ℝ => (t⁻¹ : ℂ) • (ψ - T t ψ)) (𝓝[>] 0) (𝓝 Hψ)) :
    Δ * ‖ψ‖ ^ 2 ≤ (⟪ψ, Hψ⟫_ℂ).re := by
  have h_ineq : ∀ᶠ t : ℝ in 𝓝[>] 0,
      ((1 - Real.exp (-Δ * t)) / t) * ‖ψ‖ ^ 2 ≤
        (⟪ψ, (t⁻¹ : ℂ) • (ψ - T t ψ)⟫_ℂ).re := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have h_cs : (⟪ψ, T t ψ⟫_ℂ).re ≤ ‖ψ‖ * ‖T t ψ‖ :=
      le_trans (RCLike.re_le_norm _) (norm_inner_le_norm ψ (T t ψ))
    have h_dec := hT_decay t ht.le ψ h_orth
    have h_re_T : (⟪ψ, T t ψ⟫_ℂ).re ≤ Real.exp (-Δ * t) * ‖ψ‖ ^ 2 := by
      have hψnn : 0 ≤ ‖ψ‖ := norm_nonneg ψ
      nlinarith [sq ‖ψ‖]
    have h_self : (⟪ψ, ψ⟫_ℂ).re = ‖ψ‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    have h_rhs : (⟪ψ, (t⁻¹ : ℂ) • (ψ - T t ψ)⟫_ℂ).re =
        t⁻¹ * (‖ψ‖ ^ 2 - (⟪ψ, T t ψ⟫_ℂ).re) := by
      rw [inner_smul_right, inner_sub_right]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.sub_re, h_self]
      have hinv : ((t⁻¹ : ℂ)).re = t⁻¹ := by simp
      have hinv_im : ((t⁻¹ : ℂ)).im = 0 := by simp
      simp [Complex.mul_re, hinv, hinv_im]
    rw [h_rhs, div_mul_eq_mul_div, div_eq_inv_mul]
    have ht_inv_pos : 0 < t⁻¹ := inv_pos.mpr ht
    nlinarith
  have h_deriv : HasDerivAt (fun t : ℝ => Real.exp (-Δ * t)) (-Δ) 0 := by
    have hd : HasDerivAt (fun t : ℝ => -Δ * t) (-Δ) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (-Δ)
    simpa using hd.exp
  have h_slope : Filter.Tendsto (fun t : ℝ => t⁻¹ * (Real.exp (-Δ * t) - 1)) (𝓝[>] 0) (𝓝 (-Δ)) := by
    simpa using h_deriv.tendsto_slope_zero_right
  have h_lhs_tend : Filter.Tendsto (fun t : ℝ => ((1 - Real.exp (-Δ * t)) / t) * ‖ψ‖ ^ 2)
      (𝓝[>] 0) (𝓝 (Δ * ‖ψ‖ ^ 2)) := by
    have h_neg : Filter.Tendsto (fun t : ℝ => (1 - Real.exp (-Δ * t)) / t) (𝓝[>] 0) (𝓝 Δ) := by
      have h_eq : (fun t : ℝ => (1 - Real.exp (-Δ * t)) / t) =
          (fun t : ℝ => -(t⁻¹ * (Real.exp (-Δ * t) - 1))) := by
        ext t; ring
      rw [h_eq]
      simpa using h_slope.neg
    simpa using h_neg.mul_const (‖ψ‖ ^ 2)
  have h_rhs_tend : Filter.Tendsto (fun t : ℝ => (⟪ψ, (t⁻¹ : ℂ) • (ψ - T t ψ)⟫_ℂ).re)
      (𝓝[>] 0) (𝓝 (⟪ψ, Hψ⟫_ℂ).re) := by
    have h_inner : Filter.Tendsto (fun t : ℝ => ⟪ψ, (t⁻¹ : ℂ) • (ψ - T t ψ)⟫_ℂ)
        (𝓝[>] 0) (𝓝 ⟪ψ, Hψ⟫_ℂ) :=
      ((innerSL ℂ ψ).continuous.tendsto Hψ).comp h_gen
    exact (Complex.continuous_re.tendsto _).comp h_inner
  exact le_of_tendsto_of_tendsto h_lhs_tend h_rhs_tend h_ineq

/-- **Hilbert space non-triviality from strict variance.**
    Any state `S` with `‖⟨Ω, S⟩‖ < ‖S‖` produces a nonzero vector orthogonal to `Ω`. -/
theorem nontrivial_orth_of_strict_variance
    (Ω S : H) (hΩ : ‖Ω‖ = 1) (hvar : ‖⟪Ω, S⟫_ℂ‖ < ‖S‖) :
    ∃ ψ : H, ⟪Ω, ψ⟫_ℂ = 0 ∧ ψ ≠ 0 := by
  refine ⟨S - ⟪Ω, S⟫_ℂ • Ω, ?_, ?_⟩
  · rw [inner_sub_right, inner_smul_right]
    have h1 : ⟪Ω, Ω⟫_ℂ = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, hΩ]
      norm_num
    rw [h1]
    ring
  · intro hzero
    have hS : S = ⟪Ω, S⟫_ℂ • Ω := sub_eq_zero.mp hzero
    have hnorm : ‖S‖ = ‖⟪Ω, S⟫_ℂ‖ := by
      rw [hS, norm_smul, hΩ, mul_one]
    linarith

end HilbertGap

section DiagonalCollapse

/-- **Disjoint-support collapse of diagonal/equality-class kernels.**
    Any 2-point kernel supported solely on coincident points (`x = y`) vanishes
    identically on every pair of disjointly supported test functions `f, g`.
    This formally separates `iidSchwinger` from genuine QFT Schwinger distributions. -/
theorem diagonal_kernel_vanishes_on_disjoint_supports
    {α : Type*} (S : (Fin 2 → α) → ℂ)
    (hdiag : ∀ x y : α, x ≠ y → S ![x, y] = 0)
    (f g : α → ℂ) (hdisj : Disjoint (Function.support f) (Function.support g)) :
    ∀ x y : α, S ![x, y] * f x * g y = 0 := by
  intro x y
  by_cases hxy : x = y
  · subst hxy
    by_cases hf : f x = 0
    · simp [hf]
    · have hg : g x = 0 := by
        by_contra hgnz
        have hx_fg : x ∈ Function.support f ∩ Function.support g :=
          ⟨Function.mem_support.mpr hf, Function.mem_support.mpr hgnz⟩
        exact (Set.disjoint_iff_inter_eq_empty.mp hdisj).subset hx_fg
      simp [hg]
  · simp [hdiag x y hxy]

end DiagonalCollapse

end Imscribing.YangMills.SemigroupGapBridge