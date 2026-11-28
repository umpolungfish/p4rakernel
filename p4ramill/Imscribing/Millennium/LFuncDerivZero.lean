import Mathlib

/-!
# LFuncDerivZero: rung-1 core of the Stark ladder

For an even function `Φ : ZMod N → ℂ` vanishing at 0 with `∑ Φ = 0`:

* `completedLFunction_zero_eq`: `Λ(Φ, 0) = 2 · L′(0, Φ)` (pole cancellation).
* `lfunction_deriv_zero_eq`: `2 · L′(0, Φ) = L(1, 𝓕 Φ)` (functional equation).

Together: **L′(0, Φ) = L(1, 𝓕 Φ)/2.**
-/

open Complex Real Filter HurwitzZeta ZMod
open scoped Topology
noncomputable section

namespace LFuncDerivZero

variable {N : ℕ} [NeZero N]

/-- Rung 1, core lemma (pole cancellation): for even `Φ` vanishing at 0 with
`∑ Φ = 0`, the completed L-function at `s = 0` equals `2 · L′(0, Φ)`. -/
theorem completedLFunction_zero_eq {Φ : ZMod N → ℂ} (hΦ : Φ.Even) (h0 : Φ 0 = 0)
    (hsum : ∑ j, Φ j = 0) :
    ZMod.completedLFunction Φ 0 = 2 * deriv (ZMod.LFunction Φ) 0 := by
  have hLdiff : DifferentiableAt ℂ (ZMod.LFunction Φ) 0 :=
    ZMod.differentiableAt_LFunction Φ 0 (Or.inl (by norm_num : (0:ℂ) ≠ 1))
  have hL0 : ZMod.LFunction Φ 0 = 0 := by
    rw [ZMod.LFunction_apply_zero_of_even hΦ, h0]; ring
  have hΛcont : ContinuousAt (ZMod.completedLFunction Φ) 0 :=
    (ZMod.differentiableAt_completedLFunction Φ 0 (Or.inr h0) (Or.inr hsum)).continuousAt
  -- Along the punctured nbhd: s ≠ 0 and |s| < 1.
  have hsmall : ∀ᶠ s in 𝓝[≠] (0:ℂ), s ≠ 0 ∧ ‖s‖ < 1 := by
    refine Metric.mem_nhdsWithin_iff.mpr ⟨1, one_pos, ?_⟩
    rintro s ⟨h1, h2⟩
    exact ⟨h2, by simpa using Metric.mem_ball.mp h1⟩
  have hΓne : ∀ᶠ s in 𝓝[≠] (0:ℂ), Gammaℝ s ≠ 0 := by
    filter_upwards [hsmall] with s ⟨hs0, hlt⟩ h
    rw [Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, rfl⟩ := h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact hs0 (by norm_num)
    · have habs : ‖-(2 * (n:ℂ))‖ = (2:ℝ) * (n:ℝ) := by rw [norm_neg, norm_mul]; norm_num
      have hle : (2:ℝ) ≤ 2 * (n:ℝ) := by
        have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        linarith
      rw [habs] at hlt
      linarith
  -- Λ s = Γℝ s · L s eventually.
  have hrel : ∀ᶠ s in 𝓝[≠] (0:ℂ),
      ZMod.completedLFunction Φ s = Gammaℝ s * ZMod.LFunction Φ s := by
    filter_upwards [hsmall, hΓne] with s ⟨hs0, _⟩ hΓ
    have this := ZMod.LFunction_eq_completed_div_gammaFactor_even hΦ s (Or.inl hs0)
    rw [this, mul_comm]
    exact (div_mul_cancel₀ _ hΓ).symm
  -- slope tendsto: L s / s → L′(0) along the punctured nbhd.
  have hslope : Tendsto (slope (ZMod.LFunction Φ) 0)
      (𝓝 (0:ℂ) ⊓ 𝓟 {((0:ℂ))}ᶜ) (𝓝 (deriv (ZMod.LFunction Φ) 0)) :=
    hasDerivAtFilter_iff_tendsto_slope.mp hLdiff.hasDerivAt
  have hslope' : Tendsto (fun s : ℂ => ZMod.LFunction Φ s / s) (𝓝[≠] (0:ℂ))
      (𝓝 (deriv (ZMod.LFunction Φ) 0)) := by
    have heq : slope (ZMod.LFunction Φ) 0 =ᶠ[𝓝[≠] (0:ℂ)]
        fun s : ℂ => ZMod.LFunction Φ s / s := by
      filter_upwards [hsmall] with s ⟨hs0, _⟩
      simp only [slope, hL0, sub_zero, smul_eq_mul, vsub_eq_sub]
      rw [div_eq_mul_inv, mul_comm]
    rw [show (𝓝 (0:ℂ) ⊓ 𝓟 {((0:ℂ))}ᶜ) = 𝓝[≠] (0:ℂ) from rfl] at hslope
    exact hslope.congr' heq
  -- Combine: Λ s = (s · Γℝ s) · (L s / s) → 2 · L′(0).
  have hlim : Tendsto (fun s : ℂ => ZMod.completedLFunction Φ s)
      (𝓝[≠] (0:ℂ)) (𝓝 (2 * deriv (ZMod.LFunction Φ) 0)) := by
    have hsplit : (fun s : ℂ => ZMod.completedLFunction Φ s)
        =ᶠ[𝓝[≠] (0:ℂ)] fun s : ℂ => (s * Gammaℝ s) * (ZMod.LFunction Φ s / s) := by
      filter_upwards [hsmall, hrel] with s ⟨hs0, _⟩ hrel
      rw [hrel]
      have h1 : (1:ℂ) = s * s⁻¹ := (mul_inv_cancel₀ hs0).symm
      calc Gammaℝ s * ZMod.LFunction Φ s
          = 1 * (Gammaℝ s * ZMod.LFunction Φ s) := (one_mul _).symm
        _ = (s * s⁻¹) * (Gammaℝ s * ZMod.LFunction Φ s) := by rw [h1]
        _ = (s * Gammaℝ s) * (ZMod.LFunction Φ s * s⁻¹) := by ring
        _ = (s * Gammaℝ s) * (ZMod.LFunction Φ s / s) := by rw [div_eq_mul_inv]
    exact (Gammaℝ_residue_zero.mul hslope').congr' hsplit.symm
  -- Limits along 𝓝 0 and 𝓝[≠] 0 must agree.
  have hco : Tendsto (fun s : ℂ => ZMod.completedLFunction Φ s) (𝓝[≠] (0:ℂ))
      (𝓝 (ZMod.completedLFunction Φ 0)) := hΛcont.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hco hlim


/-- Rung 1, second half: the functional equation at `s = 1` turns the pole value
into the L-function of the Fourier transform at 1. -/
theorem lfunction_deriv_zero_eq {Φ : ZMod N → ℂ} (hΦ : Φ.Even) (h0 : Φ 0 = 0)
    (hsum : ∑ j, Φ j = 0) :
    2 * deriv (ZMod.LFunction Φ) 0 = ZMod.LFunction (𝓕 Φ) 1 := by
  have hFE : ZMod.completedLFunction Φ 0 = ZMod.completedLFunction (𝓕 Φ) 1 := by
    have h := ZMod.completedLFunction_one_sub_even hΦ 1 (Or.inl (by norm_num : (1:ℂ) ≠ 0))
        (Or.inr h0)
    simpa using h
  have hev : (𝓕 Φ).Even := dft_even_iff.mpr hΦ
  have hΓ := ZMod.LFunction_eq_completed_div_gammaFactor_even hev 1
    (Or.inl (by norm_num : (1:ℂ) ≠ 0))
  have h2 : ZMod.completedLFunction (𝓕 Φ) 1 = ZMod.LFunction (𝓕 Φ) 1 := by
    rw [hΓ, Gammaℝ_one, div_one]
  rw [← completedLFunction_zero_eq hΦ h0 hsum, hFE, h2]

end LFuncDerivZero

end
