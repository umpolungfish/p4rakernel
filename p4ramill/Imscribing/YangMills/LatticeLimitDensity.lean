import Mathlib
import Imscribing.YangMills.SUNHaar

open scoped BigOperators ENNReal NNReal Matrix
open MeasureTheory Matrix

noncomputable section

namespace YangMills

/-! ## Elementary Measure-Zero Helpers on `(0, 2π)` and Left-Haar Fubini -/

section Helpers

lemma volume_trig_zero_set_eq_zero (a b : ℂ) (hab : a ≠ 0 ∨ b ≠ 0) :
    volume {θ : ℝ | θ ∈ Set.Ioo 0 (2 * Real.pi) ∧
      (Real.cos θ : ℂ) * a + (Real.sin θ : ℂ) * b = 0} = 0 := by
  set S : Set ℝ := {θ : ℝ | θ ∈ Set.Ioo 0 (2 * Real.pi) ∧
    (Real.cos θ : ℂ) * a + (Real.sin θ : ℂ) * b = 0}
  by_cases hne : S.Nonempty
  · obtain ⟨θ₀, hθ₀_mem, hθ₀_eq⟩ := hne
    have hsub : S ⊆ {θ₀ - Real.pi, θ₀, θ₀ + Real.pi} := by
      intro θ ⟨hθ_mem, hθ_eq⟩
      have hsin_eq : (Real.sin (θ - θ₀) : ℂ) = 0 := by
        have htrig : (Real.sin (θ - θ₀) : ℂ) =
            (Real.sin θ : ℂ) * (Real.cos θ₀ : ℂ) - (Real.cos θ : ℂ) * (Real.sin θ₀ : ℂ) := by
          push_cast [Real.sin_sub]; ring
        have hc : (Real.sin (θ - θ₀) : ℂ) * a = 0 := by
          have h1 := congrArg (· * (Real.sin θ₀ : ℂ)) hθ_eq
          have h2 := congrArg (· * (Real.sin θ : ℂ)) hθ₀_eq
          have hsub_eq := congrArg₂ (· - ·) h1 h2
          simp only [zero_mul, sub_zero] at hsub_eq
          linear_combination -hsub_eq + htrig * a
        have hs : (Real.sin (θ - θ₀) : ℂ) * b = 0 := by
          have h1 := congrArg (· * (Real.cos θ₀ : ℂ)) hθ_eq
          have h2 := congrArg (· * (Real.cos θ : ℂ)) hθ₀_eq
          have hsub_eq := congrArg₂ (· - ·) h1 h2
          simp only [zero_mul, sub_zero] at hsub_eq
          linear_combination hsub_eq + htrig * b
        rcases hab with ha | hb
        · exact mul_eq_zero.mp hc |>.resolve_right ha
        · exact mul_eq_zero.mp hs |>.resolve_right hb
      have hsinR : Real.sin (θ - θ₀) = 0 := Complex.ofReal_eq_zero.mp hsin_eq
      rw [Real.sin_eq_zero_iff] at hsinR
      obtain ⟨k, hk⟩ := hsinR
      have hkR : θ - θ₀ = (k : ℝ) * Real.pi := hk.symm
      have hk_gt : (-2 : ℝ) < k := by
        have : -(2 * Real.pi) < (k : ℝ) * Real.pi := by rw [hk]; linarith [hθ_mem.1, hθ₀_mem.2]
        nlinarith [Real.pi_pos]
      have hk_lt : (k : ℝ) < 2 := by
        have : (k : ℝ) * Real.pi < 2 * Real.pi := by rw [hk]; linarith [hθ_mem.2, hθ₀_mem.1]
        nlinarith [Real.pi_pos]
      have hk_int : k = -1 ∨ k = 0 ∨ k = 1 := by
        have : -2 < k ∧ k < 2 := ⟨by exact_mod_cast hk_gt, by exact_mod_cast hk_lt⟩
        omega
      rcases hk_int with (hk₁) | (hk₁) | (hk₁)
      · left
        have h₂ : k = -1 := hk₁
        have h₃ : θ - θ₀ = (k : ℝ) * Real.pi := hkR
        rw [h₂] at h₃
        norm_num at h₃
        have h : θ = θ₀ - Real.pi := by linarith
        simpa using h
      · right; left
        have h₂ : k = 0 := hk₁
        have h₃ : θ - θ₀ = (k : ℝ) * Real.pi := hkR
        rw [h₂] at h₃
        norm_num at h₃
        have h : θ = θ₀ := by linarith
        simpa using h
      · right; right
        have h₂ : k = 1 := hk₁
        have h₃ : θ - θ₀ = (k : ℝ) * Real.pi := hkR
        rw [h₂] at h₃
        norm_num at h₃
        have h : θ = θ₀ + Real.pi := by linarith
        simpa using h
    have hfin : S.Finite :=
      (Set.Finite.insert _ (Set.Finite.insert _ (Set.finite_singleton _))).subset hsub
    exact hfin.measure_zero volume
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]

lemma volume_exp_two_eq_zero (z : ℂ) :
    volume {θ : ℝ | θ ∈ Set.Ioo 0 (2 * Real.pi) ∧
      Complex.exp (2 * Complex.I * (θ : ℂ)) = z} = 0 := by
  set S : Set ℝ := {θ : ℝ | θ ∈ Set.Ioo 0 (2 * Real.pi) ∧
    Complex.exp (2 * Complex.I * (θ : ℂ)) = z}
  by_cases hne : S.Nonempty
  · obtain ⟨θ₀, hθ₀_mem, hθ₀_eq⟩ := hne
    have hsub : S ⊆ {θ₀ - Real.pi, θ₀, θ₀ + Real.pi} := by
      intro θ ⟨hθ_mem, hθ_eq⟩
      have hexp : Complex.exp (2 * Complex.I * (θ : ℂ)) = Complex.exp (2 * Complex.I * (θ₀ : ℂ)) :=
        hθ_eq.trans hθ₀_eq.symm
      rw [Complex.exp_eq_exp_iff_exists_int] at hexp
      obtain ⟨k, hk⟩ := hexp
      have hk' : (2 : ℂ) * Complex.I * ((θ - θ₀ : ℝ) : ℂ) =
          (k : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; linear_combination hk
      have hdiff : ((θ - θ₀ : ℝ) : ℂ) = ((k : ℝ) * Real.pi : ℂ) := by
        have h2I : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
        calc ((θ - θ₀ : ℝ) : ℂ)
            = ((2 : ℂ) * Complex.I)⁻¹ * ((2 : ℂ) * Complex.I * ((θ - θ₀ : ℝ) : ℂ)) := by field_simp
          _ = ((2 : ℂ) * Complex.I)⁻¹ * ((k : ℂ) * (2 * Real.pi * Complex.I)) := by rw [hk']
          _ = ((k : ℝ) * Real.pi : ℂ) := by push_cast; field_simp
      have hkR : θ - θ₀ = (k : ℝ) * Real.pi := Complex.ofReal_injective (by simpa using hdiff)
      have hk_gt : (-2 : ℝ) < k := by
        have : -(2 * Real.pi) < (k : ℝ) * Real.pi := by rw [← hkR]; linarith [hθ_mem.1, hθ₀_mem.2]
        nlinarith [Real.pi_pos]
      have hk_lt : (k : ℝ) < 2 := by
        have : (k : ℝ) * Real.pi < 2 * Real.pi := by rw [← hkR]; linarith [hθ_mem.2, hθ₀_mem.1]
        nlinarith [Real.pi_pos]
      have hk_int : k = -1 ∨ k = 0 ∨ k = 1 := by
        have : -2 < k ∧ k < 2 := ⟨by exact_mod_cast hk_gt, by exact_mod_cast hk_lt⟩
        omega
      rcases hk_int with (hk₁) | (hk₁) | (hk₁)
      · left
        have h₂ : k = -1 := hk₁
        have h₃ : θ - θ₀ = (k : ℝ) * Real.pi := hkR
        rw [h₂] at h₃
        norm_num at h₃
        have h : θ = θ₀ - Real.pi := by linarith
        simpa using h
      · right; left
        have h₂ : k = 0 := hk₁
        have h₃ : θ - θ₀ = (k : ℝ) * Real.pi := hkR
        rw [h₂] at h₃
        norm_num at h₃
        have h : θ = θ₀ := by linarith
        simpa using h
      · right; right
        have h₂ : k = 1 := hk₁
        have h₃ : θ - θ₀ = (k : ℝ) * Real.pi := hkR
        rw [h₂] at h₃
        norm_num at h₃
        have h : θ = θ₀ + Real.pi := by linarith
        simpa using h
    have hfin : S.Finite :=
      (Set.Finite.insert _ (Set.Finite.insert _ (Set.finite_singleton _))).subset hsub
    exact hfin.measure_zero volume
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]

lemma haar_null_of_slice_null {G : Type*} [MeasurableSpace G] [Group G] [MeasurableMul G]
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    (γ : ℝ → G) (hγ_meas : Measurable (fun p : ℝ × G => γ p.1 * p.2))
    {E : Set G} (hE : MeasurableSet E)
    (hslice : ∀ V : G, volume {θ : ℝ | θ ∈ Set.Ioo 0 (2 * Real.pi) ∧ γ θ * V ∈ E} = 0) :
    μ E = 0 := by
  let lam0 : Measure ℝ := volume.restrict (Set.Ioo 0 (2 * Real.pi))
  haveI : SFinite lam0 := inferInstance
  have hlam0_pos : (lam0 Set.univ) ≠ 0 := by
    simp [lam0, Real.volume_Ioo, sub_zero, Real.pi_pos]
  have h_prod_zero : (lam0 Set.univ) * (μ E) = 0 := by
    have hmeas : Measurable (fun p : ℝ × G =>
        E.indicator (fun _ => (1 : ℝ≥0∞)) (γ p.1 * p.2)) :=
      (measurable_const.indicator hE).comp hγ_meas
    calc
      (lam0 Set.univ) * (μ E)
          = ∫⁻ _θ : ℝ, μ E ∂lam0 := by rw [lintegral_const, mul_comm]
      _ = ∫⁻ θ : ℝ, μ ((fun V : G => γ θ * V) ⁻¹' E) ∂lam0 := by
            apply lintegral_congr_ae
            filter_upwards with θ
            exact (MeasureTheory.measure_preimage_mul μ (γ θ) E).symm
      _ = ∫⁻ θ : ℝ, (∫⁻ V : G,
            E.indicator (fun _ => (1 : ℝ≥0∞)) (γ θ * V) ∂μ) ∂lam0 := by
            apply lintegral_congr_ae
            filter_upwards with θ
            have hpre : MeasurableSet ((fun V : G => γ θ * V) ⁻¹' E) :=
              (hγ_meas.comp (measurable_const.prodMk measurable_id)) hE
            simp_rw [show ∀ V : G,
                E.indicator (fun _ => (1 : ℝ≥0∞)) (γ θ * V) =
                  ((fun V : G => γ θ * V) ⁻¹' E).indicator (fun _ => (1 : ℝ≥0∞)) V by
                intro V; by_cases h : γ θ * V ∈ E <;> simp [h]]
            rw [MeasureTheory.lintegral_indicator hpre]
            simp
      _ = ∫⁻ V : G, (∫⁻ θ : ℝ,
            E.indicator (fun _ => (1 : ℝ≥0∞)) (γ θ * V) ∂lam0) ∂μ := by
            exact MeasureTheory.lintegral_lintegral_swap hmeas.aemeasurable
      _ = ∫⁻ _V : G, (0 : ℝ≥0∞) ∂μ := by
            apply lintegral_congr_ae
            filter_upwards with V
            have hpre : MeasurableSet {θ : ℝ | γ θ * V ∈ E} :=
              (hγ_meas.comp (measurable_id.prodMk measurable_const)) hE
            have h₂ : (∫⁻ θ : ℝ, E.indicator (fun _ => (1 : ℝ≥0∞)) (γ θ * V) ∂lam0) = lam0 {θ : ℝ | γ θ * V ∈ E} := by
              have h₃ : (∫⁻ θ : ℝ, E.indicator (fun _ => (1 : ℝ≥0∞)) (γ θ * V) ∂lam0) = (∫⁻ θ : ℝ, ({θ : ℝ | γ θ * V ∈ E}.indicator (fun _ => (1 : ℝ≥0∞)) θ) ∂lam0) := by
                apply lintegral_congr_ae
                filter_upwards with θ
                rfl
              rw [h₃]
              have h₄ : (∫⁻ θ : ℝ, ({θ : ℝ | γ θ * V ∈ E}.indicator (fun _ => (1 : ℝ≥0∞)) θ) ∂lam0) = (∫⁻ θ in {θ : ℝ | γ θ * V ∈ E}, (1 : ℝ≥0∞) ∂lam0) := by
                rw [← MeasureTheory.lintegral_indicator hpre]
              rw [h₄]
              have h₅ : (∫⁻ θ in {θ : ℝ | γ θ * V ∈ E}, (1 : ℝ≥0∞) ∂lam0) = lam0 {θ : ℝ | γ θ * V ∈ E} := by
                simp [lam0, lintegral_const]
              rw [h₅]
            have h₆ : (∫⁻ θ : ℝ, E.indicator (fun _ => (1 : ℝ≥0∞)) (γ θ * V) ∂lam0) = 0 := by
              rw [h₂]
              have h₇ : lam0 {θ : ℝ | γ θ * V ∈ E} = 0 := by
                have h₇₁ : lam0 {θ : ℝ | γ θ * V ∈ E} = volume ({θ : ℝ | γ θ * V ∈ E} ∩ Set.Ioo 0 (2 * Real.pi)) := by
                  dsimp [lam0]
                  rw [Measure.restrict_apply hpre]
                rw [h₇₁]
                have h₇₂ : volume ({θ : ℝ | γ θ * V ∈ E} ∩ Set.Ioo 0 (2 * Real.pi)) = volume {θ : ℝ | θ ∈ Set.Ioo 0 (2 * Real.pi) ∧ γ θ * V ∈ E} := by
                  congr 1; ext θ; simp [and_comm]
                rw [h₇₂]
                exact hslice V
              rw [h₇]
              <;> simp
            rw [h₆]
      _ = 0 := by
        rw [lintegral_const]
        simp
  exact (mul_eq_zero.mp h_prod_zero).resolve_left hlam0_pos

end Helpers

end YangMills