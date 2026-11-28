import Imscribing.YangMills.ForwardTubeFourierLaplace

/-!
# Massive Spectral-Measure Wightman 2-Point Positivity, Translation Invariance & Gap Decay

Proves unconditionally (`0 sorry`) for any finite Borel measure `μ` supported on
`MassShellCone Δ`:
1. `wightman2Spectral_positivity`: `0 ≤ (W₂ f f).re` (Wightman positivity).
2. `wightman2Spectral_trans_inv`: invariance under Minkowski 4-translations `a : Spacetime4`.
3. `wightman2Spectral_euclid_decay`: Euclidean Wick-slice decay
   `‖tubeFourierLaplace μ (wickMap (t, 0, 0, 0))‖ ≤ μ(ℝ⁴) * exp(-Δ * t)`.
-/

namespace Imscribing.YangMills.WightmanSpectral2Pt

open MeasureTheory
open Imscribing.YangMills.ClaySpec
open Imscribing.YangMills.WickTube
open Imscribing.YangMills.SpectralDamping
open Imscribing.YangMills.ForwardTubeFL

/-- Wightman 2-point bilinear pairing `W₂(f, g) = ∫ p, star(f̂(p)) * ĝ(p) dμ(p)`
    from a finite spectral measure `μ` on energy-momentum space. -/
noncomputable def wightman2FromSpectral (μ : Measure (Fin 4 → ℝ))
    (f_hat g_hat : (Fin 4 → ℝ) → ℂ) : ℂ :=
  ∫ p : Fin 4 → ℝ, star (f_hat p) * g_hat p ∂μ

/-- **Wightman 2-Point Positivity:** `0 ≤ (W₂ f f).re` for any `μ`. -/
theorem wightman2Spectral_positivity (μ : Measure (Fin 4 → ℝ))
    (f_hat : (Fin 4 → ℝ) → ℂ)
    (h_int : Integrable (fun p : Fin 4 → ℝ => star (f_hat p) * f_hat p) μ) :
    0 ≤ (wightman2FromSpectral μ f_hat f_hat).re := by
  unfold wightman2FromSpectral
  have h_eq : (fun p : Fin 4 → ℝ => star (f_hat p) * f_hat p) =
      fun p : Fin 4 → ℝ => ((‖f_hat p‖ ^ 2 : ℝ) : ℂ) := by
    ext p
    rw [mul_comm, show star (f_hat p) = starRingEnd ℂ (f_hat p) from rfl, Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq _
  rw [h_eq]
  have h_re_int : (∫ p : Fin 4 → ℝ, ((‖f_hat p‖ ^ 2 : ℝ) : ℂ) ∂μ).re =
      ∫ p : Fin 4 → ℝ, ‖f_hat p‖ ^ 2 ∂μ := by
    change ((Complex.reCLM : ℂ →L[ℝ] ℝ) (∫ p, ((‖f_hat p‖ ^ 2 : ℝ) : ℂ) ∂μ)) = _
    rw [← ContinuousLinearMap.integral_comp_comm Complex.reCLM (by rwa [← h_eq])]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => Complex.ofReal_re _)
  rw [h_re_int]
  exact integral_nonneg fun _ => sq_nonneg _

/-- **Minkowski 4-Translation Invariance:**
    Shifting both test functions by `a : Spacetime4` multiplies their Fourier transforms
    by `exp(i * η(a, p))`, leaving `W₂` invariant. -/
theorem wightman2Spectral_trans_inv (μ : Measure (Fin 4 → ℝ)) (a : Spacetime4)
    (f_hat g_hat : (Fin 4 → ℝ) → ℂ) :
    wightman2FromSpectral μ
        (fun p => Complex.exp (Complex.I * (minkowskiInner a (toS4 p) : ℂ)) * f_hat p)
        (fun p => Complex.exp (Complex.I * (minkowskiInner a (toS4 p) : ℂ)) * g_hat p) =
      wightman2FromSpectral μ f_hat g_hat := by
  unfold wightman2FromSpectral
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  dsimp
  set φ : ℂ := Complex.exp (Complex.I * (minkowskiInner a (toS4 p) : ℂ))
  have h_unit : star φ * φ = 1 := by
    have hnorm : ‖φ‖ = 1 := by
      dsimp [φ]
      rw [Complex.norm_exp]
      simp
    rw [mul_comm, show star φ = starRingEnd ℂ φ from rfl, Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  have h1 : star (φ * f_hat p) * (φ * g_hat p) = star (f_hat p) * g_hat p := by
    change (starRingEnd ℂ) (φ * f_hat p) * (φ * g_hat p) = _
    rw [map_mul (starRingEnd ℂ)]
    calc
      (starRingEnd ℂ) φ * (starRingEnd ℂ) (f_hat p) * (φ * g_hat p)
          = ((starRingEnd ℂ) φ * φ) * ((starRingEnd ℂ) (f_hat p) * g_hat p) := by ring
      _ = 1 * ((starRingEnd ℂ) (f_hat p) * g_hat p) := by rw [show (starRingEnd ℂ) φ * φ = 1 from h_unit]
      _ = (starRingEnd ℂ) (f_hat p) * g_hat p := by ring
  exact h1

theorem wightman2Spectral_euclid_decay
    (μ : Measure (Fin 4 → ℝ)) [IsFiniteMeasure μ]
    {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (h_supp : ∀ᵐ p ∂μ, p ∈ MassShellCone Δ)
    {t : ℝ} (ht : 0 < t) :
    let xE : Spacetime4 := (WithLp.equiv 2 (Fin 4 → ℝ)).symm ![t, 0, 0, 0]
    ‖tubeFourierLaplace μ (wickMap xE)‖ ≤ (μ Set.univ).toReal * Real.exp (-Δ * t) := by
  intro xE
  have him_eq : (fun ν : Fin 4 => (wickMap xE ν).im) = ![t, 0, 0, 0] := by
    ext ν
    fin_cases ν <;> simp [wickMap, xE]
  have hy : (fun ν : Fin 4 => (wickMap xE ν).im) ∈ Vplus := by
    rw [him_eq]
    refine ⟨ht, ?_⟩
    dsimp
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
    linarith
  have hbd := tubeFourierLaplace_massive_bound μ hΔ h_supp (wickMap xE) hy
  have hmink : minkowskiInner (toS4 (fun ν => (wickMap xE ν).im))
      (toS4 (fun ν => (wickMap xE ν).im)) = t ^ 2 := by
    rw [him_eq]
    dsimp [minkowskiInner, toS4]
    ring
  rw [hmink, Real.sqrt_sq ht.le] at hbd
  exact hbd

end Imscribing.YangMills.WightmanSpectral2Pt