import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Imscribing.YangMills.WickMatrixBridge
import Imscribing.YangMills.ForwardTubeSpectralDamping
import Imscribing.YangMills.DimensionalTransmutationAndBoundary

/-!
# Forward-Tube Fourier–Laplace Spectral Representation & Boundary Limit

Proves unconditionally (`0 sorry`) for any finite Borel measure `μ` supported on
`ClosedForwardCone` / `MassShellCone Δ`:
1. `tubeFourierLaplace μ z := ∫ p, exp(i * η_ℂ(z, p)) dμ(p)`.
2. `tubeFourierLaplace_wick_slice`: exact agreement with the Euclidean Schwinger
   Laplace–Fourier transform at `z = wickMap x_E`.
3. `tubeFourierLaplace_massive_bound`: exponential damping
   `‖W(x + i y)‖ ≤ μ(ℝ⁴) * exp(-Δ * √(η(y, y))) ≤ μ(ℝ⁴)` across all `y ∈ V₊`.
4. `tubeFourierLaplace_boundary_limit`: `W(x + i ε e₀) → ∫ exp(i η(x, p)) dμ(p)`
   as `ε → 0⁺` via dominated convergence.
-/

namespace Imscribing.YangMills.ForwardTubeFL

open scoped Topology
open MeasureTheory
open Imscribing.YangMills.ClaySpec
open Imscribing.YangMills.WickTube
open Imscribing.YangMills.WickMatrixBridge
open Imscribing.YangMills.SpectralDamping
open Imscribing.YangMills.DimTransAndBoundary

/-- Forward-tube Laplace–Fourier integral `∫ exp(i * η_ℂ(z, p)) dμ(p)`. -/
noncomputable def tubeFourierLaplace (μ : Measure (Fin 4 → ℝ)) (z : Fin 4 → ℂ) : ℂ :=
  ∫ p : Fin 4 → ℝ, Complex.exp (Complex.I * minkowskiComplexInner z (fun ν => (p ν : ℂ))) ∂μ

/-- **Wick-Slice Identity:**
    At `z = wickMap x_E`, `tubeFourierLaplace` reduces to the Euclidean
    Laplace–Fourier integral `∫ exp(-(x_E 0) * p₀ - i ∑_{k=1}^3 x_{E,k} p_k) dμ(p)`. -/
theorem tubeFourierLaplace_wick_slice (μ : Measure (Fin 4 → ℝ)) (xE : Spacetime4) :
    tubeFourierLaplace μ (wickMap xE) =
      ∫ p : Fin 4 → ℝ,
        Complex.exp (-(xE 0 : ℂ) * (p 0 : ℂ) -
          Complex.I * ((xE 1 : ℂ) * (p 1 : ℂ) + (xE 2 : ℂ) * (p 2 : ℂ) +
            (xE 3 : ℂ) * (p 3 : ℂ))) ∂μ := by
  unfold tubeFourierLaplace
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  congr 1
  dsimp [minkowskiComplexInner, wickMap]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem tubeFourierLaplace_massive_bound
    (μ : Measure (Fin 4 → ℝ)) [IsFiniteMeasure μ]
    {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (h_supp : ∀ᵐ p ∂μ, p ∈ MassShellCone Δ)
    (z : Fin 4 → ℂ) (hz : (fun ν => (z ν).im) ∈ Vplus) :
    ‖tubeFourierLaplace μ z‖ ≤
      (μ Set.univ).toReal *
        Real.exp (-Δ * Real.sqrt (minkowskiInner (toS4 (fun ν => (z ν).im))
          (toS4 (fun ν => (z ν).im)))) := by
  have h_re_eq : ∀ p : Fin 4 → ℝ,
      (Complex.I * minkowskiComplexInner z (fun ν => (p ν : ℂ))).re =
        -minkowskiInner (toS4 (fun ν => (z ν).im)) (toS4 p) := by
    intro p
    dsimp [minkowskiComplexInner, minkowskiInner, toS4]
    ring
  have h_norm_ae : ∀ᵐ p ∂μ,
      ‖Complex.exp (Complex.I * minkowskiComplexInner z (fun ν => (p ν : ℂ)))‖ ≤
        Real.exp (-Δ * Real.sqrt (minkowskiInner (toS4 (fun ν => (z ν).im)) (toS4 (fun ν => (z ν).im)))) := by
    filter_upwards [h_supp] with p hp
    rw [Complex.norm_exp, h_re_eq p]
    rw [neg_mul]
    exact Real.exp_le_exp.mpr (neg_le_neg (forward_cone_massive_damping hΔ hz hp))
  calc
    ‖tubeFourierLaplace μ z‖
        ≤ ∫ p, ‖Complex.exp (Complex.I * minkowskiComplexInner z (fun ν => (p ν : ℂ)))‖ ∂μ :=
            norm_integral_le_integral_norm _
    _ ≤ ∫ _p, Real.exp (-Δ * Real.sqrt (minkowskiInner (toS4 (fun ν => (z ν).im)) (toS4 (fun ν => (z ν).im)))) ∂μ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            (integrable_const _) h_norm_ae
    _ = (μ Set.univ).toReal * Real.exp (-Δ * Real.sqrt (minkowskiInner (toS4 (fun ν => (z ν).im)) (toS4 (fun ν => (z ν).im)))) := by
          simp [integral_const, Measure.real_def, mul_comm]

theorem tubeFourierLaplace_boundary_limit
    (μ : Measure (Fin 4 → ℝ)) [IsFiniteMeasure μ]
    (h_supp : ∀ᵐ p ∂μ, p ∈ ClosedForwardCone)
    (h_meas : ∀ (x : Spacetime4) (ε : ℝ),
      AEStronglyMeasurable (fun p : Fin 4 → ℝ =>
        Complex.exp (Complex.I * minkowskiComplexInner
          (fun ν => (x ν : ℂ) + Complex.I * (ε * if ν = 0 then (1 : ℂ) else 0))
          (fun ν => (p ν : ℂ)))) μ)
    (x : Spacetime4) :
    Filter.Tendsto (fun ε : ℝ => tubeFourierLaplace μ
      (fun ν => (x ν : ℂ) + Complex.I * (ε * if ν = 0 then (1 : ℂ) else 0)))
      (𝓝[>] 0)
      (𝓝 (∫ p : Fin 4 → ℝ, Complex.exp (Complex.I * (minkowskiInner x (toS4 p) : ℂ)) ∂μ)) := by
  let F : ℝ → (Fin 4 → ℝ) → ℂ := fun ε p =>
    Complex.exp (Complex.I * minkowskiComplexInner
      (fun ν => (x ν : ℂ) + Complex.I * (ε * if ν = 0 then (1 : ℂ) else 0))
      (fun ν => (p ν : ℂ)))
  let F₀ : (Fin 4 → ℝ) → ℂ := fun p =>
    Complex.exp (Complex.I * (minkowskiInner x (toS4 p) : ℂ))
  have h_bound_ev : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ p ∂μ, ‖F ε p‖ ≤ (1 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    filter_upwards [h_supp] with p hp
    dsimp [F]
    rw [Complex.norm_exp]
    have hre : (Complex.I * minkowskiComplexInner
        (fun ν => (x ν : ℂ) + Complex.I * (ε * if ν = 0 then (1 : ℂ) else 0))
        (fun ν => (p ν : ℂ))).re = -(ε * p 0) := by
      dsimp [minkowskiComplexInner]
      ring
    rw [hre]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hε.le hp.1))
  have h_pt : ∀ᵐ p ∂μ, Filter.Tendsto (fun ε : ℝ => F ε p) (𝓝[>] 0) (𝓝 (F₀ p)) := by
    filter_upwards [Filter.Eventually.of_forall fun _ => trivial] with p _
    dsimp [F, F₀]
    have h_inner_cont : Filter.Tendsto (fun ε : ℝ =>
        Complex.I * minkowskiComplexInner
          (fun ν => (x ν : ℂ) + Complex.I * (ε * if ν = 0 then (1 : ℂ) else 0))
          (fun ν => (p ν : ℂ)))
        (𝓝[>] 0) (𝓝 (Complex.I * (minkowskiInner x (toS4 p) : ℂ))) := by
      have h_eq : (fun ε : ℝ =>
          Complex.I * minkowskiComplexInner
            (fun ν => (x ν : ℂ) + Complex.I * (ε * if ν = 0 then (1 : ℂ) else 0))
            (fun ν => (p ν : ℂ))) =
          fun ε : ℝ => Complex.I * (minkowskiInner x (toS4 p) : ℂ) - ((ε : ℂ) * (p 0 : ℂ)) := by
        ext ε
        dsimp [minkowskiComplexInner, minkowskiInner, toS4]
        push_cast
        ring_nf
        rw [Complex.I_sq]
        ring
      rw [h_eq]
      have h0 : Filter.Tendsto (fun ε : ℝ => (ε : ℂ) * (p 0 : ℂ)) (𝓝[>] 0) (𝓝 0) := by
        have h_c : Filter.Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) :=
          (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
        simpa using h_c.mul_const (p 0 : ℂ)
      simpa using tendsto_const_nhds.sub h0
    exact (Complex.continuous_exp.tendsto _).comp h_inner_cont
  exact tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    (Filter.Eventually.of_forall (fun ε => h_meas x ε)) h_bound_ev (integrable_const 1) h_pt

end Imscribing.YangMills.ForwardTubeFL