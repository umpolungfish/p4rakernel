import Imscribing.YangMills.WickRotationAndForwardTube

/-!
# Forward-Tube Spectral Damping & Analytic Continuation Bounds

Proves unconditionally:
1. `forward_cone_inner_nonneg`: for `y ∈ V₊` and `p ∈ ClosedForwardCone`,
   `0 ≤ minkowskiInner y p`.
2. `forward_cone_massive_damping`: on `MassShellCone Δ`,
   `Δ * √(minkowskiInner y y) ≤ minkowskiInner y p`.
3. `forwardTube_laplace_damping`: multi-point Laplace kernel is bounded by `1`
   on `ForwardTube n × (ClosedForwardCone)ⁿ` and exponentially damped on the
   mass-gap sector `MassShellCone Δ`.
-/

namespace Imscribing.YangMills.SpectralDamping

open Imscribing.YangMills.ClaySpec
open Imscribing.YangMills.ContinuumInterfaces
open Imscribing.YangMills.WickTube

/-- Closed forward energy-momentum cone V̄₊: p₀ ≥ 0 and p₁² + p₂² + p₃² ≤ p₀². -/
def ClosedForwardCone : Set (Fin 4 → ℝ) :=
  { p | 0 ≤ p 0 ∧ p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 ≤ p 0 ^ 2 }

/-- Massive spectral shell p₀² - ‖p‖² ≥ Δ² in V̄₊. -/
def MassShellCone (Δ : ℝ) : Set (Fin 4 → ℝ) :=
  { p ∈ ClosedForwardCone | Δ ^ 2 ≤ p 0 ^ 2 - (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) }

private lemma r3_cs (a b : Fin 4 → ℝ) :
    (a 1 * b 1 + a 2 * b 2 + a 3 * b 3) ^ 2 ≤
      (a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2) * (b 1 ^ 2 + b 2 ^ 2 + b 3 ^ 2) := by
  have h : 0 ≤ (a 1 * b 2 - a 2 * b 1) ^ 2 + (a 1 * b 3 - a 3 * b 1) ^ 2 +
      (a 2 * b 3 - a 3 * b 2) ^ 2 := by positivity
  linarith [h]

def toS4 (v : Fin 4 → ℝ) : ClaySpec.Spacetime4 :=
  (WithLp.equiv 2 (Fin 4 → ℝ)).symm v

/-- **Forward Cone Positivity:** `0 ≤ minkowskiInner y p` for `y ∈ V₊` and `p ∈ V̄₊`. -/
theorem forward_cone_inner_nonneg {y p : Fin 4 → ℝ}
    (hy : y ∈ Vplus) (hp : p ∈ ClosedForwardCone) :
    0 ≤ minkowskiInner (toS4 y) (toS4 p) := by
  rcases hy with ⟨hy0, hysq⟩
  rcases hp with ⟨hp0, hpsq⟩
  have hcs := r3_cs y p
  have h_prod_sq : (y 1 * p 1 + y 2 * p 2 + y 3 * p 3) ^ 2 ≤ (y 0 * p 0) ^ 2 := by
    have hnn1 : 0 ≤ y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 := by positivity
    have hnn2 : 0 ≤ p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 := by positivity
    calc
      (y 1 * p 1 + y 2 * p 2 + y 3 * p 3) ^ 2
          ≤ (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) * (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) := hcs
      _ ≤ y 0 ^ 2 * p 0 ^ 2 := mul_le_mul hysq.le hpsq hnn2 (sq_nonneg (y 0))
      _ = (y 0 * p 0) ^ 2 := by ring
  have h_lin : y 1 * p 1 + y 2 * p 2 + y 3 * p 3 ≤ y 0 * p 0 := by
    nlinarith [mul_nonneg hy0.le hp0]
  simpa [minkowskiInner, toS4] using sub_nonneg.mpr h_lin

/-- **Inverse Lorentz Cauchy–Schwarz on the Mass Shell:**
    `Δ * √(y₀² - ‖y‖²) ≤ minkowskiInner y p` for `y ∈ V₊` and `p ∈ MassShellCone Δ`. -/
theorem forward_cone_massive_damping {Δ : ℝ} (hΔ : 0 ≤ Δ) {y p : Fin 4 → ℝ}
    (hy : y ∈ Vplus) (hp : p ∈ MassShellCone Δ) :
    Δ * Real.sqrt (minkowskiInner (toS4 y) (toS4 y)) ≤ minkowskiInner (toS4 y) (toS4 p) := by
  rcases hy with ⟨hy0, hysq⟩
  rcases hp with ⟨⟨hp0, hpsq⟩, hmass⟩
  have h_inner_nn := forward_cone_inner_nonneg ⟨hy0, hysq⟩ ⟨hp0, hpsq⟩
  have h_y_norm : 0 < y 0 ^ 2 - (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) := sub_pos.mpr hysq
  have h_p_norm : Δ ^ 2 ≤ p 0 ^ 2 - (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) := hmass
  have h_cs := r3_cs y p
  set ys2 : ℝ := y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2
  set ps2 : ℝ := p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2
  set dot : ℝ := y 1 * p 1 + y 2 * p 2 + y 3 * p 3
  have h_sqrt_cs :
      Real.sqrt ys2 * Real.sqrt ps2 ≤ y 0 * p 0 := by
    have h_mul : (Real.sqrt ys2 * Real.sqrt ps2) ^ 2 ≤ (y 0 * p 0) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      exact le_trans (mul_le_mul hysq.le hpsq (by positivity) (sq_nonneg _)) (by ring_nf; rfl)
    nlinarith [Real.sqrt_nonneg ys2, Real.sqrt_nonneg ps2, mul_nonneg hy0.le hp0]
  have h_dot_le : dot ≤ Real.sqrt ys2 * Real.sqrt ps2 := by
    have h_sq : dot ^ 2 ≤ (Real.sqrt ys2 * Real.sqrt ps2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      exact h_cs
    have hnn : 0 ≤ Real.sqrt ys2 * Real.sqrt ps2 := by positivity
    nlinarith [hnn]
  have h_gap_sq : (y 0 ^ 2 - ys2) * (p 0 ^ 2 - ps2) ≤ (y 0 * p 0 - Real.sqrt ys2 * Real.sqrt ps2) ^ 2 := by
    have h_id : (y 0 * p 0 - Real.sqrt ys2 * Real.sqrt ps2) ^ 2 - (y 0 ^ 2 - ys2) * (p 0 ^ 2 - ps2) =
        (y 0 * Real.sqrt ps2 - p 0 * Real.sqrt ys2) ^ 2 := by
      have h1 : (Real.sqrt ys2) ^ 2 = ys2 := Real.sq_sqrt (by positivity)
      have h2 : (Real.sqrt ps2) ^ 2 = ps2 := Real.sq_sqrt (by positivity)
      nlinarith
    linarith [sq_nonneg (y 0 * Real.sqrt ps2 - p 0 * Real.sqrt ys2)]
  have h_prod_lb : Δ ^ 2 * (y 0 ^ 2 - ys2) ≤ (y 0 * p 0 - dot) ^ 2 := by
    have h1 : Δ ^ 2 * (y 0 ^ 2 - ys2) ≤ (y 0 ^ 2 - ys2) * (p 0 ^ 2 - ps2) := by
      nlinarith
    have h2 : y 0 * p 0 - Real.sqrt ys2 * Real.sqrt ps2 ≤ y 0 * p 0 - dot := by linarith
    have h3 : 0 ≤ y 0 * p 0 - Real.sqrt ys2 * Real.sqrt ps2 := sub_nonneg.mpr h_sqrt_cs
    have h4 : (y 0 * p 0 - Real.sqrt ys2 * Real.sqrt ps2) ^ 2 ≤ (y 0 * p 0 - dot) ^ 2 := by
      nlinarith
    exact le_trans (le_trans h1 h_gap_sq) h4
  have h_lhs_sq : (Δ * Real.sqrt (minkowskiInner (toS4 y) (toS4 y))) ^ 2 ≤
      (minkowskiInner (toS4 y) (toS4 p)) ^ 2 := by
    have hmink_y : minkowskiInner (toS4 y) (toS4 y) = y 0 ^ 2 - ys2 := by
      simp [minkowskiInner, toS4, ys2]; ring
    have hmink_yp : minkowskiInner (toS4 y) (toS4 p) = y 0 * p 0 - dot := by
      simp [minkowskiInner, toS4, dot]
    rw [mul_pow, hmink_y, Real.sq_sqrt h_y_norm.le, hmink_yp]
    exact h_prod_lb
  have h_lhs_nn : 0 ≤ Δ * Real.sqrt (minkowskiInner (toS4 y) (toS4 y)) :=
    mul_nonneg hΔ (Real.sqrt_nonneg _)
  nlinarith

/-- Forward-tube imaginary increment vector at step `k`. -/
def tubeDiffIm {n : ℕ} (z : Fin n → Fin 4 → ℂ) (k : Fin n) : Fin 4 → ℝ :=
  fun μ => if hk : (k : ℕ) = 0 then (z k μ).im else (z k μ).im - (z ⟨k - 1, by omega⟩ μ).im

/-- **Multi-Point Forward-Tube Laplace Bound:**
    The Euclidean-to-Minkowski Laplace factor `∏ k, exp (-minkowskiInner (tubeDiffIm z k) (p k))`
    is bounded by `1` on `ForwardTube n × ClosedForwardConeⁿ` and damped by
    `exp (-Δ * ∑ k, √(minkowskiInner (tubeDiffIm z k) (tubeDiffIm z k)))` on `MassShellCone Δ`. -/
theorem forwardTube_laplace_damping {n : ℕ} {Δ : ℝ} (hΔ : 0 ≤ Δ)
    {z : Fin n → Fin 4 → ℂ} (hz : z ∈ ForwardTube n)
    (p : Fin n → Fin 4 → ℝ)
    (hp_cone : ∀ k : Fin n, p k ∈ ClosedForwardCone)
    (hp_mass : ∀ k : Fin n, p k ∈ MassShellCone Δ) :
    (∏ k : Fin n, Real.exp (-minkowskiInner (toS4 (tubeDiffIm z k)) (toS4 (p k)))) ≤
      Real.exp (-Δ * ∑ k : Fin n,
        Real.sqrt (minkowskiInner (toS4 (tubeDiffIm z k)) (toS4 (tubeDiffIm z k)))) ∧
    Real.exp (-Δ * ∑ k : Fin n,
      Real.sqrt (minkowskiInner (toS4 (tubeDiffIm z k)) (toS4 (tubeDiffIm z k)))) ≤ 1 := by
  have h_prod_eq :
      (∏ k : Fin n, Real.exp (-minkowskiInner (toS4 (tubeDiffIm z k)) (toS4 (p k)))) =
        Real.exp (-∑ k : Fin n, minkowskiInner (toS4 (tubeDiffIm z k)) (toS4 (p k))) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  have h_damp_sum :
      Δ * ∑ k : Fin n,
          Real.sqrt (minkowskiInner (toS4 (tubeDiffIm z k)) (toS4 (tubeDiffIm z k))) ≤
        ∑ k : Fin n, minkowskiInner (toS4 (tubeDiffIm z k)) (toS4 (p k)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ =>
      forward_cone_massive_damping hΔ (hz k) (hp_mass k)
  have h_sum_nn : 0 ≤ ∑ k : Fin n,
      Real.sqrt (minkowskiInner (toS4 (tubeDiffIm z k)) (toS4 (tubeDiffIm z k))) :=
    Finset.sum_nonneg fun k _ => Real.sqrt_nonneg _
  rw [h_prod_eq]
  refine ⟨by simpa [neg_mul] using Real.exp_le_exp.mpr (neg_le_neg h_damp_sum), Real.exp_le_one_iff.mpr ?_⟩
  nlinarith

end Imscribing.YangMills.SpectralDamping