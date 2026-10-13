import Imscribing.NS_InjectionField
import Imscribing.NS_RegularityWitness
import Imscribing.NS_ResidualExtension
import Imscribing.FalsifierRegister

/-!
# CheapB_Control

STATUS: written against your uploaded files, NOT compiled (no Mathlib/Imscribing
in my sandbox). No `sorry`. See LIKELY FRICTION at the bottom.

## What this file shows

The shear flow  u(t,x) = ramp(t) · x₂ · e₀,   ramp(t) = t/(1-t),  p = 0

  * is smooth on the strip, blows up as t ↑ 1, is divergence-free, starts at rest;
  * therefore `regularityRegister` returns B (= nativeHeld) for it;
  * but its residual (with p = 0) is  ramp'(t) · x₂ · e₀ = (1-t)⁻² x₂ e₀,
    whose zeroth jet is unbounded on the strip;
  * therefore NO choice of `core`, `q` can satisfy `CancellationBounds` +
    `ExteriorBounds` for it (`bounded_residual_jets` would bound the jets).

So: B (as currently defined) does NOT imply the extension input. The two are
independent, and the extension input is the part that carries the analysis.
Together with `time_linear_jets_bounded` (T register, jets bounded) this gives
the 2×2 picture:

                         jets bounded      jets unbounded
     register B          OpenAI target     shear (this file)
     register T          time-linear       —

The target cell is exactly what a real construction must land in.

## What this file does NOT show (next steps, stated honestly)

  1. Shear has unbounded energy, so it is a cheap-B for `regularityRegister`
     but NOT for `strongRegularityRegister`. An energy-bounded cheap-B needs a
     concentrating profile u = a(t) w(x/λ(t)) with a²λ³ bounded; the residual
     then has λ'-terms and the lower bound is a real computation. Not done.
  2. The jets claim is for the specific pressure p = 0. For arbitrary p one
     needs the curl argument: curl(∇p) = 0, but curl of the shear's
     a'x₂e₀ part is a' e₁, unbounded, while a smooth compactly supported
     remainder has bounded curl. Needs second-derivative symmetry of p.
-/

noncomputable section
namespace Imscribing.CheapB

open Imscribing.NSInjectionField
open Imscribing.NSRegularityWitness
open Imscribing.NSResidualExtension
open Imscribing.NSReentry
open Set
open scoped ContDiff

/-! ## The flow -/

/-- a(t) = t/(1-t): a(0) = 0, singular at t = 1. -/
def ramp (t : ℝ) : ℝ := t / (1 - t)

/-- u(t,x) = ramp(t) · x₂ · e₀ (a linear shear). -/
def shear (z : Domain) : Space := (ramp z.1 * z.2 1) • basisVector 0

theorem ramp_zero : ramp 0 = 0 := by simp [ramp]

theorem shear_rest (x : Space) : shear (0, x) = 0 := by
  simp [shear, ramp_zero]

/-! ## Smoothness on the strip -/

theorem ramp_contDiffOn : ContDiffOn ℝ ∞ (fun z : Domain => ramp z.1) strip := by
  unfold ramp
  refine ContDiffOn.div contDiff_fst.contDiffOn
    (contDiff_const.sub contDiff_fst).contDiffOn ?_
  intro z hz
  have hz' : z ∈ Ioo (-1 : ℝ) 1 ×ˢ (univ : Set Space) := hz
  have h1 : z.1 < 1 := hz'.1.2
  exact ne_of_gt (by linarith)

theorem shear_contDiffOn : ContDiffOn ℝ ∞ shear strip := by
  have hproj : ContDiff ℝ ∞ (fun z : Domain => z.2 1) :=
    (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd
  show ContDiffOn ℝ ∞ (fun z : Domain => (ramp z.1 * z.2 1) • basisVector 0) strip
  exact (ramp_contDiffOn.mul hproj.contDiffOn).smul contDiffOn_const

/-! ## Derivatives -/

theorem shear_spatialDerivative (i : Fin 3) (z : Domain) :
    spatialDerivative shear i z = (ramp z.1 * basisVector i 1) • basisVector 0 := by
  let L : Space →L[ℝ] Space :=
    (ramp z.1 • (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ)).smulRight
      (basisVector 0)
  have hfun : (fun x : Space => shear (z.1, x)) = ⇑L := by
    funext x
    simp [L, shear, ContinuousLinearMap.smulRight_apply]
  unfold spatialDerivative
  rw [hfun, L.fderiv]
  simp [L, ContinuousLinearMap.smulRight_apply]

/-- The first spatial derivatives are spatially constant, so second ones vanish. -/
theorem shear_second_derivative (i j : Fin 3) (z : Domain) :
    spatialDerivative (spatialDerivative shear i) j z = 0 := by
  have hfun : (fun x : Space => spatialDerivative shear i (z.1, x)) =
      fun _ => (ramp z.1 * basisVector i 1) • basisVector 0 := by
    funext x
    exact shear_spatialDerivative i (z.1, x)
  show fderiv ℝ (fun x : Space => spatialDerivative shear i (z.1, x)) z.2
      (basisVector j) = 0
  rw [hfun]
  simp [fderiv_const_apply]

theorem shear_laplacian (z : Domain) : spatialLaplacian shear z = 0 := by
  simp [spatialLaplacian, shear_second_derivative]

theorem shear_transport (z : Domain) : transport shear z = 0 := by
  simp [transport, Fin.sum_univ_three, shear_spatialDerivative, shear,
    basisVector, EuclideanSpace.single_apply]

theorem zero_pressureGradient (z : Domain) :
    pressureGradient (fun _ : Domain => (0 : ℝ)) z = 0 := by
  simp [pressureGradient, spatial_derivative_constant]

theorem shear_divergence (z : Domain) : divergence shear z = 0 := by
  simp [divergence, Fin.sum_univ_three, shear_spatialDerivative,
    basisVector, EuclideanSpace.single_apply]

theorem shear_timeDerivative (z : Domain) (hz : z.1 ≠ 1) :
    timeDerivative shear z = (((1 - z.1) ^ 2)⁻¹ * z.2 1) • basisVector 0 := by
  have h1 : (1 - z.1) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hr : HasDerivAt ramp (((1 - z.1) ^ 2)⁻¹) z.1 := by
    have hd : HasDerivAt (fun t : ℝ => 1 - t) (-1) z.1 := by
      simpa using (hasDerivAt_id' z.1).const_sub (1 : ℝ)
    have h := (hasDerivAt_id' z.1).div hd h1
    have hnum : (1 * (1 - z.1) - z.1 * -1) = (1 : ℝ) := by ring
    exact h.congr_deriv (by beta_reduce; rw [hnum, one_div])
  have hfun : (fun t : ℝ => shear (t, z.2)) =
      fun t => ramp t • ((z.2 1) • basisVector 0) := by
    funext t
    simp [shear, mul_smul]
  unfold timeDerivative
  rw [hfun, fderiv_apply_one_eq_deriv, (hr.smul_const ((z.2 1) • basisVector 0)).deriv]
  simp [mul_smul]

/-- With p = 0 the residual is just the time derivative: transport, viscosity and
    pressure all vanish for the linear shear. -/
theorem shear_residual (ν : ℝ) (z : Domain) (hz : z.1 ≠ 1) :
    residualForce ν shear (fun _ => 0) z =
      (((1 - z.1) ^ 2)⁻¹ * z.2 1) • basisVector 0 := by
  show timeDerivative shear z + transport shear z + (-ν) • spatialLaplacian shear z
      + pressureGradient (fun _ : Domain => (0 : ℝ)) z = _
  rw [shear_timeDerivative z hz, shear_transport z, shear_laplacian z,
    zero_pressureGradient z]
  simp

/-! ## Blowup -/

theorem shear_blowsUp : BlowsUp shear 1 := by
  intro M
  have h0 : ∀ᶠ t in nhdsWithin (1 : ℝ) (Iio 1), (0 : ℝ) < t :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (lt_mem_nhds (by norm_num))
  have h1 : ∀ᶠ t in nhdsWithin (1 : ℝ) (Iio 1), t < 1 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht
  filter_upwards [h0, h1] with t ht0 ht1
  have hr : 0 < ramp t := div_pos ht0 (by linarith)
  set c : ℝ := (|M| + 1) / ramp t with hcdef
  have hc : ramp t * c = |M| + 1 := by
    rw [hcdef]; field_simp
  refine ⟨EuclideanSpace.single (1 : Fin 3) c, ?_⟩
  have h1' : shear (t, EuclideanSpace.single (1 : Fin 3) c) =
      (ramp t * c) • basisVector 0 := by
    simp [shear]
  have hnorm : ‖shear (t, EuclideanSpace.single (1 : Fin 3) c)‖ = |M| + 1 := by
    rw [h1', norm_smul, basisVector, EuclideanSpace.norm_single, norm_one, mul_one,
      hc, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hnorm]
  linarith [le_abs_self M]

/-! ## The register says B -/

theorem shear_register_B :
    regularityRegister shear (fun _ => 0) strip 1 = nativeHeld :=
  regularity_register_eq_nativeHeld shear (fun _ => 0) strip 1
    ⟨shear_contDiffOn, contDiffOn_const⟩ shear_blowsUp

/-! ## ...but the residual cannot feed the extension -/

theorem shear_residual_jets_unbounded (ν : ℝ) :
    ¬ ∀ k : ℕ, ∃ C : ℝ, ∀ z ∈ strip,
      ‖iteratedFDeriv ℝ k (residualForce ν shear (fun _ => 0)) z‖ ≤ C := by
  intro h
  obtain ⟨C, hC⟩ := h 0
  have hs2 : (2 : ℝ) ≤ |C| + 2 := by linarith [abs_nonneg C]
  set s : ℝ := |C| + 2 with hs
  have hspos : 0 < s := by linarith
  have hsinv : s⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hs2
  have hsinvpos : 0 < s⁻¹ := inv_pos.mpr hspos
  set t : ℝ := 1 - s⁻¹ with ht
  set x : Space := EuclideanSpace.single (1 : Fin 3) (1 : ℝ) with hx
  have hz : ((t, x) : Domain) ∈ strip := by
    show (t, x) ∈ Ioo (-1 : ℝ) 1 ×ˢ (univ : Set Space)
    exact ⟨⟨by rw [ht]; linarith, by rw [ht]; linarith⟩, mem_univ _⟩
  have hne : ((t, x) : Domain).1 ≠ 1 := by
    show t ≠ 1
    intro h1
    rw [ht] at h1
    linarith
  have h1t : 1 - t = s⁻¹ := by rw [ht]; ring
  have hval := hC _ hz
  rw [norm_iteratedFDeriv_zero, shear_residual ν _ hne] at hval
  have hnorm : ‖(((1 - t) ^ 2)⁻¹ * x 1) • basisVector 0‖ = s ^ 2 := by
    rw [h1t, norm_smul, basisVector, EuclideanSpace.norm_single, norm_one, mul_one]
    simp [hx, inv_pow]
  have hbig : C < s ^ 2 := by nlinarith [le_abs_self C, hs2]
  have hval' : s ^ 2 ≤ C := by
    have := hval
    simp only at this
    rwa [hnorm] at this
  linarith

/-- No `core`, `q` can make the shear satisfy the extension input. -/
theorem shear_fails_extension_input (ν : ℝ) {core : Set Domain} {q : Domain → ℝ}
    (hc : CancellationBounds (residualForce ν shear (fun _ => 0)) core q)
    (he : ExteriorBounds (residualForce ν shear (fun _ => 0)) core) : False :=
  shear_residual_jets_unbounded ν (bounded_residual_jets hc he)

/-- Headline: register B and the extension input are independent. -/
theorem B_does_not_imply_extension_input (ν : ℝ) :
    regularityRegister shear (fun _ => 0) strip 1 = nativeHeld ∧
    ¬ ∃ (core : Set Domain) (q : Domain → ℝ),
        CancellationBounds (residualForce ν shear (fun _ => 0)) core q ∧
        ExteriorBounds (residualForce ν shear (fun _ => 0)) core :=
  ⟨shear_register_B, fun ⟨_, _, hc, he⟩ => shear_fails_extension_input ν hc he⟩

/-! ## Other half of the 2×2: T register, jets bounded -/

theorem time_linear_residual (ν : ℝ) (v : Space) :
    residualForce ν (timeLinearVelocity v) (fun _ => 0) = fun _ => v := by
  funext z
  have h := time_linear_injection ν v 0 z
  rwa [injection_eq_differential_residual] at h

theorem time_linear_jets_bounded (ν : ℝ) (v : Space) :
    ∀ k : ℕ, ∃ C : ℝ, ∀ z ∈ strip,
      ‖iteratedFDeriv ℝ k (residualForce ν (timeLinearVelocity v) (fun _ => 0)) z‖ ≤ C := by
  rw [time_linear_residual]
  exact constant_jets_bounded v

end Imscribing.CheapB
end

/-
LIKELY FRICTION (could not check):

  * `shear_spatialDerivative`: the final `simp` must turn
    `((c • proj 1).smulRight e₀) v` into `(c * v 1) • e₀`. If `EuclideanSpace.proj`
    does not unfold under simp, finish with `rfl` after `ContinuousLinearMap.smul_apply`.
  * `shear_transport` / `shear_divergence`: simp must decide `(1 : Fin 3) = 0` is false
    and evaluate `EuclideanSpace.single` coordinates. If it stalls, `fin_cases`/`Fin.sum_univ_three`
    then `simp` per term.
  * `shear_timeDerivative`: the `convert ... using 1` side goal for the ramp derivative
    may need adjusting; algebra is (1·(1-t) - t·(-1))/(1-t)² = 1/(1-t)².
    `fderiv_apply_one_eq_deriv` name: `fderiv_apply_one_eq_deriv : fderiv 𝕜 f x 1 = deriv f x`.
  * `inv_anti₀` name (older Mathlib: `inv_le_inv_of_le`).
  * `shear_residual_jets_unbounded`: the last `simp [hx, inv_pow]` should reduce
    `‖(s⁻¹^2)⁻¹ * x 1‖` to `‖s^2‖`; the closing `abs_of_pos` may need `Real.norm_eq_abs` first.
  * `show (t, x) ∈ Ioo ... ×ˢ univ`: relies on `strip` unfolding as in your
    `FalsifierRegister.strip_is_Ioo_times_univ` (which is `rfl`).
-/
#print axioms Imscribing.CheapB.B_does_not_imply_extension_input
#print axioms Imscribing.CheapB.shear_register_B
