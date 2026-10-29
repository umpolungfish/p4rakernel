import Imscribing.NativeDomainCancellation

/-!
# SeparableNoGo

Status: builds. The audited theorems depend on `propext`, `Classical.choice`,
`Quot.sound` only.

## Statement

Let `U : ℝ³ → ℝ³` be smooth, bounded, nonzero somewhere, with

  (E)  U·∇U + ∇P = 0                 (steady Euler, for some smooth P)
  (L)  ΔU = -k² U                    (Laplacian eigenmode)

For `u = a(t) U(x)` and `p = a(t)² P(x)`, the differential residual is

    residualForce ν u p = (a' + ν k² a) · U .                [`sep_residual`]

If `u` lay in `FullBlowsUp`, the k = 0 jet bound makes `a' + ν k² a` bounded on
(0,1). With a(0) = 0 the scalar ODE then gives `a` bounded
(`scalar_ode_bounded`), hence `u` bounded since `U` is, which contradicts
blowup. Therefore such a flow is not in `FullBlowsUp`.  [`separable_no_go`]

Assumptions on the ansatz: `a` is continuous on [0,1), differentiable on (0,1),
with a(0) = 0; `U` is bounded.
-/

noncomputable section
namespace Imscribing.SeparableNoGo

open Imscribing.NSInjectionField
open Imscribing.NSRegularityWitness
open Imscribing.NSResidualExtension
open Imscribing.NSReentry
open Imscribing.WitnessedClosure
open Imscribing.NativeDomain
open Lean
open Set Filter
open scoped Topology ContDiff

/-! ## Time-scaling a field -/

def timeScale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ → ℝ) (f : Domain → E) : Domain → E := fun w => c w.1 • f w

/-- A spatial profile viewed as a time-independent field. -/
def staticLift {E : Type*} (f : Space → E) : Domain → E := fun w => f w.2

def sepVel (a : ℝ → ℝ) (U : Space → Space) : Velocity := timeScale a (staticLift U)

def sepPres (a : ℝ → ℝ) (P : Space → ℝ) : Pressure :=
  timeScale (fun t => a t ^ 2) (staticLift P)

theorem sepVel_apply (a : ℝ → ℝ) (U : Space → Space) (t : ℝ) (x : Space) :
    sepVel a U (t, x) = a t • U x := rfl

theorem spatialDerivative_timeScale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ → ℝ) (f : Domain → E) (hf : ContDiff ℝ ∞ f) (i : Fin 3) (z : Domain) :
    spatialDerivative (timeScale c f) i z = c z.1 • spatialDerivative f i z := by
  have hd : DifferentiableAt ℝ (fun x : Space => f (z.1, x)) z.2 :=
    ((hf.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) z.2
  show fderiv ℝ (fun x : Space => c z.1 • f (z.1, x)) z.2 (basisVector i) =
    c z.1 • fderiv ℝ (fun x : Space => f (z.1, x)) z.2 (basisVector i)
  have e : (fun x : Space => c z.1 • f (z.1, x)) =
      c z.1 • (fun x : Space => f (z.1, x)) := rfl
  rw [e, fderiv_const_smul hd]
  first
  | rfl
  | simp [ContinuousLinearMap.smul_apply]

theorem laplacian_timeScale (c : ℝ → ℝ) (f : Velocity) (hf : ContDiff ℝ ∞ f) (z : Domain) :
    spatialLaplacian (timeScale c f) z = c z.1 • spatialLaplacian f z := by
  unfold spatialLaplacian
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : spatialDerivative (timeScale c f) i = timeScale c (spatialDerivative f i) :=
    funext fun w => spatialDerivative_timeScale c f hf i w
  rw [h1]
  exact spatialDerivative_timeScale c (spatialDerivative f i)
    (spatial_derivative_smooth f hf i) i z

theorem pressureGradient_timeScale (c : ℝ → ℝ) (P : Pressure) (hP : ContDiff ℝ ∞ P)
    (z : Domain) :
    pressureGradient (timeScale c P) z = c z.1 • pressureGradient P z := by
  unfold pressureGradient
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [spatialDerivative_timeScale c P hP i z, smul_assoc]

theorem transport_timeScale (a : ℝ → ℝ) (f : Velocity) (hf : ContDiff ℝ ∞ f) (z : Domain) :
    transport (timeScale a f) z = (a z.1 * a z.1) • transport f z := by
  unfold transport
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [spatialDerivative_timeScale a f hf i z]
  show (a z.1 • f z) i • (a z.1 • spatialDerivative f i z) = _
  rw [PiLp.smul_apply, smul_eq_mul, smul_smul, smul_smul]
  congr 1
  ring

theorem timeDerivative_sepVel (a a' : ℝ → ℝ) (U : Space → Space) (z : Domain)
    (ha : HasDerivAt a (a' z.1) z.1) :
    timeDerivative (sepVel a U) z = a' z.1 • U z.2 := by
  have hfun : (fun t : ℝ => sepVel a U (t, z.2)) = fun t => a t • U z.2 := rfl
  unfold timeDerivative
  rw [hfun, fderiv_apply_one_eq_deriv, (ha.smul_const (U z.2)).deriv]

/-! ## The residual of a separable eigenmode flow -/

theorem sep_residual (ν k2 : ℝ) (a a' : ℝ → ℝ) (U : Space → Space) (P : Space → ℝ)
    (hU : ContDiff ℝ ∞ U) (hP : ContDiff ℝ ∞ P)
    (hlap : ∀ z : Domain, spatialLaplacian (staticLift U) z = (-k2) • staticLift U z)
    (heuler : ∀ z : Domain,
      transport (staticLift U) z + pressureGradient (staticLift P) z = 0)
    (z : Domain) (ha : HasDerivAt a (a' z.1) z.1) :
    residualForce ν (sepVel a U) (sepPres a P) z = (a' z.1 + ν * k2 * a z.1) • U z.2 := by
  have hlift : ContDiff ℝ ∞ (staticLift U) := hU.comp contDiff_snd
  have hliftP : ContDiff ℝ ∞ (staticLift P) := hP.comp contDiff_snd
  show timeDerivative (sepVel a U) z + transport (sepVel a U) z +
      (-ν) • spatialLaplacian (sepVel a U) z + pressureGradient (sepPres a P) z = _
  have h1 : transport (sepVel a U) z = (a z.1 * a z.1) • transport (staticLift U) z :=
    transport_timeScale a (staticLift U) hlift z
  have h2 : spatialLaplacian (sepVel a U) z = a z.1 • spatialLaplacian (staticLift U) z :=
    laplacian_timeScale a (staticLift U) hlift z
  have h3 : pressureGradient (sepPres a P) z =
      (a z.1 ^ 2) • pressureGradient (staticLift P) z :=
    pressureGradient_timeScale (fun t => a t ^ 2) (staticLift P) hliftP z
  have h4 : pressureGradient (staticLift P) z = - transport (staticLift U) z := by
    have h := heuler z
    first
    | exact eq_neg_of_add_eq_zero_right h
    | (rw [add_comm] at h; exact eq_neg_of_add_eq_zero_left h)
  have hl : staticLift U z = U z.2 := rfl
  rw [timeDerivative_sepVel a a' U z ha, h1, h2, h3, hlap z, h4, hl]
  module

/-! ## Scalar ODE: bounded forcing and rest give a bounded solution -/

theorem scalar_ode_bounded (a a' : ℝ → ℝ) (lam B : ℝ)
    (ha : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt a (a' t) t)
    (hcont : ContinuousOn a (Ico (0 : ℝ) 1)) (h0 : a 0 = 0)
    (hb : ∀ t ∈ Ioo (0 : ℝ) 1, |a' t + lam * a t| ≤ B) :
    ∀ t ∈ Ioo (0 : ℝ) 1, |a t| ≤ Real.exp |lam| * (Real.exp |lam| * B) := by
  intro t ht
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hb (1 / 2) ⟨by norm_num, by norm_num⟩)
  have hwd : ∀ s ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Real.exp (lam * s) * a s)
        (Real.exp (lam * s) * (a' s + lam * a s)) s := by
    intro s hs
    have he : HasDerivAt (fun s : ℝ => Real.exp (lam * s)) (Real.exp (lam * s) * lam) s := by
      simpa using ((hasDerivAt_id' s).const_mul lam).exp
    refine (he.mul (ha s hs)).congr_deriv ?_
    ring
  -- bounds on the exponentials over (0,1)
  have hexp_up : ∀ s ∈ Ioo (0 : ℝ) 1, Real.exp (lam * s) ≤ Real.exp |lam| := by
    intro s hs
    apply Real.exp_le_exp.mpr
    calc lam * s ≤ |lam| * s := mul_le_mul_of_nonneg_right (le_abs_self lam) hs.1.le
      _ ≤ |lam| := mul_le_of_le_one_right (abs_nonneg lam) hs.2.le
  have hexp_dn : ∀ s ∈ Ioo (0 : ℝ) 1, Real.exp (-(lam * s)) ≤ Real.exp |lam| := by
    intro s hs
    apply Real.exp_le_exp.mpr
    have hle : |lam * s| ≤ |lam| := by
      rw [abs_mul, abs_of_pos hs.1]
      exact mul_le_of_le_one_right (abs_nonneg _) hs.2.le
    have := (abs_le.mp hle).1
    linarith
  -- FTC on w(s) = exp(lam s) a(s)
  have hexpc : Continuous (fun s : ℝ => Real.exp (lam * s)) := by fun_prop
  have hwc : ContinuousOn (fun s : ℝ => Real.exp (lam * s) * a s) (Ico 0 1) :=
    hexpc.continuousOn.mul hcont
  have hC0 : 0 ≤ Real.exp |lam| * B := mul_nonneg (Real.exp_pos _).le hB
  have hftc := ftc_from_zero (fun s : ℝ => Real.exp (lam * s) * a s)
    (continuousWithinAt_Ioi_of_Ico _ hwc)
    (fun s hs => (hwd s hs).differentiableAt) (Real.exp |lam| * B)
    (fun s hs => by
      rw [(hwd s hs).deriv, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (hexp_up s hs) (hb s hs) (abs_nonneg _) (Real.exp_pos _).le) ht
  have hw : |Real.exp (lam * t) * a t| ≤ Real.exp |lam| * B := by
    have h := hftc
    simp only [mul_zero, Real.exp_zero, one_mul, h0, sub_zero] at h
    rw [Real.norm_eq_abs] at h
    have h2 : Real.exp |lam| * B * t ≤ Real.exp |lam| * B :=
      mul_le_of_le_one_right hC0 ht.2.le
    linarith
  have hinv : Real.exp (-(lam * t)) * Real.exp (lam * t) = 1 := by
    rw [← Real.exp_add]; simp
  calc |a t| = (Real.exp (-(lam * t)) * Real.exp (lam * t)) * |a t| := by rw [hinv, one_mul]
    _ = Real.exp (-(lam * t)) * (Real.exp (lam * t) * |a t|) := by ring
    _ = Real.exp (-(lam * t)) * |Real.exp (lam * t) * a t| := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp |lam| * (Real.exp |lam| * B) :=
        mul_le_mul (hexp_dn t ht) hw (abs_nonneg _) (Real.exp_pos _).le

/-! ## Exclusion of single-mode separable flows from the cell -/

theorem separable_no_go (ν k2 : ℝ) (a a' : ℝ → ℝ) (U : Space → Space) (P : Space → ℝ)
    (hU : ContDiff ℝ ∞ U) (hP : ContDiff ℝ ∞ P)
    (hlap : ∀ z : Domain, spatialLaplacian (staticLift U) z = (-k2) • staticLift U z)
    (heuler : ∀ z : Domain,
      transport (staticLift U) z + pressureGradient (staticLift P) z = 0)
    (ha : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt a (a' t) t)
    (hcont : ContinuousOn a (Ico (0 : ℝ) 1)) (h0 : a 0 = 0)
    (K : ℝ) (hK : ∀ x : Space, ‖U x‖ ≤ K)
    (x₀ : Space) (hx₀ : U x₀ ≠ 0) :
    ¬ FullBlowsUp ν (sepVel a U) (sepPres a P) openHalf 1 := by
  intro hF
  have hpos : 0 < ‖U x₀‖ := norm_pos_iff.mpr hx₀
  obtain ⟨C, hC⟩ := hF.jets 0
  -- the residual along x₀ is (a' + ν k2 a) • U x₀, bounded by C
  have hres : ∀ t ∈ Ioo (0 : ℝ) 1,
      |a' t + ν * k2 * a t| * ‖U x₀‖ ≤ C := by
    intro t ht
    have hz : ((t, x₀) : Domain) ∈ openHalf := ⟨ht, mem_univ x₀⟩
    have h1 := hC _ hz
    rw [norm_iteratedFDeriv_zero,
      sep_residual ν k2 a a' U P hU hP hlap heuler (t, x₀) (ha t ht), norm_smul,
      Real.norm_eq_abs] at h1
    exact h1
  have hb : ∀ t ∈ Ioo (0 : ℝ) 1, |a' t + ν * k2 * a t| ≤ C / ‖U x₀‖ := by
    intro t ht
    first
    | exact (le_div_iff₀ hpos).mpr (hres t ht)
    | exact (le_div_iff hpos).mpr (hres t ht)
  have hbound := scalar_ode_bounded a a' (ν * k2) (C / ‖U x₀‖) ha hcont h0 hb
  set A : ℝ := Real.exp |ν * k2| * (Real.exp |ν * k2| * (C / ‖U x₀‖)) with hA
  -- u is bounded by A * K, contradicting blowup
  have hblow := hF.blow.blowsUp
  have h0' : ∀ᶠ t in nhdsWithin (1 : ℝ) (Iio 1), (0 : ℝ) < t :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (lt_mem_nhds (by norm_num))
  have h1' : ∀ᶠ t in nhdsWithin (1 : ℝ) (Iio 1), t < 1 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht
  obtain ⟨t, ⟨x, hx⟩, ht0, ht1⟩ := ((hblow (A * K)).and (h0'.and h1')).exists
  have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨ht0, ht1⟩
  have hat : |a t| ≤ A := hbound t ht
  have hnorm : ‖sepVel a U (t, x)‖ = |a t| * ‖U x‖ := by
    rw [sepVel_apply, norm_smul, Real.norm_eq_abs]
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) hat
  have hle : ‖sepVel a U (t, x)‖ ≤ A * K := by
    rw [hnorm]
    exact mul_le_mul hat (hK x) (norm_nonneg _) hA0
  linarith [hx, hle]

end Imscribing.SeparableNoGo
end

#print axioms Imscribing.SeparableNoGo.sep_residual
#print axioms Imscribing.SeparableNoGo.scalar_ode_bounded
#print axioms Imscribing.SeparableNoGo.separable_no_go
