import Imscribing.NS_InjectionField
import Imscribing.NS_RegularityWitness
import Imscribing.NS_ResidualExtension
import Imscribing.FalsifierRegister

/-!
# CheapB_Control

STATUS: compiled.

## Reading: register values are FDE truth values

The register is a Belnap-valued readout of two vessels. In First Degree
Entailment the value B is not a classical label on a cell; it is a first-class
truth value, the value of the witness-proposition. The shear
u(t,x) = ramp(t) · x₂ · e₀ with ramp(t) = t/(1-t), p = 0, exhibits this
directly:

  * it is smooth on the strip, blows up at T = 1, so its register reads B;
  * its residual (with p = 0) is ramp'(t) · x₂ · e₀ = (1-t)⁻² x₂ e₀, whose
    zeroth jet is unbounded on the strip, so no (core, q) pair satisfies the
    cancellation and exterior bounds, and the extension input fails.

Both facts are designated pieces of evidence about the same flow, and the
register carries both. The implication from "the register reads B" to "the
extension input holds" has FDE value B: its antecedent has value B, its
consequent has value F, and ¬B ∨ F = B ∨ F = B. The implication and its denial
are both designated. The register does not project B onto a single classical
truth value, and I do not.

## The 2×2 picture, in FDE

                         jets bounded      jets unbounded
     register B          target (B, T)     shear (B, F)
     register T          time-linear (T, T) —

The first coordinate is the register value; the second is the extension
input's value. The target cell (B, T) is the open problem. The shear inhabits
the paraconsistent cell (B, F): the register reads B because the witness
features are present, and the extension input fails because the residual jets
are unbounded.

## What this file does NOT show

  1. Shear has unbounded energy, so it is a cheap-B for the plain register but
     not for the energy-strengthened register. An energy-bounded cheap-B needs
     a concentrating profile; not done.
  2. The jets claim is for p = 0. For arbitrary p one needs the curl argument:
     curl(∇p) = 0, but curl of the shear's a'x₂e₀ part is a' e₁, unbounded,
     while a smooth compactly supported remainder has bounded curl. Needs
     second-derivative symmetry of p.
-/

noncomputable section
namespace Imscribing.CheapB

open Imscribing.NSInjectionField
open Imscribing.NSRegularityWitness
open Imscribing.NSResidualExtension
open Imscribing.NSReentry
open Imscribing.Paraconsistent
open Set
open scoped ContDiff

/-! ## FDE operations on the register carrier

The register's output is a `Belnap`. The truth-lattice negation fixes N and B
and swaps T and F. The truth-lattice join has F as bottom, B as top, and N, T
incomparable with N ∨ T = B. The conditional is v(p → q) = ¬v(p) ∨ v(q).
These belong upstream in a paraconsistent module; I keep them here so the
file is self-contained.
-/

/-- FDE truth-lattice negation. -/
def fdeNeg : Belnap → Belnap
  | .N => .N
  | .T => .F
  | .F => .T
  | .B => .B

/-- FDE truth-lattice join. -/
def fdeJoin : Belnap → Belnap → Belnap
  | .F, q  => q
  | p,  .F => p
  | .N, .N => .N
  | .N, .T => .B
  | .N, .B => .B
  | .T, .N => .B
  | .T, .T => .T
  | .T, .B => .B
  | .B, _  => .B

/-- FDE conditional: v(p → q) = ¬v(p) ∨ v(q). -/
def fdeImp (p q : Belnap) : Belnap := fdeJoin (fdeNeg p) q

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

/-- With p = 0 the residual is just the time derivative: transport, viscosity
    and pressure all vanish for the linear shear. -/
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

/-! ## The register reads B -/

theorem shear_register_B :
    regularityRegister shear (fun _ => 0) strip 1 = nativeHeld :=
  regularity_register_eq_nativeHeld shear (fun _ => 0) strip 1
    ⟨shear_contDiffOn, contDiffOn_const⟩ shear_blowsUp

/-! ## The residual jets are unbounded -/

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

/-! ## The register's B value is a first-class FDE value

The shear's register reads B. The extension input fails. These are two pieces
of evidence about the same flow, and the register carries both. The implication
from the first to the second has FDE value B, and so does its denial. The
register does not project B onto a single classical truth value.

This replaces the previous theorem `B_does_not_imply_extension_input`, whose
statement asserted a classical non-implication. That assertion was wrong: it
read the register's B as a classical label on a cell and evaluated the
implication `B → extension input` by a classical case split. In FDE the
implication is `¬B ∨ F = B ∨ F = B`.
-/

/-- The shear exhibits the paraconsistent cell of the register: its register
    reads B, and the extension input fails on it. Both facts are designated
    pieces of evidence about the same flow. This is the FDE-correct formulation
    of the previous classical non-implication claim. -/
theorem shear_exhibits_paraconsistent_cell (ν : ℝ) :
    regularityRegister shear (fun _ => 0) strip 1 = nativeHeld ∧
    ¬ ∃ (core : Set Domain) (q : Domain → ℝ),
        CancellationBounds (residualForce ν shear (fun _ => 0)) core q ∧
        ExteriorBounds (residualForce ν shear (fun _ => 0)) core :=
  ⟨shear_register_B,
   fun ⟨_, _, hc, he⟩ => shear_fails_extension_input ν hc he⟩

/-- The FDE value of the implication `B → F` is `B`, and so is its denial.
    With the register reading B and the extension input reading F, the
    implication from the first to the second is not F: it is B. Both the
    implication and its negation are designated. -/
theorem shear_implication_value_is_paraconsistent :
    fdeImp .B .F = .B ∧ fdeNeg (fdeImp .B .F) = .B :=
  ⟨rfl, rfl⟩

/-! ## Time-linear control: register T, jets bounded -/

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

#print axioms Imscribing.CheapB.shear_exhibits_paraconsistent_cell
#print axioms Imscribing.CheapB.shear_register_B
#print axioms Imscribing.CheapB.shear_implication_value_is_paraconsistent