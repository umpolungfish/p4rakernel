import Imscribing.NS_Reentry
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
The source of injection computed from velocity and pressure derivatives.
Spatial derivatives are Fréchet derivatives in the Cartesian basis. The time
derivative, nonlinear transport, viscous Laplacian, and pressure gradient feed
the carried tower of NS_Reentry; its round trip derives the force identity.
-/

namespace Imscribing.NSInjectionField

open Imscribing.NSReentry
open scoped BigOperators ContDiff

noncomputable section

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Domain := ℝ × Space
abbrev Velocity := Domain → Space
abbrev Pressure := Domain → ℝ

def basisVector (i : Fin 3) : Space := EuclideanSpace.single i 1

/-- Directional spatial derivative in Cartesian direction i. -/
def spatialDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : Domain → E) (i : Fin 3) (z : Domain) : E :=
  fderiv ℝ (fun x : Space => field (z.1, x)) z.2 (basisVector i)

def timeDerivative (u : Velocity) (z : Domain) : Space :=
  fderiv ℝ (fun t : ℝ => u (t, z.2)) z.1 1

def transport (u : Velocity) (z : Domain) : Space :=
  ∑ i : Fin 3, (u z i) • spatialDerivative u i z

def spatialLaplacian (u : Velocity) (z : Domain) : Space :=
  ∑ i : Fin 3, spatialDerivative (spatialDerivative u i) i z

def pressureGradient (pressure : Pressure) (z : Domain) : Space :=
  ∑ i : Fin 3, spatialDerivative pressure i z • basisVector i

def divergence (u : Velocity) (z : Domain) : ℝ :=
  ∑ i : Fin 3, spatialDerivative u i z i

/-- Actual differential terms, with the viscous sign included. -/
def momentumTerms (ν : ℝ) (u : Velocity) (pressure : Pressure) : MomentumTerms Domain Space :=
  { acceleration := timeDerivative u
    transport := transport u
    negativeViscosity := fun z => (-ν) • spatialLaplacian u z
    pressureGradient := pressureGradient pressure }

def residualForce (ν : ℝ) (u : Velocity) (pressure : Pressure) : Velocity :=
  (momentumTerms ν u pressure).residual

def injectionForce (ν : ℝ) (u : Velocity) (pressure : Pressure) (n : ℕ) : Velocity :=
  (momentumTerms ν u pressure).derivedInjection n

/-- Source matching for the actual differential residual is a theorem. -/
theorem injection_eq_differential_residual (ν : ℝ) (u : Velocity)
    (pressure : Pressure) (n : ℕ) :
    injectionForce ν u pressure n = residualForce ν u pressure :=
  (momentumTerms ν u pressure).derived_injection_eq_residual n

/-- The vector Navier–Stokes residual equals the source returned by the tower,
    with no source-matching or separately assumed momentum-balance premise. -/
theorem differential_injection_connection (ν : ℝ) (u : Velocity)
    (pressure : Pressure) (n : ℕ) (z : Domain) :
    timeDerivative u z + transport u z + (-ν) • spatialLaplacian u z +
      pressureGradient pressure z = injectionForce ν u pressure n z :=
  navier_stokes_injection_connection (momentumTerms ν u pressure) n z

/-- Spatial differentiation preserves smoothness of the supplied field. -/
theorem spatial_derivative_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : Domain → E) (hfield : ContDiff ℝ ∞ field) (i : Fin 3) :
    ContDiff ℝ ∞ (spatialDerivative field i) := by
  have hfamily : ContDiff ℝ ∞
      (Function.uncurry (fun z : Domain => fun x : Space => field (z.1, x))) :=
    hfield.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hfamily.fderiv (contDiff_snd : ContDiff ℝ ∞ (fun z : Domain => z.2))
    (by simp)
  exact hd.clm_apply contDiff_const

theorem time_derivative_smooth (u : Velocity) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (timeDerivative u) := by
  have hfamily : ContDiff ℝ ∞
      (Function.uncurry (fun z : Domain => fun t : ℝ => u (t, z.2))) :=
    hu.comp (contDiff_snd.prodMk contDiff_fst.snd)
  have hd := hfamily.fderiv (contDiff_fst : ContDiff ℝ ∞ (fun z : Domain => z.1))
    (by simp)
  exact hd.clm_apply contDiff_const

theorem transport_smooth (u : Velocity) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (transport u) := by
  apply ContDiff.sum
  intro i _
  have hi : ContDiff ℝ ∞ (fun z => u z i) := by
    change Domain → Space at u
    fun_prop
  exact hi.smul (spatial_derivative_smooth u hu i)

theorem laplacian_smooth (u : Velocity) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (spatialLaplacian u) := by
  apply ContDiff.sum
  intro i _
  exact spatial_derivative_smooth _ (spatial_derivative_smooth u hu i) i

theorem pressure_gradient_smooth (pressure : Pressure) (hp : ContDiff ℝ ∞ pressure) :
    ContDiff ℝ ∞ (pressureGradient pressure) := by
  apply ContDiff.sum
  intro i _
  exact (spatial_derivative_smooth pressure hp i).smul contDiff_const

/-- The injection's smoothness follows from differentiating smooth velocity and
    pressure fields, rather than from a supplied predicate about the force. -/
theorem injection_smooth (ν : ℝ) (u : Velocity) (pressure : Pressure) (n : ℕ)
    (hu : ContDiff ℝ ∞ u) (hp : ContDiff ℝ ∞ pressure) :
    ContDiff ℝ ∞ (injectionForce ν u pressure n) := by
  rw [injection_eq_differential_residual]
  exact (((time_derivative_smooth u hu).add (transport_smooth u hu)).add
    ((laplacian_smooth u hu).const_smul (-ν))).add (pressure_gradient_smooth pressure hp)

/-- CONTROL: every spatial derivative of a spatially constant field vanishes. -/
theorem spatial_derivative_constant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : E) (i : Fin 3) (z : Domain) :
    spatialDerivative (fun _ => c) i z = 0 := by
  simp [spatialDerivative, fderiv_const_apply]

/-- CONTROL: zero velocity and pressure produce zero injection. -/
theorem zero_field_injection (ν : ℝ) (n : ℕ) (z : Domain) :
    injectionForce ν (fun _ => 0) (fun _ => 0) n z = 0 := by
  rw [injection_eq_differential_residual]
  simp [residualForce, momentumTerms, MomentumTerms.residual, timeDerivative,
    transport, spatialLaplacian, pressureGradient, spatialDerivative, fderiv_const_apply]

/-- A time-linear, spatially uniform velocity for the nonzero derivative control. -/
def timeLinearVelocity (v : Space) : Velocity := fun z => z.1 • v

theorem time_linear_acceleration (v : Space) (z : Domain) :
    timeDerivative (timeLinearVelocity v) z = v := by
  have h := (hasFDerivAt_id (𝕜 := ℝ) z.1).smul_const v
  have heval := congrArg (fun L : ℝ →L[ℝ] Space => L 1) h.fderiv
  simpa only [timeDerivative, timeLinearVelocity, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, one_smul] using heval

/-- CONTROL: actual differentiation of u(t,x)=t v yields injection v at every
    scale. The source follows the velocity field's derivative. -/
theorem time_linear_injection (ν : ℝ) (v : Space) (n : ℕ) (z : Domain) :
    injectionForce ν (timeLinearVelocity v) (fun _ => 0) n z = v := by
  rw [injection_eq_differential_residual]
  have hs : ∀ i z, spatialDerivative (timeLinearVelocity v) i z = 0 := by
    intro i z
    simp [spatialDerivative, timeLinearVelocity, fderiv_const_apply]
  have hfun : ∀ i, spatialDerivative (timeLinearVelocity v) i = fun _ => 0 := by
    intro i; funext z; exact hs i z
  simp [residualForce, momentumTerms, MomentumTerms.residual, time_linear_acceleration,
    transport, spatialLaplacian, pressureGradient, hs, hfun, spatial_derivative_constant]

/-- The time-linear control is incompressible. -/
theorem time_linear_divergence (v : Space) (z : Domain) :
    divergence (timeLinearVelocity v) z = 0 := by
  simp [divergence, spatialDerivative, timeLinearVelocity, fderiv_const_apply]

theorem time_linear_injection_nonzero (ν : ℝ) (v : Space) (hv : v ≠ 0)
    (n : ℕ) (z : Domain) :
    injectionForce ν (timeLinearVelocity v) (fun _ => 0) n z ≠ 0 := by
  rw [time_linear_injection]
  exact hv

end
end Imscribing.NSInjectionField
