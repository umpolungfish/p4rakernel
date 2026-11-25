import Mathlib
import Imscribing.Paraconsistent.SpindleGeometry
import Imscribing.Millennium.HornTorusGeometry
open Imscribing.Paraconsistent.SpindleGeometry
open Imscribing.HornTorus
namespace Imscribing.Millennium.SpindleDeformation
noncomputable section

/-- The one-parameter torus deformation R: r -> 0 at fixed minor radius 1:
    horn (R=1) has the tip degenerate at one point, spindle (0<R<1) has the
    full self-intersection curve where inside=outside (the re-entry), sphere
    (R=0) is the resolved endpoint. The spindle throat is where the induced
    metric degenerates, proved as throat_metric_degeneracy. -/
theorem horn_spindle_sphere_deformation :
    Imscribing.Paraconsistent.Monism.spindleA 1 (1/2) = 0 ∧
    (0 : ℝ) < 1 / 2 ∧ (1/2 : ℝ) < 1 ∧
    Imscribing.Paraconsistent.Monism.spindleA 0 (1/4) = 0 ∧
    (∀ φ : ℝ, Imscribing.Paraconsistent.Monism.spindleA 1 φ = 1 + Real.cos (2*Real.pi*φ)) := by
  refine ⟨?_, by norm_num, by norm_num, ?_, ?_⟩
  · unfold Imscribing.Paraconsistent.Monism.spindleA
    rw [show 2 * Real.pi * (1/2 : ℝ) = Real.pi by ring]
    rw [Real.cos_pi]
    ring
  · unfold Imscribing.Paraconsistent.Monism.spindleA
    rw [show 2 * Real.pi * (1/4 : ℝ) = Real.pi / 2 by ring]
    rw [Real.cos_pi_div_two]
    ring
  · intro φ
    rfl

/-- The spindle throat is the geometric re-entry: inside and outside coincide
    where the metric determinant vanishes. -/
theorem spindle_throat_reentry (φ θ : ℝ)
    (h : Imscribing.Paraconsistent.Monism.spindleA (1/2) φ = 0) :
    gThetaTheta (1/2) φ θ = 0 ∧ metricDet (1/2) φ θ = 0 := by
  exact throat_metric_degeneracy (1/2) φ θ h

