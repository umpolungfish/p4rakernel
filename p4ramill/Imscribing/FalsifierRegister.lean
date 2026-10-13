import Imscribing.NS_InjectionField
import Imscribing.PublishedNS.GenericEndpointExtension
import Imscribing.NS_RegularityWitness
import Imscribing.NS_ResidualExtension

/-!
# Falsifier: register T from a smooth flow where BlowsUp fails

This file demonstrates that the regularity register is not tracking triviality —
a smooth flow that does NOT blow up yields a T register, not B.
-/

namespace Imscribing.FalsifierRegister

open Imscribing.NSInjectionField
open Imscribing.NSRegularityWitness
open Imscribing.NSResidualExtension
open Imscribing.NSReentry
open Set
open scoped ContDiff

/-- The strip is exactly `Ioo(-1, 1) ×ˢ univ`, which is open by `isOpen_Ioo.prod isOpen_univ`. -/
theorem strip_is_Ioo_times_univ :
    (strip : Set (ℝ × Space)) = Ioo (-1 : ℝ) 1 ×ˢ (univ : Set Space) := by
  rfl

/-- The openness of `openStrip` is unconditional: it is the product of `Ioo(-1,1)` and `univ`. -/
theorem hstrip_unconditional : IsOpen (strip : Set (ℝ × Space)) := by
  simpa [strip_is_Ioo_times_univ] using isOpen_Ioo.prod isOpen_univ

/-- `hregular_of_strip` is unconditional on the strip openness, because `openStrip_isOpen` supplies it. -/
theorem hregular_of_strip_unconditional (ν : ℝ) (u : Velocity) (pr : Pressure)
    (hu : ContDiffOn ℝ ∞ u strip) (hp : ContDiffOn ℝ ∞ pr strip) :
    ContDiffOn ℝ ∞ (residualForce ν u pr) strip :=
  hregular_of_strip ν u pr hstrip_unconditional hu hp

/-!
## Falsifier: smooth flow, no blowup → register T (not B)
-/

/-- The zero flow is smooth on the strip. -/
theorem zero_flow_smooth_on_strip :
    StripSmooth (fun _ : Domain => (0 : Space)) (fun _ : Domain => (0 : ℝ)) strip :=
  zero_flow_strip_smooth strip

/-- The zero flow does not blow up at any time. -/
theorem zero_flow_no_blowup (T : ℝ) : ¬ BlowsUp (fun _ : Domain => (0 : Space)) T :=
  zero_flow_not_blowup strip T

/-- The zero flow yields register T, not B. -/
theorem zero_flow_register_T :
    evidenceValue
      (StripSmooth (fun _ : Domain => (0 : Space)) (fun _ : Domain => (0 : ℝ)) strip)
      (BlowsUp (fun _ : Domain => (0 : Space)) (1 : ℝ))
    = .T :=
  zero_flow_value_T strip 1

/-- The register for the zero flow is T, proving the register is not merely tracking triviality. -/
theorem falsifier_register_T :
    regularityRegister (fun _ : Domain => (0 : Space)) (fun _ : Domain => (0 : ℝ)) strip 1 =
      kernelSingleton .T := by
  unfold regularityRegister
  rw [zero_flow_register_T]

/-- The time-linear velocity `(t, x) ↦ t • v` is smooth on all of `Domain`. -/
theorem timeLinearVelocity_contDiff (v : Space) :
    ContDiff ℝ ∞ (timeLinearVelocity v) := by
  unfold timeLinearVelocity
  first
  | exact contDiff_fst.smul contDiff_const
  | fun_prop

/-- The time-linear velocity stays bounded by `‖v‖` as `t ↑ 1`, so it does not blow up at `1`. -/
theorem timeLinearVelocity_not_blowsUp (v : Space) :
    ¬ BlowsUp (timeLinearVelocity v) 1 := by
  intro h
  have h0 : ∀ᶠ t in nhdsWithin (1 : ℝ) (Iio 1), (0 : ℝ) < t :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (lt_mem_nhds (by norm_num))
  have h1 : ∀ᶠ t in nhdsWithin (1 : ℝ) (Iio 1), t < 1 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht
  obtain ⟨t, ⟨x, hx⟩, ht0, ht1⟩ := ((h ‖v‖).and (h0.and h1)).exists
  have hn : ‖timeLinearVelocity v (t, x)‖ = t * ‖v‖ := by
    simp [timeLinearVelocity, norm_smul, abs_of_pos ht0]
  have hle : t * ‖v‖ ≤ ‖v‖ := mul_le_of_le_one_left (norm_nonneg v) ht1.le
  linarith [hx, hn, hle]

/-- A nonzero smooth flow (time-linear velocity) also does not blow up, yielding register T. -/
theorem time_linear_register_T (v : Space) :
    evidenceValue
      (StripSmooth (timeLinearVelocity v) (fun _ => (0 : ℝ)) strip)
      (BlowsUp (timeLinearVelocity v) (1 : ℝ))
    = .T :=
  evidenceValue_T_of _ _
    ⟨(timeLinearVelocity_contDiff v).contDiffOn, contDiffOn_const⟩
    (timeLinearVelocity_not_blowsUp v)

end Imscribing.FalsifierRegister
#print axioms Imscribing.FalsifierRegister.time_linear_register_T
#print axioms Imscribing.FalsifierRegister.timeLinearVelocity_not_blowsUp