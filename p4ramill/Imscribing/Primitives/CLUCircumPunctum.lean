-- Bridge the observer-relative CLU fiber metric to CircumPunctum's re-entry tower.
-- Each punctum transport is one scale-boundary crossing. The payload survives
-- the return map exactly, while information cost is charged once per crossing.
-- Geometric displacement is retained as a separate field.
import Imscribing.Primitives.CLU
import Imscribing.CircumPunctum

namespace Imscribing.Primitives.CLUPrimitives.CircumPunctumBridge

open Imscribing.CircumPunctum

/-- A dual-metric observation keeps coordinate geometry and fiber information
    in distinct fields; the two values are never added as if they shared units. -/
structure DualMetricObservation where
  geometricDistance : ℝ
  informationCost : ℝ

/-- One CircumPunctum punctum transport, paired with the observer-relative
    information cost for crossing its re-entry boundary. -/
noncomputable def reentryObservation (b : ℝ) (hb_pos : b > 0)
    (hb_ne_one : b ≠ 1) (geometricDistance : ℝ) : DualMetricObservation :=
  ⟨geometricDistance, CLU_cost b hb_pos hb_ne_one⟩

theorem reentry_payload_roundtrip {n : ℕ} (x : V n) : μ (η x) = x :=
  μ_η_id x

/-- Each re-entry boundary receives the same information-fiber charge,
    regardless of its separately recorded geometric displacement. -/
theorem reentry_information_invariant (b : ℝ) (hb_pos : b > 0)
    (hb_ne_one : b ≠ 1) (d₁ d₂ : ℝ) :
    (reentryObservation b hb_pos hb_ne_one d₁).informationCost =
      (reentryObservation b hb_pos hb_ne_one d₂).informationCost := rfl

/-- The cost over `n` successive re-entry boundaries is the additive CLU
    fiber metric. -/
noncomputable def reentryCost (b : ℝ) (hb_pos : b > 0)
    (hb_ne_one : b ≠ 1) (n : ℕ) : ℝ :=
  (n : ℝ) * CLU_cost b hb_pos hb_ne_one

theorem reentryCost_succ (b : ℝ) (hb_pos : b > 0)
    (hb_ne_one : b ≠ 1) (n : ℕ) :
    reentryCost b hb_pos hb_ne_one (n + 1) =
      reentryCost b hb_pos hb_ne_one n + CLU_cost b hb_pos hb_ne_one := by
  simp [reentryCost, Nat.cast_add, add_mul]

theorem reentryCost_base10 (n : ℕ) :
    reentryCost 10 (by norm_num) (by norm_num) n = (n : ℝ) * Real.log 10 := by
  have hlog : Real.log (10 : ℝ) > 0 := Real.log_pos (by norm_num)
  simp [reentryCost, CLU_cost, CLU_of_base, abs_of_pos hlog]

end Imscribing.Primitives.CLUPrimitives.CircumPunctumBridge
