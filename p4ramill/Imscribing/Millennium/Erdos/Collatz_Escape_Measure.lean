/-
  The escaping set has measure zero.

  Companion to the pointwise reduction (`Collatz_Unified_Closure`): where the dichotomy is a
  pointwise statement about a single trajectory, this is the measure-theoretic half. It shows
  that the set of orbits that never descend is null, given the one classical analytic input --
  the exponential decay of the survivor measure (Chernoff on the uniform parity vector, since
  the contraction threshold log_3 2 exceeds 1/2). That input is a named hypothesis here, as the
  transcendence input is on the cycle side.

  The escaping set is the intersection of the survivor sets S_k = {survives to depth k}. These
  are nested decreasing, so no Borel-Cantelli is needed: μ(⋂ S_k) ≤ μ(S_k) ≤ ρ^k → 0.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecificLimits.Basic

namespace CollatzEscapeMeasure

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **The escaping set is null.**  Let `S k` be the survivor sets, nested decreasing, with
    measure decaying at least geometrically, `μ (S k) ≤ ρ^k` for some `ρ < 1` -- the Chernoff
    bound on the uniform parity vector.  Then the escaping set `⋂ k, S k` has measure zero.
    The nesting makes it immediate: the intersection lies in every `S k`, so its measure is
    below `ρ^k` for all `k`, hence below the limit `0`. -/
theorem measure_escape_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : ℕ → Set Ω) (ρ : ℝ≥0∞) (hρ : ρ < 1)
    (hbound : ∀ k, μ (S k) ≤ ρ ^ k) :
    μ (⋂ k, S k) = 0 := by
  have hle : ∀ k, μ (⋂ k, S k) ≤ ρ ^ k := fun k =>
    le_trans (measure_mono (Set.iInter_subset S k)) (hbound k)
  have hlim : Tendsto (fun k => ρ ^ k) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hρ
  refine le_antisymm ?_ (zero_le _)
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall hle)

/-- The same conclusion from a summability hypothesis on the survivor measures, the form the
    Chernoff bound most naturally supplies (`∑ ρ^k < ∞`).  A convergent series has terms tending
    to zero, and the intersection sits below every term. -/
theorem measure_escape_zero_of_summable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : ℕ → Set Ω) (a : ℕ → ℝ≥0∞)
    (hsum : ∑' k, a k ≠ ⊤) (hbound : ∀ k, μ (S k) ≤ a k) :
    μ (⋂ k, S k) = 0 := by
  have hz : Tendsto a atTop (𝓝 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum
  have hle : ∀ k, μ (⋂ k, S k) ≤ a k := fun k =>
    le_trans (measure_mono (Set.iInter_subset S k)) (hbound k)
  refine le_antisymm ?_ (zero_le _)
  exact ge_of_tendsto hz (Filter.Eventually.of_forall hle)

end CollatzEscapeMeasure
