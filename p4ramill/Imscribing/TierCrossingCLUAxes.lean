import Imscribing.Primitives.TierCrossing
import Imscribing.Primitives.CLU
import Imscribing.CLUZetaSICBridge

/-!
P10 strengthening (2026-11-18).
TierCrossing and CLU price two different primitive axes with the SAME law:

  * TierCrossing : Granularity (∈) axis, cost = granularitySeparation · log 10
  * CLU          : KineticChar (⊤) axis, cost = kCrystalDist · log 10 (per tier)

This module makes the shared law explicit: tierCrossingCost = separation · CLU,
and the decade-crossing theorem is the CLU power rule at b = 10. The two axes
are dual metrics on one lattice; no new axiom.
-/
namespace Imscribing.TierCrossingCLUAxes

open Imscribing.TierCrossing
open Imscribing.Primitives.CLUPrimitives
open Imscribing.Primitives
open Imscribing.CLUZetaSICBridge

/-- The cost per Granularity boundary is exactly CLU(10). TierCrossing's own
    definition is CLU applied on the ∈ axis. -/
theorem tierCrossingCost_is_separation_times_clu (g h : Granularity) :
    tierCrossingCost g h = (granularitySeparation g h : ℝ) * CLU := by
  unfold tierCrossingCost CLU CLU_of_base
  rfl

/-- The Decimal perceiver's decade crossing is the CLU power rule at b=10:
    N·ln(10) = log(10^N). -/
theorem decade_crossing_is_clu_power (N : ℝ) :
    N * CLU = Real.log ((10 : ℝ) ^ N) := by
  unfold CLU CLU_of_base
  exact tier_crossing_N_decades N

/-- The Granularity-axis cost is additive exactly as the K-axis tier cost is:
    separation adds, CLU is the common unit. -/
theorem granularity_cost_additive (g h k : Granularity) :
    tierCrossingCost g k ≤ tierCrossingCost g h + tierCrossingCost h k := by
  unfold tierCrossingCost
  have htri : granularitySeparation g k ≤
      granularitySeparation g h + granularitySeparation h k := by
    unfold granularitySeparation
    omega
  have hlog : (0 : ℝ) ≤ Real.log 10 := le_of_lt (Real.log_pos (by norm_num))
  have hcast : (granularitySeparation g k : ℝ) ≤
      (granularitySeparation g h : ℝ) + (granularitySeparation h k : ℝ) := by
    exact_mod_cast htri
  calc
    (granularitySeparation g k : ℝ) * Real.log 10 ≤
        ((granularitySeparation g h : ℝ) + (granularitySeparation h k : ℝ)) * Real.log 10 :=
      mul_le_mul_of_nonneg_right hcast hlog
    _ = (granularitySeparation g h : ℝ) * Real.log 10 +
        (granularitySeparation h k : ℝ) * Real.log 10 := by ring

/-- The two axes share one conversion factor C1 = 2/ln(10), from the geometric
    crystal distance to the fiber cost on both ∈ and ⊤. -/
theorem dual_axes_share_c1 :
    C1_conversion 10 (by norm_num) (by norm_num) = 2.0 / CLU := by
  unfold C1_conversion CLU CLU_of_base
  rfl

/-- The SIC station cost (P9) is a CLU multiple, and the Granularity axis cost
    is a CLU multiple; both axes are priced in the same observer-relative unit. -/
theorem both_axes_priced_by_clu (g h : Granularity) :
    (granularitySeparation g h : ℝ) * CLU =
      tierCrossingCost g h ∧
    sic_station_cost 10 (by norm_num) (by norm_num) = 12 * CLU := by
  exact ⟨(tierCrossingCost_is_separation_times_clu g h).symm, sic_station_cost_base10⟩

end Imscribing.TierCrossingCLUAxes
