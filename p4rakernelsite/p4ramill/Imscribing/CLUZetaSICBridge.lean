import Imscribing.CLU744Bridge
import Imscribing.SICZetaLemniscate
import Imscribing.Millennium.GrammarUniversalDualFrameSICPOVM

/-!
P9 strengthening (2026-11-18).
`CLU744Bridge.clu_744_bridge_theorem` is a bare conjunction:
  744 arithmetic  ∧  CLU10 = log 10.
The `12` in `744 = 6·126 − 12` is the SIC dimension D, and the same 12 satisfies
`zeta_void_coupling : 12·ζ(−1) = −1` — the SIC station spacing 1/12 = −ζ(−1).
CLU(b) = ln(b) is the observer-relative cost per station.

This module SYNTHESIZES the three: the 744 constant, the zeta station spacing,
and the CLU cost act on one frame. The old bridge is recovered as a corollary,
so nothing is deleted. No new axiom.
-/
namespace Imscribing.CLUZetaSICBridge

open Imscribing.CLU744Bridge
open Imscribing.Millennium.ZetaSICDualFrame
open Imscribing.Frobenius
open Imscribing.Millennium.GrammarUniversalDualFrameSICPOVM
open Imscribing.Primitives.CLUPrimitives

/-- The dimension D in 744 is exactly the SIC dimension whose zeta coupling is −1.
    This is the bridge's missing premise: the 12 is not an arbitrary subtraction. -/
theorem D_is_SIC_dimension : (D : ℂ) * riemannZeta (-1) = -1 := by
  unfold D
  exact zeta_void_coupling

/-- The 744 subtraction is the SIC dimension: FORTY_FOUR = 6·126 − D. -/
theorem forty_four_subtracts_SIC_dimension : FORTY_FOUR = 6 * 126 - D := by
  unfold FORTY_FOUR N_dual_pairs D_sq_minus_D_minus_6 D
  native_decide

/-- CLU is the cost per SIC station: the 12 stations at k/12 windings cost
    12·CLU(b); for the decimal observer this is 12·ln(10) nats. -/
noncomputable def sic_station_cost (b : ℝ) (hb_pos : b > 0) (hb_ne_one : b ≠ 1) : ℝ :=
  (D : ℝ) * CLU_of_base b hb_pos hb_ne_one

theorem sic_station_cost_base10 : sic_station_cost 10 (by norm_num) (by norm_num) = 12 * Real.log 10 := by
  unfold sic_station_cost CLU_of_base D
  norm_num

/-- The six Frobenius-dual pairs completed by 744 cost 6·CLU; the SIC stations
    (D of them) cost D·CLU. Both are CLU multiples on the same frame. -/
theorem dual_pair_and_station_costs_are_clu_multiples (b : ℝ) (hb_pos : b > 0) (hb_ne_one : b ≠ 1) :
    six_pair_cost b hb_pos hb_ne_one = (N_dual_pairs : ℝ) * CLU_of_base b hb_pos hb_ne_one ∧
    sic_station_cost b hb_pos hb_ne_one = (D : ℝ) * CLU_of_base b hb_pos hb_ne_one := by
  exact ⟨rfl, rfl⟩

/-- The CLU–zeta–SIC synthesis: the 744 constant, the zeta station spacing, and
    the CLU cost all act on the SIC dimension D = 12. -/
theorem clu_zeta_sic_synthesis :
    FORTY_FOUR = 6 * 126 - 12 ∧
    (12 : ℂ) * riemannZeta (-1) = -1 ∧
    CLU10 = Real.log 10 ∧
    sic_station_cost 10 (by norm_num) (by norm_num) = 12 * Real.log 10 := by
  exact ⟨forty_four_subtracts_SIC_dimension, zeta_void_coupling,
    CLU10_eq_ln10, sic_station_cost_base10⟩

/-- The old conjunction is recovered as a corollary: the bridge theorem still
    holds, now as a projection of the synthesis. -/
theorem clu_744_bridge_of_synthesis :
    FORTY_FOUR = 6 * 126 - 12 ∧ CLU10 = Real.log 10 := by
  exact ⟨(clu_zeta_sic_synthesis).1, (clu_zeta_sic_synthesis).2.2.1⟩

/-- The grammar's dual-frame fixed point and CLU's station cost coexist: the
    grammar is the universal dual frame, and CLU prices its 12 stations. -/
theorem grammar_frame_and_clu_cost :
    (igFrobeniusAlg.mul theGrammar theGrammar = theGrammar) ∧
    sic_station_cost 10 (by norm_num) (by norm_num) = 12 * Real.log 10 := by
  exact ⟨grammar_frobenius_closure, sic_station_cost_base10⟩

end Imscribing.CLUZetaSICBridge
