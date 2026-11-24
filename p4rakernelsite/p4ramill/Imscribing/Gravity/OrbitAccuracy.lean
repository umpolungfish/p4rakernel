import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic
import Imscribing.Millennium.ZetaSICDualFrame

/-!
# Certified accuracy for global SIC orbit histories

The comparison theorem is quantified over every competing approximate
trajectory of the same Lipschitz IVP. A residual-certified SIC history gets a
uniform Grönwall error envelope against an exact reference orbit. Whenever its
residual budget is no larger than a comparator's, its guaranteed error bound
is no larger either; with a strictly smaller residual budget, the bound is
strictly better at every positive time.

The exact SIC readout theorem is included separately. It certifies the linear
coordinate layer; the residual and reference hypotheses below certify the
continuous trajectory accuracy.
-/

noncomputable section

open Set
open scoped NNReal

namespace Imscribing.Gravity.OrbitAccuracy

open Imscribing.Millennium.ZetaSICDualFrame

private def orbitalDimension : ℕ+ := ⟨3, by norm_num⟩

noncomputable def orbitalGram : Matrix (Fin 9) (Fin 9) ℂ :=
  sicGramGeneral orbitalDimension

noncomputable def orbitalDual : Matrix (Fin 9) (Fin 9) ℂ :=
  sicDualGeneral orbitalDimension

theorem orbital_dual_left_inverse : orbitalDual * orbitalGram = 1 :=
  (sic_inverse_general orbitalDimension).1

theorem orbital_dual_right_inverse : orbitalGram * orbitalDual = 1 :=
  (sic_inverse_general orbitalDimension).2

theorem sic_phase_coordinate_reconstruction (p v : Fin 9 → ℂ) :
    orbitalDual.mulVec (orbitalGram.mulVec p) = p ∧
    orbitalDual.mulVec (orbitalGram.mulVec v) = v := by
  constructor
  · rw [Matrix.mulVec_mulVec, orbital_dual_left_inverse, Matrix.one_mulVec]
  · rw [Matrix.mulVec_mulVec, orbital_dual_left_inverse, Matrix.one_mulVec]

/-- SIC analysis followed by dual readout is the exact coordinate decoder. -/
def sicReadout (p : Fin 9 → ℂ) : Fin 9 → ℂ :=
  orbitalDual.mulVec (orbitalGram.mulVec p)

theorem sic_readout_exact (p : Fin 9 → ℂ) : sicReadout p = p := by
  exact (sic_phase_coordinate_reconstruction p (fun _ => 0)).1

/-- The SIC readout has zero coordinate error for every phase block. -/
theorem sic_readout_zero_coordinate_error (p : Fin 9 → ℂ) :
    ‖sicReadout p - p‖ = 0 := by
  rw [sic_readout_exact, sub_self, norm_zero]

/-- Against every inexact coordinate output, the exact SIC readout has strictly
smaller coordinate error. This comparison is universal over all alternative
readout vectors. -/
theorem sic_readout_strictly_more_accurate_than_any_inexact_output
    (p q : Fin 9 → ℂ) (hInexact : q ≠ p) :
    ‖sicReadout p - p‖ < ‖q - p‖ := by
  rw [sic_readout_exact, sub_self, norm_zero]
  exact norm_pos_iff.mpr (sub_ne_zero.mpr hInexact)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous global history with a certified pointwise differential defect.
The interval and invariant region are shared by every method being compared. -/
structure ResidualCertifiedHistory
    (F : ℝ → E → E) (region : ℝ → Set E) (a b ε : ℝ) where
  state : ℝ → E
  derivative : ℝ → E
  continuous : ContinuousOn state (Icc a b)
  hasDerivative : ∀ t ∈ Ico a b,
    HasDerivWithinAt state (derivative t) (Ici t) t
  residualBound : ∀ t ∈ Ico a b,
    dist (derivative t) (F t (state t)) ≤ ε
  remainsInRegion : ∀ t ∈ Ico a b, state t ∈ region t

/-- Zero certified defect makes the reference history an exact solution on
the interval interior. -/
theorem zero_defect_is_exact
    {F : ℝ → E → E} {region : ℝ → Set E} {a b : ℝ}
    (reference : ResidualCertifiedHistory F region a b 0) :
    ∀ t ∈ Ico a b,
      reference.derivative t = F t (reference.state t) := by
  intro t ht
  have hdist := reference.residualBound t ht
  have hzero : dist (reference.derivative t) (F t (reference.state t)) = 0 :=
    le_antisymm hdist (dist_nonneg)
  exact dist_eq_zero.mp hzero

/-- A residual-certified history stays within the universal IVP error envelope
around any exact reference trajectory with the same Lipschitz field. -/
theorem history_error_bound
    {F : ℝ → E → E} {region : ℝ → Set E} {a b ε δ : ℝ}
    {K : ℝ≥0}
    (lipschitz : ∀ t ∈ Ico a b, LipschitzOnWith K (F t) (region t))
    (candidate : ResidualCertifiedHistory F region a b ε)
    (reference : ResidualCertifiedHistory F region a b 0)
    (initialError : dist (candidate.state a) (reference.state a) ≤ δ) :
    ∀ t ∈ Icc a b,
      dist (candidate.state t) (reference.state t) ≤
        gronwallBound δ K ε (t - a) := by
  have h := dist_le_of_approx_trajectories_ODE_of_mem
    (v := F) (s := region) (K := K)
    (f := candidate.state) (g := reference.state)
    (f' := candidate.derivative) (g' := reference.derivative)
    (a := a) (b := b) (εf := ε) (εg := 0) (δ := δ)
    lipschitz
    candidate.continuous candidate.hasDerivative candidate.residualBound
      candidate.remainsInRegion
    reference.continuous reference.hasDerivative reference.residualBound
      reference.remainsInRegion
    initialError
  simpa using h

/-- The Grönwall error envelope increases monotonically with the certified
residual budget. -/
theorem gronwallBound_mono_residual_budget
    {δ K ε₁ ε₂ t : ℝ} (hK : 0 ≤ K) (ht : 0 ≤ t) (hε : ε₁ ≤ ε₂) :
    gronwallBound δ K ε₁ t ≤ gronwallBound δ K ε₂ t := by
  by_cases hK0 : K = 0
  · subst K
    rw [gronwallBound_K0, gronwallBound_K0]
    exact add_le_add_right (mul_le_mul_of_nonneg_right hε ht) δ
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
    rw [gronwallBound_of_K_ne_0 hK0, gronwallBound_of_K_ne_0 hK0]
    have hcoef : 0 ≤ (Real.exp (K * t) - 1) / K := by
      apply div_nonneg
      · exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hK ht))
      · exact hKpos.le
    calc
      δ * Real.exp (K * t) + ε₁ / K * (Real.exp (K * t) - 1) =
          δ * Real.exp (K * t) + ε₁ * ((Real.exp (K * t) - 1) / K) := by ring
      _ ≤ δ * Real.exp (K * t) + ε₂ * ((Real.exp (K * t) - 1) / K) :=
        add_le_add_right (mul_le_mul_of_nonneg_right hε hcoef) _
      _ = δ * Real.exp (K * t) + ε₂ / K * (Real.exp (K * t) - 1) := by ring

/-- Strictly tighter residual certification gives a strictly tighter error
envelope at every positive time. -/
theorem gronwallBound_strictMono_residual_budget
    {δ K ε₁ ε₂ t : ℝ} (hK : 0 ≤ K) (ht : 0 < t) (hε : ε₁ < ε₂) :
    gronwallBound δ K ε₁ t < gronwallBound δ K ε₂ t := by
  by_cases hK0 : K = 0
  · subst K
    rw [gronwallBound_K0, gronwallBound_K0]
    exact add_lt_add_right (mul_lt_mul_of_pos_right hε ht) δ
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
    rw [gronwallBound_of_K_ne_0 hK0, gronwallBound_of_K_ne_0 hK0]
    have hcoef : 0 < (Real.exp (K * t) - 1) / K := by
      apply div_pos
      · have hprod : 0 < K * t := mul_pos hKpos ht
        have hexp := Real.add_one_le_exp (K * t)
        linarith
      · exact hKpos
    calc
      δ * Real.exp (K * t) + ε₁ / K * (Real.exp (K * t) - 1) =
          δ * Real.exp (K * t) + ε₁ * ((Real.exp (K * t) - 1) / K) := by ring
      _ < δ * Real.exp (K * t) + ε₂ * ((Real.exp (K * t) - 1) / K) :=
        add_lt_add_right (mul_lt_mul_of_pos_right hε hcoef) _
      _ = δ * Real.exp (K * t) + ε₂ / K * (Real.exp (K * t) - 1) := by ring

/-- Universal accuracy comparison: for one Lipschitz IVP and the same initial
error budget, the SIC history's certified error envelope is no larger than
that of any competing history whose certified residual budget is at least as
large. Both bounds hold at every time in the full closed interval. -/
theorem sic_accuracy_dominates_every_weaker_residual_certificate
    {F : ℝ → E → E} {region : ℝ → Set E} {a b εS εC δ : ℝ}
    {K : ℝ≥0}
    (lipschitz : ∀ t ∈ Ico a b, LipschitzOnWith K (F t) (region t))
    (sicHistory : ResidualCertifiedHistory F region a b εS)
    (competitorHistory : ResidualCertifiedHistory F region a b εC)
    (reference : ResidualCertifiedHistory F region a b 0)
    (sicInitialError : dist (sicHistory.state a) (reference.state a) ≤ δ)
    (competitorInitialError : dist (competitorHistory.state a) (reference.state a) ≤ δ)
    (sicResidualNoLarger : εS ≤ εC) :
    ∀ t ∈ Icc a b,
      dist (sicHistory.state t) (reference.state t) ≤ gronwallBound δ K εS (t - a) ∧
      gronwallBound δ K εS (t - a) ≤ gronwallBound δ K εC (t - a) ∧
      dist (competitorHistory.state t) (reference.state t) ≤
        gronwallBound δ K εC (t - a) := by
  have hS := history_error_bound lipschitz sicHistory reference sicInitialError
  have hC := history_error_bound lipschitz competitorHistory reference competitorInitialError
  intro t ht
  have htime : 0 ≤ t - a := by linarith [ht.1]
  exact ⟨hS t ht,
    gronwallBound_mono_residual_budget (K := (K : ℝ)) (t := t - a)
      (by exact_mod_cast K.property) htime sicResidualNoLarger,
    hC t ht⟩

/-- A strictly smaller SIC residual budget gives a strictly tighter certified
error envelope at every positive time in the interval. Both trajectories remain
bounded by their respective envelopes on the same full interval. -/
theorem sic_accuracy_strictly_dominates_every_weaker_residual_certificate
    {F : ℝ → E → E} {region : ℝ → Set E} {a b εS εC δ : ℝ}
    {K : ℝ≥0}
    (lipschitz : ∀ t ∈ Ico a b, LipschitzOnWith K (F t) (region t))
    (sicHistory : ResidualCertifiedHistory F region a b εS)
    (competitorHistory : ResidualCertifiedHistory F region a b εC)
    (reference : ResidualCertifiedHistory F region a b 0)
    (sicInitialError : dist (sicHistory.state a) (reference.state a) ≤ δ)
    (competitorInitialError : dist (competitorHistory.state a) (reference.state a) ≤ δ)
    (sicResidualSmaller : εS < εC) :
    ∀ t ∈ Icc a b, a < t →
      dist (sicHistory.state t) (reference.state t) ≤ gronwallBound δ K εS (t - a) ∧
      gronwallBound δ K εS (t - a) < gronwallBound δ K εC (t - a) ∧
      dist (competitorHistory.state t) (reference.state t) ≤
        gronwallBound δ K εC (t - a) := by
  have hS := history_error_bound lipschitz sicHistory reference sicInitialError
  have hC := history_error_bound lipschitz competitorHistory reference competitorInitialError
  intro t ht hat
  have htime : 0 < t - a := by linarith
  exact ⟨hS t ht,
    gronwallBound_strictMono_residual_budget
      (K := (K : ℝ)) (t := t - a) (by exact_mod_cast K.property) htime sicResidualSmaller,
    hC t ht⟩

/-- The archived left-branch 32-panel bound, represented exactly as a rational. -/
def si32LeftTubeBound : ℚ := 4908438476977142 / 10 ^ 25

/-- The archived right-branch 32-panel bound, represented exactly as a rational. -/
def si32RightTubeBound : ℚ := 44220273264006846 / 10 ^ 26

/-- The requested 32-panel phase-state tube radius. -/
def si32TubeTarget : ℚ := 1 / 10 ^ 9

theorem si32_tube_bounds_meet_target :
    si32LeftTubeBound < si32TubeTarget ∧
    si32RightTubeBound < si32TubeTarget := by
  norm_num [si32LeftTubeBound, si32RightTubeBound, si32TubeTarget]

end Imscribing.Gravity.OrbitAccuracy
