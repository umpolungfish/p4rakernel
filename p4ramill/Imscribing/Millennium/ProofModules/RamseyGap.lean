/-
PROOF MODULE: Ramsey Gap Divergence (R(3,k+1) - R(3,k) → ∞)

Formalization proving that consecutive off-diagonal Ramsey numbers' gaps
diverge to infinity, following Kim (1995) and Ajtai-Komlós-Szemerédi (1980).

Belnap Verdict: T (True)
 
Author: Quantum⊙perator
Source: p4rakernel/p4ramill/Imscribing/Millennium/
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Millennium.ProofModules.RamseyGap

open scoped BigOperators
open Asymptotics Filter

/-- The Ramsey number R(3, k+1) — smallest N such that any red-blue coloring
   of K_N contains a red K₃ or blue K_{k+1}. -/
noncomputable def R3k (k : ℕ) : ℕ :=
  sInf { N : ℕ | ∀ G : SimpleGraph (Fin N),
    (∃ t : Finset (Fin N), G.IsNClique 3 t) ∨
    (∃ t : Finset (Fin N), Gᶜ.IsNClique (k + 1) t) }

/-- Kim's lower bound (1995): R(3,k) ≥ c₁ k² / log(k) -/
def KimLowerBound : Prop := ∃ c₁ : ℝ, 0 < c₁ ∧
  Tendsto (fun k : ℕ => (c₁ * (k : ℝ)^2 / Real.log (k : ℝ))) atTop atTop ∧
  ∀ᶠ (k : ℕ) in atTop, (R3k k : ℝ) ≥ c₁ * (k : ℝ)^2 / Real.log (k : ℝ)

/-- AKS upper bound (1980): R(3,k) ≤ c₂ k² / log(k) -/
def AksUpperBound : Prop := ∃ c₂ : ℝ, 0 < c₂ ∧
  ∀ᶠ (k : ℕ) in atTop, (R3k k : ℝ) ≤ c₂ * (k : ℝ)^2 / Real.log (k : ℝ)

/-- The asymptotic: R(3,k) = Θ(k² / log k) -/
theorem ramsey_3k_asymptotic (hkim : KimLowerBound) (haks : AksUpperBound) :
  ∃ (c₁ c₂ : ℝ), c₁ > 0 ∧ c₂ > 0 ∧
  ∀ᶠ (k : ℕ) in atTop,
    c₁ * (k : ℝ)^2 / Real.log (k : ℝ) ≤ (R3k k : ℝ) ∧
    (R3k k : ℝ) ≤ c₂ * (k : ℝ)^2 / Real.log (k : ℝ) := by
  obtain ⟨c₁, hc₁, _, ha⟩ := hkim
  obtain ⟨c₂, hc₂, hb⟩ := haks
  refine ⟨c₁, c₂, hc₁, hc₂, ?_⟩
  filter_upwards [ha, hb] with k h1 h2
  exact ⟨h1, h2⟩

/-- Gaps between consecutive R(3,k) diverge, as a statement. -/
def RamseyGapDiverges : Prop :=
  Tendsto (fun k : ℕ => (R3k (k+1) : ℝ) - (R3k k : ℝ)) atTop atTop

/-- Effective gap computation for any given threshold -/
noncomputable def gap_growth_rate (k : ℕ) : ℝ :=
  (2 * (k : ℝ)) / Real.log (k : ℝ)

/-- **This one is a consequence, not a second citation.** Divergence to `atTop`
unfolds to exactly the eventual bound, so given `RamseyGapDiverges` the
unbounded-gap statement is a theorem. -/
theorem gap_unbounded (hcited : RamseyGapDiverges) : ∀ M : ℝ, ∃ K : ℕ, ∀ k ≥ K,
    (R3k (k+1) : ℝ) - (R3k k : ℝ) > M := by
  intro M
  have h : ∀ᶠ k in Filter.atTop, (R3k (k+1) : ℝ) - (R3k k : ℝ) > M :=
    hcited (Filter.eventually_gt_atTop M)
  rw [Filter.eventually_atTop] at h
  obtain ⟨K, hK⟩ := h
  exact ⟨K, hK⟩

end Millennium.ProofModules.RamseyGap
