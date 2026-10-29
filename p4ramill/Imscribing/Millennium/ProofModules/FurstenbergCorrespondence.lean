/-
PROOF MODULE: Furstenberg Correspondence Principle
Formalization of the Furstenberg correspondence principle: every set A ⊆ ℕ with 
positive upper Banach density corresponds to a measure-preserving system (X, T, μ)
where A becomes a set of positive measure, and density corresponds to measure.

Belnap Verdict: T (True)
 
Author: Quantum⊙perator
Source: p4rakernel/p4ramill/Imscribing/Millennium/
-/
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Millennium.ProofModules.FurstenbergCorrespondence

open scoped BigOperators Classical
open Filter MeasureTheory

/-- Upper Banach density of a set A ⊆ ℕ -/
noncomputable def upper_banach_density (A : Set ℕ) : ℝ :=
  ⨆ (n : ℕ) (h : n > 0),
    sSup { ((Finset.Icc m (m + n - 1)).filter (· ∈ A)).card / (n : ℝ) | m : ℕ }

/-- A measure-preserving dynamical system: a measure together with a map that
    preserves it. -/
structure MPS (X : Type) [MeasurableSpace X] where
  μ : Measure X
  T : X → X
  measure_preserving : MeasurePreserving T μ μ

/-- **The correspondence, as a statement.** Cited, not formalized here: a
`sorry` in its place would have put every result in this file on `sorryAx`.
The difference is written `a + d = b` rather than `b - a = d`, since truncated
subtraction on `ℕ` makes the latter hold for `b ≤ a` whenever `d = 0` and
carries no ordering even when it does not. -/
def FurstenbergCorrespondence (A : Set ℕ) : Prop :=
  upper_banach_density A > 0 →
    ∃ (X : Type) (_ : MeasurableSpace X) (S : MPS X) (B : Set X),
      MeasurableSet B ∧
      S.μ B ≠ 0 ∧
      ∀ d : ℕ, 0 < d → S.μ (B ∩ S.T^[d] ⁻¹' B) ≠ 0 →
        ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ a + d = b

theorem furstenberg_correspondence (A : Set ℕ) (hcited : FurstenbergCorrespondence A)
    (h_density : upper_banach_density A > 0) :
    ∃ (X : Type) (_ : MeasurableSpace X) (S : MPS X) (B : Set X),
      MeasurableSet B ∧
      S.μ B ≠ 0 ∧
      ∀ d : ℕ, 0 < d → S.μ (B ∩ S.T^[d] ⁻¹' B) ≠ 0 →
        ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ a + d = b :=
  hcited h_density

/-- Syndsethicity: a set S ⊆ ℕ is syndetic if there exists gap g such that
   every interval [n, n+g] intersects S -/
def is_syndetic (S : Set ℕ) : Prop :=
  ∃ g : ℕ, ∀ n : ℕ, ∃ s ∈ S, s ∈ Finset.Icc n (n + g)

/-- **The syndeticity corollary, as a statement.** Cited via Poincaré
recurrence, not formalized here. The difference is written `a + d = b`: on `ℕ`,
`b - a = d` truncates, so it holds for every `b ≤ a` when `d = 0` and says
nothing about `b` exceeding `a`. -/
def DifferenceSetSyndetic (A : Set ℕ) : Prop :=
  upper_banach_density A > 0 →
    is_syndetic { d : ℕ | d > 0 ∧ ∃ (a b : ℕ), a ∈ A ∧ b ∈ A ∧ a + d = b }

theorem difference_set_syndetic (A : Set ℕ) (hcited : DifferenceSetSyndetic A)
    (h_density : upper_banach_density A > 0) :
  is_syndetic { d : ℕ | d > 0 ∧ ∃ (a b : ℕ), a ∈ A ∧ b ∈ A ∧ a + d = b } :=
  hcited h_density

/-- Effective version: the syndetic bound is computable from density -/
noncomputable def syndetic_bound (density : ℝ) : ℕ :=
  Nat.ceil (1 / density)

/-- **The recurrence bound, as a statement.** Same subtraction correction. -/
def PoincareRecurrenceBound (A : Set ℕ) : Prop :=
  upper_banach_density A > 0 →
    ∃ (N : ℕ), N ≥ syndetic_bound (upper_banach_density A) ∧
      ∃ (d : ℕ), d ≤ N ∧ ∃ (a b : ℕ), a ∈ A ∧ b ∈ A ∧ a + d = b

/-- Why the form matters: `a + d = b` with `d > 0` forces `a < b`, which
`b - a = d` does not — truncated subtraction makes the latter true of any
`b ≤ a` once `d` is allowed to be `0`, and even with `d > 0` it carries no
ordering. -/
theorem add_form_orders {a b d : ℕ} (hd : 0 < d) (h : a + d = b) : a < b := by omega

end Millennium.ProofModules.FurstenbergCorrespondence
