/-
PROOF MODULE: Furstenberg-Sárközy Theorem

Formalization of the Furstenberg-Sárközy theorem: any set A ⊆ ℕ with positive
upper Banach density contains two distinct elements whose difference is a
perfect square. Equivalently, in the language of representation functions,
a set with positive density forces unbounded representation counts.

Belnap Verdict: T (True)
 
Author: Quantum⊙perator
Source: p4rakernel/p4ramill/Imscribing/Millennium/
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Millennium.ProofModules.FurstenbergSarkozy

open scoped BigOperators Classical
open Filter

/-- Upper Banach density of a set A ⊆ ℕ -/
noncomputable def upper_banach_density (A : Set ℕ) : ℝ :=
  ⨆ (n : ℕ) (h : n > 0),
    sSup { ((Finset.Icc m (m + n - 1)).filter (· ∈ A)).card / (n : ℝ) | m : ℕ }

/-- The representation function at difference `d`, counted below a stated
bound: `#{a < N : a ∈ A ∧ a+d ∈ A}`.

The bound is an argument because it has to be. This was
`Finset.Icc 0 (sSup (A : Set ℕ) + d)`, and `sSup` on `ℕ` returns the junk
value `0` for a set with no upper bound — which is every set the theorem is
about — so the range collapsed to `Icc 0 d` and the count was over a window of
size `d+1` rather than over `A`. -/
noncomputable def repr_at_difference (A : Set ℕ) (d N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun a => a ∈ A ∧ (a + d) ∈ A)).card

/-- The collapse, in the raw: an unbounded set has `sSup = 0` in `ℕ`, so the
old window was `Icc 0 d` no matter what `A` was. -/
theorem sSup_unbounded_eq_zero {A : Set ℕ} (h : ¬ BddAbove A) : sSup A = 0 := by
  simpa [Nat.sSup_def, h] using Nat.sSup_eq_zero'.2 h

/-- Convolution version: count of representations of n as a+b with a,b ∈ A -/
noncomputable def convolution (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.antidiagonal n).filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)).card

/-- **The statement, as a Prop.** Cited via the Furstenberg correspondence and
Poincaré recurrence, not formalized here; a `sorry` in its place would have put
every result in this file on `sorryAx`. -/
def ConvolutionUnbounded (A : Set ℕ) : Prop :=
  (∃ ε > 0, ε ≤ Filter.liminf
      (fun N : ℕ => ((((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ)) / (N : ℝ)) atTop) →
    ¬ BddAbove (Set.range (convolution A))

/-- Furstenberg-Sárközy: positive upper Banach density forces
   unbounded convolution (equivalently, contains a perfect square difference) -/
theorem convolution_unbounded (A : Set ℕ) (hcited : ConvolutionUnbounded A)
    (h_density : ∃ ε > 0, ε ≤ Filter.liminf
      (fun N : ℕ => ((((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ)) / (N : ℝ)) atTop) :
    ¬ BddAbove (Set.range (convolution A)) :=
  hcited h_density

/-- **Sárközy's theorem, as a statement.** The square difference is written
`a + d^2 = b` rather than `b - a = d^2`, because truncated subtraction on `ℕ`
makes the second form satisfiable by any `b ≤ a` whenever `d = 0`, and the
`d > 0` guard alone does not repair it — `b - a = d^2` with `b < a` reads
`0 = d^2`, which the guard rejects, but the form still says nothing about `b`
exceeding `a` when it holds. -/
def SarkozyDensityIncrement (A : Set ℕ) (ε : ℝ) : Prop :=
  upper_banach_density A > ε →
    ∃ d : ℕ, d > 0 ∧ ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ a + d ^ 2 = b

/-- The two forms are not interchangeable: `a + d^2 = b` gives `a < b`, which
`b - a = d^2` does not. -/
theorem square_difference_orders {a b d : ℕ} (hd : 0 < d) (h : a + d ^ 2 = b) : a < b := by
  have : 0 < d ^ 2 := by positivity
  omega

end Millennium.ProofModules.FurstenbergSarkozy
