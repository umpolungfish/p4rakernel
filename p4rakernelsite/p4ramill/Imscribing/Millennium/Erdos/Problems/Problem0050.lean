import Mathlib

/-!
# Erdős problem #50

Prize: 50.  Status as catalogued: **OPEN**.

*References:*
* [erdosproblems.com/50](https://www.erdosproblems.com/50)
* [Er95] Erdős, Paul, Some of my favourite problems in number theory, combinatorics, and geometry.
* [Sch38] Schoenberg, I. J., On asymptotic distributions of arithmetical functions.

Let $ be the asymptotic distribution function of $arphi(n)/n$, so that for each  \in [0,1]$,
(c)$ is the natural density of $\{n : arphi(n) < cn\}$.
Is it true that there is no $ such that the derivative '(x)$ exists and is positive?
-/

open Filter Set MeasureTheory Topology
open scoped Nat Topology Classical

namespace Erdos50

/-- Natural density of a subset of ℕ. -/
def HasDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (((Finset.Icc 1 N).filter (· ∈ S)).card : ℝ) / (N : ℝ)) atTop (𝓝 d)

/-- A function  : ℝ → ℝ$ is the asymptotic distribution function of $arphi(n)/n$. -/
def IsDistributionOfPhiRatio (f : ℝ → ℝ) : Prop :=
  ∀ c ∈ Icc (0 : ℝ) 1, HasDensity {n : ℕ | (Nat.totient n : ℝ) < c * (n : ℝ)} (f c)

/-- The Erdős problem #50 statement: no point in 1$ has a strictly positive derivative. -/
def ErdosProblem50Statement : Prop :=
  ∀ (f : ℝ → ℝ), IsDistributionOfPhiRatio f →
    ¬∃ x ∈ Icc (0 : ℝ) 1, ∃ y > 0, HasDerivWithinAt f y (Icc 0 1) x

/-- Axiom (honest) : Erdős problem #50 (open problem). -/
axiom ax_erdos_problem_50 : ErdosProblem50Statement

theorem erdos_problem_50 : ErdosProblem50Statement :=
  ax_erdos_problem_50

end Erdos50
