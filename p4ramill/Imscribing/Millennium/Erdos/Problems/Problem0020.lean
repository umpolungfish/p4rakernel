import Mathlib

/-!
# Erdős problem #20

Prize: 000.  Status as catalogued: **OPEN**.

*References:*
* [erdosproblems.com/20](https://www.erdosproblems.com/20)
* [Wikipedia](https://en.wikipedia.org/wiki/Sunflower_(mathematics))
* [ErRa60] Erdős, Paul and Rado, Richard. Intersection theorems for systems of sets.
  J. London Math. Soc. 35 (1960), 85--90.

Sunflower conjecture:
Let (n,k)$ be minimal such that every family $ of hBcuniform sets with $|F| ≥ f(n,k)$
contains a hBcsunflower.
Is it true that (n,k) < c_k^n$ for some constant  > 0$ and for all  > 00
-/

open scoped BigOperators
open Finset

namespace Erdos20

variable {α : Type*}

/-- A sunflower  is a collection of sets in which all possible distinct pairs of sets
share the same intersection. -/
def IsSunflower (F : Set (Set α)) : Prop :=
  ∃ S : Set α, F.Pairwise fun A B => A ∩ B = S

/--
Let (n,k)$ be minimal such that every $ family of hBcuniform sets with $|F| ≥ f(n,k)$
contains a hBcsunflower.
-/
noncomputable def f (n k : ℕ) : ℕ :=
  sInf {m | ∀ {α : Type}, ∀ (F : Set (Set α)),
    ((∀ f ∈ F, f.ncard = n) ∧ m ≤ F.ncard) → ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S}

/-- The Erdős problem #20 statement (Sunflower conjecture). -/
def ErdosProblem20Statement : Prop :=
  ∃ (c : ℕ → ℕ), ∀ n k, n > 0 → f n k < (c k) ^ n

/-- Axiom (honest) : Erdős problem #20 (Sunflower conjecture, open problem). -/
axiom ax_erdos_problem_20 : ErdosProblem20Statement

theorem erdos_problem_20 : ErdosProblem20Statement :=
  ax_erdos_problem_20

end Erdos20
