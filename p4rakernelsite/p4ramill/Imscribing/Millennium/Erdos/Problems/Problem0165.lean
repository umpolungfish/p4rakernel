import Mathlib

/-!
# Erdős problem #165

Prize: 50.  Status as catalogued: **OPEN**.

*Reference:* [erdosproblems.com/165](https://www.erdosproblems.com/165)

Give an asymptotic formula for the off-diagonal Ramsey number R(3,k).
Campos et al. and Hefty et al. conjecture that R(3,k) ~ k² / (2 log k).
-/

open Filter Asymptotics
open scoped Topology Classical

noncomputable section

namespace Erdos165

/-- The Ramsey number R(3, k): minimal N such that every graph on Fin N contains a triangle
or an independent set of size k. -/
def classicalRamsey3 (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ G : SimpleGraph (Fin N), ¬ (G.CliqueFree 3 ∧ Gᶜ.CliqueFree k)}

/-- The Erdős problem #165 statement: R(3,k) ~ k^2 / (2 * log k). -/
def ErdosProblem165Statement : Prop :=
  (fun k : ℕ => (classicalRamsey3 k : ℝ)) ~[atTop] (fun k : ℕ => (k : ℝ) ^ 2 / (2 * Real.log (k : ℝ)))

/-- Axiom (honest) : Erdős problem #165 (open problem). -/
axiom ax_erdos_problem_165 : ErdosProblem165Statement

theorem erdos_problem_165 : ErdosProblem165Statement :=
  ax_erdos_problem_165

end Erdos165
