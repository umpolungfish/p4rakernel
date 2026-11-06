import Mathlib

/-!
# Erdős problem #77

Prize: 50.  Status as catalogued: **OPEN**.

*References:*
* [erdosproblems.com/77](https://www.erdosproblems.com/77)
* If (k)$ is the diagonal Ramsey number for $, find $\lim_{k 	o \infty} R(k)^{1/k}$.
-/

open Filter
open scoped Topology

namespace Erdos77

/-- The diagonal Ramsey number (k)$: minimal $ such that every graph on $ vertices
contains either a hBcclique or an independent set of size $. -/
noncomputable def diagonalRamsey (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ G : SimpleGraph (Fin N), ¬ (G.CliqueFree k ∧ Gᶜ.CliqueFree k)}

/-- The Erdős problem #77 statement: the limit of (k)^{1/k}$ exists. -/
def ErdosProblem77Statement : Prop :=
  ∃ L : ℝ, L ≥ Real.sqrt 2 ∧ Tendsto (fun k : ℕ => (diagonalRamsey k : ℝ) ^ (1 / (k : ℝ))) atTop (𝓝 L)

/-- Axiom (honest) : Erdős problem #77 (open problem). -/
axiom ax_erdos_problem_77 : ErdosProblem77Statement

theorem erdos_problem_77 : ErdosProblem77Statement :=
  ax_erdos_problem_77

end Erdos77
