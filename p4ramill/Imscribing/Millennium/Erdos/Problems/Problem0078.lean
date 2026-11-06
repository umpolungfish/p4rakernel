import Mathlib

/-!
# Erdős problem #78

Prize: 00.  Status as catalogued: **OPEN**.

*References:*
* [erdosproblems.com/78](https://www.erdosproblems.com/78)
* Explicit Ramsey graphs: construct graphs on n vertices whose largest clique
  and largest independent set both have size O(log n).
-/

open Filter Real
open scoped Topology

namespace Erdos78

/-- A graph on Fin n has no homogeneous set of size k. -/
def NoHomogeneousSet {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  G.CliqueFree k ∧ Gᶜ.CliqueFree k

/-- The Erdős problem #78 statement. -/
def ErdosProblem78Statement : Prop :=
  ∃ c > (0 : ℝ), ∃ G : (n : ℕ) → SimpleGraph (Fin n),
    ∀ᶠ n in atTop, NoHomogeneousSet (G n) ⌈c * Real.log (n : ℝ)⌉₊

/-- Axiom (honest) : Erdős problem #78 (open problem). -/
axiom ax_erdos_problem_78 : ErdosProblem78Statement

theorem erdos_problem_78 : ErdosProblem78Statement :=
  ax_erdos_problem_78

end Erdos78
