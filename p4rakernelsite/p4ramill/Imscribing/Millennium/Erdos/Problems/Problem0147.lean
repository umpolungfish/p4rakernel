import Mathlib
import Imscribing.Millennium.Erdos.Proofs.Janzer147.Main

/-!
# Erdős problem #147

Prize: $500.  Status as catalogued: **DISPROVED**.

Erdős conjectured that if H is a bipartite graph with minimum degree r, then
ex(H, n) ≥ C·n^{2-1/(r-1)+ε} for some ε > 0. This was disproved by showing
counterexamples where the exponent is smaller.
-/

open scoped BigOperators
open Finset
open scoped Topology
noncomputable section

def matching : SimpleGraph ℕ := {
  Adj := fun x y => ∃ (k : ℕ), (x = 2 * k ∧ y = 2 * k + 1) ∨ (x = 2 * k + 1 ∧ y = 2 * k),
  symm := by
    intro x y h
    rcases h with ⟨k, h | h⟩
    · exact ⟨k, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨k, Or.inl ⟨h.2, h.1⟩⟩
  loopless := ⟨by
    intro x h
    rcases h with ⟨k, h | h⟩ <;> omega⟩
}

/-- The infinite matching is bipartite: evens on one side, odds on the other. -/
lemma matching_is_bipartite : matching.IsBipartite := by
  rw [SimpleGraph.isBipartite_iff_exists_isBipartiteWith]
  refine ⟨{n | n % 2 = 0}, {n | n % 2 = 1}, ?_, ?_⟩
  · exact Set.disjoint_left.mpr (by intro n h₀ h₁; simp only [Set.mem_setOf_eq] at *; omega)
  · intro x y h
    rcases h with ⟨k, h | h⟩
    · left; rcases h with ⟨rfl, rfl⟩; simp
    · right; rcases h with ⟨rfl, rfl⟩; simp

/-- Every vertex has exactly one neighbor (its pair). -/
lemma matching_min_degree_one : ∀ (v : ℕ), 1 ≤ (matching.neighborSet v).encard := by
  intro v
  rw [Set.one_le_encard_iff_nonempty]
  by_cases hv : v % 2 = 0
  · refine ⟨v + 1, ?_⟩
    change ∃ k, (v = 2*k ∧ v+1 = 2*k+1) ∨ (v = 2*k+1 ∧ v+1 = 2*k)
    exact ⟨v / 2, Or.inl ⟨by omega, by omega⟩⟩
  · refine ⟨v - 1, ?_⟩
    change ∃ k, (v = 2*k ∧ v-1 = 2*k+1) ∨ (v = 2*k+1 ∧ v-1 = 2*k)
    exact ⟨v / 2, Or.inr ⟨by omega, by omega⟩⟩

lemma extremalNumber_one_matching : SimpleGraph.extremalNumber (1 : ℕ) matching = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [← Fintype.card_fin 1, SimpleGraph.extremalNumber_le_iff]
  intro G _ _
  exact le_trans G.card_edgeFinset_le_card_choose_two (by norm_num)

theorem legacy_universal_bound_false :
    ¬ (∀ r : ℕ, ∀ H : SimpleGraph ℕ, H.IsBipartite → (∀ v : ℕ, r ≤ (H.neighborSet v).encard) →
      ∃ ε > 0, ∀ n : ℕ, ∃ C > 0, C * (n : ℝ) ^ (2 - 1 / ((r - 1 : ℕ) : ℝ) + ε) ≤ (SimpleGraph.extremalNumber n H : ℝ)) := by
  intro h
  obtain ⟨ε, hε, hn⟩ := h 1 matching matching_is_bipartite matching_min_degree_one
  obtain ⟨C, hC, hbound⟩ := hn 1
  rw [extremalNumber_one_matching] at hbound
  norm_num at hbound
  linarith

/-- Counterexample: the infinite matching has min degree 1 but the conjecture fails. -/
lemma legacy_matching_counterexample :
    ∃ (r : ℕ) (H : SimpleGraph ℕ), H.IsBipartite ∧ (∀ v : ℕ, r ≤ (H.neighborSet v).encard) ∧
      ¬ (∃ ε > 0, ∀ n : ℕ, ∃ C > 0, C * (n : ℝ) ^ (2 - 1 / ((r - 1 : ℕ) : ℝ) + ε) ≤ (SimpleGraph.extremalNumber n H : ℝ)) := by
  refine ⟨1, matching, matching_is_bipartite, matching_min_degree_one, ?_⟩
  rintro ⟨ε, hε, hn⟩
  obtain ⟨C, hC, hbound⟩ := hn 1
  rw [extremalNumber_one_matching] at hbound
  norm_num at hbound
  linarith

namespace Erdos147

/-- The actual asymptotic conjecture: finite, nonempty bipartite graphs,
minimum degree at least two, and constants fixed before the eventual size. -/
def Conjecture : Prop :=
  ∀ (W : Type) [Fintype W] [Nonempty W]
    (H : SimpleGraph W) [DecidableRel H.Adj],
    H.IsBipartite → 2 ≤ H.minDegree → HasConjecturedLowerBound H H.minDegree

/-- The corrected finite-graph disproof obligation. -/
def Disproof : Prop := ¬ Conjecture

/-- Janzer's finite 4-regular counterexample refutes the actual asymptotic claim. -/
theorem erdos_problem_147 : Disproof := by
  intro h
  have hbound := h (Fin 12 × Fin 2) counterexampleGraph
    counterexampleGraph_isBipartite (by rw [counterexampleGraph_minDegree]; norm_num)
  rw [counterexampleGraph_minDegree] at hbound
  obtain ⟨ε, hε, hlower⟩ := hbound
  have hlt : witnessUpperExponent < 2 - 1 / ((4 : ℝ) - 1) + ε := by
    dsimp [witnessUpperExponent]
    norm_num at hε ⊢
    linarith
  exact (not_polynomialGrowth_isBigO_of_lt hlt)
    (hlower.trans counterexampleGraph_extremal_upper)

end Erdos147
