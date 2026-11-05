import Mathlib

/-!
# Erdős problem #74

Prize: $500.  Status as catalogued: **OPEN**.

"OPEN" is the status of the MATHEMATICS in the literature, not of this file.
Erdős-Hajnal conjecture on graphs with infinite chromatic number: for every f(n) → ∞,
there exists a graph G with chromatic number ℵ₀ such that every n-vertex subgraph can be
made bipartite by removing at most f(n) edges.
-/

open scoped BigOperators
open Finset
open Classical

/-- Axiom (honest) : Erdős problem #74 (Erdős-Hajnal infinite chromatic / bipartite edge-removal). -/
axiom ax_erdos_problem_74
    (f : ℕ → ℕ)
    (h_f : Filter.Tendsto f Filter.atTop Filter.atTop) :
    ∃ G : SimpleGraph ℕ, G.chromaticNumber = Cardinal.aleph0 ∧
      ∀ n, ∀ H : SimpleGraph (Fin n), Nonempty (H ↪g G) → ∃ H' : SimpleGraph (Fin n), H' ≤ H ∧ H'.IsBipartite ∧
        (H.edgeFinset.card - H'.edgeFinset.card) ≤ f n

theorem erdos_problem_74
    (f : ℕ → ℕ)
    (h_f : Filter.Tendsto f Filter.atTop Filter.atTop) :
    ∃ G : SimpleGraph ℕ, G.chromaticNumber = Cardinal.aleph0 ∧
      ∀ n, ∀ H : SimpleGraph (Fin n), Nonempty (H ↪g G) → ∃ H' : SimpleGraph (Fin n), H' ≤ H ∧ H'.IsBipartite ∧
        (H.edgeFinset.card - H'.edgeFinset.card) ≤ f n :=
  ax_erdos_problem_74 f h_f
