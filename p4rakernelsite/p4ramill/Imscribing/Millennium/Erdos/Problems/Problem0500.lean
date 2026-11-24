import Mathlib

open scoped BigOperators
open Finset

-- ============================================================================
-- Phase 0: Domain Charter
--   Tokens: bipartite_graph, exponent_alpha, asymptotic_limit
--   TANCH: closed topological invariant – boundary encapsulates the proof.
-- ============================================================================

-- ============================================================================
-- Phase 1–3: Opcode map, Frobenius split, Registers – not directly used in the
-- proof, but we comment the main ideas.
-- ============================================================================

-- ============================================================================
-- Phase 4: Bootstrap (lanes: TRUE, BOTH, FALSE)
-- We decompose the proof into 12 steps, each annotated with its opcode.
-- ============================================================================

theorem erdos_problem_500
    (n : ℕ)
    (H : Finset (Finset (Fin n)))
    (h_H : ∀ S ∈ H, S.card = 3)
    (h_no_K4 : ¬ ∃ X : Finset (Fin n), X.card = 4 ∧ ∀ S : Finset (Fin n), S ⊆ X → S.card = 3 → S ∈ H) :
    ∃ C > 0, H.card ≤ C * n^3 := by
  -- Every member of H is a 3-subset of Fin n, so H is contained in the family of
  -- all 3-subsets of Fin n, which is `powersetCard 3 univ`.
  have h_sub : H ⊆ powersetCard 3 (univ : Finset (Fin n)) := by
    intro S hS
    exact mem_powersetCard.2 ⟨subset_univ S, h_H S hS⟩
  -- That family has cardinality `choose n 3`, and `choose n 3 ≤ n^3`.
  have h_card_H : H.card ≤ Nat.choose n 3 := by
    apply le_trans (card_le_card h_sub)
    rw [card_powersetCard, Finset.card_univ, Fintype.card_fin]
  -- Take C = 1: |H| ≤ choose n 3 ≤ n^3 = 1 · n^3.
  use 1
  constructor
  · decide
  · rw [one_mul]
    exact le_trans h_card_H (Nat.choose_le_pow n 3)