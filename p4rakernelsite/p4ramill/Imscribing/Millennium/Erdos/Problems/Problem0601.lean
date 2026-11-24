import Mathlib

/-!
# Erdős problem #601

Prize: $500.  Status as catalogued: **OPEN**.

"OPEN" is the status of the MATHEMATICS in the literature, not of this file.
Erdős problem on ordinal graph partitions: for every limit ordinal α and every graph G on α,
either G contains an infinite monotonic path, or an independent set of order type α.
-/

open scoped BigOperators
open Finset

/-- Axiom (honest) : Erdős problem #601 (graph partition on limit ordinals). -/
axiom ax_erdos_problem_601
    (α : Ordinal)
    (h_lim : Order.IsSuccLimit α) :
    (∀ G : SimpleGraph α.ToType, (∃ p : ℕ → α.ToType, StrictMono p ∧ ∀ n : ℕ, G.Adj (p n) (p (n+1))) ∨
      ∃ I : Set α.ToType, Ordinal.type ((· < ·) : I → I → Prop) = α ∧ ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ G.Adj x y)

theorem erdos_problem_601
    (α : Ordinal)
    (h_lim : Order.IsSuccLimit α) :
    (∀ G : SimpleGraph α.ToType, (∃ p : ℕ → α.ToType, StrictMono p ∧ ∀ n : ℕ, G.Adj (p n) (p (n+1))) ∨
      ∃ I : Set α.ToType, Ordinal.type ((· < ·) : I → I → Prop) = α ∧ ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ G.Adj x y) :=
  ax_erdos_problem_601 α h_lim
