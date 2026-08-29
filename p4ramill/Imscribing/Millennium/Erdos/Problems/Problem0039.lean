import Mathlib

/-!
# Erdős problem #39

Prize: $500.  Status as catalogued: **OPEN**.

Does there exist a B₂ sequence (Sidon set) A ⊆ ℕ such that for every ε > 0,
|A ∩ [1, N]| ≫ N^{1/2 - ε}?

A B₂ sequence is a set where all pairwise sums a+b (with a ≤ b) are distinct.

## Grammatic closure decomposition for Erdős #39.

The IMASM word: `⊢∈≻⊤∋⊡⋈⊣` (B₂ trivial bound) → `⊢∈≻⊤⊥∋⊡⋈⊣` (Sidon gap).

Phase structure:
1. VINIT (⊢): The set A given at ground
2. FSPLIT (∈): Split into pairs
3. AFWD (≻): Advance to sum map
4. EVALT (⊤): Evaluate the trivial bound |A|²/2 ≤ 2N → |A| ≤ √N
5. FFUSE (∋): Fuse the trivial bound → O(√N)
6. EVALF (⊥): Evaluate the gap between O(√N) and Ω(N^{1/2 - ε})
7. FFUSE (∋): Fuse the gap
8. IFIX (⊡): Commit the ε-improvement
9. CLINK (⋈): Compose bound + construction
10. TANCH (⊣): Anchor the N^{1/2 - ε} conclusion

Key lemmas:
- `B₂_trivial_bound`: |A ∩ [1,N]| ≤ √(2N) + 1 (elementary counting)
- `Singer_lower_bound`: |A ∩ [1,N]| ≥ √N - O(1) (Singer's difference sets)
- `Erdős_ε_conjecture`: |A ∩ [1,N]| ≫ N^{1/2 - ε} (open) -/

open scoped BigOperators
open Finset

def IsB2Set (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a + b = c + d → {a, b} = {c, d}

/-- **Phase 1: The trivial B₂ bound.** |A ∩ [1,N]| ≤ √(2N) + O(1). -/
lemma B₂_trivial_bound (A : Set ℕ) (hA : IsB2Set A) (N : ℕ) :
    (A ∩ Finset.Icc 1 N).card ≤ Int.toNat ⌈(Real.sqrt (2 * N) : ℝ)⌉₊ := by sorry

/-- **Phase 2: Singer's difference set construction.** There exist B₂ sets with
|A ∩ [1,N]| ≥ √N - O(1). -/
lemma Singer_lower_bound (N : ℕ) :
    ∃ A : Set ℕ, IsB2Set A ∧ (A ∩ Finset.Icc 1 N).card ≥ Int.toNat ⌈(Real.sqrt N : ℝ)⌉₊ := by sorry

/-- **Phase 3: The ε-gap lemma.** If B₂ sets could beat √N, they must have a specific
structure (multiplicative, not additive). -/
lemma epsilon_gap_lemma (A : Set ℕ) (hA : IsB2Set A) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in Filter.atTop, (A ∩ Finset.Icc 1 N).card ≤ (N : ℝ) ^ (1 / 2 - ε) → False := by sorry

/-- **Phase 4: The main conjecture.** Does there exist a B₂ set with
|A ∩ [1,N]| ≫ N^{1/2 - ε} for every ε > 0? -/
theorem erdos_problem_39 :
    ∃ A : Set ℕ, IsB2Set A ∧
      ∀ ε > 0, ∀ᶠ N in Filter.atTop, ∃ C > 0, C * (N : ℝ)^(1/2 - ε) ≤ ((A ∩ Finset.Icc 1 N).card : ℝ) := by sorry

/-- **Weaker version:** B₂ sets have size at least N^{1/2 - o(1)}. -/
lemma erdos_problem_39_weak :
    ∃ A : Set ℕ, IsB2Set A ∧
      ∀ ε > 0, ∀ᶠ N in Filter.atTop, (A ∩ Finset.Icc 1 N).card ≥ (N : ℕ)^(1/2 - ε) := by sorry