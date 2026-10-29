import Mathlib

/-!
# Erdős problem #140 (Roth's theorem for 3-AP-free sets)

Prize: $500.  Status as catalogued: **PROVED**.

Let r₃(N) be the maximum size of a subset of {1, ..., N} with no 3-term arithmetic progression.
Roth's theorem: r₃(N) = o(N). Best known bound: r₃(N) ≤ C·N / (log N)^(1+o(1)) (Bloom–Sisask, 2020; Kelley–Meka, 2023).

## Grammatic closure decomposition for Erdős #140.

The IMASM word: `⊢∈≻⊤∋⊡⋈⊣` (Roth density increment) → `⊢∈≻⊤⊥∋⊡⋈⊣` (Bloom-Sisask).

Phase structure:
1. VINIT (⊢): The set A ⊆ [1,N] given at ground
2. FSPLIT (∈): Split into 3-AP-free subsets
3. AFWD (≻): Advance to density increment
4. EVALT (⊤): Evaluate the density increment step
6. FFUSE (∋): Fuse the iteration → o(N)
7. EVALF (⊥): Evaluate the gap between o(N) and C·N/(log N)^{1+c}
8. FFUSE (∋): Fuse the logarithmic improvement
9. IFIX (⊡): Commit the C·N/(log N)^{1+c} bound
10. CLINK (⋈): Compose density increment + log improvement
11. TANCH (⊣): Anchor the final bound

Key lemmas:
- `three_ap_of_dense`: Dense window forces 3-AP (Roth)
- `roth_theorem`: r₃(N) = o(N) (Roth 1953)
- `bloom_sisask_bound`: r₃(N) ≤ C·N/(log N)^{1+c} (Bloom–Sisask 2020)
- `kelley_meka_bound`: r₃(N) ≤ C·N/(log N)^{1+o(1)} (Kelley–Meka 2023) -/

open scoped BigOperators
open Finset

def is_3AP_free (A : Finset ℕ) : Prop :=
  ∀ a b c ∈ A, a + b = 2 * c → a = b

def r3 (N : ℕ) : ℕ :=
  sSup { n | ∃ A : Finset ℕ, A.card = n ∧ A ⊆ Finset.Icc 1 N ∧ is_3AP_free A }

/-- **Phase 1: Density increment lemma.** If A ⊆ [1,N] has density δ and no 3-AP,
there exists a subprogression where A has density δ + c·δ². -/
lemma density_increment (A : Finset ℕ) (hA : is_3AP_free A) (N : ℕ) (hA_sub : A ⊆ Finset.Icc 1 N) :
    ∃ δ > 0, ∃ N' ≤ N, ∃ A' : Finset ℕ, A' ⊆ Finset.Icc 1 N' ∧ is_3AP_free A' ∧
      A'.card ≥ (A.card : ℚ) / N * N' + (A.card : ℚ)^2 / N^2 := by sorry

/-- **Phase 2: Roth's theorem.** r₃(N) = o(N). -/
theorem roth_theorem :
    ∀ ε > 0, ∀ᶠ N in Filter.atTop, (r3 N : ℝ) ≤ ε * N := by sorry

/-- **Phase 3: Bloom–Sisask bound.** r₃(N) ≤ C·N / (log N)^{1+c}. -/
theorem bloom_sisask_bound :
    ∃ C > 0, ∃ c > 0, ∀ᶠ N in Filter.atTop, (r3 N : ℝ) ≤ C * N / (Real.log N) ^ (1 + c) := by sorry

/-- **Phase 4: Kelley–Meka bound.** r₃(N) ≤ C·N / (log N)^{1+o(1)}. -/
theorem kelley_meka_bound :
    ∀ ε > 0, ∃ C > 0, ∀ᶠ N in Filter.atTop, (r3 N : ℝ) ≤ C * N / (Real.log N) ^ (1 + ε) := by sorry

/-- **Phase 5: Original problem #140 statement.** -/
theorem erdos_problem_140
    (r3_func : ℕ → ℕ)
    (h_r3 : ∀ N, r3_func N = sSup { n | ∃ A : Finset ℕ, A.card = n ∧ A ⊆ Finset.Icc 1 N ∧ is_3AP_free A }) :
    ∀ C > 0, ∀ᶠ N in Filter.atTop, r3_func N ≤ C * N / (Real.log N) ^ C := by sorry