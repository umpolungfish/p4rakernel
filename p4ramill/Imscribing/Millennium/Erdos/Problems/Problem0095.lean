import Mathlib

/-!
# Erdős problem #95 (Erdős distinct distances problem)

Prize: $500.  Status as catalogued: **PROVED** (Guth–Katz, 2010).

For any finite set A ⊂ ℝ² of N points, let g(A) be the number of distinct distances
determined by pairs of points in A. The problem asks for the minimum of g(A) over all
N-point sets A.

Guth–Katz proved g(A) ≥ C·N / log N. The known upper bound from the square grid
is g(A) ≤ C·N / √log N.

## Grammatic closure decomposition for Erdős #95.

The IMASM word: `⊢∈≻⊤∋⊡⋈⊣` (Elekes-Sharir framework) → `⊢∈≻⊤⊥∋⊡⋈⊣` (Guth-Katz polynomial partitioning).

Phase structure:
1. VINIT (⊢): The point set A ⊂ ℝ² given at ground
2. FSPLIT (∈): Split into distance multiplicities
3. AFWD (≻): Advance to Elekes-Sharir reduction
4. EVALT (⊤): Evaluate the incidence geometry bound
5. FFUSE (∋): Fuse the ES bound → N³/²
6. EVALF (⊥): Evaluate the gap between N³/² and N/log N
7. FFUSE (∋): Fuse the polynomial partitioning
8. IFIX (⊡): Commit the N/log N bound
9. CLINK (⋈): Compose ES + partitioning
10. TANCH (⊣): Anchor the Guth-Katz bound

Key lemmas:
- `guth_katz_lower_bound`: g(A) ≥ C·N / log N (Guth–Katz 2010)
- `grid_upper_bound`: g(A) ≤ C·N / √log N (square grid construction)
- `sum_sq_multiplicities`: ∑ m_i² ≤ C·N³ (multiplicity sum) -/

open scoped BigOperators
open Finset

/-- The number of distinct distances in A. -/
def g (A : Finset (ℝ × ℝ)) : ℕ :=
  (A.product A).filter (fun p => p.1 ≠ p.2)
  |>.image (fun p => dist p.1 p.2)
  |>.card

/-- The multiplicity of a distance u in A. -/
def multiplicity (A : Finset (ℝ × ℝ)) (u : ℝ) : ℕ :=
  (A.product A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = u) |>.card

/-- The sum of squares of distance multiplicities. -/
def sum_sq_multiplicities (A : Finset (ℝ × ℝ)) : ℕ :=
  let dists := (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2)
  ∑ u in dists, (multiplicity A u) ^ 2

/-- **Phase 1: Elekes–Sharir reduction.** The distinct distances problem reduces to
an incidence problem between points and lines in ℝ³. -/
lemma elekes_sharir_reduction (A : Finset (ℝ × ℝ)) (hA : 0 < A.card) :
    sum_sq_multiplicities A ≤ (A.card : ℕ) ^ 3 := by sorry

/-- **Phase 2: Guth–Katz lower bound.** g(A) ≥ C·N / log N. -/
theorem guth_katz_lower_bound (A : Finset (ℝ × ℝ)) (hA : 0 < A.card) :
    g A ≥ (A.card : ℕ) / (Nat.log (A.card + 1) + 1) := by sorry

/-- **Phase 3: Square grid upper bound.** For A = [√N] × [√N], g(A) ≤ C·N / √log N. -/
theorem grid_upper_bound :
    ∃ C > 0, ∀ᶠ N in Filter.atTop, ∃ A : Finset (ℝ × ℝ),
      A.card = N ∧ g A ≤ C * N / (Nat.log N + 1) := by sorry

/-- **Phase 4: Original problem #95 statement (sum of squares of multiplicities).** -/
theorem erdos_problem_95 :
    ∀ ε > 0, ∃ C > 0, ∀ A : Finset (ℝ × ℝ),
      sum_sq_multiplicities A ≤ C * A.card ^ (3 + ε) := by sorry

/-- **Phase 5: The sum of squares of multiplicities is at most C·N³.** -/
lemma sum_sq_cubic (A : Finset (ℝ × ℝ)) :
    sum_sq_multiplicities A ≤ (A.card : ℕ) ^ 3 := by sorry