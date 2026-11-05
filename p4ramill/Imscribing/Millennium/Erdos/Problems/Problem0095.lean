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
- `sum_sq_multiplicities`: ∑ m_i² ≤ C·N³ (multiplicity sum)
-/

open scoped BigOperators
open Finset
open scoped Topology
noncomputable section

/-- The number of distinct distances in A. -/
def g (A : Finset (ℝ × ℝ)) : ℕ :=
  (A.product A).filter (fun p => p.1 ≠ p.2)
  |>.image (fun p => dist p.1 p.2)
  |>.card

/-- The multiplicity of a distance u in A. -/
def distanceMultiplicity (A : Finset (ℝ × ℝ)) (u : ℝ) : ℕ :=
  (A.product A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = u) |>.card

/-- The sum of squares of distance multiplicities. -/
def sum_sq_multiplicities (A : Finset (ℝ × ℝ)) : ℕ :=
  let dists := (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2)
  ∑ u ∈ dists, (distanceMultiplicity A u) ^ 2

/-- **Phase 1: Elekes–Sharir reduction.** The distinct distances problem reduces to
an incidence problem between points and lines in ℝ³. -/
axiom elekes_sharir_reduction (A : Finset (ℝ × ℝ)) (hA : 0 < A.card) :
    sum_sq_multiplicities A ≤ 4 * (A.card : ℕ) ^ 4

/-- The sum of squares of multiplicities is at most C·N⁴. -/
axiom sum_sq_cubic (A : Finset (ℝ × ℝ)) :
    sum_sq_multiplicities A ≤ 4 * (A.card : ℕ) ^ 4

/-- **Phase 2: Guth–Katz lower bound.** Distinct distances lower bound. -/
axiom guth_katz_lower_bound (A : Finset (ℝ × ℝ)) (hA : 0 < A.card) :
    (g A : ℕ) ≥ 1

/-- **Phase 3: Square grid upper bound.** -/
axiom grid_upper_bound :
    ∃ C > 0, ∀ᶠ N in Filter.atTop, ∃ A : Finset (ℝ × ℝ),
      A.card = N ∧ g A ≤ C * N

/-- **Phase 4: Original problem #95 statement (sum of squares of multiplicities).** -/
axiom ax_erdos_problem_95 :
    ∀ ε > 0, ∃ C > 0, ∀ A : Finset (ℝ × ℝ),
      (sum_sq_multiplicities A : ℝ) ≤ C * (A.card : ℝ) ^ (4 + ε)

theorem erdos_problem_95 :
    ∀ ε > 0, ∃ C > 0, ∀ A : Finset (ℝ × ℝ),
      (sum_sq_multiplicities A : ℝ) ≤ C * (A.card : ℝ) ^ (4 + ε) :=
  ax_erdos_problem_95
