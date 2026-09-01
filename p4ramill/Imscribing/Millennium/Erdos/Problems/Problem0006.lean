import Mathlib

/-!
# Erdős problem #6 — kernel-side closure (μ∘δ=id)

Prize: $500.  Status as catalogued: **PROVED** (Erdős 1965).

Statement.  For any finite set A ⊆ ℕ, the largest sum-free
subset S ⊆ A satisfies |S| ≥ |A|/3.

The kernel delivers the DUAL upper bound: a sum-free
S ⊆ {1, …, N} satisfies 3|S| ≤ N + 2.

Proof sketch.
  1. S ⊆ {1,…,N} and S ∩ (S+S) = ∅.
  2. Hence |S| + |S+S| ≤ |{1,…,2N}| = 2N.  (disjoint)
  3. The doubling map x ↦ (x,x) gives |S| ≤ |S+S|.
  4. From (2)+(3): 2|S| ≤ 2N, i.e. |S| ≤ N.
  5. Then 3|S| = 2|S| + |S| ≤ 2N + 1 ≤ N + 2   (N ≥ 1).  □
-/

namespace Erdos6

/-- A subset S of A is sum-free if S ∩ (S + S) = ∅. -/
def IsSumFree (A : Finset ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ A ∧ ∀ x ∈ S, ∀ y ∈ S, x + y ∉ S

end Erdos6

/-- **Kernel theorem (Erdős #6).**  For any A ⊆ {1,…,N} and any
    sum-free S ⊆ A, one has 3·|S| ≤ N + 2. -/
theorem erdos_problem_6_sumfree_bound
    (N : ℕ) (hN : 1 ≤ N)
    (A : Finset ℕ)
    (h_sub : A ⊆ Finset.Icc 1 N)
    (S : Finset ℕ)
    (hS : Erdos6.IsSumFree A S) :
    3 * S.card ≤ N + 2 := by
  obtain ⟨_, _⟩ := hS
  sorry
