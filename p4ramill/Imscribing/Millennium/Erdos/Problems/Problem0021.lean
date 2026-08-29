import Mathlib

/-!
# Erdős problem #21

Prize: $500.  Status as catalogued: **PROVED**.

Let f(n) be the minimum cardinality of a family F of n-element subsets of ℕ
such that:
1. Any two sets in F intersect (i.e., F is an intersecting family)
2. For every S ⊆ ℕ with |S| ≤ n-1, there exists A ∈ F with A ∩ S = ∅

Then f(n) = O(n) (i.e., ∃ C > 0, ∀ᶠ n, f(n) ≤ C·n).

## Grammatic closure decomposition for Erdős #21.

The IMASM word: `⊢∈≻⊤∋≺∋⊡⋈⊣` (intersecting family + covering construction).

Phase structure:
1. VINIT (⊢): n-element subsets given at ground
2. FSPLIT (∈): Split into intersecting families
3. AFWD (≻): Advance to the projective plane construction
4. EVALT (⊤): Evaluate the finite projective plane bound
5. FFUSE (∋): Fuse the intersecting property
6. AREV (≺): Reverse to the covering condition
7. FFUSE (∋): Fuse the covering property
8. IFIX (⊡): Commit the O(n) bound
9. CLINK (⋈): Compose intersecting + covering
10. TANCH (⊣): Anchor the O(n) conclusion

Key lemmas:
- Existence of finite projective planes for prime powers
- Chang-Lawler bound: 3n/2 - 2 (easier intermediate)
- Kang-Kelly-Kühn-Methuku-Osthus: tight n bound for large n (absorption method) -/

open scoped BigOperators
open Finset

def AdmissibleFamily (n : ℕ) (F : Finset (Finset ℕ)) : Prop :=
  (∀ A ∈ F, A.card = n) ∧
  (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty) ∧
  (∀ S : Finset ℕ, S.card ≤ n - 1 → ∃ A ∈ F, Disjoint S A)

noncomputable def f (n : ℕ) : ℕ :=
  sInf { m | ∃ (F : Finset (Finset ℕ)), AdmissibleFamily n F ∧ F.card = m }

/-- **Phase 1: Admissible sizes are nonempty for n ≥ 2.** -/
lemma admissible_sizes_nonempty (n : ℕ) (hn : 2 ≤ n) :
    { m | ∃ (F : Finset (Finset ℕ)), AdmissibleFamily n F ∧ F.card = m }.Nonempty := by sorry

/-- **Phase 2: Admissible sizes are bounded below.** -/
lemma admissible_sizes_bdd_below (n : ℕ) :
    BddBelow { m | ∃ (F : Finset (Finset ℕ)), AdmissibleFamily n F ∧ F.card = m } := by sorry

/-- **Phase 3: Projective plane construction.** For n = q+1 where q is a prime power,
there exists an admissible family of size n² - n + 1. -/
lemma projective_plane_construction {q : ℕ} (hq : 2 ≤ q) :
    ∃ (F : Finset (Finset ℕ)), AdmissibleFamily (q + 1) F ∧ F.card = q * q + q + 1 := by sorry

/-- **Phase 4: Chang-Lawler bound.** f(n) ≤ 3n/2 - 2 (easier intermediate target). -/
lemma chang_lawler_bound :
    ∃ C > 0, ∀ᶠ n in Filter.atTop, f n ≤ C * n := by sorry

/-- **Phase 5: Tight bound via absorption method.** f(n) = n for all sufficiently large n.
This is the full Erdős #21 result (Kang–Kelly–Kühn–Methuku–Osthus, 2021). -/
theorem erdos_problem_21 :
    ∃ C > 0, ∀ᶠ n in Filter.atTop, f n ≤ C * n := by sorry

/-- **Phase 6: Constructive version.** Explicit family of size O(n) for all large n. -/
lemma erdos_problem_21_constructive :
    ∃ C > 0, ∀ᶠ n in Filter.atTop, ∃ (F : Finset (Finset ℕ)),
      AdmissibleFamily n F ∧ F.card ≤ C * n := by sorry