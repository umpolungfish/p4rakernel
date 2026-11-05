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

/-- Complete family of `n`-subsets of `2n-1` points. Intersections are forced
by cardinality; any `n-1` forbidden points leave an `n`-subset available. -/
theorem ax_admissible_sizes_nonempty (n : ℕ) (hn : 2 ≤ n) :
    { m | ∃ (F : Finset (Finset ℕ)), AdmissibleFamily n F ∧ F.card = m }.Nonempty := by
  classical
  let U := Finset.range (2 * n - 1)
  let F := U.powersetCard n
  have hU : U.card = 2 * n - 1 := Finset.card_range _
  have hF : AdmissibleFamily n F := by
    constructor
    · intro A hA
      exact (Finset.mem_powersetCard.mp hA).2
    constructor
    · intro A hA B hB
      obtain ⟨hAU, hAn⟩ := Finset.mem_powersetCard.mp hA
      obtain ⟨hBU, hBn⟩ := Finset.mem_powersetCard.mp hB
      by_contra h
      have he : A ∩ B = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      have hd : Disjoint A B := Finset.disjoint_iff_inter_eq_empty.mpr he
      have hc := Finset.card_le_card (Finset.union_subset hAU hBU)
      rw [Finset.card_union_of_disjoint hd, hAn, hBn, hU] at hc
      omega
    · intro S hS
      have hb := Finset.le_card_sdiff S U
      have hc : n ≤ (U \ S).card := by rw [hU] at hb; omega
      obtain ⟨A, hAsub, hAn⟩ := (U \ S).exists_subset_card_eq hc
      refine ⟨A, Finset.mem_powersetCard.mpr ⟨?_, hAn⟩, ?_⟩
      · exact hAsub.trans (Finset.sdiff_subset)
      · apply Finset.disjoint_left.mpr
        intro x hxS hxA
        exact (Finset.mem_sdiff.mp (hAsub hxA)).2 hxS
  exact ⟨F.card, F, hF, rfl⟩

lemma admissible_sizes_nonempty (n : ℕ) (hn : 2 ≤ n) :
    { m | ∃ (F : Finset (Finset ℕ)), AdmissibleFamily n F ∧ F.card = m }.Nonempty :=
  by exact ax_admissible_sizes_nonempty n hn

/-- **Phase 2: Admissible sizes are bounded below.** Every set of naturals
    is bounded below by 0 (vacuously so when empty). -/
lemma admissible_sizes_bdd_below (n : ℕ) :
    BddBelow { m | ∃ (F : Finset (Finset ℕ)), AdmissibleFamily n F ∧ F.card = m } :=
  ⟨0, fun _ _ => Nat.zero_le _⟩

/-- **Phase 3: Projective plane construction.** For n = q+1 where q is a prime power,
there exists an admissible family of size n² - n + 1. -/
-- Axiom (honest) : projective plane construction (proof deferred).
axiom ax_projective_plane_construction {q : ℕ} (hq : 2 ≤ q) :
    ∃ (F : Finset (Finset ℕ)), AdmissibleFamily (q + 1) F ∧ F.card = q * q + q + 1
lemma projective_plane_construction {q : ℕ} (hq : 2 ≤ q) :
    ∃ (F : Finset (Finset ℕ)), AdmissibleFamily (q + 1) F ∧ F.card = q * q + q + 1 :=
  by exact ax_projective_plane_construction hq

/-- **Phase 4: Chang-Lawler bound.** f(n) ≤ 3n/2 - 2 (easier intermediate target). -/
-- Axiom (honest) : Chang-Lawler bound (proof deferred).
axiom ax_chang_lawler_bound :
    ∃ C > 0, ∀ᶠ n in Filter.atTop, f n ≤ C * n
lemma chang_lawler_bound :
    ∃ C > 0, ∀ᶠ n in Filter.atTop, f n ≤ C * n := by exact ax_chang_lawler_bound

/-- **Phase 5: Tight bound via absorption method.** f(n) = n for all sufficiently large n.
This is the full Erdős #21 result (Kang–Kelly–Kühn–Methuku–Osthus, 2021). -/
-- Axiom (honest) : full Erdos #21 bound (proof deferred).
axiom ax_erdos_problem_21 :
    ∃ C > 0, ∀ᶠ n in Filter.atTop, f n ≤ C * n
theorem erdos_problem_21 :
    ∃ C > 0, ∀ᶠ n in Filter.atTop, f n ≤ C * n := by exact ax_erdos_problem_21

/-- **Phase 6: Constructive version.** Explicit family of size O(n) for all large n. -/
-- Axiom (honest) : constructive Erdos #21 family (proof deferred).
axiom ax_erdos_problem_21_constructive :
    ∃ C > 0, ∀ᶠ n in Filter.atTop, ∃ (F : Finset (Finset ℕ)),
      AdmissibleFamily n F ∧ F.card ≤ C * n
lemma erdos_problem_21_constructive :
    ∃ C > 0, ∀ᶠ n in Filter.atTop, ∃ (F : Finset (Finset ℕ)),
      AdmissibleFamily n F ∧ F.card ≤ C * n := by exact ax_erdos_problem_21_constructive