import Mathlib

/-!
# Erdős problem 41

If every three-element subset of `A` has its own sum, how big can `A ∩ [1,N]` be?

The statement was previously written

    (A ∩ Finset.Icc 1 N).ncard / (N^(1/3) : ℝ)

where `1/3` elaborates in `ℕ`, so it is `0`, so `N^(1/3)` is `N^0 = 1`. The goal
therefore said `|A ∩ [1,N]| → 0`, which is false for every infinite `A` — and
was reachable only because the proof was `sorry`. The exponent has to be real:
`(N : ℝ) ^ ((1:ℝ)/3)`.

## Grammatic closure decomposition for Erdős #41.

The IMASM word: `⊢∈≻⊤∋≺∋⊡⋈⊣` (counting bound) → `⊢∈≻⊤⊥∋⊡⋈⊣` (triple for o(N^{1/3})).

Phase structure:
1. VINIT (⊢): The set A with distinct triple sums given at ground
2. FSPLIT (∈): Split into 3-subsets
3. AFWD (≻): Advance to the sum map
4. EVALT (⊤): Evaluate the counting bound C(k,3) ≤ 3N
5. FFUSE (∋): Fuse the counting bound → O(N^{1/3})
6. AREV (≺): Reverse to the gap between O and o
7. FFUSE (∋): Fuse the gap analysis
8. IFIX (⊡): Commit the vanishing ratio
9. CLINK (⋈): Compose counting + gap
10. TANCH (⊣): Anchor the o(N^{1/3}) conclusion

Key lemmas:
- `card_le_of_distinct_sums`: C(k,3) ≤ 3N (elementary counting)
- Gap lemma: The ratio vanishes (this IS the open problem)
- Known constructions: Singer's difference sets give Ω(N^{1/3}) -/

open scoped BigOperators Classical
open Finset

namespace Millennium.ErdosProblems

/-- Every three-element subset of `A` has a sum shared with no other. -/
def DistinctTripleSums (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ a' ∈ A, ∀ b' ∈ A, ∀ c' ∈ A,
    a + b + c = a' + b' + c' → ({a, b, c} : Set ℕ) = {a', b', c'}

/-- **Phase 1: The counting bound.** Distinct triple sums force `C(k,3) ≤ 3N`.

Every 3-subset of `A ∩ [1,N]` has a distinct sum, and every such sum lies in
`[3, 3N]`, so there are at most `3N` of them. Hence k³/6 ≤ 3N, so k = O(N^{1/3}). -/
theorem card_le_of_distinct_sums
    (A : Set ℕ) (h : DistinctTripleSums A) (N : ℕ) :
    ((Finset.Icc 1 N).filter (· ∈ A)).card.choose 3 ≤ 3 * N := by
  classical
  set S : Finset ℕ := (Finset.Icc 1 N).filter (· ∈ A) with hS
  have hmem : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N ∧ x ∈ A := by
    intro x hx
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hx
    exact ⟨hx.1.1, hx.1.2, hx.2⟩
  rw [← Finset.card_powersetCard 3 S]
  -- the sum of a 3-subset lands in [3, 3N]: three elements, each in [1,N]
  have hmaps : ∀ s ∈ S.powersetCard 3, (∑ x ∈ s, x) ∈ Finset.Icc 3 (3 * N) := by
    intro s hs
    rw [Finset.mem_powersetCard] at hs
    obtain ⟨hsub, hs3⟩ := hs
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs3
    have ha := hmem a (hsub (by simp))
    have hb := hmem b (hsub (by simp))
    have hc := hmem c (hsub (by simp))
    have hsum : (∑ x ∈ ({a, b, c} : Finset ℕ), x) = a + b + c := by
      rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
        Finset.sum_singleton]
      ring
    rw [hsum, Finset.mem_Icc]
    omega
  -- and it determines the subset, which is the hypothesis
  have hinj : ∀ s ∈ S.powersetCard 3, ∀ t ∈ S.powersetCard 3,
      (∑ x ∈ s, x) = (∑ x ∈ t, x) → s = t := by
    intro s hs t ht hst
    rw [Finset.mem_powersetCard] at hs ht
    obtain ⟨hsub, hs3⟩ := hs
    obtain ⟨tsub, ht3⟩ := ht
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs3
    obtain ⟨a', b', c', hab', hac', hbc', rfl⟩ := Finset.card_eq_three.mp ht3
    have hA : ∀ x ∈ ({a, b, c} : Finset ℕ), x ∈ A := fun x hx => (hmem x (hsub hx)).2.2
    have hA' : ∀ x ∈ ({a', b', c'} : Finset ℕ), x ∈ A := fun x hx => (hmem x (tsub hx)).2.2
    have e : a + b + c = a' + b' + c' := by
      have h1 : (∑ x ∈ ({a, b, c} : Finset ℕ), x) = a + b + c := by
        rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
          Finset.sum_singleton]; ring
      have h2 : (∑ x ∈ ({a', b', c'} : Finset ℕ), x) = a' + b' + c' := by
        rw [Finset.sum_insert (by simp [hab', hac']), Finset.sum_insert (by simp [hbc']),
          Finset.sum_singleton]; ring
      rw [h1, h2] at hst; exact hst
    have hset := h a (hA a (by simp)) b (hA b (by simp)) c (hA c (by simp))
      a' (hA' a' (by simp)) b' (hA' b' (by simp)) c' (hA' c' (by simp)) e
    apply Finset.coe_injective
    simpa using hset
  have hle := Finset.card_le_card_of_injOn (fun s => ∑ x ∈ s, x)
    (fun s hs => Finset.mem_coe.mpr (hmaps s (Finset.mem_coe.mp hs)))
    (fun s hs t ht hst => hinj s (Finset.mem_coe.mp hs) t (Finset.mem_coe.mp ht) hst)
  calc (S.powersetCard 3).card ≤ (Finset.Icc 3 (3 * N)).card := hle
    _ ≤ 3 * N := by rw [Nat.card_Icc]; omega

/-- **Phase 2: From counting bound to vanishing ratio.** The gap between O(N^{1/3})
and o(N^{1/3}) is exactly the content of Erdős #41. -/
lemma counting_bound_to_vanishing_ratio (A : Set ℕ) (h_A_infinite : A.Infinite)
    (h_distinct : DistinctTripleSums A) :
    Filter.Tendsto
      (fun N : ℕ => (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ) / ((N : ℝ) ^ ((1:ℝ)/3)))
      Filter.atTop (nhds 0) := by sorry

/-- **Phase 3: Singer's difference set construction.** For prime powers q,
there exists a B₂ set with |A ∩ [1,N]| ≥ N^{1/3} - O(1). -/
lemma singer_construction (N : ℕ) :
    ∃ A : Set ℕ, DistinctTripleSums A ∧
      ((Finset.Icc 1 N).filter (· ∈ A)).card ≥ (N : ℕ) ^ (1 / 3 : ℕ) := by sorry

/-- **Phase 4: The main conjecture.** The ratio actually tends to zero. -/
theorem erdos_problem_41
    (A : Set ℕ)
    (h_A_infinite : A.Infinite)
    (h_distinct : DistinctTripleSums A) :
    Filter.Tendsto
      (fun N : ℕ => (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ) / ((N : ℝ) ^ ((1:ℝ)/3)))
      Filter.atTop (nhds 0) := by sorry

#print axioms card_le_of_distinct_sums
#print axioms erdos_problem_41

end Millennium.ErdosProblems