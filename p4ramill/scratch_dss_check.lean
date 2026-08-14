import Mathlib

open scoped BigOperators
open Finset Nat

def distinct_subset_sums (A : Finset ℕ) : Prop :=
  ∀ S T : Finset ℕ, S ⊆ A → T ⊆ A →
  S.sum id = T.sum id → S = T

/-- `{3,5,6,7}` has 16 subsets with 16 distinct sums, yet its fourth smallest
element is 7 < 8 = 2^3. So distinct subset sums does NOT force `elems[i] ≥ 2^i`. -/
theorem dss_counterexample :
    ¬ (∀ (A : Finset ℕ),
      A.Nonempty →
      distinct_subset_sums A →
      let elems := A.sort (· ≤ ·)
      ∀ i, (h : i < elems.length) → elems[i] ≥ 2 ^ i) := by
  intro h
  have hA : ({3, 5, 6, 7} : Finset ℕ).Nonempty := by decide
  -- `S ⊆ A` quantifies over all of `Finset ℕ` and carries no `Decidable`
  -- instance; membership in the powerset does, the powerset being concrete.
  have key : ∀ S ∈ ({3,5,6,7} : Finset ℕ).powerset,
             ∀ T ∈ ({3,5,6,7} : Finset ℕ).powerset,
             S.sum id = T.sum id → S = T := by decide
  have hdistinct : distinct_subset_sums {3,5,6,7} := fun S T hS hT hsum =>
    key S (Finset.mem_powerset.mpr hS) T (Finset.mem_powerset.mpr hT) hsum
  -- `Finset.sort` goes through `Multiset.sort` on a `Quot`, so neither `rfl` nor
  -- `decide` reduces it. Sort is pinned instead by its characterisation: sorted,
  -- and carrying the same multiset. That keeps the proof inside the kernel —
  -- `native_decide` would close it too, at the price of `Lean.trustCompiler`.
  have hsort : ({3,5,6,7} : Finset ℕ).sort (· ≤ ·) = [3,5,6,7] := by
    apply List.Perm.eq_of_pairwise' (Finset.pairwise_sort _ _) (by decide)
    rw [← Multiset.coe_eq_coe, Finset.sort_eq]
    decide
  have hbad := h {3,5,6,7} hA hdistinct 3 (by rw [hsort]; norm_num)
  simp only [hsort] at hbad
  norm_num at hbad

#print axioms dss_counterexample
