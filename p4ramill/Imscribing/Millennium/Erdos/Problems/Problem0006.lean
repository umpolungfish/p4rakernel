import Mathlib

/-!
# Sum-free subsets: the sharp interval bound

For sum-free `S ⊆ [1,N]`, reflect `S` about its largest element.
The reflection is injective and disjoint from `S`, and both sets fit inside
`[0,N]`. Their retained union proves `2|S| ≤ N+1`.
-/

namespace Erdos6

/-- A subset S of A is sum-free if S ∩ (S + S) = ∅. -/
def IsSumFree (A : Finset ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ A ∧ ∀ x ∈ S, ∀ y ∈ S, x + y ∉ S

end Erdos6

/-- **Kernel theorem (Erdős #6), corrected.**  The bound as previously
    stated here (`3·|S| ≤ N + 2`) is FALSE: `N = 11`, `S = {6,…,11}` is
    sum-free (`x,y ≥ 6 → x+y ≥ 12 > 11`) with `3·6 = 18 > 13 = N+2`.
    What holds trivially from `S ⊆ A ⊆ [1,N]` is `|S| ≤ N`. The sharp
    upper bound `2·|S| ≤ N+1` (attained by `(N/2,N]`) is kept as an
    explicit theorem; the Erdős–1965 `|S| ≥ |A|/3` existence theorem is
    the open/formalization-gap marker. -/
theorem erdos_problem_6_sumfree_bound_trivial
    (N : ℕ) (hN : 1 ≤ N)
    (A : Finset ℕ)
    (h_sub : A ⊆ Finset.Icc 1 N)
    (S : Finset ℕ)
    (hS : Erdos6.IsSumFree A S) :
    S.card ≤ N := by
  obtain ⟨hSA, _⟩ := hS
  calc S.card ≤ A.card := Finset.card_le_card hSA
    _ ≤ (Finset.Icc 1 N).card := Finset.card_le_card h_sub
    _ = N := by simp

/-- Sharp upper bound, proved by the disjoint reflected copy. -/
theorem erdos_problem_6_sumfree_bound_sharp
    (N : ℕ) (hN : 1 ≤ N)
    (A : Finset ℕ)
    (h_sub : A ⊆ Finset.Icc 1 N)
    (S : Finset ℕ)
    (hS : Erdos6.IsSumFree A S) :
    2 * S.card ≤ N + 1 := by
  classical
  by_cases hne : S.Nonempty
  · let m := S.max' hne
    have hm : m ∈ S := S.max'_mem hne
    have hmax : ∀ x ∈ S, x ≤ m := fun x hx => S.le_max' x hx
    have hmN : m ≤ N := (Finset.mem_Icc.mp (h_sub (hS.1 hm))).2
    let R := S.image (fun x => m - x)
    have hR : R.card = S.card := by
      apply Finset.card_image_of_injOn
      intro x hx y hy hxy
      change m - x = m - y at hxy
      have := hmax x hx
      have := hmax y hy
      omega
    have hd : Disjoint S R := by
      apply Finset.disjoint_left.mpr
      intro x hx hxR
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hxR
      have hy_le := hmax y hy
      have hsum : x + y = m := by omega
      exact hS.2 x hx y hy (hsum.symm ▸ hm)
    have hu : S ∪ R ⊆ Finset.range (N + 1) := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_range.mpr (by have := hmax x hx; omega)
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_range.mpr (by omega)
    have hc := Finset.card_le_card hu
    rw [Finset.card_union_of_disjoint hd, hR, Finset.card_range] at hc
    omega
  · have h : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [h]
