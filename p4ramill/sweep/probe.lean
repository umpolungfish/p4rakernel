import Mathlib
import Imscribing.Classical.Szemeredi
open Finset
open scoped Classical
open Imscribing.Classical.Szemeredi

/-- Translation invariance at every `k`: a `k`-AP-free subset of an interval of
length `N` is no larger than `r_k k N`. -/
theorem card_le_r_k (k N m : ℕ) (A : Finset ℕ)
    (hsub : A ⊆ Finset.Ico m (m + N)) (hA : APFree k A) :
    A.card ≤ r_k k N := by
  set B : Finset ℕ := A.image (fun x => x - m) with hB
  have hmem : ∀ x ∈ A, m ≤ x ∧ x < m + N := by
    intro x hx
    have := hsub hx
    rw [Finset.mem_Ico] at this
    exact this
  -- the shift is injective on A, so cardinality is preserved
  have hinj : Set.InjOn (fun x => x - m) A := by
    intro x hx y hy hxy
    have hx' := hmem x hx
    have hy' := hmem y hy
    simp only at hxy
    omega
  have hcard : B.card = A.card := by
    rw [hB, Finset.card_image_of_injOn hinj]
  -- the shifted set lands in range N
  have hBsub : B ⊆ Finset.range N := by
    intro b hb
    rw [hB, Finset.mem_image] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    have := hmem x hx
    rw [Finset.mem_range]
    omega
  -- and is still progression-free: an AP in B lifts to one in A by adding m back
  have hBfree : APFree k B := by
    intro a d hd hcontra
    refine hA (a + m) d hd ?_
    intro i hi
    have hbi : a + i * d ∈ B := hcontra i hi
    rw [hB, Finset.mem_image] at hbi
    obtain ⟨x, hx, hxeq⟩ := hbi
    have := hmem x hx
    have : x = a + i * d + m := by omega
    subst this
    have : a + m + i * d = a + i * d + m := by ring
    rw [this]
    exact hx
  rw [← hcard]
  unfold r_k
  refine Finset.le_sup (f := fun A : Finset ℕ => A.card) ?_
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hBsub, hBfree⟩
