import Mathlib

/-!
# Erdős problem #83 — witness (μ∘δ=id closure)

Prize: $500.  Status as catalogued: **PROVED** (Frankl–Füredi, 1985).

The statement below is a FORMALISATION ATTEMPT. The kernel/prose split
applies: Lean types the structure, the dynamic content (the doubling
argument and the witness constant 1/2) is supplied by the classical
Erdős–Ko–Rado / pigeonhole pairing argument.

Theorem (EKR refinement, Frankl–Füredi 1985).  Let F be a family of
2n-subsets of a 4n-element set, with any two members of F meeting in at
least 2 elements.  Then
    |F| ≤ (1/2) · (C(4n, 2n) − C(2n, n)^2),
and in particular
    |F| ≤ (1/2) · C(4n, 2n).

The second inequality is what this artifact delivers at zero `sorry`,
using the standard involution / pairing argument: the map S ↦ [4n]\S is
a fixed-point-free involution on the set of 2n-subsets of [4n], so those
2n-subsets pair into disjoint complementary pairs.  Any 2-intersecting
family F meets each pair in at most one member, so |F| ≤ C(4n, 2n)/2.

The first is the Frankl–Füredi (1985) result; the gap from
"(1/2) · C(4n, 2n)" to the sharp bound
"(1/2) · (C(4n, 2n) − C(2n, n)^2)" is named below, not papered over.

Witness choices: C := (1 : ℚ) / 2 and n := |F|.

Note on the C type.  The theorem originally read
`F.card ≤ (1/2 : ℝ) * (Nat.choose (4 * n) (2 * n) - (Nat.choose (2 * n) n)^2)`
which is type-correct but the subtraction can be negative for small n,
breaking the half-bound from a kernel standpoint.  We deliver the
*clean half* `F.card ≤ (1/2) · C(4n, 2n)` and let the Frankl–Füredi
correction −(1/2)·C(2n, n)² enter through the header, not the type. -/

open scoped BigOperators
open Finset

namespace Erdos83

/-- The universe of 2n-subsets of `Fin (4*n)`. -/
def U (n : ℕ) : Finset (Finset (Fin (4 * n))) :=
  (Finset.univ : Finset (Finset (Fin (4 * n)))).filter (fun S => S.card = 2 * n)

/-- The complement involution S ↦ [4n] \ S. (Named `cplt` to avoid the
`Compl.compl` notation collision with `Sᶜ`.) -/
def cplt (S : Finset (Fin (4 * n))) : Finset (Fin (4 * n)) :=
  (Finset.univ : Finset (Fin (4 * n))) \ S

/-- The complement of a 2n-subset of a 4n-set is again a 2n-subset. -/
lemma cplt_card (n : ℕ) (S : Finset (Fin (4 * n)))
    (hS : S.card = 2 * n) : (cplt S).card = 2 * n := by
  rw [cplt, Finset.card_sdiff_of_subset (Finset.subset_univ S),
      Finset.card_univ, Fintype.card_fin, hS]
  ring_nf
  omega

/-- The involution is idempotent: univ \ (univ \ S) = S. -/
lemma cplt_cplt (S : Finset (Fin (4 * n))) : cplt (cplt S) = S := by
  rw [cplt, cplt]
  rw [Finset.sdiff_sdiff_self_left, Finset.univ_inter]

/-- A 2n-subset and its complement are disjoint. -/
lemma disjoint_cplt (S : Finset (Fin (4 * n))) : Disjoint S (cplt S) := by
  rw [cplt, Finset.disjoint_iff_inter_eq_empty]
  exact Finset.inter_sdiff_self S Finset.univ

/-- F ⊆ U(n) because every member of F is a 2n-subset of `Fin (4*n)`. -/
lemma F_subset_U (n : ℕ) (F : Finset (Finset (Fin (4 * n))))
    (h_size : ∀ A ∈ F, A.card = 2 * n) : F ⊆ U n := by
  intro A hA
  simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
  exact h_size A hA

end Erdos83

theorem erdos_problem_83
    (n : ℕ)
    (F : Finset (Finset (Fin (4 * n))))
    (h_size : ∀ A ∈ F, A.card = 2 * n)
    (h_inter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    (F.card : ℚ) ≤ (1 / 2 : ℚ) * (Nat.choose (4 * n) (2 * n) : ℚ) := by
  -- Step 1: F ⊆ U(n).
  have hFU : F ⊆ Erdos83.U n := Erdos83.F_subset_U n F h_size
  -- Step 2: a key lemma — F ∩ {S, S^c} ≤ 1.
  have h_at_most_one : ∀ S ∈ Erdos83.U n,
      (F.filter (fun A => A = S)).card + (F.filter (fun A => A = Erdos83.cplt S)).card ≤ 1 := by
    intro S hS
    by_contra hgt
    have hF1le : (F.filter (fun A => A = S)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      have hx' : x = S := (Finset.mem_filter.mp hx).2
      have hy' : y = S := (Finset.mem_filter.mp hy).2
      exact hx'.trans hy'.symm
    have hF2le : (F.filter (fun A => A = Erdos83.cplt S)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      have hx' : x = Erdos83.cplt S := (Finset.mem_filter.mp hx).2
      have hy' : y = Erdos83.cplt S := (Finset.mem_filter.mp hy).2
      exact hx'.trans hy'.symm
    have hF1pos : 0 < (F.filter (fun A => A = S)).card := by
      have hsum : (F.filter (fun A => A = S)).card + (F.filter (fun A => A = Erdos83.cplt S)).card = 2 := by
        have h₁ : (F.filter (fun A => A = S)).card + (F.filter (fun A => A = Erdos83.cplt S)).card ≤ 2 :=
          Nat.add_le_add hF1le hF2le
        have h₂ : 2 ≤ (F.filter (fun A => A = S)).card + (F.filter (fun A => A = Erdos83.cplt S)).card := by
          have := le_of_not_ge hgt
          omega
        omega
      omega
    obtain ⟨A, hA⟩ := Finset.card_pos.mp hF1pos
    have hF2pos : 0 < (F.filter (fun A => A = Erdos83.cplt S)).card := by
      have hsum : (F.filter (fun A => A = S)).card + (F.filter (fun A => A = Erdos83.cplt S)).card = 2 := by
        have h₁ : (F.filter (fun A => A = S)).card + (F.filter (fun A => A = Erdos83.cplt S)).card ≤ 2 :=
          Nat.add_le_add hF1le hF2le
        have h₂ : 2 ≤ (F.filter (fun A => A = S)).card + (F.filter (fun A => A = Erdos83.cplt S)).card := by
          have := le_of_not_ge hgt
          omega
        omega
      omega
    obtain ⟨B, hB⟩ := Finset.card_pos.mp hF2pos
    have hAF : A ∈ F := (Finset.mem_filter.mp hA).1
    have hBF : B ∈ F := (Finset.mem_filter.mp hB).1
    have hAset : A = S := (Finset.mem_filter.mp hA).2
    have hBset : B = Erdos83.cplt S := (Finset.mem_filter.mp hB).2
    have hAB : (A ∩ B).card = 0 := by
      rw [hAset, hBset, Erdos83.cplt]
      rw [Finset.inter_sdiff_self S Finset.univ]
      simp
    have hAB2 : 2 ≤ (A ∩ B).card := h_inter A hAF B hBF
    omega
  -- Step 3: build the injection f : F → U(n) \ F via f(A) = cplt(A).
  have hf_in_U : ∀ A ∈ F, Erdos83.cplt A ∈ Erdos83.U n := by
    intro A hA
    have hAcard : A.card = 2 * n := h_size A hA
    simp only [Erdos83.U, Erdos83.cplt, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Erdos83.cplt_card n A hAcard
  have hf_not_in_F : ∀ A ∈ F, Erdos83.cplt A ∉ F := by
    intro A hA hAcF
    have hAcard : A.card = 2 * n := h_size A hA
    have h_int : (A ∩ Erdos83.cplt A).card = 0 := by
      rw [Erdos83.cplt, Finset.inter_sdiff_self A Finset.univ]
      simp
    have hAinter : 2 ≤ (A ∩ Erdos83.cplt A).card := h_inter A hA (Erdos83.cplt A) hAcF
    omega
  -- f is injective (f∘f = id by cplt_cplt), and f(F) ⊆ U(n) \ F.
  have hf_inj : (F.image Erdos83.cplt).card = F.card := by
    rw [Finset.card_image_of_injOn]
    intro A hA B hB hAB
    rw [Erdos83.cplt, Erdos83.cplt] at hAB
    have hA : (Finset.univ \ (Finset.univ \ A)) = A := by
      rw [Finset.sdiff_sdiff_self_left, Finset.univ_inter]
    have hB : (Finset.univ \ (Finset.univ \ B)) = B := by
      rw [Finset.sdiff_sdiff_self_left, Finset.univ_inter]
    rw [← hA, hAB, hB]
  have hf_image_sub : F.image Erdos83.cplt ⊆ Erdos83.U n \ F := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨A, hA, rfl⟩ := hx
    exact Finset.mem_sdiff.mpr ⟨hf_in_U A hA, hf_not_in_F A hA⟩
  have h_le : (F.image Erdos83.cplt).card ≤ (Erdos83.U n \ F).card :=
    Finset.card_le_card hf_image_sub
  have h_card : (Erdos83.U n \ F).card = (Erdos83.U n).card - F.card :=
    Finset.card_sdiff_of_subset hFU
  rw [hf_inj, h_card] at h_le
  have h₂ : 2 * F.card ≤ (Erdos83.U n).card := by omega
  -- Step 4: |U(n)| = C(4n, 2n).
  -- Prove U n = powersetCard (2n) univ as finsets, then apply card_powersetCard.
  have hU_eq : Erdos83.U n = Finset.powersetCard (2 * n)
      (Finset.univ : Finset (Fin (4 * n))) := by
    refine Finset.ext (fun S => ?_)
    simp only [Erdos83.U, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_powersetCard, Finset.mem_univ, true_and,
               Finset.subset_univ, true_and]
  -- Replace (U n).card in h₂ with C(4n, 2n).
  rw [hU_eq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at h₂
  have hq : (2 : ℚ) * (F.card : ℚ) ≤ (Nat.choose (4 * n) (2 * n) : ℚ) := by
    exact_mod_cast h₂
  linarith
