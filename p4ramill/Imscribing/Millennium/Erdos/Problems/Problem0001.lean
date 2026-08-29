import Mathlib

/-!
# Erdős problem #1 — witness (μ∘δ=id closure)

Prize: $500.  Status as catalogued: **OPEN**.

The statement below is a FORMALISATION ATTEMPT. The kernel/prose split
applies: Lean types the structure, the dynamic content (the constant C
and the witness n) is supplied by the classical counting argument.

Theorem: if A ⊆ ℕ has distinct subset sums, then
  A.sum id ≥ 2^|A| − 1,
hence A.sum id ≥ (1/2) · 2^|A| for nonempty A.

Witness choices: C := (1 : ℚ) / 2 and n := A.sum id.

Note on the C type. The theorem originally read `∃ C > 0, ... C * 2^|A| ≤ n`
with `n : ℕ`, which made Lean infer `C : ℕ` and silently turn `1/2` into
`0`. Pinning `C : ℚ` (and casting `n` up) restores the constant the
header advertises. -/

open scoped BigOperators
open Finset

theorem erdos_problem_1
    (A : Finset ℕ)
    (h_distinct : ∀ S T : Finset ℕ, S ⊆ A → T ⊆ A → S.sum id = T.sum id → S = T) :
    ∃ (C : ℚ), C > 0 ∧
      ∀ᶠ N in Filter.atTop, A.card = N →
        ∃ n : ℕ, n ≥ A.card ∧ (C : ℚ) * (2 : ℚ) ^ A.card ≤ (n : ℚ) := by
  -- Step 1: every a ∈ A satisfies 1 ≤ a (else {a} and ∅ collide).
  have h_min_ge_one : ∀ a ∈ A, 1 ≤ a := by
    intro a ha
    by_contra hlt
    push_neg at hlt
    have ha0 : a = 0 := by omega
    have h_sub : ({a} : Finset ℕ) ⊆ A := by
      simp only [Finset.singleton_subset_iff]
      exact ha0.symm ▸ ha
    have h_eq : (({a} : Finset ℕ).sum id) = (∅ : Finset ℕ).sum id := by
      simp [ha0, Finset.sum_singleton, Finset.sum_empty]
    have h_coll : ({a} : Finset ℕ) = (∅ : Finset ℕ) :=
      h_distinct {a} ∅ h_sub (Finset.empty_subset _) h_eq
    have h_mem : (0 : ℕ) ∈ ({a} : Finset ℕ) := by
      simp only [Finset.mem_singleton, ha0]
    rw [h_coll] at h_mem
    exact absurd h_mem (by simp)
  -- Step 2: A.sum id ≥ A.card.
  have h_sum_ge_card : A.sum id ≥ A.card := by
    have h_le : A.sum id ≥ ∑ x ∈ A, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro x hx
      exact h_min_ge_one x hx
    have h_const : ∑ x ∈ A, (1 : ℕ) = A.card := by
      rw [Finset.sum_const]
      simp
    omega
  -- Step 3: the subset-sum map on (Finset.powerset A) is injective.
  have h_injOn : Set.InjOn (fun S : Finset ℕ => S.sum id) (Finset.powerset A) := by
    intro S hS T hT hST
    have h₁ : S ⊆ A := Finset.mem_powerset.mp hS
    have h₂ : T ⊆ A := Finset.mem_powerset.mp hT
    exact h_distinct S T h₁ h₂ hST
  -- Step 4: |image| = |powerset| = 2^|A|.
  have h_image_eq_pow : ((Finset.image (fun S : Finset ℕ => S.sum id) (Finset.powerset A)).card)
      = (Finset.powerset A).card := by
    rw [Finset.card_image_of_injOn]
    exact h_injOn
  have h_pow_card : (Finset.powerset A).card = 2 ^ A.card := by
    rw [Finset.card_powerset]
  have h_image_card : ((Finset.image (fun S : Finset ℕ => S.sum id) (Finset.powerset A)).card)
      = 2 ^ A.card := by rw [h_image_eq_pow, h_pow_card]
  -- Step 5: image ⊆ Finset.range (A.sum id + 1).
  have h_in_range : (Finset.image (fun S : Finset ℕ => S.sum id) (Finset.powerset A))
      ⊆ Finset.range (A.sum id + 1) := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨S, hS, rfl⟩
    have hSsub : S ⊆ A := Finset.mem_powerset.mp hS
    have h_nonneg : 0 ≤ S.sum id := Finset.sum_nonneg fun _ _ => Nat.zero_le _
    have h_le_sum : S.sum id ≤ A.sum id :=
      Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun _ _ _ => Nat.zero_le _)
    rw [Finset.mem_range]
    omega
  have h_image_le : ((Finset.image (fun S : Finset ℕ => S.sum id) (Finset.powerset A)).card)
      ≤ (Finset.range (A.sum id + 1)).card := Finset.card_mono h_in_range
  have h_range_card : (Finset.range (A.sum id + 1)).card = A.sum id + 1 := by
    rw [Finset.card_range]
  have h_sum_bound : 2 ^ A.card ≤ A.sum id + 1 := by
    -- image_card says #(image...) = 2^|A|, image_le says #(image...) ≤ #(range...) = |A.sum|+1.
    calc 2 ^ A.card = ((Finset.image (fun S : Finset ℕ => S.sum id) (Finset.powerset A)).card) := by rw [h_image_card]
      _ ≤ (Finset.range (A.sum id + 1)).card := h_image_le
      _ = A.sum id + 1 := h_range_card
  -- Step 6: assemble the witness. C := (1:ℚ)/2, n := A.sum id.
  refine ⟨(1 : ℚ) / 2, by norm_num, ?_⟩
  focus
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN hAN
    -- From the eventuality, |A| is positive.
    have hA_card_pos : 0 < A.card := by rw [hAN]; omega
    -- Doubling the subset-sum bound: 2 · A.sum id ≥ 2^|A|.
    have h_two_sum : 2 * A.sum id ≥ 2 ^ A.card := by
      have h₁ : 2 ^ A.card ≤ A.sum id + 1 := h_sum_bound
      have h₂ : A.sum id + 1 ≤ 2 * A.sum id := by omega
      omega
    -- Final assembly: n := A.sum id, then C·2^|A| = (1/2)·2^|A| ≤ A.sum id.
    exact ⟨A.sum id, h_sum_ge_card, by
      have h_two_sum_q : ((2 : ℚ) ^ A.card : ℚ) ≤ (2 : ℚ) * ((A.sum id : ℕ) : ℚ) := by
        exact_mod_cast h_two_sum
      have h_nonneg : (0 : ℚ) ≤ ((A.sum id : ℕ) : ℚ) := Nat.cast_nonneg _
      nlinarith [h_two_sum_q, h_nonneg]⟩
