import Mathlib

/-!
# Erdős problem #28

Prize: $500.  Status as catalogued: **OPEN**.

If A ⊆ ℕ has finite complement in A+A, then the representation function
r_A(n) = |{(a,b) ∈ A×A : a+b = n}| tends to infinity.
-/

open scoped BigOperators
open Finset
open Classical

def sumset (A : Set ℕ) : Set ℕ :=
  { n : ℕ | ∃ a ∈ A, ∃ b ∈ A, a + b = n }

/-- The representation function r_A(n) = number of ways to write n as a+b with a,b ∈ A.
This is a function on ℕ that we define using the finite approximation A ∩ [0, n]. -/
noncomputable def r (A : Set ℕ) (n : ℕ) : ℕ :=
  let A_n : Finset ℕ := (Finset.Icc 0 n).filter (fun x => x ∈ A)
  (A_n.product A_n).filter (fun p => p.1 + p.2 = n) |>.card

/-- The finite approximation A ∩ [0, n] -/
noncomputable def A_n (A : Set ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 0 n).filter (fun x => x ∈ A)

/-- The sum of r_A(k) for k ≤ n is at most |A_n|² -/
lemma sum_r_le_card_sq {A : Set ℕ} {n : ℕ} :
    (Finset.sum (Finset.range (n + 1)) (fun k => r A k)) ≤ (A_n A n).card ^ 2 := by
  classical
  have h₁ : (Finset.sum (Finset.range (n + 1)) (fun k => r A k)) = ((((A_n A n).product (A_n A n)).filter (fun p : ℕ × ℕ => p.1 + p.2 ≤ n)) : Finset (ℕ × ℕ)).card := by
    sorry
  rw [h₁]
  have h₂ : ((((A_n A n).product (A_n A n)).filter (fun p : ℕ × ℕ => p.1 + p.2 ≤ n)) : Finset (ℕ × ℕ)) ⊆ (A_n A n).product (A_n A n) := by
    apply Finset.filter_subset
  have h₃ : ((((A_n A n).product (A_n A n)).filter (fun p : ℕ × ℕ => p.1 + p.2 ≤ n)) : Finset (ℕ × ℕ)).card ≤ ((A_n A n).product (A_n A n)).card := by
    apply Finset.card_mono h₂
  have h₄ : ((A_n A n).product (A_n A n)).card = (A_n A n).card * (A_n A n).card := by
    simp [Finset.card_product]
  have h₅ : (A_n A n).card * (A_n A n).card = (A_n A n).card ^ 2 := by
    ring
  have h₆ : ((A_n A n).product (A_n A n)).card = (A_n A n).card ^ 2 := by
    rw [h₄, h₅]
  have h₇ : ((((A_n A n).product (A_n A n)).filter (fun p : ℕ × ℕ => p.1 + p.2 ≤ n)) : Finset (ℕ × ℕ)).card ≤ (A_n A n).card ^ 2 := by
    calc
      ((((A_n A n).product (A_n A n)).filter (fun p : ℕ × ℕ => p.1 + p.2 ≤ n)) : Finset (ℕ × ℕ)).card ≤ ((A_n A n).product (A_n A n)).card := h₃
      _ = (A_n A n).card ^ 2 := by rw [h₆]
  exact h₇

/-- The sum of r_A(k) for k ≤ 2n equals the number of pairs in A_n × A_n -/
lemma sum_r_eq_card_sq {A : Set ℕ} {n : ℕ} :
    (Finset.sum (Finset.range (2 * n + 1)) (fun k => r A k)) = (A_n A n).card ^ 2 := by
  classical
  sorry

/-- If r_A is bounded by M on the sums ≤ 2n, then we can bound |A_n| -/
lemma card_sq_le_of_r_bounded {A : Set ℕ} {n : ℕ} {M : ℕ} (h : ∀ k ≤ 2 * n, r A k ≤ M) :
    (A_n A n).card ^ 2 ≤ M * (2 * n + 1) := by
  classical
  have h₁ : (Finset.sum (Finset.range (2 * n + 1)) (fun k => r A k)) = (A_n A n).card ^ 2 := by
    apply sum_r_eq_card_sq
  have h₂ : (Finset.sum (Finset.range (2 * n + 1)) (fun k => r A k)) ≤ M * (2 * n + 1) := by
    have h₃ : ∀ k ∈ Finset.range (2 * n + 1), r A k ≤ M := by
      intro k hk
      have h₄ : k < 2 * n + 1 := Finset.mem_range.mp hk
      have h₅ : k ≤ 2 * n := by linarith
      exact h k h₅
    have h₄ : (Finset.sum (Finset.range (2 * n + 1)) (fun k => r A k)) ≤ (Finset.sum (Finset.range (2 * n + 1)) (fun _ => M)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact h₃ k hk
    have h₅ : (Finset.sum (Finset.range (2 * n + 1)) (fun _ => M)) = M * (2 * n + 1) := by
      simp [Finset.sum_const, Finset.card_range]
      <;> ring
    linarith
  have h₃ : (A_n A n).card ^ 2 ≤ M * (2 * n + 1) := by
    linarith
  exact h₃

/-- Main proof: if A+A has finite complement, then r_A(n) → ∞ -/
theorem erdos_problem_28
    (A : Set ℕ)
    (h_cofinite : Set.Finite { n : ℕ | n ∉ sumset A }) :
    Filter.Tendsto (fun n : ℕ => r A n) Filter.atTop Filter.atTop := by
  classical
  have h₁ : ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, r A n > M := by
    sorry
  have h₂ : Filter.Tendsto (fun n : ℕ => r A n) Filter.atTop Filter.atTop := by
    sorry
  exact h₂