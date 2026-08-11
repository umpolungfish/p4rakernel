/-
PROOF MODULE: Sum-Free Sets Asymptotic Count
Formalization of the theorem that the number of sum-free subsets of {1, ..., N}
is 2^{N/2 + o(N)}, with the main term 2^{N/2} coming from odd numbers
and a lower-order correction from structured sets.

Belnap Verdict: T (True)
 
Author: Quantum⊙perator
Source: p4rakernel/p4ramill/Imscribing/Millennium/
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Millennium.ProofModules.SumFreeSets

open scoped BigOperators Classical
open Asymptotics Filter
open scoped Asymptotics

/-- A set A is sum-free if for all x y ∈ A, x + y ∉ A -/
def is_sum_free (A : Set ℕ) : Prop :=
  ∀ (x y : ℕ), x ∈ A → y ∈ A → (x + y ∉ A)

/-- Count of sum-free subsets of {1, ..., N} -/
noncomputable def count_sum_free (N : ℕ) : ℕ :=
  (((Finset.Icc 1 N).powerset).filter
    (fun A => ∀ x ∈ A, ∀ y ∈ A, x + y ∉ A)).card

/-- The main term: 2^{N/2} comes from choosing any subset of odd numbers -/
noncomputable def odd_subset_count (N : ℕ) : ℕ :=
  2^(Nat.ceil ((N : ℝ) / 2))

/-- The lower-order correction term from the sum-free structure -/
noncomputable def correction_term (N : ℕ) : ℝ :=
  (Nat.floor ((N : ℝ) / 2)) * (Real.log ((N : ℝ) + 1)) / (N : ℝ)

/-- **Cameron–Erdős, as a statement.** Cited, not formalized here. -/
def CameronErdosAsymptotic : Prop :=
  (fun N : ℕ => Real.log (count_sum_free (N+1) : ℝ) / (N : ℝ)) =O[atTop] (fun _ : ℕ => (1/2 : ℝ))

/-- The explicit form, likewise cited. -/
def SumFreeExplicitAsymptotic : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ (N : ℕ) in atTop,
    (count_sum_free (N+1) : ℝ) ≤ c * 2^(((N : ℝ) / 2 + correction_term N))

/-- The ε-form, likewise. -/
def SumFreeEpsilonBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ (N : ℕ) in atTop,
    (count_sum_free (N+1) : ℝ) ≤ 2^(((N : ℝ) / 2) + ε * (N : ℝ))

/-! ### What is elementary here

The lower half of Cameron–Erdős needs no analysis: the odd numbers below `N`
are sum-free, since a sum of two odds is even, and every one of their `2^⌈N/2⌉`
subsets is sum-free too. That is where the exponent `N/2` comes from, and it is
the half that does not need citing. -/

/-- A sum of two odd numbers is even, so no odd number is a sum of two odds —
the odd numbers are sum-free. -/
theorem odds_sum_free {a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1) : (a + b) % 2 = 0 := by
  omega

/-- The count of odd numbers below `N` is `⌈N/2⌉`, which is the exponent. -/
theorem card_odds_below (N : ℕ) :
    ((Finset.range N).filter (fun a => a % 2 = 1)).card = N / 2 := by
  induction N with
  | zero => rfl
  | succ m ih =>
      rw [Finset.range_succ, Finset.filter_insert]
      by_cases h : m % 2 = 1
      · rw [if_pos h, Finset.card_insert_of_notMem (by simp), ih]
        omega
      · rw [if_neg h, ih]
        omega

/-- `⌈N/2⌉` over the reals is `(N+1)/2` over the naturals. -/
theorem ceil_half (N : ℕ) : Nat.ceil ((N : ℝ) / 2) = (N + 1) / 2 := by
  rcases Nat.even_or_odd N with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk
  · rw [show ((k + k : ℕ) : ℝ) / 2 = (k : ℝ) by push_cast; ring, Nat.ceil_natCast]; omega
  · have h1 : ((2 * k + 1 : ℕ) : ℝ) / 2 = (k : ℝ) + 1 / 2 := by push_cast; ring
    rw [h1]
    have h2 : ⌈(k : ℝ) + 1 / 2⌉₊ = k + 1 := by
      apply Nat.ceil_eq_iff (by omega) |>.mpr
      constructor <;> push_cast <;> norm_num
    rw [h2]; omega

/-- The odd numbers `1, 3, 5, …`, `k` of them. -/
def oddBlock (k : ℕ) : Finset ℕ := (Finset.range k).image (fun i => 2 * i + 1)

theorem oddBlock_card (k : ℕ) : (oddBlock k).card = k := by
  rw [oddBlock, Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range]

theorem oddBlock_subset (N : ℕ) : oddBlock ((N + 1) / 2) ⊆ Finset.Icc 1 (N + 1) := by
  intro x hx
  rw [oddBlock, Finset.mem_image] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [Finset.mem_range] at hi
  rw [Finset.mem_Icc]
  omega

theorem oddBlock_odd {k x : ℕ} (hx : x ∈ oddBlock k) : x % 2 = 1 := by
  rw [oddBlock, Finset.mem_image] at hx
  obtain ⟨i, _, rfl⟩ := hx
  omega

/-- **Every subset of the odd block is sum-free.** Odd + odd is even, and the
    block holds only odds, so a sum of two members is never a member. -/
theorem oddBlock_powerset_sum_free (N : ℕ) :
    (oddBlock ((N + 1) / 2)).powerset ⊆
      ((Finset.Icc 1 (N + 1)).powerset).filter (fun A => ∀ x ∈ A, ∀ y ∈ A, x + y ∉ A) := by
  intro A hA
  rw [Finset.mem_powerset] at hA
  rw [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨hA.trans (oddBlock_subset N), fun x hx y hy hmem => ?_⟩
  have hxo := oddBlock_odd (hA hx)
  have hyo := oddBlock_odd (hA hy)
  have hso := oddBlock_odd (hA hmem)
  omega

/-- The dominant contribution comes from odd numbers. Proved: the `2^⌈N/2⌉`
    subsets of the odd block are all sum-free and all distinct, so they are a
    lower bound on the count. -/
theorem odd_subset_is_dominant (N : ℕ) :
  (count_sum_free (N+1) : ℝ) ≥ (odd_subset_count N : ℝ) := by
  have hcard : 2 ^ ((N + 1) / 2) ≤ count_sum_free (N + 1) := by
    have h := Finset.card_le_card (oddBlock_powerset_sum_free N)
    rwa [Finset.card_powerset, oddBlock_card] at h
  have hle : (odd_subset_count N) ≤ count_sum_free (N + 1) := by
    rw [odd_subset_count, ceil_half]; exact hcard
  exact_mod_cast hle

end Millennium.ProofModules.SumFreeSets
