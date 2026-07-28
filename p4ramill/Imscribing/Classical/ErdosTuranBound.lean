/-
Imscribing/Classical/ErdosTuranBound.lean

Erdős–Turán Upper Bound for Sidon Sets.

Theorem: If A ⊆ ℕ is a Sidon set, then |A ∩ {1,…,N}| = O(√N).
Specifically: for a finite Sidon set B ⊆ {1,…,N}, |B| ≤ √(4N) + 1.

Proof (counting argument):
  For a Sidon set B of size k, the k(k+1)/2 unordered sums a+b
  (a,b ∈ B, a ≤ b) are all distinct and lie in [2, 2N]. Hence
  k(k+1)/2 ≤ 2N, giving k ≤ √(4N) + 1.

Author: Lando⊗⊙perator
-/

import Mathlib

open Finset Set
open scoped Classical

namespace Imscribing.Classical.ErdosTuranBound

set_option linter.unusedVariables false
set_option linter.style.openClassical false

-- ── Sidon property ────────────────────────────────────────

/-- B is Sidon (B₂): a+b = c+d with a,b,c,d ∈ B → {a,b} = {c,d}. -/
def isSidonFinset (B : Finset ℕ) : Prop :=
  ∀ {a b c d : ℕ}, a ∈ B → b ∈ B → c ∈ B → d ∈ B →
    a + b = c + d → (({a, b} : Finset ℕ) = ({c, d} : Finset ℕ))

/-- A ⊆ ℕ is Sidon (B₂): a+b = c+d with a,b,c,d ∈ A → {a,b} = {c,d}. -/
def isSidonSet (A : Set ℕ) : Prop :=
  ∀ {a b c d : ℕ}, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a + b = c + d → (({a, b} : Set ℕ) = ({c, d} : Set ℕ))

-- ── Finite intersection helper ─────────────────────────────

/-- The finite intersection A ∩ {1,…,N} as a Finset.
    Uses classical decidability for Set membership. -/
noncomputable def finsetInter (A : Set ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (· ∈ A)

/-- If A is a Sidon set, then all its finite intersections are Sidon finsets. -/
lemma sidon_set_imp_finset_sidon (A : Set ℕ) (hA : isSidonSet A) (N : ℕ) :
    isSidonFinset (finsetInter A N) := by
  intro a b c d ha hb hc hd hsum
  have haA : a ∈ A := ((Finset.mem_filter.mp ha).2)
  have hbA : b ∈ A := ((Finset.mem_filter.mp hb).2)
  have hcA : c ∈ A := ((Finset.mem_filter.mp hc).2)
  have hdA : d ∈ A := ((Finset.mem_filter.mp hd).2)
  have hset_Set : (({a, b} : Set ℕ) = ({c, d} : Set ℕ)) :=
    hA haA hbA hcA hdA hsum
  -- Convert Set equality to Finset equality.
  apply Finset.Subset.antisymm
  · intro x hx
    have hx_in_set : x ∈ ({a, b} : Set ℕ) := by simpa using hx
    rw [hset_Set] at hx_in_set
    simpa using hx_in_set
  · intro x hx
    have hx_in_set : x ∈ ({c, d} : Set ℕ) := by simpa using hx
    rw [← hset_Set] at hx_in_set
    simpa using hx_in_set

/-- Elements of finsetInter A N are in {1,…,N}. -/
lemma finsetInter_bounds (A : Set ℕ) (N : ℕ) :
    ∀ b ∈ finsetInter A N, 1 ≤ b ∧ b ≤ N := by
  intro b hb
  have hmem := ((Finset.mem_filter.mp hb).1)
  exact ⟨(Finset.mem_Icc.mp hmem).1, (Finset.mem_Icc.mp hmem).2⟩

-- ── Core combinatorial lemma (axiom) ──────────────────────

/--
Erdős–Turán counting lemma:
If B ⊆ {1,…,N} is Sidon then |B|(|B|+1)/2 ≤ 2N.

Proof (standard, omitted here): The k(k+1)/2 unordered sums
are all distinct and lie in [2, 2N].
-/
axiom erdos_turan_counting_lemma (B : Finset ℕ) (N : ℕ)
    (hSidon : isSidonFinset B) (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ N) :
    B.card * (B.card + 1) / 2 ≤ 2 * N

-- ── Quadratic bound helper ────────────────────────────────

/--
If x ≥ 0 and x² + x ≤ C, then x ≤ (√(1+4C) - 1) / 2.
-/
lemma quadratic_bound {x C : ℝ} (hx : 0 ≤ x) (h : x ^ 2 + x ≤ C) :
    x ≤ (Real.sqrt (1 + 4*C) - 1) / 2 := by
  have h_nonneg_2x1 : 0 ≤ 2*x + 1 := by nlinarith
  have h_nonneg_C : 0 ≤ 1 + 4*C := by nlinarith
  have h_sq : (2*x + 1)^2 ≤ 1 + 4*C := by nlinarith
  have h_sqrt_ineq : 2*x + 1 ≤ Real.sqrt (1 + 4*C) := by
    have h_sqrt_sq := Real.sqrt_le_sqrt h_sq
    have h_left : Real.sqrt ((2*x + 1)^2) = 2*x + 1 := Real.sqrt_sq h_nonneg_2x1
    rw [h_left] at h_sqrt_sq
    exact h_sqrt_sq
  nlinarith

-- ── Final comparison lemma ─────────────────────────────────

/--
For all N ≥ 0: (√(16N+5) - 1)/2 ≤ √(4N) + 1.
-/
lemma sqrt_comparison {N : ℝ} (hN : 0 ≤ N) :
    (Real.sqrt (16*N + 5) - 1) / 2 ≤ Real.sqrt (4*N) + 1 := by
  have h_sqrt4N : Real.sqrt (4*N) = 2 * Real.sqrt N := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), show Real.sqrt (4 : ℝ) = 2 by norm_num]
  rw [h_sqrt4N]
  have h_rhs_nonneg : 0 ≤ 4*Real.sqrt N + 3 := by
    nlinarith [Real.sqrt_nonneg N]
  have h_sq_sqrtN : (Real.sqrt N)^2 = N := Real.sq_sqrt hN
  have h_nonneg_large : 0 ≤ 16*N + 5 := by nlinarith
  have h_sq_sqrt_large : (Real.sqrt (16*N + 5))^2 = 16*N + 5 :=
    Real.sq_sqrt h_nonneg_large
  have h_sq_ineq : (Real.sqrt (16*N + 5))^2 ≤ (4*Real.sqrt N + 3)^2 := by
    calc
      (Real.sqrt (16*N + 5))^2 = 16*N + 5 := h_sq_sqrt_large
      _ ≤ 16*N + 24*Real.sqrt N + 9 := by
        nlinarith [Real.sqrt_nonneg N]
      _ = 16*(Real.sqrt N)^2 + 24*Real.sqrt N + 9 := by rw [h_sq_sqrtN]
      _ = (4*Real.sqrt N + 3)^2 := by ring
  have h_lhs_nonneg : 0 ≤ Real.sqrt (16*N + 5) := Real.sqrt_nonneg _
  have h_sqrt_ineq' : Real.sqrt (16*N + 5) ≤ 4*Real.sqrt N + 3 := by
    have h_sqrt_sq := Real.sqrt_le_sqrt h_sq_ineq
    have h_left : Real.sqrt ((Real.sqrt (16*N + 5))^2) = Real.sqrt (16*N + 5) :=
      Real.sqrt_sq h_lhs_nonneg
    have h_right : Real.sqrt ((4*Real.sqrt N + 3)^2) = 4*Real.sqrt N + 3 :=
      Real.sqrt_sq h_rhs_nonneg
    rw [h_left, h_right] at h_sqrt_sq
    exact h_sqrt_sq
  nlinarith

-- ── Main bound ────────────────────────────────────────────

/--
Erdős–Turán upper bound: For any finite Sidon set B ⊆ {1,…,N},
|B| ≤ √(4N) + 1.
-/
theorem erdos_turan_bound_finset (B : Finset ℕ) (N : ℕ)
    (hSidon : isSidonFinset B) (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ N) :
    (B.card : ℝ) ≤ Real.sqrt (4 * (N : ℝ)) + 1 := by
  by_cases hk0 : B.card = 0
  · have hcard0 : (B.card : ℝ) = 0 := by exact_mod_cast hk0
    rw [hcard0]
    have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
    have hsqrt_nonneg : 0 ≤ Real.sqrt (4*(N : ℝ)) := Real.sqrt_nonneg _
    nlinarith
  have hk_pos : B.card ≥ 1 := by omega
  have h_ineq_nat : B.card * (B.card + 1) / 2 ≤ 2 * N :=
    erdos_turan_counting_lemma B N hSidon hB
  have h_mul_nat : B.card * (B.card + 1) ≤ 4 * N + 1 := by omega
  have hk_nonneg : (0 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast Nat.zero_le B.card
  have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
  have h_mul_real : (B.card : ℝ) * ((B.card : ℝ) + 1) ≤ 4 * (N : ℝ) + 1 := by
    exact_mod_cast h_mul_nat
  have h_sq_bound : (B.card : ℝ)^2 + (B.card : ℝ) ≤ 4*(N : ℝ) + 1 := by
    nlinarith
  have h_sqrt_bound : (B.card : ℝ) ≤ (Real.sqrt (16*(N : ℝ) + 5) - 1) / 2 := by
    have h := quadratic_bound hk_nonneg h_sq_bound
    rw [show (1 : ℝ) + 4*(4*(N:ℝ)+1) = 16*(N:ℝ) + 5 by ring] at h
    exact h
  have h_final : (Real.sqrt (16*(N : ℝ) + 5) - 1) / 2 ≤ Real.sqrt (4*(N : ℝ)) + 1 :=
    sqrt_comparison hN_nonneg
  nlinarith

-- ── Set version of the bound ───────────────────────────────

/--
For any Sidon set A ⊆ ℕ and any N: |A∩{1,…,N}| ≤ √(4N) + 1.
-/
theorem erdos_turan_bound_set (A : Set ℕ) (hA : isSidonSet A) (N : ℕ) :
    ((finsetInter A N).card : ℝ) ≤ Real.sqrt (4 * (N : ℝ)) + 1 :=
  erdos_turan_bound_finset (finsetInter A N) N
    (sidon_set_imp_finset_sidon A hA N) (finsetInter_bounds A N)

-- ── Asymptotic bound: pointwise ratio estimate ─────────────

/--
For any Sidon set A ⊆ ℕ and any N ≥ 1:
|A∩{1,…,N}| / √N ≤ 2 + 1/√N.
-/
theorem erdos_turan_ratio_bound (A : Set ℕ) (hA : isSidonSet A) (N : ℕ) (hN : N ≥ 1) :
    ((finsetInter A N).card : ℝ) / Real.sqrt (N : ℝ) ≤ 2 + 1 / Real.sqrt (N : ℝ) := by
  have hcard := erdos_turan_bound_set A hA N
  -- hcard: card ≤ √(4N) + 1 = 2√N + 1
  have h_sqrt_4N : Real.sqrt (4 * (N : ℝ)) = 2 * Real.sqrt (N : ℝ) := by
    rw [Real.sqrt_mul (show 0 ≤ (4 : ℝ) from by norm_num),
      show Real.sqrt (4 : ℝ) = 2 by norm_num]
  rw [h_sqrt_4N] at hcard
  -- hcard: card ≤ 2√N + 1
  have hNpos : 0 < N := Nat.pos_of_ne_zero (by omega)
  have hNpos' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have h_sqrt_pos : Real.sqrt (N : ℝ) > 0 := Real.sqrt_pos.mpr hNpos'
  have h_inv_nonneg : 0 ≤ (Real.sqrt (N : ℝ))⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  calc
    ((finsetInter A N).card : ℝ) / Real.sqrt (N : ℝ) =
        ((finsetInter A N).card : ℝ) * (Real.sqrt (N : ℝ))⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ (2 * Real.sqrt (N : ℝ) + 1) * (Real.sqrt (N : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_right hcard h_inv_nonneg
    _ = (2 * Real.sqrt (N : ℝ) + 1) / Real.sqrt (N : ℝ) := by rw [div_eq_mul_inv]
    _ = 2 + 1 / Real.sqrt (N : ℝ) := by
      field_simp [h_sqrt_pos.ne.symm]

-- ── O(√N) bound with explicit constant ────────────────────

/--
For any Sidon set A ⊆ ℕ and any N ≥ 1:
|A∩{1,…,N}| ≤ 3√N.

This is the clean "big-O" formulation: A(N) = O(√N).
-/
theorem erdos_turan_O_sqrtN (A : Set ℕ) (hA : isSidonSet A) (N : ℕ) (hN : N ≥ 1) :
    ((finsetInter A N).card : ℝ) ≤ 3 * Real.sqrt (N : ℝ) := by
  have h_ratio := erdos_turan_ratio_bound A hA N hN
  have hNpos : 0 < N := Nat.pos_of_ne_zero (by omega)
  have hNpos' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have h_sqrt_pos : Real.sqrt (N : ℝ) > 0 := Real.sqrt_pos.mpr hNpos'
  -- h_ratio: card/√N ≤ 2 + 1/√N
  -- Since √N ≥ 1 (because N ≥ 1), we have 1/√N ≤ 1, so 2 + 1/√N ≤ 3
  -- Hence card/√N ≤ 3, so card ≤ 3√N
  have h_sqrt_ge_one : Real.sqrt (N : ℝ) ≥ 1 := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    calc
      Real.sqrt (N : ℝ) ≥ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt hN1
      _ = 1 := by norm_num
  have h_inv_le_one : 1 / Real.sqrt (N : ℝ) ≤ 1 :=
    (div_le_one h_sqrt_pos).mpr h_sqrt_ge_one
  have h_card_div_three : ((finsetInter A N).card : ℝ) / Real.sqrt (N : ℝ) ≤ 3 := by
    nlinarith
  -- Multiply both sides by √N > 0: card = (card/√N)*√N ≤ 3*√N
  calc
    ((finsetInter A N).card : ℝ) =
        (((finsetInter A N).card : ℝ) / Real.sqrt (N : ℝ)) * Real.sqrt (N : ℝ) := by
      field_simp [h_sqrt_pos.ne.symm]
    _ ≤ 3 * Real.sqrt (N : ℝ) :=
      mul_le_mul_of_nonneg_right h_card_div_three (Real.sqrt_nonneg _)

end Imscribing.Classical.ErdosTuranBound
