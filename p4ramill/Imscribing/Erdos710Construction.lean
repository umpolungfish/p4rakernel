import Mathlib

/-!
# Erdős 710: an explicit subquadratic witness

This file is self-contained: `Adm`, `Lam`, and `f` have the same meaning
as in the question.  The construction gives the **explicit** upper bound

  f n ≤ 2 * (n + 1) * (Nat.sqrt n + 2) + 1.

Consequently the bound is O(n^(3/2)).  This is not the conjectured sharp
asymptotic and it does not formalize the separate finite matching certificate.

This source addresses the reported Lean errors at the cast and divisibility proofs.
It has not been recompiled against a local Mathlib build.
-/

namespace Erdos710

open Finset

def Adm (n : ℕ) (L : ℤ) (a : Fin n → ℤ) : Prop :=
  (∀ i : Fin n, (n : ℤ) < a i ∧ a i < (n : ℤ) + L) ∧
  Function.Injective a ∧
  (∀ i : Fin n, ((i.val + 1 : ℕ) : ℤ) ∣ a i)

def Lam (n : ℕ) : Set ℤ :=
  {L : ℤ | 0 ≤ L ∧ ∃ a : Fin n → ℤ, Adm n L a}

noncomputable def f (n : ℕ) : ℤ := sInf (Lam n)

-- The radix is strictly larger than sqrt n.
def radix (n : ℕ) : ℕ := Nat.sqrt n + 1

-- This multiplier is strictly larger than n and congruent to 1 mod radix.
def shift (n : ℕ) : ℕ := radix n * (n / radix n + 1) + 1

-- Working in Nat first makes the injectivity proof particularly simple.
def sqrtWitnessNat (n : ℕ) (i : Fin n) : ℕ :=
  let d := i.val + 1
  if d < radix n then d * shift n else d * radix n

def sqrtWitness (n : ℕ) (i : Fin n) : ℤ :=
  (sqrtWitnessNat n i : ℤ)

def sqrtBound (n : ℕ) : ℤ :=
  ((2 * (n + 1) * (radix n + 1) : ℕ) : ℤ) + 1

private theorem radix_pos (n : ℕ) : 0 < radix n := by
  unfold radix
  omega

private theorem radix_le_succ (n : ℕ) : radix n ≤ n + 1 := by
  unfold radix
  have hs := Nat.sqrt_le_self n
  omega

private theorem radix_sq_gt (n : ℕ) : n < radix n * radix n := by
  simpa [radix, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt n

private theorem shift_gt (n : ℕ) : n < shift n := by
  have hdecomp := Nat.mod_add_div n (radix n)
  have hrem : n % radix n < radix n := Nat.mod_lt n (radix_pos n)
  unfold shift
  nlinarith

private theorem shift_le (n : ℕ) : shift n ≤ 2 * (n + 1) := by
  have hdiv := Nat.div_mul_le_self n (radix n)
  have hr := radix_le_succ n
  unfold shift
  nlinarith

-- Distinctness between the two branches follows from reduction modulo radix.
private theorem no_cross (n i j : ℕ)
    (hi : 0 < i) (hir : i < radix n)
    (heq : i * shift n = j * radix n) : False := by
  have hmod : (i * shift n) % radix n = i % radix n := by
    calc
      (i * shift n) % radix n =
          (i * radix n * (n / radix n + 1) + i) % radix n := by
            congr 1
            unfold shift
            ring
      _ = i % radix n := by
        have hdvd : radix n ∣ i * radix n * (n / radix n + 1) := by
          refine ⟨i * (n / radix n + 1), ?_⟩
          ring
        rw [Nat.add_mod]
        simp [Nat.mod_eq_zero_of_dvd hdvd]
  have hzero : (i * shift n) % radix n = 0 := by
    rw [heq]
    apply Nat.mod_eq_zero_of_dvd
    exact ⟨j, by ring⟩
  rw [hmod, Nat.mod_eq_of_lt hir] at hzero
  omega

private theorem sqrtWitnessNat_bounds (n : ℕ) (i : Fin n) :
    n < sqrtWitnessNat n i ∧
      sqrtWitnessNat n i ≤ 2 * (n + 1) * (radix n + 1) := by
  have hdpos : 0 < i.val + 1 := by omega
  have hdle : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
  by_cases hsmall : i.val + 1 < radix n
  · unfold sqrtWitnessNat
    rw [if_pos hsmall]
    constructor
    · calc
        n < shift n := shift_gt n
        _ ≤ (i.val + 1) * shift n := by
          simpa using Nat.mul_le_mul_right (shift n) (by omega : 1 ≤ i.val + 1)
    · calc
        (i.val + 1) * shift n ≤ radix n * shift n :=
          Nat.mul_le_mul_right _ (Nat.le_of_lt hsmall)
        _ ≤ radix n * (2 * (n + 1)) :=
          Nat.mul_le_mul_left _ (shift_le n)
        _ ≤ 2 * (n + 1) * (radix n + 1) := by
          nlinarith
  · unfold sqrtWitnessNat
    rw [if_neg hsmall]
    have hlarge : radix n ≤ i.val + 1 := by omega
    constructor
    · calc
        n < radix n * radix n := radix_sq_gt n
        _ ≤ (i.val + 1) * radix n :=
          Nat.mul_le_mul_right _ hlarge
    · calc
        (i.val + 1) * radix n ≤ n * radix n :=
          Nat.mul_le_mul_right _ hdle
        _ ≤ 2 * (n + 1) * (radix n + 1) := by
          nlinarith

private theorem sqrtWitness_injective (n : ℕ) :
    Function.Injective (sqrtWitness n) := by
  intro i j hij
  have hnat : sqrtWitnessNat n i = sqrtWitnessNat n j := by
    change (sqrtWitnessNat n i : ℤ) = (sqrtWitnessNat n j : ℤ) at hij
    exact_mod_cast hij
  by_cases hi : i.val + 1 < radix n
  · by_cases hj : j.val + 1 < radix n
    · have hmul : (i.val + 1) * shift n = (j.val + 1) * shift n := by
        simpa [sqrtWitnessNat, hi, hj] using hnat
      have hne : shift n ≠ 0 := by
        have hp := shift_gt n
        omega
      have heq := mul_right_cancel₀ hne hmul
      exact Fin.ext (by omega)
    · have hmul : (i.val + 1) * shift n = (j.val + 1) * radix n := by
        simpa [sqrtWitnessNat, hi, hj] using hnat
      exact False.elim (no_cross n (i.val + 1) (j.val + 1)
        (by omega) hi hmul)
  · by_cases hj : j.val + 1 < radix n
    · have hmul : (j.val + 1) * shift n = (i.val + 1) * radix n := by
        have h := hnat
        simp [sqrtWitnessNat, hi, hj] at h
        exact h.symm
      exact False.elim (no_cross n (j.val + 1) (i.val + 1)
        (by omega) hj hmul)
    · have hmul : (i.val + 1) * radix n = (j.val + 1) * radix n := by
        simpa [sqrtWitnessNat, hi, hj] using hnat
      have hne : radix n ≠ 0 := by
        have hp := radix_pos n
        omega
      have heq := mul_right_cancel₀ hne hmul
      exact Fin.ext (by omega)

-- Main constructive theorem: the requested distinct divisible tuple.
theorem sqrtWitness_adm (n : ℕ) : Adm n (sqrtBound n) (sqrtWitness n) := by
  refine ⟨?_, sqrtWitness_injective n, ?_⟩
  · intro i
    obtain ⟨hlo, hhi⟩ := sqrtWitnessNat_bounds n i
    constructor
    · change (n : ℤ) < (sqrtWitnessNat n i : ℤ)
      exact_mod_cast hlo
    · change (sqrtWitnessNat n i : ℤ) <
        (n : ℤ) + (((2 * (n + 1) * (radix n + 1) : ℕ) : ℤ) + 1)
      have hhiZ : (sqrtWitnessNat n i : ℤ) ≤
          ((2 * (n + 1) * (radix n + 1) : ℕ) : ℤ) := by
        exact_mod_cast hhi
      have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
      omega
  · intro i
    have hdiv : i.val + 1 ∣ sqrtWitnessNat n i := by
      by_cases hsmall : i.val + 1 < radix n
      · simpa only [sqrtWitnessNat, if_pos hsmall] using
          (dvd_mul_right (i.val + 1) (shift n))
      · simpa only [sqrtWitnessNat, if_neg hsmall] using
          (dvd_mul_right (i.val + 1) (radix n))
    change ((i.val + 1 : ℕ) : ℤ) ∣ (sqrtWitnessNat n i : ℤ)
    exact_mod_cast hdiv

theorem sqrtBound_mem_Lam (n : ℕ) : sqrtBound n ∈ Lam n := by
  refine ⟨?_, sqrtWitness n, sqrtWitness_adm n⟩
  unfold sqrtBound
  positivity

-- A bound for the original `f`, using the least-element property of sInf.
theorem f_le_sqrtBound (n : ℕ) : f n ≤ sqrtBound n := by
  unfold f
  have hb : BddBelow (Lam n) := ⟨0, fun _ hL => hL.1⟩
  exact csInf_le hb (sqrtBound_mem_Lam n)

end Erdos710
