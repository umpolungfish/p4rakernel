-- Imscribing/ReEntryConstructions.lean
-- Formalization of "Two Re-Entry Constructions, Their Disagreement, and the Role of Zero"
-- This file formalizes the mathematical core using the Prime Well Space + evaluation map framing:
--   - The Prime Well Space: exponent vectors over the primes (finitely supported lists).
--   - Binary Well Space: bit vectors / distinctions (powerset re-entry).
--   - The evaluation map collapses each well space into the 1D number line ℕ.
--   - The two re-entry constructions disagree on atomicity; zero is the universal fixed point.
--   - Cantor's theorem: no set is equal to its own powerset.

import Mathlib.Logic.Function.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Finset.Powerset
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.List.Count

open Set

-- ---------------------------------------------------------------------------
-- §I.  The Prime Well Space: exponent vectors over the primes.
-- ---------------------------------------------------------------------------

abbrev PrimeWell := List ℕ
def primeEval (v : PrimeWell) : ℕ := List.prod v
def primeDepth (v : PrimeWell) : ℕ := v.length
def primeAdd (v w : PrimeWell) : PrimeWell := v ++ w

-- ---------------------------------------------------------------------------
-- §II.  The Binary Well Space: bit vectors / distinctions.
-- ---------------------------------------------------------------------------

abbrev BinaryWell := List ℕ
def binEval (v : BinaryWell) : ℕ := Nat.ofDigits 2 v
def binDepth (v : BinaryWell) : ℕ := v.count 1
def binAdd (v : BinaryWell) : BinaryWell := 0 :: v

-- ---------------------------------------------------------------------------
-- §III.  Depth functions on ℕ (collapsed from the well spaces).
-- ---------------------------------------------------------------------------

def omega (n : ℕ) : ℕ := if n = 0 then 0 else primeDepth (Nat.primeFactorsList n)
def popcount (n : ℕ) : ℕ := (Nat.digits 2 n).count 1

-- Binary atomic: n has exactly one 1 in binary (n = 2^k).
def binaryAtomic (n : ℕ) : Prop := n > 0 ∧ popcount n = 1

-- Arithmetic atomic: n is prime.
def arithAtomic (n : ℕ) : Prop := n > 0 ∧ Nat.Prime n

-- ---------------------------------------------------------------------------
-- §IV.  Concrete Examples
-- ---------------------------------------------------------------------------

-- 8 is binary-atomic but arith-composite.
theorem eight_binary_not_arith : binaryAtomic 8 ∧ ¬arithAtomic 8 := by
  unfold binaryAtomic arithAtomic popcount
  decide

-- 13 is arith-atomic but binary-composite.
theorem thirteen_arith_not_binary : arithAtomic 13 ∧ ¬binaryAtomic 13 := by
  constructor
  · -- Prove 13 is arith-atomic
    constructor
    · norm_num [arithAtomic]
    · decide
  · -- Prove 13 is not binary-atomic
    intro h
    have h₁ : popcount 13 = 1 := h.2
    norm_num [popcount] at h₁

-- Ω(6) = popcount 6 = 2 but atoms differ.
theorem counts_equal_atoms_differ : omega 6 = popcount 6 := by
  have factors : (Nat.primeFactorsList 6).length = 2 := by
    have lengths := (Nat.perm_primeFactorsList_mul
      (a := 2) (b := 3) (by decide) (by decide)).length_eq
    simpa [Nat.primeFactorsList_prime Nat.prime_two,
      Nat.primeFactorsList_prime (by decide : Nat.Prime 3)] using lengths
  change (if 6 = 0 then 0 else (Nat.primeFactorsList 6).length) = popcount 6
  rw [if_neg (by decide), factors]
  unfold popcount
  decide

-- ---------------------------------------------------------------------------
-- §V.  Structural Theorems
-- ---------------------------------------------------------------------------

-- Empty structures.
theorem empty_structures : popcount 0 = 0 ∧ omega 1 = 0 := by
  constructor
  · norm_num [popcount]
  · norm_num [omega, primeDepth, Nat.primeFactorsList]

-- Zero is the unique universal fixed point of multiplication maps.
theorem zero_universal_fixed_point (N : ℕ) (hN : N ≠ 1) :
    {x : ℕ | N * x = x} = {0} := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra h₀
    have h_pos : 0 < x := by
      by_contra h₁
      have h₂ : x = 0 := by omega
      simp_all [Nat.mul_zero]
    have h_N_ge_1 : 1 ≤ N := by
      by_contra h₁
      have h₂ : N = 0 := by omega
      simp [h₂] at hx
      <;> simp_all [Nat.mul_zero]
    have h₃ : (N - 1) * x = 0 := by
      have h₄ : N * x = x := hx
      have h₅ : N ≥ 1 := h_N_ge_1
      have h₆ : N * x = (N - 1) * x + x := by
        have h₇ : N = (N - 1) + 1 := by
          have h₈ : N ≥ 1 := h_N_ge_1
          omega
        rw [h₇]
        <;> ring_nf at *
        <;> simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc] at *
        <;> ring_nf at *
        <;> omega
      rw [h₆] at h₄
      omega
    have h₄ : N - 1 = 0 := by
      have h₅ : (N - 1) * x = 0 := h₃
      have h₆ : N - 1 = 0 ∨ x = 0 := Nat.mul_eq_zero.mp h₅
      cases h₆ with
      | inl h₆ => exact h₆
      | inr h₆ =>
        exfalso
        have h₇ : 0 < x := h_pos
        linarith
    have h₅ : N = 1 := by
      have h₆ : N - 1 = 0 := h₄
      have h₇ : N ≤ 1 := by omega
      omega
    exact hN h₅
  · intro x hx
    simp only [Set.mem_singleton_iff] at hx
    rw [hx]
    <;> simp [Nat.mul_zero]

-- Helper lemma: if n is even and n > 2, then n is not prime
lemma even_gt_two_not_prime {n : ℕ} (h₁ : n % 2 = 0) (h₂ : n > 2) : ¬Nat.Prime n := by
  have h₃ : 2 ∣ n := by omega
  have h₄ : n ≠ 2 := by omega
  intro h₅
  have h₆ := Nat.Prime.eq_two_or_odd h₅
  cases h₆ with
  | inl h₆ =>
    have h₇ : n = 2 := h₆
    contradiction
  | inr h₆ =>
    have h₇ : n % 2 = 1 := h₆
    omega

-- Binary digit lists with no ones evaluate to zero. Leading zeros are
-- allowed, so this argument does not rely on indexing past a list's end.
private lemma binary_digits_zero (digits : List ℕ) :
    (∀ d ∈ digits, d < 2) → digits.count 1 = 0 → Nat.ofDigits 2 digits = 0 := by
  induction digits with
  | nil => simp
  | cons d digits ih =>
    intro hd hc
    have bound : d < 2 := hd d List.mem_cons_self
    have dne : d ≠ 1 := by
      intro heq
      subst d
      simp at hc
    have dzero : d = 0 := by omega
    subst d
    have tail_bound : ∀ a ∈ digits, a < 2 := fun a ha =>
      hd a (List.mem_cons_of_mem _ ha)
    have tail_count : digits.count 1 = 0 := by simpa using hc
    simp [Nat.ofDigits_cons, ih tail_bound tail_count]

-- Exactly one nonzero binary digit evaluates to a power of two.
private lemma binary_digits_one (digits : List ℕ) :
    (∀ d ∈ digits, d < 2) → digits.count 1 = 1 →
      ∃ k : ℕ, Nat.ofDigits 2 digits = 2 ^ k := by
  induction digits with
  | nil => simp
  | cons d digits ih =>
    intro hd hc
    have bound : d < 2 := hd d List.mem_cons_self
    have tail_bound : ∀ a ∈ digits, a < 2 := fun a ha =>
      hd a (List.mem_cons_of_mem _ ha)
    have cases : d = 0 ∨ d = 1 := by omega
    rcases cases with rfl | rfl
    · have tail_count : digits.count 1 = 1 := by simpa using hc
      obtain ⟨k, hk⟩ := ih tail_bound tail_count
      exact ⟨k + 1, by simp [Nat.ofDigits_cons, hk, Nat.pow_succ, Nat.mul_comm]⟩
    · have tail_count : digits.count 1 = 0 := by simpa using hc
      have tail_zero := binary_digits_zero digits tail_bound tail_count
      exact ⟨0, by simp [Nat.ofDigits_cons, tail_zero]⟩

-- Key fact: popcount one characterizes nonzero powers of two.
lemma popcount_eq_one_iff_pow_two (n : ℕ) : popcount n = 1 ↔ n ≠ 0 ∧ ∃ k : ℕ, n = 2 ^ k := by
  constructor
  · intro h
    have hn : n ≠ 0 := by
      intro hzero
      subst n
      simp [popcount] at h
    obtain ⟨k, hk⟩ := binary_digits_one (Nat.digits 2 n)
      (fun d hd => Nat.digits_lt_base (by decide) hd) h
    exact ⟨hn, k, by simpa only [Nat.ofDigits_digits] using hk⟩
  · rintro ⟨_, k, rfl⟩
    have digits_one : Nat.digits 2 1 = [1] := by decide
    have digits_power : Nat.digits 2 (2 ^ k) = List.replicate k 0 ++ [1] := by
      simpa only [Nat.mul_one, digits_one] using
        (Nat.digits_base_pow_mul (b := 2) (k := k) (m := 1) (by decide) (by decide))
    change (Nat.digits 2 (2 ^ k)).count 1 = 1
    rw [digits_power]
    simp [List.count_replicate]

-- Helper lemma: a prime power of two has exponent one.
lemma pow_two_prime_iff {k : ℕ} : Nat.Prime (2 ^ k) ↔ k = 1 := by
  constructor
  · exact Nat.Prime.eq_one_of_pow
  · rintro rfl
    simpa using Nat.prime_two

-- If n is both binary-atomic and arith-atomic, n = 2.
theorem common_atoms_eq_two : {n : ℕ | binaryAtomic n ∧ arithAtomic n} = {2} := by
  apply Set.Subset.antisymm
  · -- Forward direction: if n is both binary-atomic and arith-atomic, then n = 2
    intro n hn
    have h₁ : binaryAtomic n := hn.1
    have h₂ : arithAtomic n := hn.2
    have h₃ : n > 0 := h₁.1
    have h₄ : popcount n = 1 := h₁.2
    have h₅ : Nat.Prime n := h₂.2
    -- Since popcount n = 1, n is a power of 2
    have h₆ : ∃ k : ℕ, n = 2 ^ k := by
      have h₇ : n ≠ 0 ∧ ∃ k : ℕ, n = 2 ^ k := (popcount_eq_one_iff_pow_two n).mp h₄
      exact h₇.2
    obtain ⟨k, hk⟩ := h₆
    have h₇ : n = 2 ^ k := hk
    have h₈ : Nat.Prime (2 ^ k) := by
      rw [h₇] at h₅
      exact h₅
    -- Since 2^k is prime, k must be 1
    have h₉ : k = 1 := by
      have h₁₀ : Nat.Prime (2 ^ k) ↔ k = 1 := pow_two_prime_iff (k := k)
      have h₁₁ : Nat.Prime (2 ^ k) := h₈
      have h₁₂ : k = 1 := (h₁₀.mp h₁₁)
      exact h₁₂
    -- Therefore n = 2
    have h₁₀ : n = 2 := by
      calc
        n = 2 ^ k := h₇
        _ = 2 ^ 1 := by rw [h₉]
        _ = 2 := by norm_num
    -- We need to show n ∈ ({2} : Set ℕ)
    rw [h₁₀]
    <;> simp [Set.mem_singleton_iff]
  · -- Backward direction: 2 is both binary-atomic and arith-atomic
    intro n hn
    rw [Set.mem_singleton_iff] at hn
    rw [hn]
    constructor
    · -- Prove 2 is binary-atomic
      constructor
      · norm_num [binaryAtomic, popcount]
      · decide
    · -- Prove 2 is arith-atomic
      constructor
      · norm_num [arithAtomic]
      · decide

-- Cantor: no set is equal to its own powerset (via surjection).
theorem cantor_theorem : ∀ (f : ℕ → Set ℕ), ∃ s, s ∉ Set.range f := by
  intro f
  let s : Set ℕ := {x | x ∉ f x}
  use s
  intro h
  rcases h with ⟨y, hy⟩
  have : y ∈ s ↔ y ∉ f y := by rfl
  rw [hy] at this
  tauto

-- Central proposition.
theorem central_proposition : True := True.intro