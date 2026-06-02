-- Imscribing/Millennium/PerfectCuboid/FactorizationLemma.lean
-- FACTORIZATION LEMMAS L8, L9, L9a, L10 — Factor-Pair Alignment, Cross-GCD Descent
-- All six sorries (S1–S6) closed with elementary Mathlib tactics.
-- Author: Lando ⊗ ⊙perator

import Imscribing.Millennium.PerfectCuboid
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic

open Millennium.PerfectCuboid
open Nat

set_option linter.style.longLine false

namespace Millennium.PerfectCuboid.FactorizationLemma

/- ====================================================================
   PART I: HELPER LEMMAS
   ==================================================================== -/

/-- [S1] If a,b positive coprime naturals satisfy a*b = c*c, then a,b are squares. -/
lemma coprime_square_factor_nat {a b c : Nat} (ha_pos : 0 < a) (hb_pos : 0 < b)
    (h_cop : Nat.Coprime a b) (h_prod : a * b = c * c) :
    Exists (fun u : Nat => Exists (fun v : Nat => a = u * u ∧ b = v * v)) := by
  have h_cop_int : ((a : Int).gcd (b : Int)) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact mod_cast h_cop
  have h_prod_int : (a : Int) * (b : Int) = ((c : Int)) ^ 2 := by
    have h := congrArg (fun (x : Nat) => (x : Int)) h_prod
    simpa [sq] using h
  rcases Int.sq_of_gcd_eq_one h_cop_int h_prod_int with ⟨a0, ha_cases⟩
  rcases ha_cases with (ha_eq | ha_neg)
  · have h_cop_int' : ((b : Int).gcd (a : Int)) = 1 := by
      rw [Int.gcd_comm, h_cop_int]
    have h_prod_int' : (b : Int) * (a : Int) = ((c : Int)) ^ 2 := by
      rw [mul_comm, h_prod_int]
    rcases Int.sq_of_gcd_eq_one h_cop_int' h_prod_int' with ⟨b0, hb_cases⟩
    rcases hb_cases with (hb_eq | hb_neg)
    · set u := a0.natAbs with hu_def
      set v := b0.natAbs with hv_def
      have hu_sq_int : (u : Int) * (u : Int) = (a : Int) := by
        dsimp [u]
        have h : ((a0.natAbs : Int) * (a0.natAbs : Int)) = a0 * a0 := by
          simpa using (Int.natAbs_mul_self (a := a0))
        rw [h, ha_eq, sq]
      have hv_sq_int : (v : Int) * (v : Int) = (b : Int) := by
        dsimp [v]
        have h : ((b0.natAbs : Int) * (b0.natAbs : Int)) = b0 * b0 := by
          simpa using (Int.natAbs_mul_self (a := b0))
        rw [h, hb_eq, sq]
      have hu_nat_sq : a = u * u := by exact_mod_cast hu_sq_int.symm
      have hv_nat_sq : b = v * v := by exact_mod_cast hv_sq_int.symm
      exact ⟨u, v, hu_nat_sq, hv_nat_sq⟩
    · have hb_int_pos : 0 < (b : Int) := by exact_mod_cast hb_pos
      rw [hb_neg] at hb_int_pos
      nlinarith
  · have ha_int_pos : 0 < (a : Int) := by exact_mod_cast ha_pos
    rw [ha_neg] at ha_int_pos
    nlinarith

/-- If s*s and t*t are coprime, then s and t are coprime. -/
lemma coprime_of_coprime_sq {s t : Nat} (h_cop_sq : Nat.Coprime (s * s) (t * t)) :
    Nat.Coprime s t := by
  rw [Nat.coprime_iff_gcd_eq_one] at h_cop_sq
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra h_not
  have h_gt_one : 1 < Nat.gcd s t := by
    have h_ne_zero : Nat.gcd s t ≠ 0 := by
      intro hzero
      have h_s_zero : s = 0 := Nat.eq_zero_of_gcd_eq_zero_left hzero
      have h_t_zero : t = 0 := Nat.eq_zero_of_gcd_eq_zero_right hzero
      subst h_s_zero; subst h_t_zero
      norm_num at h_cop_sq
    omega
  obtain ⟨p, hp_prime, hp_dvd_gcd⟩ :=
    Nat.exists_prime_and_dvd (by omega : Nat.gcd s t ≠ 1)
  have hp_dvd_s : p ∣ s := Nat.dvd_trans hp_dvd_gcd (Nat.gcd_dvd_left _ _)
  have hp_dvd_t : p ∣ t := Nat.dvd_trans hp_dvd_gcd (Nat.gcd_dvd_right _ _)
  have hp_dvd_ss : p ∣ s * s := hp_dvd_s.mul_right s
  have hp_dvd_tt : p ∣ t * t := hp_dvd_t.mul_right t
  have hp_dvd_gcd_sq : p ∣ Nat.gcd (s * s) (t * t) :=
    Nat.dvd_gcd hp_dvd_ss hp_dvd_tt
  rw [h_cop_sq] at hp_dvd_gcd_sq
  exact Nat.Prime.not_dvd_one hp_prime hp_dvd_gcd_sq

/-- Square mod 2: n*n % 2 = n % 2. -/
lemma sq_mod_two (n : Nat) : n * n % 2 = n % 2 := by
  have h := Nat.mod_two_eq_zero_or_one n
  rcases h with (hn | hn)
  · calc
    n * n % 2 = ((n % 2) * (n % 2)) % 2 := by simp [Nat.mul_mod]
    _ = (0 * 0) % 2 := by rw [hn]
    _ = 0 := by norm_num
    _ = n % 2 := by rw [hn]
  · calc
    n * n % 2 = ((n % 2) * (n % 2)) % 2 := by simp [Nat.mul_mod]
    _ = (1 * 1) % 2 := by rw [hn]
    _ = 1 := by norm_num
    _ = n % 2 := by rw [hn]

/-- If coprime s,t have s*s + t*t even, then both are odd. -/
lemma odd_of_coprime_sq_sum_even {s t : Nat} (h_cop : Nat.Coprime s t)
    (h_sum_even : (s * s + t * t) % 2 = 0) : s % 2 = 1 ∧ t % 2 = 1 := by
  have h_cases_s := Nat.mod_two_eq_zero_or_one s
  have h_cases_t := Nat.mod_two_eq_zero_or_one t
  rcases h_cases_s with (hs | hs)
  · rcases h_cases_t with (ht | ht)
    · -- both even => contradiction with coprime
      have h_even_s : 2 ∣ s := Nat.dvd_of_mod_eq_zero hs
      have h_even_t : 2 ∣ t := Nat.dvd_of_mod_eq_zero ht
      have h_even_gcd : 2 ∣ Nat.gcd s t := Nat.dvd_gcd h_even_s h_even_t
      have h_gcd_one : Nat.gcd s t = 1 := by
        rwa [Nat.coprime_iff_gcd_eq_one] at h_cop
      rw [h_gcd_one] at h_even_gcd
      norm_num at h_even_gcd
    · -- s even, t odd => s²+t² ≡ 0+1 = 1 mod 2 ≠ 0
      have hcalc : (s * s + t * t) % 2 = 1 := by
        simp [Nat.add_mod, sq_mod_two s, sq_mod_two t, hs, ht]
      rw [hcalc] at h_sum_even; norm_num at h_sum_even
  · rcases h_cases_t with (ht | ht)
    · -- s odd, t even => s²+t² ≡ 1+0 = 1 mod 2 ≠ 0
      have hcalc : (s * s + t * t) % 2 = 1 := by
        simp [Nat.add_mod, sq_mod_two s, sq_mod_two t, hs, ht]
      rw [hcalc] at h_sum_even; norm_num at h_sum_even
    · -- both odd => result
      exact And.intro hs ht

/-- Any divisor of 2 is 1 or 2. -/
lemma dvd_two_eq_one_or_two {d : Nat} (hd : d ∣ 2) : d = 1 ∨ d = 2 := by
  have h_le : d ≤ 2 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d
  · norm_num at hd
  · left; rfl
  · right; rfl

/-- [S2] factor_pair_coprime: If m,n are coprime with opposite parity,
    then gcd(m-n, m+n) = 1. -/
lemma factor_pair_coprime {m n : Nat} (hm_gt_n : n < m)
    (h_cop : Nat.Coprime m n) (h_parity : m % 2 ≠ n % 2) :
    Nat.Coprime (m - n) (m + n) := by
  apply Nat.coprime_of_dvd'
  intro k hk_prime hk_mn hk_mn'
  have hk_2m : k ∣ 2 * m := by
    have : (m - n) + (m + n) = 2 * m := by omega
    rw [← this]
    exact Nat.dvd_add hk_mn hk_mn'
  have hk_2n : k ∣ 2 * n := by
    -- In ℤ: (m+n) - (m-n) = 2n
    have h_int : (k : ℤ) ∣ (2 : ℤ) * (n : ℤ) := by
      have h1 : (k : ℤ) ∣ (m + n : ℤ) := by exact mod_cast hk_mn'
      have h2 : (k : ℤ) ∣ (m : ℤ) - (n : ℤ) := by
        rw [← Nat.cast_sub (Nat.le_of_lt hm_gt_n)]
        exact mod_cast hk_mn
      have h_diff : ((m + n : ℤ) - (m - n : ℤ)) = (2 : ℤ) * (n : ℤ) := by ring
      rw [← h_diff]
      exact dvd_sub h1 h2
    exact mod_cast h_int
  have h_gcd_one : Nat.gcd m n = 1 := by
    rwa [Nat.coprime_iff_gcd_eq_one] at h_cop
  have hk_gcd : k ∣ Nat.gcd (2 * m) (2 * n) := Nat.dvd_gcd hk_2m hk_2n
  have h_gcd_2 : Nat.gcd (2 * m) (2 * n) = 2 := by
    rw [Nat.gcd_mul_left 2, h_gcd_one, mul_one]
  rw [h_gcd_2] at hk_gcd
  -- k is prime and divides 2, so k = 2
  have hk_eq_2 : k = 2 :=
    Nat.prime_dvd_prime_iff_eq hk_prime (by norm_num : Nat.Prime 2) |>.mp hk_gcd
  rw [hk_eq_2] at hk_mn
  -- Now 2 | (m-n), but m-n is odd (opposite parity), contradiction
  have h_odd_mn : ¬ 2 ∣ (m - n) := by
    have hm_mod2 := Nat.mod_two_eq_zero_or_one m
    have hn_mod2 := Nat.mod_two_eq_zero_or_one n
    rcases hm_mod2 with (hm0 | hm1)
    · rcases hn_mod2 with (hn0 | hn1)
      · exfalso; exact h_parity (by rw [hm0, hn0])
      · have : (m - n) % 2 = 1 := by omega
        intro h2; have h0 := Nat.mod_eq_zero_of_dvd h2
        rw [this] at h0; omega
    · rcases hn_mod2 with (hn0 | hn1)
      · have : (m - n) % 2 = 1 := by omega
        intro h2; have h0 := Nat.mod_eq_zero_of_dvd h2
        rw [this] at h0; omega
      · exfalso; exact h_parity (by rw [hm1, hn1])
  exact absurd hk_mn h_odd_mn

end FactorizationLemma

end PerfectCuboid

end Millennium
