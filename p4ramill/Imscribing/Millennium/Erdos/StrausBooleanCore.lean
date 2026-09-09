/-
  StrausBooleanCore.lean
  THE BOOLEAN CORE FOR ERDŐS-STRAUS
  =====================================================================
  Author: Lando⊗⊙perator

  This module formalizes the general algebraic ladder identity for the
  Erdős-Straus conjecture and establishes new infinite covering classes
  on the Boolean Core.

  The fundamental mechanism: for any rung r ≥ 1 and factor t ≥ 1 with
  r ∣ t + 1, setting K = (t + 1) / r, whenever 4a = n + r and t ∣ a,
  the rational fraction 4/n splits identically into three unit fractions:
      4/n = 1/a + 1/(K * n * a) + 1/(K * n * (a / t))

  This provides the direct bridge from paraconsistent NegMReachable and
  quadratic non-residue navigation into classical Lean 4 theorems.
-/

import Imscribing.Millennium.Erdos.StrausGreedyFamily
import Mathlib

namespace Erdos.StrausBooleanCore

open Erdos.StrausGreedy

/-- **The unified algebraic ladder identity.**
    For any odd rung `r` and divisor parameter `t` satisfying `r * K = t + 1`,
    whenever `4 * a = n + r` and `t ∣ a`, the three fractions with denominators
    `a`, `K * n * a`, and `K * n * (a / t)` sum to exactly `4 / n`. -/
theorem straus_general_ladder_identity (n r t a K : ℕ)
    (hn : 0 < n) (ha : 0 < a) (ht : 0 < t) (hr : 0 < r) (hK : 0 < K)
    (hladder : 4 * a = n + r)
    (hK_eq : r * K = t + 1)
    (hta : t ∣ a) :
    (4 : ℚ) / n = 1 / (a : ℚ) + 1 / ((K * n * a : ℕ) : ℚ) + 1 / ((K * n * (a / t) : ℕ) : ℚ) := by
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have haq : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have htq : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ht.ne'
  have hrq : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hKq : (K : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hK.ne'
  obtain ⟨q, rfl⟩ := hta
  have hq_pos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | pos
    · exfalso; simp at ha
    · exact pos
  have hq_div : (t * q) / t = q := Nat.mul_div_cancel_left q ht
  have hqq : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq_pos.ne'
  have hK_cast : ((t : ℚ) + 1) = (r : ℚ) * K := by exact_mod_cast hK_eq.symm
  have hladder_q : ((n : ℚ) + r) = 4 * ((t : ℚ) * q) := by exact_mod_cast hladder.symm
  have hH1 : 1 / ((K : ℚ) * n * ((t : ℚ) * q)) + 1 / ((K : ℚ) * n * q) =
             (r : ℚ) / (n * ((t : ℚ) * q)) := by
    calc 1 / ((K : ℚ) * n * ((t : ℚ) * q)) + 1 / ((K : ℚ) * n * q)
        = ((t : ℚ) + 1) / ((K : ℚ) * n * ((t : ℚ) * q)) := by field_simp; ring
      _ = ((r : ℚ) * K) / ((K : ℚ) * n * ((t : ℚ) * q)) := by rw [hK_cast]
      _ = (r : ℚ) / (n * ((t : ℚ) * q)) := by field_simp
  have hH2 : 1 / ((t : ℚ) * q) + (r : ℚ) / (n * ((t : ℚ) * q)) = (4 : ℚ) / n := by
    calc 1 / ((t : ℚ) * q) + (r : ℚ) / (n * ((t : ℚ) * q))
        = ((n : ℚ) + r) / (n * ((t : ℚ) * q)) := by field_simp
      _ = (4 * ((t : ℚ) * q)) / (n * ((t : ℚ) * q)) := by rw [hladder_q]
      _ = (4 : ℚ) / n := by field_simp
  have H : 1 / ((t * q : ℕ) : ℚ) + 1 / ((K * n * (t * q) : ℕ) : ℚ) + 1 / ((K * n * ((t * q) / t) : ℕ) : ℚ) = (4 : ℚ) / n := by
    rw [hq_div]
    push_cast
    rw [add_assoc, hH1, hH2]
  exact H.symm

/-- **Representation from the general ladder identity.** -/
theorem threeUnit_of_ladder (n r t a K : ℕ)
    (hn : 0 < n) (ha : 0 < a) (ht : 0 < t) (hr : 0 < r) (hK : 0 < K)
    (hladder : 4 * a = n + r)
    (hK_eq : r * K = t + 1)
    (hta : t ∣ a) :
    IsThreeUnit n a (K * n * a) (K * n * (a / t)) := by
  have hq_pos : 0 < a / t := by
    obtain ⟨q, rfl⟩ := hta
    rw [Nat.mul_div_cancel_left q ht]
    rcases Nat.eq_zero_or_pos q with rfl | pos
    · exfalso; simp at ha
    · exact pos
  refine ⟨ha, by positivity, by positivity, ?_⟩
  exact straus_general_ladder_identity n r t a K hn ha ht hr hK hladder hK_eq hta

/-- **The bridge theorem.**
    `NegMReachable (n * a) r` together with `4 * a = n + r` and coprimality
    yields a classical three-unit fraction representation on the Boolean Core. -/
theorem threeUnit_of_negMReachable (n r a : ℕ)
    (hn : 0 < n) (hr0 : 0 < r) (ha0 : 0 < a)
    (ha : 4 * a = n + r) (hcop : Nat.Coprime r (n * a))
    (hreach : NegMReachable (n * a) r) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ (4 : ℚ) / n = 1 / x + 1 / y + 1 / z := by
  obtain ⟨u, hu0, hudvd, hu⟩ := hreach
  let M := n * a
  have hM0 : 0 < M := Nat.mul_pos hn ha0
  have hM2 : 0 < M * M := Nat.mul_pos hM0 hM0
  obtain ⟨v, hv_eq⟩ := hudvd
  have huv : u * v = M * M := hv_eq.symm
  have hv0 : 0 < v := by
    rcases Nat.eq_zero_or_pos v with rfl | pos
    · exfalso
      rw [mul_zero] at huv
      linarith [hM2, huv]
    · exact pos
  have hv_dvd : r ∣ M + v := v_condition_free r M u v hr0 huv hcop hu
  have hclosed : ClosedAtRungSq n r := ⟨a, u, v, ha0, hu0, hv0, ha, huv, hu, hv_dvd⟩
  exact threeUnit_of_closedAtRungSq n r hn hr0 hclosed

/-- **New covering class: n ≡ 117 (mod 128).**
    Derived from the primitive root power 2⁵ = 32 ≡ -1 (mod 11) at rung r = 11,
    with multiplier K = (32 + 1) / 11 = 3. -/
theorem straus_cover_mod128 (n : ℕ) (hn : 0 < n) (hw : n % 128 = 117) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h11 : 4 ∣ (n + 11) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 11) / 4
  have ha4 : 4 * a = n + 11 := Nat.mul_div_cancel' h11
  have ha_pos : 0 < a := by omega
  have h32_dvd : 32 ∣ a := by
    have hdvd128 : 128 ∣ n + 11 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd128
    use m
    omega
  refine ⟨a, 3 * n * a, 3 * n * (a / 32), ?_⟩
  have hrep := threeUnit_of_ladder n 11 32 a 3 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h32_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **New covering class: n ≡ 29 (mod 40).**
    Derived from t = 10 ≡ -1 (mod 11) at rung r = 11, with K = 1. -/
theorem straus_cover_mod40 (n : ℕ) (hn : 0 < n) (hw : n % 40 = 29) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h11 : 4 ∣ (n + 11) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 11) / 4
  have ha4 : 4 * a = n + 11 := Nat.mul_div_cancel' h11
  have ha_pos : 0 < a := by omega
  have h10_dvd : 10 ∣ a := by
    have hdvd40 : 40 ∣ n + 11 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd40
    use m
    omega
  refine ⟨a, 1 * n * a, 1 * n * (a / 10), ?_⟩
  have hrep := threeUnit_of_ladder n 11 10 a 1 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h10_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **New covering class: n ≡ 101 (mod 108).**
    Derived from t = 27 ≡ -1 (mod 7) at rung r = 7, with K = (27 + 1) / 7 = 4. -/
theorem straus_cover_mod108 (n : ℕ) (hn : 0 < n) (hw : n % 108 = 101) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h7 : 4 ∣ (n + 7) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 7) / 4
  have ha4 : 4 * a = n + 7 := Nat.mul_div_cancel' h7
  have ha_pos : 0 < a := by omega
  have h27_dvd : 27 ∣ a := by
    have hdvd108 : 108 ∣ n + 7 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd108
    use m
    omega
  refine ⟨a, 4 * n * a, 4 * n * (a / 27), ?_⟩
  have hrep := threeUnit_of_ladder n 7 27 a 4 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h27_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **All even integers admit a three-unit fraction representation.** -/
theorem straus_even (n : ℕ) (hn : 0 < n) (heven : n % 2 = 0) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have hm : n = 2 * (n / 2) := (Nat.div_add_mod n 2).symm.trans (by omega)
  let m := n / 2
  have hm0 : 0 < m := by omega
  refine ⟨m, m + 1, m * (m + 1), hm0, by positivity, by positivity, ?_⟩
  have hmq : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm0.ne'
  have hmp1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have hprod : (m : ℚ) * ((m : ℚ) + 1) ≠ 0 := mul_ne_zero hmq hmp1
  have hnq : (n : ℚ) = 2 * (m : ℚ) := by exact_mod_cast hm
  rw [hnq]
  push_cast
  field_simp
  ring

/-- **All integers n ≡ 3 (mod 4) admit a three-unit fraction representation.** -/
theorem straus_mod4_three (n : ℕ) (hn : 0 < n) (h3 : n % 4 = 3) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  let k := n / 4
  have hnk : n = 4 * k + 3 := by omega
  let a := k + 1
  let M := n * a
  have ha0 : 0 < a := by omega
  have hM0 : 0 < M := Nat.mul_pos hn ha0
  refine ⟨a, M + 1, M * (M + 1), ha0, by positivity, by positivity, ?_⟩
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have haq : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha0.ne'
  have hMq : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hM0.ne'
  have hMp1 : ((M : ℚ) + 1) ≠ 0 := by positivity
  have hprod : (M : ℚ) * ((M : ℚ) + 1) ≠ 0 := mul_ne_zero hMq hMp1
  have hstep : (4 : ℚ) * a = (n : ℚ) + 1 := by
    have : 4 * a = n + 1 := by omega
    exact_mod_cast this
  have hM_def : (M : ℚ) = (n : ℚ) * a := by
    show ((n * a : ℕ) : ℚ) = (n : ℚ) * (a : ℚ)
    push_cast
    rfl
  have hsplit : 1 / ((M : ℚ) + 1) + 1 / ((M : ℚ) * ((M : ℚ) + 1)) = 1 / (M : ℚ) := by
    field_simp
  have hmain : 1 / (a : ℚ) + 1 / (M : ℚ) = (4 : ℚ) / n := by
    rw [hM_def]
    calc
      1 / (a : ℚ) + 1 / ((n : ℚ) * a) = ((n : ℚ) + 1) / (n * a) := by
        field_simp
      _ = ((4 : ℚ) * a) / (n * a) := by rw [← hstep]
      _ = (4 : ℚ) / n := by
        rw [mul_div_mul_right (4 : ℚ) (n : ℚ) haq]
  rw [← hsplit] at hmain
  rw [← hmain]
  push_cast
  ring

/-- **All integers n ≡ 5 (mod 8) admit a three-unit fraction representation.** -/
theorem straus_mod8_five (n : ℕ) (hn : 0 < n) (h5 : n % 8 = 5) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h3 : 4 ∣ (n + 3) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 3) / 4
  have ha4 : 4 * a = n + 3 := Nat.mul_div_cancel' h3
  have ha_pos : 0 < a := by omega
  have h2_dvd : 2 ∣ a := by
    have hdvd8 : 8 ∣ n + 3 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd8
    use m
    omega
  refine ⟨a, 1 * n * a, 1 * n * (a / 2), ?_⟩
  have hrep := threeUnit_of_ladder n 3 2 a 1 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h2_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **All integers divisible by 3 admit a three-unit fraction representation.** -/
theorem straus_div3 (n : ℕ) (hn : 0 < n) (h3 : 3 ∣ n) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  obtain ⟨m, rfl⟩ := h3
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | pos
    · exfalso; simp at hn
    · exact pos
  let N := 3 * m
  refine ⟨m, N + 1, N * (N + 1), hm0, by positivity, by positivity, ?_⟩
  have hmq : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm0.ne'
  have hNq : (N : ℚ) ≠ 0 := by positivity
  have hNp1 : ((N : ℚ) + 1) ≠ 0 := by positivity
  have hprod : (N : ℚ) * ((N : ℚ) + 1) ≠ 0 := mul_ne_zero hNq hNp1
  have hsplit : 1 / ((N : ℚ) + 1) + 1 / ((N : ℚ) * ((N : ℚ) + 1)) = 1 / (N : ℚ) := by
    field_simp
  have hN_eq : (N : ℚ) = 3 * (m : ℚ) := by
    show ((3 * m : ℕ) : ℚ) = 3 * (m : ℚ)
    push_cast; rfl
  have hmain : 1 / (m : ℚ) + 1 / (N : ℚ) = (4 : ℚ) / (N : ℚ) := by
    rw [hN_eq]
    field_simp
    ring
  rw [← hsplit] at hmain
  rw [← hmain]
  push_cast
  ring

/-- **All integers n ≡ 17 (mod 24) admit a three-unit fraction representation.**
    Derived from the ladder at rung r = 7 with t = 6 and multiplier K = 1. -/
theorem straus_mod24_seventeen (n : ℕ) (hn : 0 < n) (h17 : n % 24 = 17) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h7 : 4 ∣ (n + 7) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 7) / 4
  have ha4 : 4 * a = n + 7 := Nat.mul_div_cancel' h7
  have ha_pos : 0 < a := by omega
  have h6_dvd : 6 ∣ a := by
    have hdvd24 : 24 ∣ n + 7 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd24
    use m
    omega
  refine ⟨a, 1 * n * a, 1 * n * (a / 6), ?_⟩
  have hrep := threeUnit_of_ladder n 7 6 a 1 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h6_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **Complete reduction to the n ≡ 1 (mod 24) frontier.**
    Every positive integer not congruent to 1 modulo 24 unconditionally admits
    a three-unit fraction representation for 4/n, verified on standard classical axioms. -/
theorem straus_of_ne_one_mod24 (n : ℕ) (hn : 0 < n) (hne : n % 24 ≠ 1) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have hmod : n % 24 < 24 := Nat.mod_lt n (by decide)
  have hcases : n % 2 = 0 ∨ n % 4 = 3 ∨ n % 8 = 5 ∨ 3 ∣ n ∨ n % 24 = 17 := by
    omega
  rcases hcases with h | h | h | h | h
  · exact straus_even n hn h
  · exact straus_mod4_three n hn h
  · exact straus_mod8_five n hn h
  · exact straus_div3 n hn h
  · exact straus_mod24_seventeen n hn h

/-- **Winding-order closure via primitive root on the torus.**
    When a prime factor `p` of `M = n * a` is a primitive root modulo an odd prime rung `r`
    (its winding loop wraps all `r - 1` non-zero residues) and carries enough budget
    `p^(r-1) ∣ M²`, the winding midpoint reaches the antipodal coordinate `-M`,
    closing `4/n` into three unit fractions. -/
theorem threeUnit_of_primitiveRoot (n r a p : ℕ)
    (hn : 0 < n) (hr0 : 1 < r) (ha0 : 0 < a) (hp : 0 < p)
    (ha : 4 * a = n + r) (hcop : Nat.Coprime r (n * a))
    (hrM : ¬ (r ∣ (n * a)))
    (hprim : ∀ x : ZMod r, x ≠ 0 → ∃ j : ℕ, j < r - 1 ∧ (p : ZMod r) ^ j = x)
    (hpow : (p : ℕ) ^ (r - 1) ∣ (n * a) * (n * a)) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ (4 : ℚ) / n = 1 / x + 1 / y + 1 / z := by
  have hr_pos : 0 < r := by omega
  have hreach : NegMReachable (n * a) r :=
    negMReachable_of_primitiveRoot (n * a) r p hr0 hp hrM hprim hpow
  exact threeUnit_of_negMReachable n r a hn hr_pos ha0 ha hcop hreach

/-- Frontier prime n = 193 closes at rung 7 via winding on the primitive root. -/
theorem straus_193 :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / 193 = 1 / a + 1 / b + 1 / c := by
  refine ⟨50, 1380, 1331700, by positivity, by positivity, by positivity, by norm_num⟩

/-- Frontier prime n = 313 closes at rung 7 via winding on the primitive root. -/
theorem straus_313 :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / 313 = 1 / a + 1 / b + 1 / c := by
  refine ⟨80, 3580, 4482160, by positivity, by positivity, by positivity, by norm_num⟩

/-- Frontier prime n = 457 closes at greedy rung 3. -/
theorem straus_457 :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / 457 = 1 / a + 1 / b + 1 / c := by
  refine ⟨115, 17520, 184152720, by positivity, by positivity, by positivity, by norm_num⟩

/-- Frontier prime n = 673 closes at rung 7 via winding on the primitive root. -/
theorem straus_673 :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / 673 = 1 / a + 1 / b + 1 / c := by
  refine ⟨170, 16345, 374006290, by positivity, by positivity, by positivity, by norm_num⟩

/-- Frontier value n = 2521 closes at rung 23 on the squared budget M². -/
theorem straus_2521 :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / 2521 = 1 / a + 1 / b + 1 / c := by
  refine ⟨636, 69748, 131876031, by positivity, by positivity, by positivity, by norm_num⟩

/-- Frontier prime n = 73 closes at rung 7. -/
theorem straus_73 :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / 73 = 1 / a + 1 / b + 1 / c := by
  refine ⟨20, 210, 30660, by positivity, by positivity, by positivity, by norm_num⟩

/-- Frontier value n = 97 closes at greedy rung 3. -/
theorem straus_97 :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / 97 = 1 / a + 1 / b + 1 / c := by
  refine ⟨25, 810, 392850, by positivity, by positivity, by positivity, by norm_num⟩

/-- **Multiplicative descent theorem.**
    If `n = c * m` with `c > 0` and `4/m = 1/a + 1/b + 1/d`,
    then `4/n = 1/(c * a) + 1/(c * b) + 1/(c * d)`. -/
theorem straus_mul_descent (m c a b d : ℕ)
    (hm : 0 < m) (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hrep : (4 : ℚ) / m = 1 / a + 1 / b + 1 / d) :
    (4 : ℚ) / (c * m) = 1 / (c * a) + 1 / (c * b) + 1 / (c * d) := by
  have hcq : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  have hmq : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have haq : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have hbq : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hdiv : (4 : ℚ) / ((c : ℚ) * m) = ((4 : ℚ) / m) * (1 / c) := by
    field_simp
  rw [hdiv, hrep]
  field_simp

/-- **Descent from any factor not congruent to 1 modulo 24.**
    If `n` has any proper divisor `m` not congruent to 1 modulo 24,
    then `4/n` admits an unconditional three-unit fraction solution. -/
theorem straus_of_has_non1_factor (n c m : ℕ)
    (hn : n = c * m) (hc : 0 < c) (hm : 0 < m) (hme : m % 24 ≠ 1) :
    ∃ a b d : ℕ, 0 < a ∧ 0 < b ∧ 0 < d ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / d := by
  obtain ⟨a, b, d, ha, hb, hd, hrep⟩ := straus_of_ne_one_mod24 m hm hme
  refine ⟨c * a, c * b, c * d, by positivity, by positivity, by positivity, ?_⟩
  rw [hn]
  push_cast
  exact straus_mul_descent m c a b d hm hc ha hb hd hrep

/-- **New covering class inside n ≡ 1 (mod 24): n ≡ 97 (mod 120).**
    Derived from the ladder at rung r = 3 with t = 5 and K = 2,
    since 3 * 2 = 5 + 1 and 4 * a = n + 3 with 5 ∣ a. -/
theorem straus_cover_mod120_ninety_seven (n : ℕ) (hn : 0 < n) (hw : n % 120 = 97) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h3 : 4 ∣ (n + 3) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 3) / 4
  have ha4 : 4 * a = n + 3 := Nat.mul_div_cancel' h3
  have ha_pos : 0 < a := by omega
  have h5_dvd : 5 ∣ a := by
    have hdvd20 : 20 ∣ n + 3 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd20
    use m
    omega
  refine ⟨a, 2 * n * a, 2 * n * (a / 5), ?_⟩
  have hrep := threeUnit_of_ladder n 3 5 a 2 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h5_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- Executable entry point for compilation to ELF and auditing via vox. -/
def main : IO Unit := do
  IO.println "=== Erdos-Straus Boolean Core Verification ==="
  IO.println "Unified ladder identity and bridge theorems verified."
  IO.println "Covering classes verified: mod 128, mod 40, mod 108, mod 120 (97)."
  IO.println "Frontier reduction verified: all n ≢ 1 (mod 24) solved unconditionally."
  IO.println "Multiplicative descent theorem and factor reduction verified."
  IO.println "Frontier witnesses (73, 97, 193, 313, 457, 673, 2521) verified."
  return ()

end Erdos.StrausBooleanCore
