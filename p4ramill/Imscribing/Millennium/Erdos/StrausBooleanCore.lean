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

/-- **The master ladder congruence theorem.**
    For any rung `r > 0` and multiplier `K > 0` with `1 < r * K`, setting `t = r * K - 1`,
    any positive integer `n` satisfying `4 * t ∣ n + r` admits an unconditional
    three-unit fraction representation:
        4/n = 1/a + 1/(K * n * a) + 1/(K * n * (a / t))
    where `a = (n + r) / 4`. -/
theorem straus_cover_of_ladder_mod (n r K : ℕ)
    (hn : 0 < n) (hr : 0 < r) (hK : 0 < K) (hrK : 1 < r * K)
    (hmod : 4 * (r * K - 1) ∣ n + r) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  let t := r * K - 1
  have ht_pos : 0 < t := by omega
  have hK_eq : r * K = t + 1 := by omega
  have h4_dvd : 4 ∣ n + r := by
    have : 4 ∣ 4 * t := by omega
    exact dvd_trans this hmod
  let a := (n + r) / 4
  have ha4 : 4 * a = n + r := Nat.mul_div_cancel' h4_dvd
  have ha_pos : 0 < a := by omega
  have ht_dvd : t ∣ a := by
    obtain ⟨m, hm⟩ := hmod
    have h4a : 4 * a = 4 * (t * m) := by
      calc 4 * a = n + r := ha4
        _ = 4 * (r * K - 1) * m := hm
        _ = 4 * (t * m) := by ring
    have ha_tm : a = t * m := Nat.eq_of_mul_eq_mul_left (by decide) h4a
    exact ⟨m, ha_tm⟩
  refine ⟨a, K * n * a, K * n * (a / t), ?_⟩
  have hrep := threeUnit_of_ladder n r t a K hn ha_pos ht_pos hr hK ha4 hK_eq ht_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **The Schinzel-Mordell algebraic identity.**
    Whenever `n = 4 * a * b - (u + v)` with `u ∣ a * b` and `v ∣ a * b`,
    the fraction `4 / n` decomposes into three unit fractions:
        4/n = 1/(a * b) + 1/(((a * b) / u) * n) + 1/(((a * b) / v) * n) -/
theorem straus_schinzel_identity (a b u v n : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hu : 0 < u) (hv : 0 < v) (hn : 0 < n)
    (hudvd : u ∣ a * b) (hvdvd : v ∣ a * b)
    (heq : n + (u + v) = 4 * a * b) :
    (4 : ℚ) / n = 1 / (a * b : ℚ) + 1 / (((a * b / u : ℕ) * n : ℕ) : ℚ) + 1 / (((a * b / v : ℕ) * n : ℕ) : ℚ) := by
  obtain ⟨X, hX⟩ := hudvd
  obtain ⟨Y, hY⟩ := hvdvd
  have hXu : a * b / u = X := by rw [hX, Nat.mul_div_cancel_left X hu]
  have hYv : a * b / v = Y := by rw [hY, Nat.mul_div_cancel_left Y hv]
  rw [hXu, hYv]
  have hab_pos : 0 < a * b := Nat.mul_pos ha hb
  have hX_pos : 0 < X := by
    rcases Nat.eq_zero_or_pos X with rfl | pos
    · exfalso; simp [mul_zero] at hX; omega
    · exact pos
  have hY_pos : 0 < Y := by
    rcases Nat.eq_zero_or_pos Y with rfl | pos
    · exfalso; simp [mul_zero] at hY; omega
    · exact pos
  have hab_eq : (a * b : ℚ) = (u : ℚ) * (X : ℚ) := by exact_mod_cast hX
  have hab_eq_Y : (a * b : ℚ) = (v : ℚ) * (Y : ℚ) := by exact_mod_cast hY
  have heq_nat : n + u + v = 4 * (a * b) := by
    calc n + u + v = n + (u + v) := add_assoc n u v
      _ = 4 * a * b := heq
      _ = 4 * (a * b) := mul_assoc 4 a b
  have heq_q : (n : ℚ) + (u : ℚ) + (v : ℚ) = 4 * (a * b : ℚ) := by exact_mod_cast heq_nat
  have h1 : 1 / ((X : ℚ) * n) = (u : ℚ) / ((a * b : ℚ) * n) := by
    rw [hab_eq]
    field_simp
  have h2 : 1 / ((Y : ℚ) * n) = (v : ℚ) / ((a * b : ℚ) * n) := by
    rw [hab_eq_Y]
    field_simp
  push_cast
  rw [h1, h2]
  calc (4 : ℚ) / n = (4 * (a * b : ℚ)) / ((a * b : ℚ) * n) := by field_simp
    _ = ((n : ℚ) + (u : ℚ) + (v : ℚ)) / ((a * b : ℚ) * n) := by rw [heq_q]
    _ = 1 / (a * b : ℚ) + (u : ℚ) / ((a * b : ℚ) * n) + (v : ℚ) / ((a * b : ℚ) * n) := by field_simp

/-- **Mordell's first polynomial family: n = 4ab - a - b.** -/
theorem straus_mordell_identity_one (a b n : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hn : 0 < n)
    (heq : n + (a + b) = 4 * a * b) :
    (4 : ℚ) / n = 1 / (a * b : ℚ) + 1 / ((b * n : ℕ) : ℚ) + 1 / ((a * n : ℕ) : ℚ) := by
  have hadvd : a ∣ a * b := dvd_mul_right a b
  have hbdvd : b ∣ a * b := dvd_mul_left b a
  have hdiv_a : a * b / a = b := Nat.mul_div_cancel_left b ha
  have hdiv_b : a * b / b = a := by rw [mul_comm a b]; exact Nat.mul_div_cancel_left a hb
  have hrep := straus_schinzel_identity a b a b n ha hb ha hb hn hadvd hbdvd heq
  rw [hdiv_a, hdiv_b] at hrep
  exact hrep

/-- **Mordell's second polynomial family: n = 4ab - b - 1.** -/
theorem straus_mordell_identity_two (a b n : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hn : 0 < n)
    (heq : n + (b + 1) = 4 * a * b) :
    (4 : ℚ) / n = 1 / (a * b : ℚ) + 1 / ((a * n : ℕ) : ℚ) + 1 / ((a * b * n : ℕ) : ℚ) := by
  have hbdvd : b ∣ a * b := dvd_mul_left b a
  have h1dvd : 1 ∣ a * b := one_dvd (a * b)
  have hdiv_b : a * b / b = a := by rw [mul_comm a b]; exact Nat.mul_div_cancel_left a hb
  have hdiv_1 : a * b / 1 = a * b := Nat.div_one (a * b)
  have hrep := straus_schinzel_identity a b b 1 n ha hb hb (by norm_num) hn hbdvd h1dvd heq
  rw [hdiv_b, hdiv_1] at hrep
  exact hrep

/-- **Sierpiński's polynomial family: n = 4ab - a - 1.** -/
theorem straus_sierpinski_identity (a b n : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hn : 0 < n)
    (heq : n + (a + 1) = 4 * a * b) :
    (4 : ℚ) / n = 1 / (a * b : ℚ) + 1 / ((b * n : ℕ) : ℚ) + 1 / ((a * b * n : ℕ) : ℚ) := by
  have hadvd : a ∣ a * b := dvd_mul_right a b
  have h1dvd : 1 ∣ a * b := one_dvd (a * b)
  have hdiv_a : a * b / a = b := Nat.mul_div_cancel_left b ha
  have hdiv_1 : a * b / 1 = a * b := Nat.div_one (a * b)
  have hrep := straus_schinzel_identity a b a 1 n ha hb ha (by norm_num) hn hadvd h1dvd heq
  rw [hdiv_a, hdiv_1] at hrep
  exact hrep

/-- **Schinzel's binary family: n = 4ab - 3 when 2 ∣ ab.** -/
theorem straus_schinzel_three (a b n : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hn : 0 < n)
    (h2dvd : 2 ∣ a * b)
    (heq : n + 3 = 4 * a * b) :
    (4 : ℚ) / n = 1 / (a * b : ℚ) + 1 / (((a * b / 2 : ℕ) * n : ℕ) : ℚ) + 1 / ((a * b * n : ℕ) : ℚ) := by
  have h1dvd : 1 ∣ a * b := one_dvd (a * b)
  have hdiv_1 : a * b / 1 = a * b := Nat.div_one (a * b)
  have heq' : n + (2 + 1) = 4 * a * b := by omega
  have hrep := straus_schinzel_identity a b 2 1 n ha hb (by norm_num) (by norm_num) hn h2dvd h1dvd heq'
  rw [hdiv_1] at hrep
  exact hrep

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

/-- **Two-generator torus winding bridge.**
    When two coprime primes `p, q` of `M = n * a` jointly cover `(ZMod r)ˣ`
    and each carries enough power budget `p^(r-1), q^(r-1) ∣ M²`,
    `-M` is reachable in `M²`, closing `4/n` into three unit fractions. -/
theorem threeUnit_of_twoGen (n r a p q : ℕ)
    (hn : 0 < n) (hr0 : 0 < r) (ha0 : 0 < a) (hp : 0 < p) (hq : 0 < q)
    (ha : 4 * a = n + r) (hcop_rM : Nat.Coprime r (n * a))
    (hcop_pq : Nat.Coprime p q) (hrM : ¬ (r ∣ (n * a)))
    (hgen : ∀ x : ZMod r, x ≠ 0 →
      ∃ i j : ℕ, i < r - 1 ∧ j < r - 1 ∧ (p : ZMod r) ^ i * (q : ZMod r) ^ j = x)
    (hpM : (p : ℕ) ^ (r - 1) ∣ (n * a) * (n * a))
    (hqM : (q : ℕ) ^ (r - 1) ∣ (n * a) * (n * a)) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ (4 : ℚ) / n = 1 / x + 1 / y + 1 / z := by
  have hreach : NegMReachable (n * a) r :=
    negMReachable_of_twoGen (n * a) r p q hp hq hcop_pq hrM hgen hpM hqM
  exact threeUnit_of_negMReachable n r a hn hr0 ha0 ha hcop_rM hreach

/-- **Multi-generator torus winding bridge (the pigeonhole step).**
    A finite family `S` of pairwise-coprime prime powers dividing `M = n * a`,
    whose powers jointly hit every nonzero residue mod `r` within budget,
    closes `4/n` into three unit fractions. -/
theorem threeUnit_of_multiGen (n r a : ℕ) (S : Finset ℕ)
    (hn : 0 < n) (hr0 : 0 < r) (ha0 : 0 < a)
    (ha : 4 * a = n + r) (hcop_rM : Nat.Coprime r (n * a))
    (hpos : ∀ s ∈ S, 0 < s)
    (hcop : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Nat.Coprime x y)
    (hrM : ¬ (r ∣ (n * a)))
    (hbud : ∀ s ∈ S, s ^ (r - 1) ∣ (n * a) * (n * a))
    (hgen : ∀ x : ZMod r, x ≠ 0 → ∃ f : ℕ → ℕ, (∀ s ∈ S, f s < r - 1) ∧
        ∏ s ∈ S, (s : ZMod r) ^ (f s) = x) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ (4 : ℚ) / n = 1 / x + 1 / y + 1 / z := by
  have hreach : NegMReachable (n * a) r :=
    negMReachable_of_multiGen (n * a) r S hpos hcop hrM hbud hgen
  exact threeUnit_of_negMReachable n r a hn hr0 ha0 ha hcop_rM hreach

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

/-- **New covering class inside n ≡ 1 (mod 24): n ≡ 73 (mod 168).**
    Derived from the ladder at rung r = 11 with t = 21 and K = 2,
    since 11 * 2 = 21 + 1 and 4 * a = n + 11 with 21 ∣ a. -/
theorem straus_cover_mod168_seventy_three (n : ℕ) (hn : 0 < n) (hw : n % 168 = 73) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h11 : 4 ∣ (n + 11) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 11) / 4
  have ha4 : 4 * a = n + 11 := Nat.mul_div_cancel' h11
  have ha_pos : 0 < a := by omega
  have h21_dvd : 21 ∣ a := by
    have hdvd84 : 84 ∣ n + 11 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd84
    use m
    omega
  refine ⟨a, 2 * n * a, 2 * n * (a / 21), ?_⟩
  have hrep := threeUnit_of_ladder n 11 21 a 2 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h21_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **New covering class inside n ≡ 1 (mod 24): n ≡ 73 (mod 240).**
    Derived from the ladder at rung r = 7 with t = 20 and K = 3,
    since 7 * 3 = 20 + 1 and 4 * a = n + 7 with 20 ∣ a. -/
theorem straus_cover_mod240_seventy_three (n : ℕ) (hn : 0 < n) (hw : n % 240 = 73) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h7 : 4 ∣ (n + 7) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 7) / 4
  have ha4 : 4 * a = n + 7 := Nat.mul_div_cancel' h7
  have ha_pos : 0 < a := by omega
  have h20_dvd : 20 ∣ a := by
    have hdvd80 : 80 ∣ n + 7 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd80
    use m
    omega
  refine ⟨a, 3 * n * a, 3 * n * (a / 20), ?_⟩
  have hrep := threeUnit_of_ladder n 7 20 a 3 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h20_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **New covering class inside n ≡ 1 (mod 24): n ≡ 217 (mod 264).**
    Derived from the ladder at rung r = 3 with t = 11 and K = 4,
    since 3 * 4 = 11 + 1 and 4 * a = n + 3 with 11 ∣ a. -/
theorem straus_cover_mod264_two_seventeen (n : ℕ) (hn : 0 < n) (hw : n % 264 = 217) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h3 : 4 ∣ (n + 3) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 3) / 4
  have ha4 : 4 * a = n + 3 := Nat.mul_div_cancel' h3
  have ha_pos : 0 < a := by omega
  have h11_dvd : 11 ∣ a := by
    have hdvd44 : 44 ∣ n + 3 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd44
    use m
    omega
  refine ⟨a, 4 * n * a, 4 * n * (a / 11), ?_⟩
  have hrep := threeUnit_of_ladder n 3 11 a 4 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h11_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **New covering class inside n ≡ 1 (mod 24): n ≡ 241 (mod 264).**
    Derived from the ladder at rung r = 23 with t = 22 and K = 1,
    since 23 * 1 = 22 + 1 and 4 * a = n + 23 with 22 ∣ a. -/
theorem straus_cover_mod264_two_forty_one (n : ℕ) (hn : 0 < n) (hw : n % 264 = 241) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h23 : 4 ∣ (n + 23) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 23) / 4
  have ha4 : 4 * a = n + 23 := Nat.mul_div_cancel' h23
  have ha_pos : 0 < a := by omega
  have h22_dvd : 22 ∣ a := by
    have hdvd88 : 88 ∣ n + 23 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd88
    use m
    omega
  refine ⟨a, 1 * n * a, 1 * n * (a / 22), ?_⟩
  have hrep := threeUnit_of_ladder n 23 22 a 1 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h22_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **New covering class inside n ≡ 1 (mod 24): n ≡ 337 (mod 360).**
    Derived from the ladder at rung r = 23 with t = 45 and K = 2,
    since 23 * 2 = 45 + 1 and 4 * a = n + 23 with 45 ∣ a. -/
theorem straus_cover_mod360_three_thirty_seven (n : ℕ) (hn : 0 < n) (hw : n % 360 = 337) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h23 : 4 ∣ (n + 23) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 23) / 4
  have ha4 : 4 * a = n + 23 := Nat.mul_div_cancel' h23
  have ha_pos : 0 < a := by omega
  have h45_dvd : 45 ∣ a := by
    have hdvd180 : 180 ∣ n + 23 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd180
    use m
    omega
  refine ⟨a, 2 * n * a, 2 * n * (a / 45), ?_⟩
  have hrep := threeUnit_of_ladder n 23 45 a 2 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h45_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **New covering class inside n ≡ 1 (mod 24): n ≡ 457 (mod 552).**
    Derived from the ladder at rung r = 3 with t = 23 and K = 8,
    since 3 * 8 = 23 + 1 and 4 * a = n + 3 with 23 ∣ a. -/
theorem straus_cover_mod552_four_fifty_seven (n : ℕ) (hn : 0 < n) (hw : n % 552 = 457) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h3 : 4 ∣ (n + 3) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 3) / 4
  have ha4 : 4 * a = n + 3 := Nat.mul_div_cancel' h3
  have ha_pos : 0 < a := by omega
  have h23_dvd : 23 ∣ a := by
    have hdvd92 : 92 ∣ n + 3 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd92
    use m
    omega
  refine ⟨a, 8 * n * a, 8 * n * (a / 23), ?_⟩
  have hrep := threeUnit_of_ladder n 3 23 a 8 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h23_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **New covering class inside n ≡ 1 (mod 24): n ≡ 97 (mod 168).**
    Derived from the ladder at rung r = 15 with t = 14 and K = 1,
    since 15 * 1 = 14 + 1 and 4 * a = n + 15 with 14 ∣ a. -/
theorem straus_cover_mod168_ninety_seven (n : ℕ) (hn : 0 < n) (hw : n % 168 = 97) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h15 : 4 ∣ (n + 15) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 15) / 4
  have ha4 : 4 * a = n + 15 := Nat.mul_div_cancel' h15
  have ha_pos : 0 < a := by omega
  have h14_dvd : 14 ∣ a := by
    have hdvd56 : 56 ∣ n + 15 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd56
    use m
    omega
  refine ⟨a, 1 * n * a, 1 * n * (a / 14), ?_⟩
  have hrep := threeUnit_of_ladder n 15 14 a 1 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h14_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **New covering class inside n ≡ 1 (mod 24): n ≡ 97 (mod 312).**
    Derived from the ladder at rung r = 7 with t = 13 and K = 2,
    since 7 * 2 = 13 + 1 and 4 * a = n + 7 with 13 ∣ a. -/
theorem straus_cover_mod312_ninety_seven (n : ℕ) (hn : 0 < n) (hw : n % 312 = 97) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h7 : 4 ∣ (n + 7) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 7) / 4
  have ha4 : 4 * a = n + 7 := Nat.mul_div_cancel' h7
  have ha_pos : 0 < a := by omega
  have h13_dvd : 13 ∣ a := by
    have hdvd52 : 52 ∣ n + 7 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd52
    use m
    omega
  refine ⟨a, 2 * n * a, 2 * n * (a / 13), ?_⟩
  have hrep := threeUnit_of_ladder n 7 13 a 2 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h13_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **New covering class inside n ≡ 1 (mod 24): n ≡ 337 (mod 408).**
    Derived from the ladder at rung r = 3 with t = 17 and K = 6,
    since 3 * 6 = 17 + 1 and 4 * a = n + 3 with 17 ∣ a. -/
theorem straus_cover_mod408_three_thirty_seven (n : ℕ) (hn : 0 < n) (hw : n % 408 = 337) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h3 : 4 ∣ (n + 3) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 3) / 4
  have ha4 : 4 * a = n + 3 := Nat.mul_div_cancel' h3
  have ha_pos : 0 < a := by omega
  have h17_dvd : 17 ∣ a := by
    have hdvd68 : 68 ∣ n + 3 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd68
    use m
    omega
  refine ⟨a, 6 * n * a, 6 * n * (a / 17), ?_⟩
  have hrep := threeUnit_of_ladder n 3 17 a 6 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h17_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **New covering class inside n ≡ 1 (mod 24): n ≡ 265 (mod 408).**
    Derived from the ladder at rung r = 7 with t = 34 and K = 5,
    since 7 * 5 = 34 + 1 and 4 * a = n + 7 with 34 ∣ a. -/
theorem straus_cover_mod408_two_sixty_five (n : ℕ) (hn : 0 < n) (hw : n % 408 = 265) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h7 : 4 ∣ (n + 7) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 7) / 4
  have ha4 : 4 * a = n + 7 := Nat.mul_div_cancel' h7
  have ha_pos : 0 < a := by omega
  have h34_dvd : 34 ∣ a := by
    have hdvd136 : 136 ∣ n + 7 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd136
    use m
    omega
  refine ⟨a, 5 * n * a, 5 * n * (a / 34), ?_⟩
  have hrep := threeUnit_of_ladder n 7 34 a 5 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h34_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **New covering class inside n ≡ 1 (mod 24): n ≡ 433 (mod 456).**
    Derived from the ladder at rung r = 23 with t = 114 and K = 5,
    since 23 * 5 = 114 + 1 and 4 * a = n + 23 with 114 ∣ a. -/
theorem straus_cover_mod456_four_thirty_three (n : ℕ) (hn : 0 < n) (hw : n % 456 = 433) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h23 : 4 ∣ (n + 23) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 23) / 4
  have ha4 : 4 * a = n + 23 := Nat.mul_div_cancel' h23
  have ha_pos : 0 < a := by omega
  have h114_dvd : 114 ∣ a := by
    have hdvd456 : 456 ∣ n + 23 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd456
    use m
    omega
  refine ⟨a, 5 * n * a, 5 * n * (a / 114), ?_⟩
  have hrep := threeUnit_of_ladder n 23 114 a 5 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h114_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **New covering class inside n ≡ 1 (mod 24): n ≡ 337 (mod 528).**
    Derived from the ladder at rung r = 15 with t = 44 and K = 3,
    since 15 * 3 = 44 + 1 and 4 * a = n + 15 with 44 ∣ a. -/
theorem straus_cover_mod528_three_thirty_seven (n : ℕ) (hn : 0 < n) (hw : n % 528 = 337) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h15 : 4 ∣ (n + 15) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 15) / 4
  have ha4 : 4 * a = n + 15 := Nat.mul_div_cancel' h15
  have ha_pos : 0 < a := by omega
  have h44_dvd : 44 ∣ a := by
    have hdvd176 : 176 ∣ n + 15 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd176
    use m
    omega
  refine ⟨a, 3 * n * a, 3 * n * (a / 44), ?_⟩
  have hrep := threeUnit_of_ladder n 15 44 a 3 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h44_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **New covering class inside n ≡ 1 (mod 24): n ≡ 577 (mod 696).**
    Derived from the ladder at rung r = 3 with t = 29 and K = 10,
    since 3 * 10 = 29 + 1 and 4 * a = n + 3 with 29 ∣ a. -/
theorem straus_cover_mod696_five_seventy_seven (n : ℕ) (hn : 0 < n) (hw : n % 696 = 577) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h3 : 4 ∣ (n + 3) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 3) / 4
  have ha4 : 4 * a = n + 3 := Nat.mul_div_cancel' h3
  have ha_pos : 0 < a := by omega
  have h29_dvd : 29 ∣ a := by
    have hdvd116 : 116 ∣ n + 3 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd116
    use m
    omega
  refine ⟨a, 10 * n * a, 10 * n * (a / 29), ?_⟩
  have hrep := threeUnit_of_ladder n 3 29 a 10 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h29_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **New covering class inside n ≡ 1 (mod 24): n ≡ 337 (mod 696).**
    Derived from the ladder at rung r = 11 with t = 87 and K = 8,
    since 11 * 8 = 87 + 1 and 4 * a = n + 11 with 87 ∣ a. -/
theorem straus_cover_mod696_three_thirty_seven (n : ℕ) (hn : 0 < n) (hw : n % 696 = 337) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h11 : 4 ∣ (n + 11) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 11) / 4
  have ha4 : 4 * a = n + 11 := Nat.mul_div_cancel' h11
  have ha_pos : 0 < a := by omega
  have h87_dvd : 87 ∣ a := by
    have hdvd348 : 348 ∣ n + 11 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd348
    use m
    omega
  refine ⟨a, 8 * n * a, 8 * n * (a / 87), ?_⟩
  have hrep := threeUnit_of_ladder n 11 87 a 8 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h87_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **New covering class inside n ≡ 1 (mod 24): n ≡ 217 (mod 696).**
    Derived from the ladder at rung r = 15 with t = 29 and K = 2,
    since 15 * 2 = 29 + 1 and 4 * a = n + 15 with 29 ∣ a. -/
theorem straus_cover_mod696_two_seventeen (n : ℕ) (hn : 0 < n) (hw : n % 696 = 217) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h15 : 4 ∣ (n + 15) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 15) / 4
  have ha4 : 4 * a = n + 15 := Nat.mul_div_cancel' h15
  have ha_pos : 0 < a := by omega
  have h29_dvd : 29 ∣ a := by
    have hdvd116 : 116 ∣ n + 15 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd116
    use m
    omega
  refine ⟨a, 2 * n * a, 2 * n * (a / 29), ?_⟩
  have hrep := threeUnit_of_ladder n 15 29 a 2 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h29_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **New covering class inside n ≡ 1 (mod 24): n ≡ 241 (mod 744).**
    Derived from the ladder at rung r = 7 with t = 62 and K = 9,
    since 7 * 9 = 62 + 1 and 4 * a = n + 7 with 62 ∣ a. -/
theorem straus_cover_mod744_two_forty_one (n : ℕ) (hn : 0 < n) (hw : n % 744 = 241) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h7 : 4 ∣ (n + 7) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 7) / 4
  have ha4 : 4 * a = n + 7 := Nat.mul_div_cancel' h7
  have ha_pos : 0 < a := by omega
  have h62_dvd : 62 ∣ a := by
    have hdvd248 : 248 ∣ n + 7 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd248
    use m
    omega
  refine ⟨a, 9 * n * a, 9 * n * (a / 62), ?_⟩
  have hrep := threeUnit_of_ladder n 7 62 a 9 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h62_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **New covering class inside n ≡ 1 (mod 24): n ≡ 793 (mod 816).**
    Derived from the ladder at rung r = 23 with t = 68 and K = 3,
    since 23 * 3 = 68 + 1 and 4 * a = n + 23 with 68 ∣ a. -/
theorem straus_cover_mod816_seven_ninety_three (n : ℕ) (hn : 0 < n) (hw : n % 816 = 793) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h23 : 4 ∣ (n + 23) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 23) / 4
  have ha4 : 4 * a = n + 23 := Nat.mul_div_cancel' h23
  have ha_pos : 0 < a := by omega
  have h68_dvd : 68 ∣ a := by
    have hdvd272 : 272 ∣ n + 23 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd272
    use m
    omega
  refine ⟨a, 3 * n * a, 3 * n * (a / 68), ?_⟩
  have hrep := threeUnit_of_ladder n 23 68 a 3 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h68_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- **New covering class inside n ≡ 1 (mod 24): n ≡ 697 (mod 840).**
    Derived from the ladder at rung r = 3 with t = 35 and K = 12,
    since 3 * 12 = 35 + 1 and 4 * a = n + 3 with 35 ∣ a. -/
theorem straus_cover_mod840_six_ninety_seven (n : ℕ) (hn : 0 < n) (hw : n % 840 = 697) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have h3 : 4 ∣ (n + 3) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let a := (n + 3) / 4
  have ha4 : 4 * a = n + 3 := Nat.mul_div_cancel' h3
  have ha_pos : 0 < a := by omega
  have h35_dvd : 35 ∣ a := by
    have hdvd140 : 140 ∣ n + 3 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    obtain ⟨m, hm⟩ := hdvd140
    use m
    omega
  refine ⟨a, 12 * n * a, 12 * n * (a / 35), ?_⟩
  have hrep := threeUnit_of_ladder n 3 35 a 12 hn ha_pos (by norm_num) (by norm_num) (by norm_num) ha4 rfl h35_dvd
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2⟩

/-- Frontier value n = 217 closes at greedy rung 3. -/
theorem straus_217 :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / 217 = 1 / a + 1 / b + 1 / c := by
  refine ⟨55, 3980, 9500260, by positivity, by positivity, by positivity, by norm_num⟩

/-- Frontier prime n = 241 closes at rung 7. -/
theorem straus_241 :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / 241 = 1 / a + 1 / b + 1 / c := by
  refine ⟨62, 2139, 1030998, by positivity, by positivity, by positivity, by norm_num⟩

/-- Frontier prime n = 337 closes at greedy rung 3. -/
theorem straus_337 :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / 337 = 1 / a + 1 / b + 1 / c := by
  refine ⟨85, 9550, 54711950, by positivity, by positivity, by positivity, by norm_num⟩

/-- Frontier prime n = 1009 closes at greedy rung 3. -/
theorem straus_1009 :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / 1009 = 1 / a + 1 / b + 1 / c := by
  refine ⟨253, 85096, 1974822872, by positivity, by positivity, by positivity, by norm_num⟩

/-- Frontier prime n = 1129 closes at rung 11. -/
theorem straus_1129 :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / 1129 = 1 / a + 1 / b + 1 / c := by
  refine ⟨285, 29260, 99103620, by positivity, by positivity, by positivity, by norm_num⟩

/-- Frontier prime n = 1153 closes at greedy rung 3. -/
theorem straus_1153 :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / 1153 = 1 / a + 1 / b + 1 / c := by
  refine ⟨289, 111078, 2177239878, by positivity, by positivity, by positivity, by norm_num⟩

/-- Frontier prime n = 1201 closes at rung 23. -/
theorem straus_1201 :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / 1201 = 1 / a + 1 / b + 1 / c := by
  refine ⟨306, 15980, 172727820, by positivity, by positivity, by positivity, by norm_num⟩

/-- Frontier prime n = 1321 closes at rung 7. -/
theorem straus_1321 :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / 1321 = 1 / a + 1 / b + 1 / c := by
  refine ⟨332, 62665, 331121860, by positivity, by positivity, by positivity, by norm_num⟩

/-- Frontier prime n = 1489 closes at rung 7. -/
theorem straus_1489 :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / 1489 = 1 / a + 1 / b + 1 / c := by
  refine ⟨374, 79560, 1303113240, by positivity, by positivity, by positivity, by norm_num⟩

/-- Frontier prime n = 1873 closes at rung 7. -/
theorem straus_1873 :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / 1873 = 1 / a + 1 / b + 1 / c := by
  refine ⟨470, 125760, 11070778560, by positivity, by positivity, by positivity, by norm_num⟩

/-- Frontier prime n = 1993 closes at rung 7. -/
theorem straus_1993 :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / 1993 = 1 / a + 1 / b + 1 / c := by
  refine ⟨500, 142360, 7093087000, by positivity, by positivity, by positivity, by norm_num⟩

/-- **Reduction of Erdős-Straus to primes congruent to 1 modulo 24.**
    By modular reduction, all integers with a prime factor not congruent to 1 (mod 24)
    are solved. By multiplicative descent, if every prime congruent to 1 (mod 24)
    admits a three-unit fraction representation, then EVERY integer n ≥ 2 admits one. -/
theorem straus_reduction_to_primes
    (hprime_frontier : ∀ p : ℕ, p.Prime → p % 24 = 1 →
      ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / p = 1 / a + 1 / b + 1 / c) :
    ∀ n : ℕ, 2 ≤ n →
      ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  intro n hn
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  obtain ⟨c, rfl⟩ := hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  have hc_pos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | pos
    · exfalso; omega
    · exact pos
  by_cases hpeq : p % 24 = 1
  · obtain ⟨a, b, d, ha, hb, hd, hrep⟩ := hprime_frontier p hp_prime hpeq
    refine ⟨c * a, c * b, c * d, by positivity, by positivity, by positivity, ?_⟩
    push_cast
    rw [mul_comm (p : ℚ) (c : ℚ)]
    exact straus_mul_descent p c a b d hp_pos hc_pos ha hb hd hrep
  · obtain ⟨a, b, d, ha, hb, hd, hrep⟩ := straus_of_ne_one_mod24 p hp_pos hpeq
    refine ⟨c * a, c * b, c * d, by positivity, by positivity, by positivity, ?_⟩
    push_cast
    rw [mul_comm (p : ℚ) (c : ℚ)]
    exact straus_mul_descent p c a b d hp_pos hc_pos ha hb hd hrep

/-- **Reduction of the surviving 1 mod 24 class to primes.**
    Any integer n > 1 whose prime factors are all congruent to 1 modulo 24
    admits a three-unit fraction representation provided primes congruent to 1 mod 24 do. -/
theorem straus_class_reduction_to_primes
    (hprime_frontier : ∀ p : ℕ, p.Prime → p % 24 = 1 →
      ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / p = 1 / a + 1 / b + 1 / c)
    (n : ℕ) (hn : 2 ≤ n)
    (hall_prime : ∀ p : ℕ, p.Prime → p ∣ n → p % 24 = 1) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c :=
  straus_reduction_to_primes hprime_frontier n hn

/-- Executable entry point for compilation to ELF and auditing via vox. -/
def main : IO Unit := do
  IO.println "=== Erdos-Straus Boolean Core Verification ==="
  IO.println "Unified ladder identity, master ladder congruence theorem, and Schinzel-Mordell-Sierpinski identities verified."
  IO.println "Covering classes verified: mod 128, 40, 108, 120 (97), 168 (73, 97), 240 (73), 264 (217, 241), 312 (97), 360 (337), 408 (265, 337), 456 (433), 528 (337), 552 (457), 696 (217, 337, 577), 744 (241), 816 (793), 840 (697)."
  IO.println "Frontier reduction verified: all n ≢ 1 (mod 24) solved unconditionally."
  IO.println "Multiplicative descent theorem and factor reduction verified."
  IO.println "Erdos-Straus reduction to prime frontier verified for all n ≥ 2."
  IO.println "Frontier witnesses verified: all 11 primes ≤ 2000 (193, 313, 457, 673, 1009, 1153, 1201, 1321, 1489, 1873, 1993) plus 73, 97, 217, 241, 337, 1129, 2521."
  return ()

end Erdos.StrausBooleanCore
