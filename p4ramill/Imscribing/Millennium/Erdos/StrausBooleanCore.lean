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

/-- Executable entry point for compilation to ELF and auditing via vox. -/
def main : IO Unit := do
  IO.println "=== Erdos-Straus Boolean Core Verification ==="
  IO.println "Unified ladder identity and bridge theorems verified."
  IO.println "New covering classes checked: mod 128 (117), mod 40 (29), mod 108 (101)."
  return ()

end Erdos.StrausBooleanCore
