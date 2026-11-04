import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc

open ArithmeticFunction

local notation "σ" => ArithmeticFunction.sigma (1 : ℕ)

lemma descent_7_5 (z : ℕ) (hz_pos : z > 0) (h_eq : 7 * σ z = 5 * z) : False := by
  have h_cop_7_5 : Nat.Coprime 7 5 := by decide
  have h7z : 7 ∣ z := by
    have h7_dvd_5z : 7 ∣ 5 * z := by
      rw [← h_eq]; exact ⟨σ z, by ring⟩
    exact h_cop_7_5.dvd_of_dvd_mul_left h7_dvd_5z

  obtain ⟨k, hk⟩ := h7z
  have hk_pos : k > 0 := by
    by_contra h
    have h₁ : k = 0 := by omega
    rw [h₁] at hk
    have h₂ : z = 0 := by
      simp [hk, mul_zero]
    linarith

  have h_sigma_eq : σ z = 5 * k := by
    have h₁ : 7 * σ z = 35 * k := by
      calc
        7 * σ z = 5 * z := h_eq
        _ = 5 * (7 * k) := by rw [hk]
        _ = 35 * k := by ring
    have h₂ : 7 * σ z = 7 * (5 * k) := by linarith
    exact mul_left_cancel₀ (by norm_num : (7 : ℕ) ≠ 0) h₂

  -- σ z ≥ z because z is one of its own divisors
  have h_sigma_ge : σ z ≥ z := by
    calc
      σ z = ∑ d ∈ (Nat.divisors z), d := by
        rw [ArithmeticFunction.sigma_apply]
        simp [pow_one]
      _ ≥ z := by
        have hz_mem : z ∈ Nat.divisors z := by
          rw [Nat.mem_divisors]
          exact ⟨dvd_rfl, by omega⟩
        have h_le : z ≤ ∑ d ∈ (Nat.divisors z), d := by
          simpa using
            Finset.single_le_sum
              (s := Nat.divisors z)
              (f := fun d => d)
              (by intro d hd; exact Nat.zero_le d)
              hz_mem
        exact h_le

  -- Contradiction: σ z = 5 * k < 7 * k = z but σ z ≥ z
  have h₁ : σ z < z := by
    have h₂ : 5 * k < 7 * k := by nlinarith
    calc
      σ z = 5 * k := by rw [h_sigma_eq]
      _ < 7 * k := h₂
      _ = z := by rw [hk]

  linarith