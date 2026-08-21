import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace Erdos1135

open scoped Nat

-- The Collatz map in "shortcut" form: T(n) = (3n+1)/2 if n odd, n/2 if n even
def col (n : ℕ) : ℕ := if Even n then n / 2 else (3 * n + 1) / 2

lemma col_even {n : ℕ} (h : Even n) : col n = n / 2 := by
  unfold col; rw [if_pos h]

lemma col_odd {n : ℕ} (h : ¬ Even n) : col n = (3 * n + 1) / 2 := by
  unfold col; rw [if_neg h]

lemma odd_positive {n : ℕ} (hn : n ≥ 1) : (3 * n + 1) / 2 ≥ 1 := by
  have h : 3 * n + 1 ≥ 2 := by
    have h₁ : n ≥ 1 := hn
    have h₂ : 3 * n ≥ 3 := by nlinarith
    omega
  have h₁ : (3 * n + 1) / 2 ≥ 1 := by
    have h₂ : 2 ≤ 3 * n + 1 := by omega
    have h₃ : (3 * n + 1) / 2 ≥ 1 := by
      apply Nat.le_div_iff_mul_le (by norm_num) |>.mpr
      <;> nlinarith
    exact h₃
  exact h₁

-- 1 is odd, so the shortcut map sends it to (3·1+1)/2 = 2, and 2 back to 1: the
-- terminal two-cycle, not a fixed point.
lemma col_one : col 1 = 2 := by norm_num [col, Nat.even_iff]
lemma col_two : col 2 = 1 := by norm_num [col, Nat.even_iff]

-- Even numbers contract: col(n) = n/2 < n for n ≥ 2
lemma even_contracts {n : ℕ} (h_even : Even n) (hn : n > 1) : col n < n := by
  rw [col_even h_even]
  have h₁ : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
  exact h₁

-- Modular arithmetic helpers
lemma mod_4_cases {n : ℕ} (h_odd : ¬ Even n) :
    n % 4 = 1 ∨ n % 4 = 3 := by
  have h₁ : n % 2 = 1 := by
    have h₂ : ¬Even n := h_odd
    have h₃ : n % 2 = 1 := by
      rw [Nat.even_iff] at h₂
      omega
    exact h₃
  have h₂ : n % 4 = 1 ∨ n % 4 = 3 := by
    have : n % 4 = 1 ∨ n % 4 = 3 := by
      omega
    exact this
  exact h₂

lemma odd_mod_3_mod_8 {n : ℕ} (h_odd : ¬ Even n) (h_mod : n % 4 = 3) :
    n % 8 = 3 ∨ n % 8 = 7 := by omega

lemma mod_8_cases_3 {n : ℕ} (h : n % 8 = 3) : ∃ m, n = 8 * m + 3 := by
  use n / 8; omega

lemma mod_8_cases_7 {n : ℕ} (h : n % 8 = 7) : ∃ m, n = 8 * m + 7 := by
  use n / 8; omega

-- For n ≡ 1 (mod 4): col²(n) = (3n+1)/4 < n
lemma odd_mod_four_contracts {n : ℕ} (h_odd : ¬ Even n) (h_mod : n % 4 = 1) (hn : 1 < n) :
    col (col n) < n := by sorry

/-- PART 2: Helper lemmas for n = 8m + 3 -/
-- Each lemma computes col^k directly as a function of the parameter (no n pattern matching)

lemma col3_8m_plus_3 (m : ℕ) : (col^[3]) (8 * m + 3) = 9 * m + 4 := by sorry

lemma col4_8m_plus_3_even_m (t : ℕ) : (col^[4]) (8 * (2 * t) + 3) = 9 * t + 2 := by sorry

lemma col5_8m_plus_3_m4s_plus_1 (s : ℕ) : (col^[5]) (8 * (4 * s + 1) + 3) = 27 * s + 10 := by sorry

lemma col5_8m_plus_3_m4s_plus_3 (s : ℕ) : (col^[5]) (8 * (4 * s + 3) + 3) = 81 * s + 71 := by sorry

lemma col6_8m_plus_3_m4s_plus_3_s_even (u : ℕ) : (col^[6]) (8 * (4 * (2 * u) + 3) + 3) = 243 * u + 107 := by sorry

lemma col6_8m_plus_3_m4s_plus_3_s_odd (u : ℕ) : (col^[6]) (8 * (4 * (2 * u + 1) + 3) + 3) = 81 * u + 76 := by sorry

lemma col7_8m_plus_3_m8s_plus_7_u_even (w : ℕ) : (col^[7]) (8 * (8 * (2 * w) + 7) + 3) = 81 * w + 38 := by sorry


/-- PART 3: Helper lemmas for n = 8m + 7 -/

lemma col3_8m_plus_7 (m : ℕ) : (col^[3]) (8 * m + 7) = 27 * m + 26 := by sorry

lemma col4_8m_plus_7_even_m (t : ℕ) : (col^[4]) (8 * (2 * t) + 7) = 27 * t + 13 := by sorry

lemma col5_8m_plus_7_m4s_plus_1 (s : ℕ) : (col^[5]) (8 * (4 * s + 1) + 7) = 81 * s + 40 := by sorry

lemma col6_8m_plus_7_m4s_plus_3 (s : ℕ) : (col^[6]) (8 * (4 * s + 3) + 7) = (243 * s + 242) / 2 := by sorry


/-- Contract lemmas -/

lemma col6_8m_plus_3_m4s_plus_3_s_even_contract (u : ℕ) : (col^[6]) (8 * (4 * (2 * u) + 3) + 3) < 8 * (4 * (2 * u) + 3) + 3 := by sorry

lemma col7_8m_plus_3_m4s_plus_3_s_odd_contract (u : ℕ) : (col^[7]) (8 * (4 * (2 * u + 1) + 3) + 3) < 8 * (4 * (2 * u + 1) + 3) + 3 := by sorry

lemma col6_8m_plus_3_m4s_plus_3_s_odd_contract (u : ℕ) : u ≥ 1 → (col^[6]) (8 * (4 * (2 * u + 1) + 3) + 3) < 8 * (4 * (2 * u + 1) + 3) + 3 := by sorry


/-- PART 4: Main contraction proofs and theorems -/

-- Strong induction on m for n = 8m + 3
lemma n_mod_8_is_3_contract (m : ℕ) : ∀ (n : ℕ), n = 8 * m + 3 → (∃ k : ℕ, (col^[k]) n < n) := by
  intro n hn
  have h_main : ∃ k : ℕ, (col^[k]) (8 * m + 3) < 8 * m + 3 := by sorry
  sorry

-- Strong induction on m for n = 8m + 7
lemma n_mod_8_is_7_contract (m : ℕ) : ∀ (n : ℕ), n = 8 * m + 7 → (∃ k : ℕ, (col^[k]) n < n) := by
  intro n hn
  have h_main : ∃ k : ℕ, (col^[k]) (8 * m + 7) < 8 * m + 7 := by sorry
  sorry

-- Combines both cases for odd n ≡ 3 (mod 4)
lemma odd_n_mod_3_contract {n : ℕ} (h_odd : ¬ Even n) (h_mod : n % 4 = 3) (hn : n > 1) :
    ∃ k : ℕ, (col^[k]) n < n := by
  have h_cases : n % 8 = 3 ∨ n % 8 = 7 := by sorry
  have h_main : ∃ k : ℕ, (col^[k]) n < n := by sorry
  sorry

-- Every n ≥ 1 has a stopping time
lemma stopping_time_exists (n : ℕ) (hn : n ≥ 1) : ∃ k : ℕ, (col^[k]) n = 1 := by
  have h_main : ∃ k : ℕ, (col^[k]) n = 1 := by sorry
  sorry

-- Collatz sequence stays positive
lemma pos_iter (n : ℕ) (hn : n ≥ 1) (k : ℕ) : (col^[k]) n ≥ 1 := by
  have h_main : (col^[k]) n ≥ 1 := by sorry
  sorry

-- Main theorem: Collatz conjecture for Erdos Problem 1135
theorem erdos_problem_1135 (n : ℕ) (hn : n ≥ 1) : ∃ k : ℕ, (col^[k]) n = 1 := by
  have h_main : ∃ k : ℕ, (col^[k]) n = 1 := by sorry
  sorry

end Erdos1135
