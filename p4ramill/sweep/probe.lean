import Mathlib
open Finset

/-- From a Roth bound `r₃(N) ≤ C·N/(log N)^(1+ε)`, the dyadic block terms sum. -/
theorem summable_blocks_of_log_bound
    (C ε : ℝ) (hε : 0 < ε) (hC : 0 ≤ C) (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (h : ∀ N : ℕ, N₀ ≤ N → (rothNumberNat N : ℝ) ≤ C * N / (Real.log N) ^ (1 + ε)) :
    Summable (fun j : ℕ => (rothNumberNat (2 ^ j) : ℝ) / 2 ^ j) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := C / (Real.log 2) ^ (1 + ε) with hK
  have hKnn : 0 ≤ K := by
    apply div_nonneg hC
    exact le_of_lt (Real.rpow_pos_of_pos hlog2 _)
  -- the comparison series
  have hp : Summable (fun j : ℕ => K * (1 / (j : ℝ) ^ (1 + ε))) :=
    (Real.summable_one_div_nat_rpow.mpr (by linarith)).mul_left K
  -- shift past the first N₀ indices, where the bound has nothing to say
  rw [← summable_nat_add_iff N₀]
  refine Summable.of_nonneg_of_le (fun j => by positivity) ?_ ((summable_nat_add_iff N₀).mpr hp)
  intro j
  set n : ℕ := j + N₀ with hn
  have h2n : (N₀ : ℕ) ≤ 2 ^ n := le_trans (Nat.le_of_lt (Nat.lt_two_pow_self)) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hbound := h (2 ^ n) h2n
  have hlogpow : Real.log ((2 : ℕ) ^ n : ℕ) = n * Real.log 2 := by
    push_cast
    rw [Real.log_pow]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 1 ≤ n := by omega
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hlrpow : (0 : ℝ) < (Real.log 2) ^ (1 + ε) := Real.rpow_pos_of_pos hlog2 _
  have hnrpow : (0 : ℝ) < (n : ℝ) ^ (1 + ε) := Real.rpow_pos_of_pos hnpos _
  have hsplit : ((n : ℝ) * Real.log 2) ^ (1 + ε)
      = (n : ℝ) ^ (1 + ε) * (Real.log 2) ^ (1 + ε) :=
    Real.mul_rpow (le_of_lt hnpos) (le_of_lt hlog2)
  calc (rothNumberNat (2 ^ n) : ℝ) / 2 ^ n
      ≤ (C * ((2:ℕ) ^ n : ℕ) / (Real.log ((2:ℕ) ^ n : ℕ)) ^ (1 + ε)) / 2 ^ n := by
        gcongr
    _ = K * (1 / (n : ℝ) ^ (1 + ε)) := by
        rw [hlogpow]
        push_cast
        rw [hsplit, hK]
        field_simp
