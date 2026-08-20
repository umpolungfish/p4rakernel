-- Imscribing/Millennium/Erdos/CollatzDepthSplit.lean
--
-- The depth-k residue split for the shortcut Collatz map, with the odd-step
-- count as the graded coordinate.
--
-- For r mod 2^k, the k-fold iterate is affine in t:
--     col^[k] (2^k * t + r) = 3 ^ oddSteps r k * t + col^[k] r
-- so the class contracts exactly when 3 ^ oddSteps r k < 2 ^ k.  The coordinate
-- is j/k against log 2 / log 3 = 0.630930, and the class r = 2^k - 1 takes an
-- odd step every time, giving ratio (3/2)^k at every depth.  That is the bound
-- on the method: a fixed-depth split leaves the all-odd class standing, at every
-- k, and the next rung is a criterion that reads the class rather than the depth.

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace CollatzDepthSplit

/-- Shortcut Collatz map: `n/2` on evens, `(3n+1)/2` on odds. -/
def col (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- Number of odd steps taken in the first `k` steps from `r`. -/
def oddSteps : ℕ → ℕ → ℕ
  | _, 0     => 0
  | r, (k+1) => (if r % 2 = 0 then 0 else 1) + oddSteps (col r) k

/-- A residue class contracts when its multiplier loses to its divisor. -/
def Contracts (k r : ℕ) : Prop := 3 ^ oddSteps r k < 2 ^ k

instance (k r : ℕ) : Decidable (Contracts k r) := by unfold Contracts; infer_instance

/-! ## The shift theorem: the iterate is affine on each class -/

theorem col_shift : ∀ (k t r : ℕ),
    col^[k] (2 ^ k * t + r) = 3 ^ oddSteps r k * t + col^[k] r := by
  intro k
  induction k with
  | zero => intro t r; simp [oddSteps]
  | succ k ih =>
    intro t r
    have hp : (2:ℕ) ^ (k+1) * t = 2 * (2 ^ k * t) := by ring
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    rcases Nat.even_or_odd r with h | h
    · obtain ⟨m, hm⟩ := h
      have hr2 : r % 2 = 0 := by omega
      have hstep : col (2 ^ (k+1) * t + r) = 2 ^ k * t + col r := by
        have hpar : (2 ^ (k+1) * t + r) % 2 = 0 := by rw [hp]; omega
        unfold col
        rw [if_pos hpar, if_pos hr2, hp]
        omega
      rw [hstep, ih t (col r)]
      rw [oddSteps, if_pos hr2, Nat.zero_add]
    · obtain ⟨m, hm⟩ := h
      have hr2 : r % 2 = 1 := by omega
      have hstep : col (2 ^ (k+1) * t + r) = 2 ^ k * (3 * t) + col r := by
        have hpar0 : ¬ ((2 ^ (k+1) * t + r) % 2 = 0) := by rw [hp]; omega
        have hr0 : ¬ (r % 2 = 0) := by omega
        unfold col
        rw [if_neg hpar0, if_neg hr0]
        have h3 : 3 * (2 ^ (k+1) * t + r) + 1 = 2 * (2 ^ k * (3 * t)) + (3 * r + 1) := by
          rw [hp]; ring
        rw [h3]; omega
      rw [hstep, ih (3 * t) (col r)]
      rw [oddSteps, if_neg (by omega : ¬ r % 2 = 0)]
      ring

/-! ## Contraction from the coordinate -/

/-- A class with gap `m` below `2^k` contracts for every `t ≥ 1` once its
    constant `col^[k] r` sits within `m` of `r`. -/
theorem col_lt_of_gap {k r m : ℕ} (hm : 3 ^ oddSteps r k + m = 2 ^ k)
    (hc : col^[k] r < r + m) :
    ∀ t, 1 ≤ t → col^[k] (2 ^ k * t + r) < 2 ^ k * t + r := by
  intro t ht
  rw [col_shift]
  have hmt : m * 1 ≤ m * t := Nat.mul_le_mul_left m ht
  have hsplit : 2 ^ k * t = 3 ^ oddSteps r k * t + m * t := by
    rw [← hm]; ring
  rw [hsplit]
  omega

/-! ## The all-odd class survives at every depth -/

theorem col_pred_pow (i m : ℕ) :
    col (3 ^ i * 2 ^ (m+1) - 1) = 3 ^ (i+1) * 2 ^ m - 1 := by
  have hM : 3 ^ i * 2 ^ (m+1) = 2 * (3 ^ i * 2 ^ m) := by ring
  have hpos : 1 ≤ 3 ^ i * 2 ^ m := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hnext : 3 ^ (i+1) * 2 ^ m = 3 * (3 ^ i * 2 ^ m) := by ring
  have hodd : ¬ ((3 ^ i * 2 ^ (m+1) - 1) % 2 = 0) := by rw [hM]; omega
  unfold col
  rw [if_neg hodd, hM, hnext]
  omega

theorem oddSteps_all_ones : ∀ (k i : ℕ), oddSteps (3 ^ i * 2 ^ k - 1) k = k := by
  intro k
  induction k with
  | zero => intro i; simp [oddSteps]
  | succ k ih =>
    intro i
    have hM : 3 ^ i * 2 ^ (k+1) = 2 * (3 ^ i * 2 ^ k) := by ring
    have hpos : 1 ≤ 3 ^ i * 2 ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hodd : ¬ ((3 ^ i * 2 ^ (k+1) - 1) % 2 = 0) := by rw [hM]; omega
    rw [oddSteps, if_neg hodd, col_pred_pow, ih (i+1)]
    omega

/-- The class `2^k - 1` takes an odd step at every one of the `k` steps. -/
theorem oddSteps_pred_two_pow (k : ℕ) : oddSteps (2 ^ k - 1) k = k := by
  have h := oddSteps_all_ones k 0
  simpa using h

/-- No depth closes the all-odd class: at every `k ≥ 1` the residue `2^k - 1`
    carries multiplier `3^k` against divisor `2^k`. -/
theorem not_contracts_pred_two_pow {k : ℕ} (hk : 1 ≤ k) : ¬ Contracts k (2 ^ k - 1) := by
  unfold Contracts
  rw [oddSteps_pred_two_pow]
  have h : (2:ℕ) ^ k < 3 ^ k := Nat.pow_lt_pow_left (by norm_num) (by omega)
  omega

/-! ## The depth-4, -5 and -6 classes, computed -/

theorem col4_16t3 (t : ℕ) : col^[4] (16 * t + 3) = 9 * t + 2 := by
  have h : (16:ℕ) = 2 ^ 4 := by norm_num
  rw [h, col_shift]
  norm_num [show oddSteps 3 4 = 2 by decide, show col^[4] 3 = 2 by decide]

theorem col4_16t3_contracts (t : ℕ) : col^[4] (16 * t + 3) < 16 * t + 3 := by
  rw [col4_16t3]; omega

theorem col4_16t7 (t : ℕ) : col^[4] (16 * t + 7) = 27 * t + 13 := by
  have h : (16:ℕ) = 2 ^ 4 := by norm_num
  rw [h, col_shift]
  norm_num [show oddSteps 7 4 = 3 by decide, show col^[4] 7 = 13 by decide]

/-- The `7 (mod 16)` class grows at depth four, for every `t`. -/
theorem col4_16t7_grows (t : ℕ) : 16 * t + 7 < col^[4] (16 * t + 7) := by
  rw [col4_16t7]; omega

theorem col5_32s15 (s : ℕ) : col^[5] (32 * s + 15) = 81 * s + 40 := by
  have h : (32:ℕ) = 2 ^ 5 := by norm_num
  rw [h, col_shift]
  norm_num [show oddSteps 15 5 = 4 by decide, show col^[5] 15 = 40 by decide]

theorem col5_32s15_grows (s : ℕ) : 32 * s + 15 < col^[5] (32 * s + 15) := by
  rw [col5_32s15]; omega

theorem col5_32s31 (s : ℕ) : col^[5] (32 * s + 31) = 243 * s + 242 := by
  have h : (32:ℕ) = 2 ^ 5 := by norm_num
  rw [h, col_shift]
  norm_num [show oddSteps 31 5 = 5 by decide, show col^[5] 31 = 242 by decide]

/-- Step six splits on the parity of `s`, because `243 * s + 242 ≡ s (mod 2)`.
    The even half. -/
theorem col6_64u31 (u : ℕ) : col^[6] (64 * u + 31) = 243 * u + 121 := by
  have h : (64:ℕ) = 2 ^ 6 := by norm_num
  rw [h, col_shift]
  norm_num [show oddSteps 31 6 = 5 by decide, show col^[6] 31 = 121 by decide]

/-- The odd half: a sixth odd step, not a halving. -/
theorem col6_64u63 (u : ℕ) : col^[6] (64 * u + 63) = 729 * u + 728 := by
  have h : (64:ℕ) = 2 ^ 6 := by norm_num
  rw [h, col_shift]
  norm_num [show oddSteps 63 6 = 6 by decide, show col^[6] 63 = 728 by decide]

theorem col6_64u31_grows (u : ℕ) : 64 * u + 31 < col^[6] (64 * u + 31) := by
  rw [col6_64u31]; omega

theorem col6_64u63_grows (u : ℕ) : 64 * u + 63 < col^[6] (64 * u + 63) := by
  rw [col6_64u63]; omega

/-! ## The census at each depth -/

/-- Odd residues mod 16 that survive depth four. -/
theorem survivors_mod_16 :
    ((List.range 16).filter (fun r => decide (r % 2 = 1) && decide (2 ^ 4 ≤ 3 ^ oddSteps r 4)))
      = [7, 9, 11, 15] := by decide

/-- Odd residues mod 32 that survive depth five. -/
theorem survivors_mod_32 :
    ((List.range 32).filter (fun r => decide (r % 2 = 1) && decide (2 ^ 5 ≤ 3 ^ oddSteps r 5)))
      = [7, 9, 15, 27, 31] := by decide

end CollatzDepthSplit
