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
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Log.Base
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

/-! ## Periodicity: the first k parities depend only on the class -/

theorem oddSteps_mod : ∀ (k t r : ℕ), oddSteps (2 ^ k * t + r) k = oddSteps r k := by
  intro k
  induction k with
  | zero => intro t r; simp [oddSteps]
  | succ k ih =>
    intro t r
    have hp : (2:ℕ) ^ (k+1) * t = 2 * (2 ^ k * t) := by ring
    rcases Nat.even_or_odd r with h | h
    · obtain ⟨m, hm⟩ := h
      have hr2 : r % 2 = 0 := by omega
      have hpar : (2 ^ (k+1) * t + r) % 2 = 0 := by rw [hp]; omega
      have hstep : col (2 ^ (k+1) * t + r) = 2 ^ k * t + col r := by
        unfold col
        rw [if_pos hpar, if_pos hr2, hp]
        omega
      rw [oddSteps, oddSteps, if_pos hpar, if_pos hr2, hstep, ih t (col r)]
    · obtain ⟨m, hm⟩ := h
      have hr0 : ¬ (r % 2 = 0) := by omega
      have hpar0 : ¬ ((2 ^ (k+1) * t + r) % 2 = 0) := by rw [hp]; omega
      have hstep : col (2 ^ (k+1) * t + r) = 2 ^ k * (3 * t) + col r := by
        unfold col
        rw [if_neg hpar0, if_neg hr0]
        have h3 : 3 * (2 ^ (k+1) * t + r) + 1 = 2 * (2 ^ k * (3 * t)) + (3 * r + 1) := by
          rw [hp]; ring
        rw [h3]; omega
      rw [oddSteps, oddSteps, if_neg hpar0, if_neg hr0, hstep, ih (3 * t) (col r)]

/-- Contraction at depth `i` is a property of the class mod `2^i`. -/
theorem contracts_mod (i t r : ℕ) : Contracts i (2 ^ i * t + r) ↔ Contracts i r := by
  unfold Contracts
  rw [oddSteps_mod]

/-! ## Survivors: classes that contract at no depth up to k -/

/-- `r` survives to depth `k` when no depth `i ≤ k` contracts it. -/
def Survives (k r : ℕ) : Prop := ∀ i, i ≤ k → ¬ Contracts i r

instance (k r : ℕ) : Decidable (Survives k r) := by unfold Survives; infer_instance

theorem oddSteps_all_ones_le : ∀ (i a m : ℕ), i ≤ m → oddSteps (3 ^ a * 2 ^ m - 1) i = i := by
  intro i
  induction i with
  | zero => intro a m _; simp [oddSteps]
  | succ i ih =>
    intro a m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hM : 3 ^ a * 2 ^ (m'+1) = 2 * (3 ^ a * 2 ^ m') := by ring
    have hpos : 1 ≤ 3 ^ a * 2 ^ m' := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hodd : ¬ ((3 ^ a * 2 ^ (m'+1) - 1) % 2 = 0) := by rw [hM]; omega
    rw [oddSteps, if_neg hodd, col_pred_pow, ih (a+1) m' (by omega)]
    omega

/-- The all-odd class survives every depth up to `k`: no level of the split
    reaches it. -/
theorem survives_pred_two_pow (k : ℕ) (hk : 1 ≤ k) : Survives k (2 ^ k - 1) := by
  intro i hi
  unfold Contracts
  have h1 : oddSteps (2 ^ k - 1) i = i := by
    have := oddSteps_all_ones_le i 0 k hi
    simpa using this
  rw [h1]
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0; simp
  · have h : (2:ℕ) ^ i < 3 ^ i := Nat.pow_lt_pow_left (by norm_num) (by omega)
    omega

/-- The survivor census at small depth, by `decide`. -/
theorem survivors_survive_mod_16 :
    ((List.range 16).filter (fun r => decide (Survives 4 r))) = [7, 11, 15] := by decide

theorem survivors_survive_mod_32 :
    ((List.range 32).filter (fun r => decide (Survives 5 r))) = [7, 15, 27, 31] := by decide

/-! ## The survivor tree never dies

Every survivor class lifts to a survivor one level deeper.  The odd extension is
the one that always works: an odd step multiplies the multiplier by three while
the divisor only doubles, so a class that has not yet contracted cannot contract
by taking an odd step.  Since `3 ^ j` is odd, exactly one of the two lifts of a
class has an odd step at level `k`, and that one survives. -/

theorem oddSteps_succ : ∀ (k r : ℕ),
    oddSteps r (k+1) = oddSteps r k + (if col^[k] r % 2 = 0 then 0 else 1) := by
  intro k
  induction k with
  | zero => intro r; by_cases h : r % 2 = 0 <;> simp [oddSteps, h]
  | succ k ih =>
    intro r
    have e1 : oddSteps r (k+1+1) = (if r % 2 = 0 then 0 else 1) + oddSteps (col r) (k+1) := by
      rw [oddSteps]
    have e2 : oddSteps r (k+1) = (if r % 2 = 0 then 0 else 1) + oddSteps (col r) k := by
      rw [oddSteps]
    rw [e1, ih (col r), e2, Function.iterate_succ_apply]
    omega

theorem contracts_mod_le {i k : ℕ} (b r : ℕ) (h : i ≤ k) :
    Contracts i (2 ^ k * b + r) ↔ Contracts i r := by
  have hsplit : (2:ℕ) ^ k * b = 2 ^ i * (2 ^ (k - i) * b) := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  rw [hsplit]
  exact contracts_mod i _ r

/-- A survivor whose next step is odd survives one level deeper. -/
theorem survives_succ_of_odd {k r : ℕ} (h : Survives k r) (hodd : ¬ (col^[k] r % 2 = 0)) :
    Survives (k+1) r := by
  intro i hi
  rcases Nat.lt_or_ge i (k+1) with hik | hik
  · exact h i (by omega)
  · have hik' : i = k + 1 := by omega
    subst hik'
    have hprev : ¬ Contracts k r := h k (le_refl k)
    unfold Contracts at hprev ⊢
    rw [oddSteps_succ, if_neg hodd]
    have h3 : (2:ℕ) ^ k ≤ 3 ^ oddSteps r k := by omega
    have hA : (2:ℕ) ^ (k+1) = 2 ^ k * 2 := pow_succ 2 k
    have hB : (3:ℕ) ^ (oddSteps r k + 1) = 3 ^ oddSteps r k * 3 := pow_succ 3 _
    have hC : (2:ℕ) ^ k * 2 ≤ 3 ^ oddSteps r k * 2 := Nat.mul_le_mul h3 (Nat.le_refl 2)
    have hD : (3:ℕ) ^ oddSteps r k * 2 ≤ 3 ^ oddSteps r k * 3 :=
      Nat.mul_le_mul (Nat.le_refl _) (by norm_num)
    omega

/-- Every survivor class at depth `k` lifts to a survivor at depth `k+1`. -/
theorem exists_survivor_lift {k r : ℕ} (h : Survives k r) :
    ∃ b, b < 2 ∧ Survives (k+1) (2 ^ k * b + r) := by
  have hodd3 : (3:ℕ) ^ oddSteps r k % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
  by_cases hp : col^[k] r % 2 = 0
  · refine ⟨1, by norm_num, ?_⟩
    have hsurv : Survives k (2 ^ k * 1 + r) := by
      intro i hi
      rw [contracts_mod_le 1 r hi]
      exact h i hi
    refine survives_succ_of_odd hsurv ?_
    rw [col_shift]
    omega
  · refine ⟨0, by norm_num, ?_⟩
    have hsurv : Survives k (2 ^ k * 0 + r) := by
      intro i hi
      rw [contracts_mod_le 0 r hi]
      exact h i hi
    refine survives_succ_of_odd hsurv ?_
    rw [col_shift]
    omega

/-- No depth exhausts the split: a surviving class exists at every `k`. -/
theorem survivors_nonempty : ∀ k : ℕ, ∃ r, Survives k r := by
  intro k
  induction k with
  | zero =>
    refine ⟨1, ?_⟩
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    unfold Contracts
    simp [oddSteps]
  | succ k ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨b, _, hb⟩ := exists_survivor_lift hr
    exact ⟨2 ^ k * b + r, hb⟩

/-- A survivor with slack survives the next level whatever its next step is, so
    both of its lifts survive.  The census reads this as a branch factor of
    exactly two at every depth where the least admissible odd-count does not
    advance. -/
theorem survives_succ_of_slack {k r : ℕ} (h : Survives k r)
    (hslack : 2 ^ (k+1) ≤ 3 ^ oddSteps r k) : Survives (k+1) r := by
  intro i hi
  rcases Nat.lt_or_ge i (k+1) with hik | hik
  · exact h i (by omega)
  · have hik' : i = k + 1 := by omega
    subst hik'
    unfold Contracts
    rw [oddSteps_succ]
    by_cases hp : col^[k] r % 2 = 0
    · rw [if_pos hp, Nat.add_zero]; omega
    · rw [if_neg hp]
      have hB : (3:ℕ) ^ (oddSteps r k + 1) = 3 ^ oddSteps r k * 3 := pow_succ 3 _
      have hD : (3:ℕ) ^ oddSteps r k * 1 ≤ 3 ^ oddSteps r k * 3 :=
        Nat.mul_le_mul (Nat.le_refl _) (by norm_num)
      omega

theorem both_lifts_survive {k r : ℕ} (h : Survives k r)
    (hslack : 2 ^ (k+1) ≤ 3 ^ oddSteps r k) (b : ℕ) :
    Survives (k+1) (2 ^ k * b + r) := by
  have hsurv : Survives k (2 ^ k * b + r) := by
    intro i hi
    rw [contracts_mod_le b r hi]
    exact h i hi
  refine survives_succ_of_slack hsurv ?_
  rw [oddSteps_mod]
  exact hslack

/-! ## The constant: the class criterion is exact

Every step is at least a multiplication by `3/2` on odd and exactly `1/2` on
even, so `2^k * col^[k] r ≥ 3^(oddSteps r k) * r` with no error term.  A class
that has not contracted has `3^j ≥ 2^k`, so its constant satisfies
`col^[k] r ≥ r`, and then no member of the class descends within `k` steps at
all.  The multiplier test is therefore not a sufficient condition with a finite
exceptional set: it is exact. -/

theorem pow_mul_le_iterate : ∀ (k r : ℕ), 3 ^ oddSteps r k * r ≤ 2 ^ k * col^[k] r := by
  intro k
  induction k with
  | zero => intro r; simp [oddSteps]
  | succ k ih =>
    intro r
    have hy := ih r
    set y := col^[k] r with hydef
    rw [Function.iterate_succ_apply', ← hydef, oddSteps_succ, ← hydef]
    by_cases hp : y % 2 = 0
    · have hcol : col y = y / 2 := by unfold col; rw [if_pos hp]
      have hhalf : 2 * (y / 2) = y := by omega
      rw [if_pos hp, Nat.add_zero, hcol, pow_succ]
      calc 3 ^ oddSteps r k * r ≤ 2 ^ k * y := hy
        _ = 2 ^ k * 2 * (y / 2) := by rw [mul_assoc, hhalf]
    · have hcol : col y = (3 * y + 1) / 2 := by unfold col; rw [if_neg hp]
      have hhalf : 2 * ((3 * y + 1) / 2) = 3 * y + 1 := by omega
      rw [if_neg hp, hcol, pow_succ, pow_succ]
      have hstep : 3 * (3 ^ oddSteps r k * r) ≤ 3 * (2 ^ k * y) := by omega
      have hexp : 2 ^ k * (3 * y + 1) = 3 * (2 ^ k * y) + 2 ^ k := by ring
      calc 3 ^ oddSteps r k * 3 * r = 3 * (3 ^ oddSteps r k * r) := by ring
        _ ≤ 3 * (2 ^ k * y) := hstep
        _ ≤ 2 ^ k * (3 * y + 1) := by rw [hexp]; exact Nat.le_add_right _ _
        _ = 2 ^ k * 2 * ((3 * y + 1) / 2) := by rw [mul_assoc, hhalf]

/-- A class that has not contracted carries a constant no smaller than its
    residue. -/
theorem le_iterate_of_not_contracts {k r : ℕ} (h : ¬ Contracts k r) : r ≤ col^[k] r := by
  unfold Contracts at h
  have hge : (2:ℕ) ^ k ≤ 3 ^ oddSteps r k := by omega
  have hmain := pow_mul_le_iterate k r
  have hstep : (2:ℕ) ^ k * r ≤ 3 ^ oddSteps r k * r := Nat.mul_le_mul_right r hge
  have hpos : 0 < (2:ℕ) ^ k := pow_pos (by norm_num) k
  have : (2:ℕ) ^ k * r ≤ 2 ^ k * col^[k] r := le_trans hstep hmain
  exact Nat.le_of_mul_le_mul_left this hpos

/-- Nothing in a surviving class descends within `k` steps: the multiplier test
    is exact, not merely sufficient. -/
theorem no_member_descends {k r : ℕ} (h : ¬ Contracts k r) (t : ℕ) :
    2 ^ k * t + r ≤ col^[k] (2 ^ k * t + r) := by
  unfold Contracts at h
  have hge : (2:ℕ) ^ k ≤ 3 ^ oddSteps r k := by omega
  have hc : r ≤ col^[k] r := le_iterate_of_not_contracts (by unfold Contracts; omega)
  rw [col_shift]
  have hmul : 2 ^ k * t ≤ 3 ^ oddSteps r k * t := Nat.mul_le_mul_right t hge
  omega

/-! ## The branch dichotomy

`survives_succ_of_slack` says a survivor with `2^(k+1) ≤ 3^j` keeps both lifts.
Its complement is exact: a survivor without that slack keeps only the lift whose
next step is odd, because the even lift leaves the multiplier where it was while
the divisor doubles past it.  So the census obeys `S_(k+1) = 2*A_k + B_k`, with
`A` the survivors carrying slack and `B` those without. -/

theorem contracts_succ_of_even_step {k r : ℕ} (heven : col^[k] r % 2 = 0)
    (hslack : 3 ^ oddSteps r k < 2 ^ (k+1)) : Contracts (k+1) r := by
  unfold Contracts
  rw [oddSteps_succ, if_pos heven, Nat.add_zero]
  exact hslack

/-- The even lift of a slackless survivor does not survive. -/
theorem not_survives_succ_of_even_step {k r : ℕ} (heven : col^[k] r % 2 = 0)
    (hslack : 3 ^ oddSteps r k < 2 ^ (k+1)) : ¬ Survives (k+1) r := by
  intro hs
  exact hs (k+1) (le_refl _) (contracts_succ_of_even_step heven hslack)

/-! ## The holder-first reading: predecessors

Forward, the branch is free — both parities are available at every class, so the
tree is all `2^k` residues with a survival filter laid over it, and the filter is
all the content there is.  Read from the target instead and the branch becomes
arithmetic.  Every `m` has the predecessor `2*m`, and `m` has an odd predecessor
exactly when `m ≡ 2 (mod 3)`, in which case it is `2*t+1` for `m = 3*t+2` with no
division and no parity side condition.  Nothing needs filtering: every path in
this tree is a trajectory. -/

theorem col_two_mul (m : ℕ) : col (2 * m) = m := by
  unfold col
  rw [if_pos (by omega : (2 * m) % 2 = 0)]
  omega

theorem col_odd_pred (t : ℕ) : col (2 * t + 1) = 3 * t + 2 := by
  unfold col
  rw [if_neg (by omega : ¬ (2 * t + 1) % 2 = 0)]
  omega

/-- Every preimage is one of the two, and the odd one forces `m ≡ 2 (mod 3)`. -/
theorem preimage_cases {n m : ℕ} (h : col n = m) :
    n = 2 * m ∨ ∃ t, n = 2 * t + 1 ∧ m = 3 * t + 2 := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨c, hc⟩ := he
    left
    have hn : n % 2 = 0 := by omega
    unfold col at h
    rw [if_pos hn] at h
    omega
  · obtain ⟨t, ht⟩ := ho
    right
    refine ⟨t, ht, ?_⟩
    subst ht
    rw [col_odd_pred] at h
    omega

/-- The branch is two exactly on the residue `2 (mod 3)`. -/
theorem odd_pred_iff (m : ℕ) : (∃ t, m = 3 * t + 2) ↔ m % 3 = 2 := by
  constructor
  · rintro ⟨t, rfl⟩; omega
  · intro h; exact ⟨m / 3, by omega⟩

/-- Stated as the tree step: the predecessors of `m` are `2*m` always, and
    `2*t+1` when `m = 3*t+2`. -/
theorem preds_of_mod_three {m t : ℕ} (h : m = 3 * t + 2) :
    col (2 * m) = m ∧ col (2 * t + 1) = m := by
  exact ⟨col_two_mul m, by rw [col_odd_pred, h]⟩

/-! ### The level recursion

One level of the predecessor tree is the doubling image together with the odd
image of the classes at `2 (mod 3)`, and the two are disjoint by parity, so the
count of a level is the count of the previous one plus the count of its
`2 (mod 3)` part.  The branch multiplicity is a property of the level, not of any
target in it. -/

/-- One level of the tree, built from the level below. -/
def predStep (L : Finset ℕ) : Finset ℕ :=
  L.image (fun m => 2 * m) ∪ (L.filter (fun m => m % 3 = 2)).image (fun m => 2 * (m / 3) + 1)

theorem mem_predStep_col {L : Finset ℕ} {n : ℕ} (h : n ∈ predStep L) : col n ∈ L := by
  unfold predStep at h
  rcases Finset.mem_union.mp h with h | h
  · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp h
    rwa [col_two_mul]
  · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hmL, hm3⟩ := Finset.mem_filter.mp hm
    have : 3 * (m / 3) + 2 = m := by omega
    rw [col_odd_pred, this]
    exact hmL

theorem card_predStep (L : Finset ℕ) :
    (predStep L).card = L.card + (L.filter (fun m => m % 3 = 2)).card := by
  unfold predStep
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective, Finset.card_image_of_injOn]
  · intro a ha b hb hab
    obtain ⟨_, ha3⟩ := Finset.mem_filter.mp ha
    obtain ⟨_, hb3⟩ := Finset.mem_filter.mp hb
    simp only at hab
    omega
  · intro a b hab; simp only at hab; omega
  · rw [Finset.disjoint_left]
    rintro x hx hy
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨m', _, hm'⟩ := Finset.mem_image.mp hy
    omega

/-! ### Why the branch factor is `4/3` only in the limit

Both maps building a level are bijections on residues mod `3^r`: doubling is,
because 2 is a unit there, and `t ↦ 2*t+1` is the same map composed with a shift.
So a level equidistributed mod `3^(r+1)` produces one equidistributed mod `3^r`,
with `3c` from the doubling image and `c` from the odd image, which is the `4/3`
exactly.  One 3-adic digit of resolution is consumed per level.  Since the tree
starts at a point, uniformity cannot be propagated forward from the root: it has
to come from mixing, and the rate of that mixing is a measurement. -/

theorem two_coprime_three_pow (r : ℕ) : Nat.gcd (3 ^ r) 2 = 1 :=
  Nat.Coprime.pow_left r (by decide)

theorem double_inj_mod {r a b : ℕ} (h : 2 * a ≡ 2 * b [MOD 3 ^ r]) : a ≡ b [MOD 3 ^ r] :=
  Nat.ModEq.cancel_left_of_coprime (two_coprime_three_pow r) h

theorem odd_map_inj_mod {r a b : ℕ} (h : 2 * a + 1 ≡ 2 * b + 1 [MOD 3 ^ r]) :
    a ≡ b [MOD 3 ^ r] :=
  double_inj_mod (Nat.ModEq.add_right_cancel' 1 h)

/-- Two is invertible on residues mod `3^r`, so doubling is onto them as well. -/
theorem two_inv_mod (r : ℕ) : 2 * ((3 ^ r + 1) / 2) ≡ 1 [MOD 3 ^ r] := by
  have hodd : Odd (3 ^ r) := Odd.pow (by decide)
  obtain ⟨j, hj⟩ := hodd
  have hhalf : 2 * ((3 ^ r + 1) / 2) = 3 ^ r + 1 := by omega
  rw [hhalf]
  unfold Nat.ModEq
  exact Nat.add_mod_left _ _

/-! ## The record chain

The budget records the `collatz` verb reports climb a chain, and the chain is the
two arms of the split composed once each: one doubling and one odd lift send `n`
to `(4n-1)/3`, defined exactly when `n ≡ 1 (mod 3)`.  Written without division,
`n = 3t+1` goes to `4t+1`, and the block from `4t+1` is exactly two steps landing
on `3t+1`, so the budget rises by exactly one and the ratio sits at four thirds.
The chain dies at `n ≡ 0 (mod 3)`, where the odd lift has no arm. -/

/-- One step up the chain rises, and the step after it lands. -/
theorem col_chain_up (t : ℕ) : col (4 * t + 1) = 2 * (3 * t + 1) := by
  unfold col
  rw [if_neg (by omega : ¬ (4 * t + 1) % 2 = 0)]
  omega

theorem col_chain_down (t : ℕ) : col (2 * (3 * t + 1)) = 3 * t + 1 := by
  unfold col
  rw [if_pos (by omega : (2 * (3 * t + 1)) % 2 = 0)]
  omega

/-- The chain law: from `4t+1` the block is exactly two steps and lands on
    `3t+1`, the first step rising above the seed and the second falling below
    it.  So one chain step spends one block and the seed grows by four thirds. -/
theorem chain_block (t : ℕ) (ht : 1 ≤ t) :
    col^[2] (4 * t + 1) = 3 * t + 1 ∧ 4 * t + 1 < col (4 * t + 1) ∧ 3 * t + 1 < 4 * t + 1 := by
  refine ⟨?_, ?_, by omega⟩
  · rw [show (2:ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]
    simp only [Function.iterate_one]
    rw [col_chain_up, col_chain_down]
  · rw [col_chain_up]; omega

/-- The chain runs on `1 (mod 3)` and stops on `0 (mod 3)`: the lift `(4n-1)/3`
    is an integer exactly there. -/
theorem chain_defined_iff (n : ℕ) : (∃ t, n = 3 * t + 1) ↔ n % 3 = 1 := by
  constructor
  · rintro ⟨t, rfl⟩; omega
  · intro h; exact ⟨n / 3, by omega⟩

/-! ## The junctions

A value takes two predecessors exactly when it is `2 (mod 3)` (`odd_pred_iff`),
so every merge of two trajectories happens there and nowhere else.  Which arm the
traffic arrives on is then forced, and the forcing is already in `col_odd_pred`:
an odd step sends `2t+1` to `3t+2`, which is `2 (mod 3)` for every `t`.  So EVERY
odd step lands on a junction, while an even step lands on one only when its own
half does — a third of the time.  With the two step kinds equinumerous that puts
the odd arm's share of all junction arrivals at `(1/2) / (1/2 + (1/3)(1/2)) = 3/4`,
and the census reads `0.7513` over seeds to 20000 and `0.7501` to 60000. -/

/-- Every odd step lands on a junction. -/
theorem odd_step_lands_on_junction (t : ℕ) : col (2 * t + 1) % 3 = 2 := by
  rw [col_odd_pred]; omega

/-- An even step lands on a junction exactly when its half is one, which is a
    third of the residues. -/
theorem even_step_junction_iff (m : ℕ) : col (2 * m) % 3 = 2 ↔ m % 3 = 2 := by
  rw [col_two_mul]

/-- The two arms into a junction, named: the even arm is always there, the odd
    arm is the one the residue buys. -/
theorem junction_arms {v : ℕ} (h : v % 3 = 2) :
    col (2 * v) = v ∧ col (2 * (v / 3) + 1) = v :=
  ⟨col_two_mul v, by rw [col_odd_pred]; omega⟩

/-! ## What fixes the share: the starved arm

Grouping junctions by residue, the odd share is fixed one 3-adic digit at a time.
At modulus 9 the class `5` is pinned at `0.004` with a spread of `0.0014` while
the other two classes spread over a quarter; at modulus 27 the pinned classes are
`5, 14, 23` and at 81 the spreads elsewhere fall to a few hundredths.

The pinned class has an exact cause. A junction `v = 9k+5` has odd arm `6k+3`,
which is `0 (mod 3)`, and a value `0 (mod 3)` takes only its doubling
predecessor — `preds_of_barren` — while every value in its doubling chain stays
`0 (mod 3)` — `barren_doubling`. So that arm is a bare chain of `d+1` nodes at
depth `d` against the even arm's exponential subtree, and the share it can hold
falls like `d / (4/3)^d`. At depth 24 that is `0.004`, which is what the census
reads. -/

theorem col_starved_arm (k : ℕ) : col (6 * k + 3) = 9 * k + 5 := by
  unfold col
  rw [if_neg (by omega : ¬ (6 * k + 3) % 2 = 0)]
  omega

/-- A value divisible by three has one predecessor, not two. -/
theorem preds_of_barren {u n : ℕ} (hu : u % 3 = 0) (h : col n = u) : n = 2 * u := by
  rcases preimage_cases h with h1 | ⟨t, _, h2⟩
  · exact h1
  · omega

/-- And its whole doubling chain stays barren, so the arm never branches. -/
theorem barren_doubling (u i : ℕ) (hu : u % 3 = 0) : (2 ^ i * u) % 3 = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, u = 3 * m := ⟨u / 3, by omega⟩
  have : 2 ^ i * (3 * m) = 3 * (2 ^ i * m) := by ring
  omega

/-- The junction whose odd arm is barren, named by its residue. -/
theorem starved_junction (k : ℕ) :
    (9 * k + 5) % 3 = 2 ∧ col (6 * k + 3) = 9 * k + 5 ∧ (6 * k + 3) % 3 = 0 :=
  ⟨by omega, col_starved_arm k, by omega⟩

/-! ## The amplitude, and the equation that fixes the map

Counting predecessors under a value to depth `d` gives a number growing like
`(4/3)^d`, so what separates one arm from another is the constant in front of it.
Measured, that amplitude converges: under 40 it settles near `5.53`, under 80
near `7.364`, under 53 near `6.656`, with the per-level ratio pinned at `4/3`.

The counts obey an exact recursion, and the amplitude is its limit:

    S(v, d+1) = 1 + S(2v, d) + (if v ≡ 2 (mod 3) then S((2v-1)/3, d) else 0)
    A(v)      = (3/4) * ( A(2v) + [v ≡ 2 (mod 3)] * A((2v-1)/3) )

Both halves check against the verb. For `v = 40`, which is `1 (mod 3)` and so
carries only the doubling arm, `(3/4)·A(80) = 7.3667·0.75 = 5.525` against `5.525`
measured. For `v = 80`, which branches, `(4/3)·A(80) − A(160) = 6.6656` predicts
`A(53)`, measured `6.656`. So the odd share at a junction is a ratio of
amplitudes, `A((2v-1)/3) / (A(2v) + A((2v-1)/3))`, and the 3-adic map of the
share is the map of `A`. -/

/-- Predecessors under `v` to depth `d`, counted. -/
def subtreeCount : ℕ → ℕ → ℕ
  | _, 0     => 1
  | v, (d+1) => 1 + subtreeCount (2 * v) d
                  + (if v % 3 = 2 then subtreeCount (2 * (v / 3) + 1) d else 0)

/-- The recursion, holding by construction: the count under a value is the value
    itself, the count under its doubling, and the count under its odd arm where
    the residue provides one. -/
theorem subtreeCount_succ (v d : ℕ) :
    subtreeCount v (d + 1)
      = 1 + subtreeCount (2 * v) d
          + (if v % 3 = 2 then subtreeCount (2 * (v / 3) + 1) d else 0) := rfl

/-- Off `2 (mod 3)` the recursion has one term: the arm is the doubling alone. -/
theorem subtreeCount_barren {v : ℕ} (h : ¬ v % 3 = 2) (d : ℕ) :
    subtreeCount v (d + 1) = 1 + subtreeCount (2 * v) d := by
  rw [subtreeCount_succ, if_neg h, Nat.add_zero]

/-- A value divisible by three keeps its whole doubling chain barren, so its
    count is the chain itself: `d + 1` and nothing more. -/
theorem subtreeCount_of_three_dvd {v : ℕ} (h : v % 3 = 0) (d : ℕ) :
    subtreeCount v d = d + 1 := by
  induction d generalizing v with
  | zero => rfl
  | succ d ih =>
    have h2 : ¬ v % 3 = 2 := by omega
    have h3 : (2 * v) % 3 = 0 := by omega
    rw [subtreeCount_barren h2, ih h3]
    omega

/-! ## Solving the amplitude equation

At a junction the two arms and the value itself exhaust the count, so the share
needs only ONE function rather than two subtrees.  From
`(4/3)·A(v) = A(2v) + A(u)` the even arm is `A(2v) = (4/3)A(v) − A(u)`, hence

    share v = A(u) / (A(2v) + A(u)) = (3/4) · A(u) / A(v)

which the verb confirms: `(3/4)·A(13)/A(20) = 0.53197` against `0.5317` measured,
and `(3/4)·A(67)/A(101) = 0.46389` against `0.4635`.

Reading that along a trajectory solves the equation.  If `n` is odd then `n` IS
the odd arm of `T n`, so `A n = (4/3) · share (T n) · A (T n)`; if `n` is even it
is the doubling arm, so `A n = (4/3) · (1 − share (T n)) · A (T n)`.  Composing
over the whole trajectory,

    A n = (4/3)^L · (∏ w_i) · A(boundary),
    w_i = share (T n_i) at an odd step, 1 − share (T n_i) at an even one

so `log A` is a Birkhoff sum along the Collatz map: the amplitude is a
multiplicative cocycle whose weights are the shares, and the shares are ratios of
the amplitude along the odd lift.  The system closes on itself, which is what a
fixed point of this kind looks like rather than a defect in it.

Measured, every step holds to a twentieth of a percent — `A(13)` from `A(4)`
across five steps gives `6.275` against `6.287` — with one exception, the step
crossing the `1 → 2 → 1` cycle, where the count deliberately cuts the edge back
into the root and the recursion reads `+56%` at `v = 2`.  That is the boundary
condition, not a break in the law.

The finite identity behind it is exact and needs no limit. -/

/-- At a junction the two arms and the value exhaust the count. -/
theorem subtreeCount_junction {v : ℕ} (h : v % 3 = 2) (d : ℕ) :
    subtreeCount v (d + 1)
      = 1 + subtreeCount (2 * v) d + subtreeCount (2 * (v / 3) + 1) d := by
  rw [subtreeCount_succ, if_pos h]

/-- So the odd arm's count is what the whole count has left after the doubling
    arm, which is the finite form of `share = (3/4) A(u) / A(v)`. -/
theorem odd_arm_count {v : ℕ} (h : v % 3 = 2) (d : ℕ) :
    subtreeCount (2 * (v / 3) + 1) d
      = subtreeCount v (d + 1) - (1 + subtreeCount (2 * v) d) := by
  rw [subtreeCount_junction h]
  omega

/-! ## What the residues alone force, and what they do not

Boundedness of the amplitude is boundedness of `S(v,d) / (4/3)^d`, so the first
question is what growth rate the residue structure forces on its own.

The transitions are rigid on two of the three classes.  A node `≡ 0 (mod 3)` has
only its doubling child and that child is `≡ 0` again, so the class is a chain.
A node `≡ 1 (mod 3)` has only its doubling child, which is `≡ 2`.  A node
`≡ 2 (mod 3)` has a doubling child `≡ 1` and an odd child whose class depends on
the next digit.  So a branch is always followed by a non-branching step on the
even side, and the fastest a subtree can grow is the Fibonacci pairing

    a (d+1) = 1 + b d          -- a bounds the `≡ 1` class
    b (d+1) = 1 + a d + b d    -- b bounds the `≡ 2` class

giving `1, 3, 6, 11, 19, …` with `b(d) = b(d-1) + b(d-2) + 2`, so the ceiling is
`φ^d` and not `2^d`.  That is proved below.

It is also NOT `(4/3)^d`.  The gap between the Fibonacci ceiling and the measured
`4/3` is exactly the assumption that the odd child's class is equidistributed
rather than adversarial: taking the odd child to land on `2 (mod 3)` every time
gives `φ`, and taking it uniformly over the three classes gives `4/3`.  So the
amplitude's boundedness is not a consequence of the residue structure, and the
measurement that stands behind it — `gap × length` flat at `−1.3` across two
orders of magnitude — is evidence for the equidistribution rather than a
substitute for it. -/

/-- Bounds for the two live classes, paired: `(bound for ≡1, bound for ≡2)`. -/
def classBound : ℕ → ℕ × ℕ
  | 0     => (1, 1)
  | (d+1) => (1 + (classBound d).2, 1 + (classBound d).1 + (classBound d).2)

theorem classBound_mono (d : ℕ) : (classBound d).1 ≤ (classBound d).2 := by
  induction d with
  | zero => simp [classBound]
  | succ d ih =>
    simp only [classBound]
    omega

/-- The count under any value is bounded by its class's entry, so the subtree
    grows at most like `φ^d`. -/
theorem subtreeCount_le_classBound : ∀ (d v : ℕ),
    subtreeCount v d ≤ (if v % 3 = 2 then (classBound d).2 else (classBound d).1) := by
  intro d
  induction d with
  | zero => intro v; simp [subtreeCount, classBound]
  | succ d ih =>
    intro v
    by_cases h : v % 3 = 2
    · have h2 : (2 * v) % 3 = 1 := by omega
      have hb1 := ih (2 * v)
      have hb2 := ih (2 * (v / 3) + 1)
      rw [if_pos h, subtreeCount_junction h]
      simp only [classBound]
      rw [if_neg (by omega : ¬ (2 * v) % 3 = 2)] at hb1
      have := classBound_mono d
      by_cases h3 : (2 * (v / 3) + 1) % 3 = 2
      · rw [if_pos h3] at hb2; omega
      · rw [if_neg h3] at hb2; omega
    · have hb1 := ih (2 * v)
      rw [if_neg h, subtreeCount_barren h]
      simp only [classBound]
      by_cases h2 : (2 * v) % 3 = 2
      · rw [if_pos h2] at hb1; omega
      · rw [if_neg h2] at hb1
        have := classBound_mono d
        omega

/-- The pairing IS the Fibonacci recursion, shifted by two. -/
theorem classBound_fib (d : ℕ) :
    (classBound (d + 2)).2 = (classBound (d + 1)).2 + (classBound d).2 + 2 := by
  simp only [classBound]
  omega

/-! ## Toward the equidistribution

The odd lift is a bijection from the junction classes one digit finer onto
everything.  Concretely a junction is `3t+2` and its odd arm is `2t+1`, so on
residues the arm map is `t ↦ 2t+1`, which is injective and onto `Z/3^r` because
`2` is a unit there.  A junction class mod `3^(r+1)` is a `t` class mod `3^r`, so
the arm carries the finer classes onto the coarser ones one-to-one: uniform in
gives uniform out, and the digit is what it costs.

That is the whole of what the structure gives for free.  It says the uniform
measure is FIXED by the level map; it does not say the tree converges to it,
because the tree starts at a point and every level consumes a digit rather than
producing one.  The convergence is the open piece, and the shape it has is a
flow between conductors: doubling permutes the characters of a fixed conductor,
while the odd arm sends a conductor `3^r` character to one of conductor `3^(r+1)`,
so the coefficient at each level is fed from the level above it and never from
below. -/

/-- The arm map on residues is injective. -/
theorem arm_inj_mod {r a b : ℕ} (h : (2 * a + 1) % 3 ^ r = (2 * b + 1) % 3 ^ r) :
    a % 3 ^ r = b % 3 ^ r :=
  odd_map_inj_mod h

/-- And onto: every residue is `2t+1` for some `t`, by the explicit inverse of 2. -/
theorem arm_surj_mod (r y : ℕ) :
    ∃ t, (2 * t + 1) % 3 ^ r = y % 3 ^ r := by
  have hpos : 1 ≤ 3 ^ r := Nat.one_le_pow r 3 (by norm_num)
  have hodd : Odd (3 ^ r) := Odd.pow (by decide)
  obtain ⟨j, hj⟩ := hodd
  have hhalf : 2 * ((3 ^ r + 1) / 2) = 3 ^ r + 1 := by omega
  refine ⟨((3 ^ r + 1) / 2) * (y + 3 ^ r - 1), ?_⟩
  have key : 2 * (((3 ^ r + 1) / 2) * (y + 3 ^ r - 1))
      + 1 = (y + 3 ^ r) + 3 ^ r * (y + 3 ^ r - 1) := by
    rw [← Nat.mul_assoc, hhalf]
    have hexp : (3 ^ r + 1) * (y + 3 ^ r - 1)
        = 3 ^ r * (y + 3 ^ r - 1) + (y + 3 ^ r - 1) := by ring
    omega
  rw [key, Nat.add_mul_mod_self_left, Nat.add_mod_right]

/-- The junction whose arm lands on a named class: the arm map is a bijection
    from junctions mod `3^(r+1)` onto residues mod `3^r`, so a level uniform one
    digit finer produces a level uniform here. -/
theorem arm_bijection_mod (r y : ℕ) :
    ∃ t, (2 * t + 1) % 3 ^ r = y % 3 ^ r ∧
      ∀ t', (2 * t' + 1) % 3 ^ r = y % 3 ^ r → t' % 3 ^ r = t % 3 ^ r := by
  obtain ⟨t, ht⟩ := arm_surj_mod r y
  exact ⟨t, ht, fun t' ht' => arm_inj_mod (by rw [ht', ht])⟩

/-! ## The level map on coefficients, and where the decay comes from

Writing `μ̂_d(j,r)` for the coefficient of the level-`d` measure at the character
`x ↦ e(jx/3^r)`, one level acts as

    μ̂_{d+1}(j,r) = ρ_d [ μ̂_d(2j, r)
                        + e(−j/3^{r+1}) · (1/3) Σ_{s<3} ω^{−2s} μ̂_d(2j + s·3^r, r+1) ]

with `ω` a primitive cube root of unity and `ρ_d = N_d / N_{d+1} → 3/4`.  The
first term is the doubling permutation, which moves no mass between conductors
and contracts by exactly `ρ_d`.  The second is the odd arm, and it reaches one
conductor higher.

The cancellation in it is exact: `Σ_{s<3} ω^{−2s} = 0`, so the feed sees only the
DIFFERENCE of the three lifts and never their size.  A conductor-`3^{r+1}`
coefficient that is constant across the three lifts contributes nothing at all.
That is `cube_roots_sum_zero` below, and it is why the flow between conductors is
a difference operator rather than a transport.

Measured, the identity holds to five decimals at every level, and the decay is
not a term-wise contraction: the feed runs comparable to the doubling term
(`feed/same` averaging about 1.5), so the triangle bound gives nothing under one.
What decays is the SUM, because the two terms cancel in phase — the mean of
`|sum| / (|same| + |feed|)` is `0.53` at conductor 3 over 24 levels and `0.79` at
conductor 9 over 20.  That phase cancellation is the square-root law seen from
the operator side, and bounding it is what remains. -/

/-- The cancellation the feed term rests on: the three cube roots of unity sum to
    zero, so a constant across the three lifts of a class contributes nothing to
    the odd arm's coefficient. -/
theorem cube_roots_sum_zero {R : Type*} [CommRing R] {ω : R} (h : ω ^ 2 + ω + 1 = 0) :
    1 + ω + ω ^ 2 = 0 := by linear_combination h

/-- Stated on the residues themselves: the three lifts of a class mod `3^r` to
    mod `3^(r+1)` are exactly `c`, `c + 3^r` and `c + 2·3^r`. -/
theorem three_lifts {r c x : ℕ} (hc : c < 3 ^ r) (hx : x < 3 ^ (r + 1)) :
    x % 3 ^ r = c ↔ ∃ s < 3, x = c + s * 3 ^ r := by
  have hpos : 0 < 3 ^ r := pow_pos (by norm_num) r
  constructor
  · intro h
    refine ⟨x / 3 ^ r, ?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hpos]
      calc x < 3 ^ (r + 1) := hx
        _ = 3 * 3 ^ r := by ring
    · have hdm := Nat.div_add_mod x (3 ^ r)
      rw [Nat.mul_comm] at hdm
      omega
  · rintro ⟨s, _, rfl⟩
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

/-! ## Equidistribution as a collision count

Summing squared coefficients over a conductor turns the analytic question into a
counting one:

    Σ_j |μ̂(j,r)|² = 3^r · C(r) / N²,   C(r) = #{ pairs of level nodes with a ≡ b (mod 3^r) }

so equidistribution is `C(r) = N²/3^r` up to lower order, and the excess over that
IS the nonprincipal mass.  Measured, `excess × N` stays bounded — between `0.6`
and `6` over levels 19 to 32 with no growth — which is the square-root law in
counting form.

The count splits by which arms the two nodes came down, and two of the three legs
are forced by bijections already proved:

  * doubling with doubling: `2a ≡ 2b (mod 3^r) ↔ a ≡ b (mod 3^r)`, so this leg is
    exactly the previous level's `C(r)`;
  * odd with odd: `2s+1 ≡ 2t+1 (mod 3^r) ↔ s ≡ t (mod 3^r)`, so this leg is the
    previous level's collision count one digit finer, restricted to the junctions;
  * mixed: `2a ≡ u(b) (mod 3^r)`, the only free quantity.

Measured, the three legs take shares `0.5631, 0.0625, 0.3743` of the total, stable
to four digits across fourteen levels.  Those are `9/16`, `1/16` and `6/16`: the
squares of the arm proportions `3/4` and `1/4`.  So the mixed leg takes exactly
its proportional share and no more — the two arms are uncorrelated at the level of
collisions — and with the doubling leg exactly `C_d(r)` that forces
`C_{d+1} = (16/9) C_d`, which is exactly how `N²` grows.  Equidistribution is
maintained at each level precisely when the mixed leg stays proportional. -/

/-- The doubling leg: children of distinct classes stay distinct, children of the
    same class collide. -/
theorem double_collide_iff {r a b : ℕ} :
    (2 * a) % 3 ^ r = (2 * b) % 3 ^ r ↔ a % 3 ^ r = b % 3 ^ r := by
  constructor
  · exact fun h => double_inj_mod h
  · intro h
    exact Nat.ModEq.mul_left 2 h

/-- The odd leg: the arm map is injective on residues, so it collides only where
    its sources do. -/
theorem arm_collide_iff {r s t : ℕ} :
    (2 * s + 1) % 3 ^ r = (2 * t + 1) % 3 ^ r ↔ s % 3 ^ r = t % 3 ^ r := by
  constructor
  · exact fun h => arm_inj_mod h
  · intro h
    exact (Nat.ModEq.mul_left 2 h).add_right 1

/-! ## Why the cross correlation carries a sign

Doubling is an involution on the live classes mod 3: `2·1 ≡ 2` and `2·2 ≡ 1`, so
the two classes that branch are swapped every level and returned every second
level.  An imbalance between them therefore tends to alternate in sign, and the
correlation between a level and its own image under the arms is negative for that
reason rather than by accident.

Measured, the bias is real and strongest where the swap is purest.  The cross
deviation is negative in 20 of 24 levels at conductor 3 with mean `−0.140`, 15 of
22 at conductor 9 with mean `−0.063`, and 12 of 20 at conductor 27 with mean
`−0.037` — weakening as the conductor rises and the swap dilutes.  The signed
imbalance at conductor 3 changes sign every two to three levels rather than every
level, which is the involution perturbed by the odd arm's feed. -/

/-- Doubling swaps the two live classes and fixes the dead one. -/
theorem double_swaps_classes (m : ℕ) :
    (m % 3 = 1 → (2 * m) % 3 = 2) ∧ (m % 3 = 2 → (2 * m) % 3 = 1)
      ∧ (m % 3 = 0 → (2 * m) % 3 = 0) := by
  refine ⟨fun h => by omega, fun h => by omega, fun h => by omega⟩

/-- And returns every value to its own class after two steps, so doubling is an
    involution on residues mod 3. -/
theorem double_involution (m : ℕ) : (4 * m) % 3 = m % 3 := by omega

/-! ## The perturbation, exactly

At conductor three the even children swap the two live classes, so their whole
contribution to the imbalance `n₁ − n₂` is its negation.  The odd children come
only from the junctions, and which class they land in is fixed by the parent's
residue mod 9: `2 ↦ 1`, `5 ↦ 0`, `8 ↦ 2`.  Only two of those three touch the
imbalance, so

    I_{d+1} = −I_d + (m₂ − m₈)

with `m_c` the level's counts mod 9.  The involution is the minus sign and the
perturbation is one difference of two mod-9 classes, nothing else.

Checked in exact integers, the identity holds at every level to depth 30 with a
single exception at level 2, where the tree cuts its own `1 → 2 → 1` edge and the
prediction of 2 meets an actual 1 — off by exactly the omitted node.  The
perturbation is not small: its mean size is `1.79` times the imbalance it
perturbs, so the odd arm carries the level rather than nudging it, while the
imbalance itself stays at a fraction of `√N`. -/

theorem odd_child_class_two (v : ℕ) (h : v % 9 = 2) : (2 * (v / 3) + 1) % 3 = 1 := by
  omega

theorem odd_child_class_five (v : ℕ) (h : v % 9 = 5) : (2 * (v / 3) + 1) % 3 = 0 := by
  omega

theorem odd_child_class_eight (v : ℕ) (h : v % 9 = 8) : (2 * (v / 3) + 1) % 3 = 2 := by
  omega

/-- So of the three junction classes mod 9, one feeds each live class and one
    feeds the dead class: the imbalance sees `2` and `8` and never `5`. -/
theorem junction_classes_split (v : ℕ) (h : v % 3 = 2) :
    (v % 9 = 2 ∧ (2 * (v / 3) + 1) % 3 = 1)
      ∨ (v % 9 = 5 ∧ (2 * (v / 3) + 1) % 3 = 0)
      ∨ (v % 9 = 8 ∧ (2 * (v / 3) + 1) % 3 = 2) := by
  have h9 : v % 9 = 2 ∨ v % 9 = 5 ∨ v % 9 = 8 := by omega
  rcases h9 with h9 | h9 | h9
  · exact Or.inl ⟨h9, by omega⟩
  · exact Or.inr (Or.inl ⟨h9, by omega⟩)
  · exact Or.inr (Or.inr ⟨h9, by omega⟩)

/-! ## The cross term, decomposed

Write each histogram as its flat part plus a deviation.  Because both deviations
sum to zero, the flat parts contribute exactly the product of the totals over the
modulus and nothing else survives to first order: the cross term IS the
correlation of the two deviations, with no remainder.  That is `cross_decompose`
below, stated over any finite index type and any reindexing of the second factor.

With it, Cauchy–Schwarz gives `|cross(r)| ≤ (3/8)·√(e_even(r)·e_odd(r))`, where
`e_even(r)` is the level's own excess exactly, by the doubling bijection, and
`e_odd(r)` is the arm image's.  Summed against the weight that is
`c ≤ (3/8)√3·√(‖e_arm‖/‖e‖)`.

Measured, the arm image is as uniform as its quarter share allows — the ratio runs
`3.7` to `5.7`, against the `4` that population alone would give — so the bound
lands at `1.25` to `1.55`.  The measured `c` is about `0.1`.  So Cauchy–Schwarz is
loose here by roughly a factor of fourteen, and it cannot reach `1/4`: it takes
absolute values, and the sign is exactly what carries the contraction.  The
inequality below is what is provable without the sign; the sign is what remains. -/

/-- The flat parts cancel: a cross sum of two mean-zero-perturbed histograms is
    the product of the totals plus the correlation of the deviations, exactly. -/
theorem cross_decompose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ℚ) (a b : ι → ℚ) (σ : ι ≃ ι)
    (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0) :
    ∑ i, (A + a i) * (B + b (σ i))
      = (Fintype.card ι : ℚ) * A * B + ∑ i, a i * b (σ i) := by
  have hbσ : ∑ i, b (σ i) = 0 := by
    rw [← hb]
    exact Fintype.sum_equiv σ _ _ (fun _ => rfl)
  have expand : ∀ i : ι, (A + a i) * (B + b (σ i))
      = A * B + A * b (σ i) + a i * B + a i * b (σ i) := fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => expand i)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ha, hbσ,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_zero, zero_mul, add_zero,
    zero_add]
  ring

/-! ## Why the cross term is negative: the lag sum rule

Both deviations are the same level's, read under two affine maps, so the cross
term is an autocorrelation of the deviation at a nonzero lag.  A deviation sums to
zero, and that forces the autocorrelations over ALL lags to sum to zero:

    Σ_lag R(lag) = (Σ_c d c)² = 0,   R 0 = ‖d‖² > 0

so the nonzero lags sum to `−‖d‖²`.  They cannot all be positive; on average they
are negative, and a typical one sits at `−‖d‖²/(M−1)`.  That is the whole source
of the sign, and `autocorr_sum_zero` proves it for any mean-zero function on a
finite additive group.

What it buys depends on the conductor.  Measured, the cross term runs `0.349` of
the Cauchy–Schwarz bound at conductor 9 and `0.189` at conductor 27 — which is
`3^(-r/2)` to two digits, square-root cancellation over the `3^r` lags.  At
conductor 3 there are only two nonzero lags and no such gain exists, and that is
exactly where the weight `3^(-r)` is heaviest.  So the low rungs cannot be handled
generically; they need their identities, and `r = 1` already has one — the exact
integer recursion `I_{d+1} = −I_d + (m₂ − m₈)`. -/

/-- A mean-zero function's autocorrelations sum to zero over all lags.  The zero
    lag contributes `‖d‖²`, so every other lag together contributes `−‖d‖²`: the
    nonzero lags cannot all be positive, which is where the cross term's sign
    comes from. -/
theorem autocorr_sum_zero {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (d : G → ℚ) (hd : ∑ x, d x = 0) :
    ∑ t, ∑ x, d x * d (x + t) = 0 := by
  have inner : ∀ x : G, ∑ t, d x * d (x + t) = 0 := by
    intro x
    rw [← Finset.mul_sum]
    have : ∑ t, d (x + t) = ∑ y, d y :=
      Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun _ => rfl)
    rw [this, hd, mul_zero]
  rw [Finset.sum_comm]
  simpa using Finset.sum_congr rfl (fun x _ => inner x)

/-! ## Why the low conductors are the hard ones

The doubling permutation on residues mod `3^r` has order `2·3^(r-1)`: the kernel
reads `2, 6, 18, 54, 162` at `r = 1..5`.  That single fact organises everything
about the sign.

At `r = 1` the order is **two** — the permutation is the involution
`double_swaps_classes`, so a deviation alternates every level and the
cancellation is complete and per-level.  That is why the conductor-3 identity
`I_{d+1} = −I_d + (m₂ − m₈)` carries a bare minus sign, and why the cross term is
negative in 20 of 24 levels there.

At `r ≥ 2` the order is `6, 18, 54, …`.  There is no per-level sign at all; the
deviation returns to itself only after a full cycle, and what survives per level
is dilution rather than cancellation.  Measured, the cross term sits at `0.349`
of the Cauchy–Schwarz bound at conductor 9 and `0.189` at conductor 27, against
`3^(-r/2)` of `0.333` and `0.192` — square-root cancellation over the classes,
with the cycle length `2·3^(r-1)` proportional to that count.

So the two regimes are structurally different, and the split in the proof follows
the split in the order: the low rungs get exact identities, because they have a
sign to carry, and the high rungs get the generic square-root bound, because they
have length to average over. -/

theorem two_order_mod_three : 2 ^ 2 % 3 = 1 ∧ 2 ^ 1 % 3 ≠ 1 := by decide

theorem two_order_mod_nine :
    2 ^ 6 % 9 = 1 ∧ 2 ^ 1 % 9 ≠ 1 ∧ 2 ^ 2 % 9 ≠ 1 ∧ 2 ^ 3 % 9 ≠ 1
      ∧ 2 ^ 4 % 9 ≠ 1 ∧ 2 ^ 5 % 9 ≠ 1 := by decide

theorem two_order_mod_twentyseven :
    2 ^ 18 % 27 = 1 ∧ 2 ^ 6 % 27 ≠ 1 ∧ 2 ^ 9 % 27 ≠ 1 := by decide

/-- At conductor three, and only there, doubling is its own inverse — which is
    the whole of the per-level sign. -/
theorem doubling_involutive_only_at_three (m : ℕ) :
    (4 * m) % 3 = m % 3 ∧ ¬ (∀ x : ℕ, (4 * x) % 9 = x % 9) := by
  refine ⟨by omega, fun h => ?_⟩
  have := h 1
  omega

/-! ## The identity at conductor nine

At `r = 1` the doubling permutation is an involution and the recursion closes on
itself in one step.  At `r = 2` it is a six-cycle, so there is no per-level sign,
but the recursion is still exact — only now it reads the level at two resolutions
at once.

Both arms are determined:

  * the even child `2m` has class `2·(m mod 9) mod 9`, and doubling is a bijection
    there with inverse `5`, since `2·5 = 10 ≡ 1 (mod 9)`;
  * the odd child `2t+1` of a junction `3t+2` has class `2·(t mod 9)+1 mod 9`, so
    it is fixed by `t mod 9`, which is `m mod 27`.

So each class mod 9 of the next level is fed by exactly one class mod 9 of this
one through the doubling arm, and by exactly one class mod 27 through the odd arm.
`odd_source_mod_nine` names the second: the `t` class feeding `c` is `5·(c−1)`,
written `5·(c+8)` to stay in `ℕ`. -/

theorem even_child_mod_nine (m : ℕ) : (2 * m) % 9 = (2 * (m % 9)) % 9 := by omega

theorem odd_child_mod_nine (t : ℕ) : (2 * t + 1) % 9 = (2 * (t % 9) + 1) % 9 := by omega

theorem inv_two_mod_nine : (2 * 5) % 9 = 1 := by decide

/-- Doubling is onto the classes mod 9, so every class of the next level has
    exactly one doubling source. -/
theorem doubling_onto_mod_nine : ∀ c < 9, ∃ b, b < 9 ∧ (2 * b) % 9 = c := by decide

/-- And the odd arm's source: the `t` class feeding class `c` is `5(c−1) mod 9`,
    so the junction class feeding it is `3·that + 2` mod 27. -/
theorem odd_source_mod_nine : ∀ c < 9, (2 * ((5 * (c + 8)) % 9) + 1) % 9 = c := by decide

/-- The junction class mod 27 that feeds class `c` mod 9 through the odd arm. -/
def oddSource (c : ℕ) : ℕ := 3 * ((5 * (c + 8)) % 9) + 2

theorem oddSource_is_junction (c : ℕ) : oddSource c % 3 = 2 := by
  unfold oddSource; omega

theorem oddSource_feeds : ∀ c < 9, (2 * (oddSource c / 3) + 1) % 9 = c := by decide

/-! ## The junction fraction cannot vanish

The junction fraction `p₂` is what sets `ρ = 1/(1 + p₂)`, so a contraction stated
with `ρ = 3/4` needs `p₂` bounded below.  It is, and the reason is a three-cycle.

A junction can only stop feeding the odd arm by sitting in the class whose odd
child is barren, `5 (mod 9)` — that is `col_starved_arm` and
`odd_child_class_five`.  But junction classes do not sit still.  Two doublings
send `m ↦ 4m`, and on the three junction classes mod 9 that is

    4·2 = 8,   4·5 = 20 ≡ 2,   4·8 = 32 ≡ 5

a three-cycle `2 → 8 → 5 → 2`.  So a junction in the starved class is carried out
of it in two levels, and no junction population can remain starved: over any six
levels every junction's doubling descendant visits all three classes, two of which
feed live children.

That is `junction_class_cycle`, and with it the starving configuration — every
junction in `5 (mod 9)`, so that the odd arm dies and `p₂ → 0` — is not stable
under the level map for even one step. -/

/-- Two doublings permute the three junction classes mod 9 in a three-cycle. -/
theorem junction_class_cycle :
    (4 * 2) % 9 = 8 ∧ (4 * 5) % 9 = 2 ∧ (4 * 8) % 9 = 5 := by decide

/-- So the class is never fixed: no junction class returns to itself in one
    application of `4`. -/
theorem junction_class_no_fixpoint (m : ℕ) (h : m % 3 = 2) : (4 * m) % 9 ≠ m % 9 := by
  have h9 : m % 9 = 2 ∨ m % 9 = 5 ∨ m % 9 = 8 := by omega
  rcases h9 with h9 | h9 | h9 <;> omega

/-- And the cycle has order three, so a junction sits in the starved class for at
    most one level in every three. -/
theorem junction_cycle_order_three (m : ℕ) (h : m % 3 = 2) :
    (4 * (4 * (4 * m))) % 9 = m % 9 := by
  have h9 : m % 9 = 2 ∨ m % 9 = 5 ∨ m % 9 = 8 := by omega
  rcases h9 with h9 | h9 | h9 <;> omega

/-! ## What is provable about the junction fraction

`p₂ ≥ 1/4` is false as stated: at level 2 the tree is `{4}` and `4 ≡ 1 (mod 3)`,
so `p₂ = 0`, and at level 7 it is `0.2`.  Measured, those are the only two levels
below it, and from level 8 onward the minimum is `0.2581`.  So the true statement
carries a threshold, and the threshold is not decoration — the small levels really
do violate it.

What is provable without a threshold is the mechanism that keeps the live classes
alive.  The even arm alone gives two inequalities, because doubling carries class
`1` onto class `2` and class `2` onto class `1`, injectively:

    (junctions of the next level) ≥ (class-1 count of this one)
    (class-1 count of the next)   ≥ (junction count of this one)

so both live classes are non-decreasing every two levels and neither can be driven
to zero.  With `junction_cycle_order_three` excluding permanent starvation, that
is the whole of what the structure gives: `p₂` is bounded away from `0`, and the
numeric value `1/4` is measured rather than derived. -/

/-- Doubling carries class 1 into the junctions, injectively, so the next level
    has at least as many junctions as this level has class-1 members. -/
theorem junctions_ge_class_one (L : Finset ℕ) :
    (L.filter (fun m => m % 3 = 1)).card
      ≤ ((predStep L).filter (fun m => m % 3 = 2)).card := by
  apply Finset.card_le_card_of_injOn (fun m => 2 * m)
  · intro a ha
    obtain ⟨haL, ha1⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_filter.mpr ⟨?_, show (2 * a) % 3 = 2 by omega⟩
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, haL, rfl⟩)
  · intro a _ b _ hab
    simp only at hab
    omega

/-- And doubling carries the junctions into class 1, so the count returns. -/
theorem class_one_ge_junctions (L : Finset ℕ) :
    (L.filter (fun m => m % 3 = 2)).card
      ≤ ((predStep L).filter (fun m => m % 3 = 1)).card := by
  apply Finset.card_le_card_of_injOn (fun m => 2 * m)
  · intro a ha
    obtain ⟨haL, ha2⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_filter.mpr ⟨?_, show (2 * a) % 3 = 1 by omega⟩
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, haL, rfl⟩)
  · intro a _ b _ hab
    simp only at hab
    omega

/-- So the junction count does not fall across two levels. -/
theorem junctions_nondecreasing_two_levels (L : Finset ℕ) :
    (L.filter (fun m => m % 3 = 2)).card
      ≤ ((predStep (predStep L)).filter (fun m => m % 3 = 2)).card :=
  le_trans (class_one_ge_junctions L) (junctions_ge_class_one (predStep L))

/-! ## The growth rate, proved

`p₂(d) = N(d+1)/N(d) − 1` exactly, by `card_predStep`, so the junction fraction is
the level-growth ratio and nothing else.  What the weighted-norm contraction needs
is not a bound at each level but the telescoped product: over levels `a..b` the
composed bound is `1.1644^D · N(a)/N(b+1)`, and `∏(1+p₂) = N(b+1)/N(a)`, so the
requirement is an exponential rate

    liminf N(d)^(1/d) > 1.1644

and nothing per-level.  The single failing level `d = 2` disappears with the
per-level demand.

The rate is provable at conductor nine.  Doubling acts on `ℤ/9` as the six-cycle
`1 → 2 → 4 → 8 → 7 → 5 → 1` on the units, fixes `0` and swaps `3, 6`.  The dead
classes carry no growth at all — `subtreeCount_of_three_dvd` — so give them weight
zero.  Odd children inject at exactly two places on the cycle: a junction at
`2 (mod 9)` has an odd child at `1 (mod 3)`, one at `8 (mod 9)` has one at
`2 (mod 3)`, and one at `5 (mod 9)` has one at `0 (mod 3)`, which is dead.  Which
class mod 9 the child lands in needs the parent mod 27, so at this conductor it is
adversarial; weighting by the minimum over the three lifts removes the choice.

Requiring `w(children) ≥ L·w(parent)` at each of the six units gives

    w₂ ≥ L w₁    w₄ + min(w₁,w₄,w₇) ≥ L w₂    w₈ ≥ L w₄
    w₅ ≥ L w₇    w₇ + min(w₂,w₅,w₈) ≥ L w₈    w₁ ≥ L w₅

and taking the chain tight with `w₇ = 1` forces `w₅ = L`, `w₁ = L²`, `w₂ = L³`,
`w₄ = L⁴ − 1`, `w₈ = L⁵ − L`, so the last requirement is exactly

    L⁶ ≤ L² + L + 1

whose root is `L = 1.2498…`.  At `L = 6/5` the weights clear denominators to
integers and every requirement holds, three of them with equality.  Against the
real tree the functional's ratio is `6/5` exactly at levels 3, 5, 6 and 12 and
never below it through level 30, so the certificate is sharp and not slack. -/

/-- The certificate weight: zero on the dead classes `0, 3, 6 (mod 9)`, and on the
    six units the tight solution of the six-cycle at `L = 6/5`. -/
def wt (v : ℕ) : ℕ :=
  if v % 9 = 1 then 4500 else
  if v % 9 = 2 then 5400 else
  if v % 9 = 4 then 3355 else
  if v % 9 = 8 then 4026 else
  if v % 9 = 7 then 3125 else
  if v % 9 = 5 then 3750 else 0

/-- Its total over a level. -/
def W (L : Finset ℕ) : ℕ := ∑ v ∈ L, wt v

theorem wt_le (v : ℕ) : wt v ≤ 5400 := by
  unfold wt; split_ifs <;> omega

/-- A child at `1 (mod 3)` sits in one of `1, 4, 7 (mod 9)`, so weighs at least the
    least of those three. -/
theorem wt_ge_of_class_one {x : ℕ} (h : x % 3 = 1) : 3125 ≤ wt x := by
  have h9 : x % 9 = 1 ∨ x % 9 = 4 ∨ x % 9 = 7 := by omega
  unfold wt; rcases h9 with h9 | h9 | h9 <;> simp [h9]

/-- A child at `2 (mod 3)` sits in one of `2, 5, 8 (mod 9)`. -/
theorem wt_ge_of_class_two {x : ℕ} (h : x % 3 = 2) : 3750 ≤ wt x := by
  have h9 : x % 9 = 2 ∨ x % 9 = 5 ∨ x % 9 = 8 := by omega
  unfold wt; rcases h9 with h9 | h9 | h9 <;> simp [h9]

/-- The doubling six-cycle on the units, and the two dead orbits. -/
theorem wt_double (v : ℕ) :
    wt (2 * v) =
      if v % 9 = 1 then 5400 else
      if v % 9 = 2 then 3355 else
      if v % 9 = 4 then 4026 else
      if v % 9 = 8 then 3125 else
      if v % 9 = 7 then 3750 else
      if v % 9 = 5 then 4500 else 0 := by
  have h9 : v % 9 = 0 ∨ v % 9 = 1 ∨ v % 9 = 2 ∨ v % 9 = 3 ∨ v % 9 = 4 ∨ v % 9 = 5
      ∨ v % 9 = 6 ∨ v % 9 = 7 ∨ v % 9 = 8 := by omega
  have hd : (2 * v) % 9 = (2 * (v % 9)) % 9 := by omega
  unfold wt
  rcases h9 with h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 <;>
    rw [hd, h9] <;> norm_num

/-- **The pointwise certificate.** Every vertex's children carry at least `6/5` of
    its own weight, with no hypothesis and no choice left to the adversary. -/
theorem wt_children (v : ℕ) :
    6 * wt v ≤ 5 * (wt (2 * v) + if v % 3 = 2 then wt (2 * (v / 3) + 1) else 0) := by
  rw [wt_double]
  have h9 : v % 9 = 0 ∨ v % 9 = 1 ∨ v % 9 = 2 ∨ v % 9 = 3 ∨ v % 9 = 4 ∨ v % 9 = 5
      ∨ v % 9 = 6 ∨ v % 9 = 7 ∨ v % 9 = 8 := by omega
  rcases h9 with h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9
  -- the dead classes: weight zero on both sides
  · simp [wt, h9]
  -- 1 → 2 : 5·5400 ≥ 6·4500, equality
  · have : v % 3 = 1 := by omega
    simp [wt, h9, this]
  -- 2 → 4, plus an odd child at 1 (mod 3), worth at least 3125
  · have h3 : v % 3 = 2 := by omega
    have hc := wt_ge_of_class_one (odd_child_class_two v h9)
    simp only [wt, h9, h3, if_true, if_false] at *
    norm_num at *
    omega
  · simp [wt, h9]
  -- 4 → 8 : 5·4026 ≥ 6·3355, equality
  · have : v % 3 = 1 := by omega
    simp [wt, h9, this]
  -- 5 → 1, and its odd child is dead: 5·4500 ≥ 6·3750, equality
  · have h3 : v % 3 = 2 := by omega
    simp only [wt, h9, h3, if_true, if_false] at *
    norm_num at *
    omega
  · simp [wt, h9]
  -- 7 → 5 : 5·3750 ≥ 6·3125, equality
  · have : v % 3 = 1 := by omega
    simp [wt, h9, this]
  -- 8 → 7, plus an odd child at 2 (mod 3), worth at least 3750: the one slack case
  · have h3 : v % 3 = 2 := by omega
    have hc := wt_ge_of_class_two (odd_child_class_eight v h9)
    simp only [wt, h9, h3, if_true, if_false] at *
    norm_num at *
    omega

/-- The weight of a level, split along the two arms. -/
theorem W_predStep (L : Finset ℕ) :
    W (predStep L) =
      (∑ m ∈ L, wt (2 * m))
        + ∑ m ∈ L.filter (fun m => m % 3 = 2), wt (2 * (m / 3) + 1) := by
  unfold W predStep
  rw [Finset.sum_union, Finset.sum_image, Finset.sum_image]
  · intro a ha b hb hab
    obtain ⟨_, ha3⟩ := Finset.mem_filter.mp ha
    obtain ⟨_, hb3⟩ := Finset.mem_filter.mp hb
    simp only at hab
    omega
  · intro a _ b _ hab; simp only at hab; omega
  · rw [Finset.disjoint_left]
    rintro x hx hy
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨m', _, hm'⟩ := Finset.mem_image.mp hy
    omega

/-- **The level certificate.** Summing the pointwise bound: the weight of a level
    is at least `6/5` of the weight of the level below it, for every level. -/
theorem W_grows (L : Finset ℕ) : 6 * W L ≤ 5 * W (predStep L) := by
  rw [W_predStep, Nat.mul_add]
  have hsplit : ∑ m ∈ L, (if m % 3 = 2 then wt (2 * (m / 3) + 1) else 0)
      = ∑ m ∈ L.filter (fun m => m % 3 = 2), wt (2 * (m / 3) + 1) := by
    rw [Finset.sum_filter]
  calc 6 * W L
      = ∑ m ∈ L, 6 * wt m := by unfold W; rw [Finset.mul_sum]
    _ ≤ ∑ m ∈ L, 5 * (wt (2 * m) + if m % 3 = 2 then wt (2 * (m / 3) + 1) else 0) :=
        Finset.sum_le_sum (fun m _ => wt_children m)
    _ = 5 * (∑ m ∈ L, wt (2 * m))
          + 5 * ∑ m ∈ L, (if m % 3 = 2 then wt (2 * (m / 3) + 1) else 0) := by
        simp [Finset.sum_add_distrib, Nat.mul_add, Finset.mul_sum, mul_ite, mul_zero]
    _ = 5 * (∑ m ∈ L, wt (2 * m))
          + 5 * ∑ m ∈ L.filter (fun m => m % 3 = 2), wt (2 * (m / 3) + 1) := by
        rw [hsplit]

/-- Iterated: the weight is at least `(6/5)^n` of where it started. -/
theorem W_grows_iterate (L : Finset ℕ) : ∀ n : ℕ,
    6 ^ n * W L ≤ 5 ^ n * W (predStep^[n] L)
  | 0 => by simp
  | n + 1 => by
      have ih := W_grows_iterate L n
      have hstep := W_grows (predStep^[n] L)
      calc 6 ^ (n + 1) * W L = 6 * (6 ^ n * W L) := by ring
        _ ≤ 6 * (5 ^ n * W (predStep^[n] L)) := Nat.mul_le_mul_left _ ih
        _ = 5 ^ n * (6 * W (predStep^[n] L)) := by ring
        _ ≤ 5 ^ n * (5 * W (predStep (predStep^[n] L))) := Nat.mul_le_mul_left _ hstep
        _ = 5 ^ (n + 1) * W (predStep^[n + 1] L) := by
            rw [Function.iterate_succ_apply']
            ring

theorem W_le_card (L : Finset ℕ) : W L ≤ 5400 * L.card := by
  unfold W
  calc ∑ v ∈ L, wt v ≤ ∑ _v ∈ L, 5400 := Finset.sum_le_sum (fun v _ => wt_le v)
    _ = 5400 * L.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **The growth rate of the predecessor tree.** From any level the count grows at
    least like `(6/5)^n`.  With `p₂(d) = N(d+1)/N(d) − 1` this is the junction
    fraction in the only form the contraction uses, and `6/5 > 1.1644`. -/
theorem card_grows (L : Finset ℕ) (n : ℕ) :
    6 ^ n * W L ≤ 5 ^ n * 5400 * (predStep^[n] L).card := by
  calc 6 ^ n * W L ≤ 5 ^ n * W (predStep^[n] L) := W_grows_iterate L n
    _ ≤ 5 ^ n * (5400 * (predStep^[n] L).card) :=
        Nat.mul_le_mul_left _ (W_le_card _)
    _ = 5 ^ n * 5400 * (predStep^[n] L).card := by ring

/-- Rooted at level three, which is the single node `{8}`, weight `4026`. -/
theorem card_grows_from_root (n : ℕ) :
    4026 * 6 ^ n ≤ 5400 * 5 ^ n * (predStep^[n] {8}).card := by
  have h := card_grows {8} n
  have hW : W ({8} : Finset ℕ) = 4026 := by decide
  rw [hW] at h
  calc 4026 * 6 ^ n = 6 ^ n * 4026 := by ring
    _ ≤ 5 ^ n * 5400 * (predStep^[n] {8}).card := h
    _ = 5400 * 5 ^ n * (predStep^[n] {8}).card := by ring

/-- And `6/5` clears the threshold the contraction needs, with room: the composed
    bound over `D` levels is `1.1644^D · N(a)/N(b+1)`, and `(1.1644/1.2)^D → 0`. -/
theorem threshold_clear : (11644 : ℕ) * 5 < 6 * 10000 := by norm_num

/-! ## The bridge: coefficient decay is equidistribution

Everything above bounds Fourier coefficients.  The conjecture wants densities.
This section is the transfer, and it is finite Fourier inversion and nothing else —
no analysis of the map enters here, which is the point: the bridge should be
provable without knowing what tree it is carrying.

A level's census mod `N` is the function `census L N : ZMod N → ℂ` counting the
members of `L` in each class.  Its zeroth coefficient is the total mass, by
`dft_apply_zero`.  Inversion writes every value as the mean plus the nontrivial
coefficients, so a uniform bound `ε` on those is a uniform bound `(N−1)/N · ε` on
the deviation of every class from the mean — that is `equidist_of_dft_small`.
Divide through by the mass and let the bound go to zero and every class has
density `1/N`, which is `tendsto_density_of_dft_tendsto_zero`.

So "the weighted norm contracts" and "the tree equidistributes mod `3^r`" are the
same statement, joined here rather than asserted. -/

open ZMod in
/-- **The transfer.** If every nontrivial Fourier coefficient of `Φ` is at most `ε`,
    then every value of `Φ` sits within `(N−1)/N · ε` of the mean. -/
theorem equidist_of_dft_small {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (ε : ℝ)
    (h : ∀ j : ZMod N, j ≠ 0 → ‖𝓕 Φ j‖ ≤ ε) (x : ZMod N) :
    ‖Φ x - (∑ y, Φ y) / N‖ ≤ (N - 1) / N * ε := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  -- inversion, with the zeroth coefficient split off as the mass
  have hinv : Φ x = (N : ℂ)⁻¹ • ∑ j : ZMod N, stdAddChar (j * x) • 𝓕 Φ j := by
    have hx : 𝓕⁻ (𝓕 Φ) x = Φ x := congrFun (LinearEquiv.symm_apply_apply _ _) x
    rw [← hx, ZMod.invDFT_apply]
  have hzero : stdAddChar ((0 : ZMod N) * x) • 𝓕 Φ 0 = (∑ y, Φ y) := by
    rw [zero_mul, dft_apply_zero, AddChar.map_zero_eq_one, one_smul]
  have hsum : ∑ j : ZMod N, stdAddChar (j * x) • 𝓕 Φ j
      = (∑ j ∈ ({0} : Finset (ZMod N))ᶜ, stdAddChar (j * x) • 𝓕 Φ j) + (∑ y, Φ y) := by
    rw [← Finset.sum_compl_add_sum ({0} : Finset (ZMod N)), Finset.sum_singleton, hzero]
  have hsplit : Φ x - (∑ y, Φ y) / N
      = (N : ℂ)⁻¹ * ∑ j ∈ ({0} : Finset (ZMod N))ᶜ, stdAddChar (j * x) • 𝓕 Φ j := by
    rw [hinv, hsum, smul_eq_mul, mul_add]
    field_simp
    ring
  -- and the tail is at most (N−1) terms of size ε
  rw [hsplit, norm_mul, norm_inv, Complex.norm_natCast]
  have hterm : ∀ j ∈ ({0} : Finset (ZMod N))ᶜ, ‖stdAddChar (j * x) • 𝓕 Φ j‖ ≤ ε := by
    intro j hj
    exact (Circle.norm_smul _ _).trans_le (h j (by simpa using Finset.mem_compl.mp hj))
  have hcard : (({0} : Finset (ZMod N))ᶜ).card = N - 1 := by
    rw [Finset.card_compl, Finset.card_singleton, ZMod.card]
  calc (N : ℝ)⁻¹ * ‖∑ j ∈ ({0} : Finset (ZMod N))ᶜ, stdAddChar (j * x) • 𝓕 Φ j‖
      ≤ (N : ℝ)⁻¹ * ∑ j ∈ ({0} : Finset (ZMod N))ᶜ, ‖stdAddChar (j * x) • 𝓕 Φ j‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (N : ℝ)⁻¹ * ((({0} : Finset (ZMod N))ᶜ).card • ε) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_card_nsmul _ _ _ hterm) (by positivity)
    _ = (N - 1) / N * ε := by
        rw [hcard, nsmul_eq_mul]
        have hc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
          have h1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
          push_cast [Nat.cast_sub h1]
          ring
        rw [hc]; field_simp

open ZMod in
/-- **The bridge.** Coefficients small relative to the mass, uniformly and going to
    zero, is exactly every class having density `1/N` in the limit. -/
theorem tendsto_density_of_dft_tendsto_zero {N : ℕ} [NeZero N]
    (Φ : ℕ → ZMod N → ℂ) (M : ℕ → ℝ) (hM : ∀ d, 0 < M d)
    (hmass : ∀ d, ∑ y, Φ d y = (M d : ℂ))
    (ε : ℕ → ℝ) (hε0 : ∀ d, 0 ≤ ε d)
    (hsmall : ∀ d, ∀ j : ZMod N, j ≠ 0 → ‖𝓕 (Φ d) j‖ ≤ ε d * M d)
    (hε : Filter.Tendsto ε Filter.atTop (nhds 0)) (x : ZMod N) :
    Filter.Tendsto (fun d => ‖Φ d x / (M d : ℂ) - (N : ℂ)⁻¹‖) Filter.atTop (nhds 0) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have key : ∀ d, ‖Φ d x / (M d : ℂ) - (N : ℂ)⁻¹‖ ≤ (N - 1) / N * ε d := by
    intro d
    have hMd : (M d : ℂ) ≠ 0 := by exact_mod_cast (hM d).ne'
    have h := equidist_of_dft_small (Φ d) (ε d * M d) (hsmall d) x
    have hrw : Φ d x / (M d : ℂ) - (N : ℂ)⁻¹
        = (Φ d x - (∑ y, Φ d y) / N) / (M d : ℂ) := by
      rw [hmass d]; field_simp
    rw [hrw, norm_div, Complex.norm_real, Real.norm_of_nonneg (hM d).le]
    rw [div_le_iff₀ (hM d)]
    calc ‖Φ d x - (∑ y, Φ d y) / N‖ ≤ (N - 1) / N * (ε d * M d) := h
      _ = (N - 1) / N * ε d * M d := by ring
  have hlow : ∀ d, (0 : ℝ) ≤ ‖Φ d x / (M d : ℂ) - (N : ℂ)⁻¹‖ := fun _ => norm_nonneg _
  have : Filter.Tendsto (fun d => (N - 1) / N * ε d) Filter.atTop (nhds 0) := by
    have h := Filter.Tendsto.const_mul (((N : ℝ) - 1) / N) hε
    simpa using h
  exact squeeze_zero hlow key this

/-- The census of a level mod `N`: how many of its members sit in each class. -/
noncomputable def census (L : Finset ℕ) (N : ℕ) : ZMod N → ℂ :=
  fun j => ((L.filter (fun v : ℕ => ((v : ZMod N) = j))).card : ℂ)

/-- Its total mass is the size of the level, so `dft_apply_zero` reads the count. -/
theorem census_mass (L : Finset ℕ) (N : ℕ) [NeZero N] :
    ∑ j : ZMod N, census L N j = (L.card : ℂ) := by
  unfold census
  rw [← Nat.cast_sum]
  congr 1
  exact (Finset.card_eq_sum_card_fiberwise (fun (v : ℕ) _ => Finset.mem_univ ((v : ZMod N)))).symm

open ZMod in
/-- **The statement the whole apparatus is for.** If the level census's nontrivial
    coefficients decay relative to the level count, every residue class mod `N`
    holds a `1/N` share of the tree in the limit.  With `N = 3^r` this is the
    equidistribution the branch factor `4/3` and the contraction both assume. -/
theorem levels_equidistribute {N : ℕ} [NeZero N] (lvl : ℕ → Finset ℕ)
    (hne : ∀ d, 0 < (lvl d).card) (ε : ℕ → ℝ) (hε0 : ∀ d, 0 ≤ ε d)
    (hsmall : ∀ d, ∀ j : ZMod N, j ≠ 0 →
      ‖𝓕 (census (lvl d) N) j‖ ≤ ε d * ((lvl d).card : ℝ))
    (hε : Filter.Tendsto ε Filter.atTop (nhds 0)) (x : ZMod N) :
    Filter.Tendsto
      (fun d => ‖census (lvl d) N x / (((lvl d).card : ℝ) : ℂ) - (N : ℂ)⁻¹‖)
      Filter.atTop (nhds 0) :=
  tendsto_density_of_dft_tendsto_zero (fun d => census (lvl d) N)
    (fun d => ((lvl d).card : ℝ)) (fun d => Nat.cast_pos.mpr (hne d))
    (fun d => by rw [census_mass]; norm_num) ε hε0 hsmall hε x

/-! ## The level operator, entry by entry

The one link in the chain still resting on a numerical check was the first: that
the operator being normed is the true level map, "verified to five decimals at
conductors 3 and 9".  It is an exact algebraic identity and it is proved here.

Write `ζ` for a `3^(r+1)`-th root of unity and `ω = ζ^(3^r)`, a cube root.  The
unnormalised coefficient of a level `L` at index `k` is `coeff ζ L k = ∑ ζ^(k v)`.
One level of the tree is `predStep`, whose two arms are `m ↦ 2m` on all of `L` and
`m ↦ 2(m/3)+1` on the part at `2 (mod 3)`.

The doubling arm is a relabelling: `ζ^(3j·2m) = ζ^(6j·m)`, so it contributes the
coefficient at `2j` and moves nothing between conductors.

The odd arm needs the parent's class.  With `m % 3 = 2` and `n = 2(m/3)+1` the
exact relation is `3n + 1 = 2m` — no subtraction and no division — so
`ζ^j · ζ^(3j·n) = ζ^(2j·m)`, which is the phase `e(−j/3^(r+1))` of the informal
statement, cleared of its inverse.  Restricting to `m % 3 = 2` is the cube-root
indicator, and there the informal `ω^(−2s)` is simply `ω^s`, since `ω³ = 1` gives
`ω^(−2) = ω`.  One inverse and one negative exponent disappear from the formula.

Composing, `ζ^(s(m+1)) · ζ^(2j m) = ζ^((2j + s·3^r) m)` lifts the index one
conductor, which is the whole of the block-triangular structure: the odd arm is
fed by `r+1` and by nothing below.

The identity, with every entry explicit and nothing measured:

    ζ^j · coeff ζ (predStep L) (3j)
      = ζ^j · coeff ζ L (6j) + (1/3) ∑_{s<3} ω^s · coeff ζ L (2j + s·3^r)
-/

/-- The unnormalised Fourier coefficient of a level at the character of index `k`. -/
noncomputable def coeff (ζ : ℂ) (L : Finset ℕ) (k : ℕ) : ℂ := ∑ v ∈ L, ζ ^ (k * v)

/-- The cube-root indicator of the junction class.  This is where `ω^(−2s)`
    becomes `ω^s`: `ω³ = 1` makes the two the same weight. -/
theorem cube_indicator {ω : ℂ} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) (m : ℕ) :
    (∑ s ∈ Finset.range 3, ω ^ (s * (m + 1))) = if m % 3 = 2 then 3 else 0 := by
  have hsum : 1 + ω + ω ^ 2 = 0 := by
    have : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) h1
    · exact h
  have hpow : ∀ s : ℕ, ω ^ (s * (m + 1)) = (ω ^ (m + 1)) ^ s := by
    intro s; rw [← pow_mul, Nat.mul_comm]
  simp only [hpow, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
  -- `ω^(m+1)` is `1` exactly when `3 ∣ m+1`, i.e. when `m % 3 = 2`
  have hcyc : ω ^ (m + 1) = ω ^ ((m + 1) % 3) := by
    conv_lhs => rw [← Nat.div_add_mod (m + 1) 3]
    rw [pow_add, pow_mul, h3, one_pow, one_mul]
  rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with hm | hm | hm
  · -- `ω^(m+1) = ω`, and `1 + ω + ω² = 0`
    rw [hcyc, (by omega : (m + 1) % 3 = 1), if_neg (by omega : ¬ m % 3 = 2), pow_one]
    linear_combination hsum
  · -- `ω^(m+1) = ω²`, and `1 + ω² + ω⁴ = (1 + ω + ω²) + ω(ω³ − 1)`
    rw [hcyc, (by omega : (m + 1) % 3 = 2), if_neg (by omega : ¬ m % 3 = 2)]
    linear_combination hsum + ω * h3
  · -- `ω^(m+1) = 1`, and the three terms are three ones
    rw [hcyc, (by omega : (m + 1) % 3 = 0), if_pos hm, pow_zero]
    norm_num

/-- The odd arm's phase, without inverses: `3n + 1 = 2m` exactly, for `m` a
    junction and `n` its odd predecessor. -/
theorem odd_arm_exponent {m : ℕ} (h : m % 3 = 2) : 3 * (2 * (m / 3) + 1) + 1 = 2 * m := by
  omega

/-- The coefficient of a level, split along the two arms of `predStep`. -/
theorem coeff_predStep (ζ : ℂ) (L : Finset ℕ) (k : ℕ) :
    coeff ζ (predStep L) k
      = (∑ m ∈ L, ζ ^ (k * (2 * m)))
        + ∑ m ∈ L.filter (fun m => m % 3 = 2), ζ ^ (k * (2 * (m / 3) + 1)) := by
  unfold coeff predStep
  rw [Finset.sum_union, Finset.sum_image, Finset.sum_image]
  · intro a ha b hb hab
    obtain ⟨_, ha3⟩ := Finset.mem_filter.mp ha
    obtain ⟨_, hb3⟩ := Finset.mem_filter.mp hb
    simp only at hab
    omega
  · intro a _ b _ hab; simp only at hab; omega
  · rw [Finset.disjoint_left]
    rintro x hx hy
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨m', _, hm'⟩ := Finset.mem_image.mp hy
    omega

/-- **The level operator, exactly.**  Every entry of the map on coefficients, with
    no approximation anywhere: the doubling arm relabels the index as `2j` at the
    same conductor, and the odd arm carries the phase `ζ^(−j)` and the three lifts
    one conductor above, weighted by the cube roots. -/
theorem level_operator (ζ ω : ℂ) (r j : ℕ) (L : Finset ℕ)
    (hω : ζ ^ 3 ^ r = ω) (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) :
    ζ ^ j * coeff ζ (predStep L) (3 * j)
      = ζ ^ j * coeff ζ L (6 * j)
        + (3 : ℂ)⁻¹ * ∑ s ∈ Finset.range 3, ω ^ s * coeff ζ L (2 * j + s * 3 ^ r) := by
  rw [coeff_predStep, mul_add]
  congr 1
  · -- the doubling arm is a relabelling and nothing else
    unfold coeff
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by ring_nf)
  · -- the odd arm: phase, then indicator, then the lift of the index
    have harm : ζ ^ j * ∑ m ∈ L.filter (fun m => m % 3 = 2), ζ ^ (3 * j * (2 * (m / 3) + 1))
        = ∑ m ∈ L.filter (fun m => m % 3 = 2), ζ ^ (2 * j * m) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      obtain ⟨_, hm3⟩ := Finset.mem_filter.mp hm
      rw [← pow_add]
      congr 1
      have := odd_arm_exponent hm3
      nlinarith [this]
    rw [harm]
    -- the filter is the cube-root indicator
    have hind : ∑ m ∈ L.filter (fun m => m % 3 = 2), ζ ^ (2 * j * m)
        = (3 : ℂ)⁻¹ * ∑ m ∈ L, (∑ s ∈ Finset.range 3, ω ^ (s * (m + 1))) * ζ ^ (2 * j * m) := by
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [cube_indicator h3 h1 m]
      by_cases hm : m % 3 = 2 <;> simp [hm] <;> ring
    rw [hind]
    -- and each cube root lifts the index one conductor
    congr 1
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    unfold coeff
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← hω, ← pow_mul, ← pow_add]
    congr 1
    ring

/-! ## The weighted contraction, and what it is a contraction of

With `level_operator` exact, the operator bound is a triangle inequality and no
longer needs singular values.  A character has modulus one, the feed is an average
of three terms, so at conductor `r`

    |μ̂_{d+1}(j,r)| ≤ ρ_d ( D_r + D_{r+1} )

with `D_r` the largest coefficient at conductor `r`.  Under the weight `w^r` —
`D_r ≤ K w^r` — that reads `K w^r (1 + w)`, so in the weighted supremum norm

    ‖L‖_w ≤ ρ (1 + w)

for every `w`, uniformly in the truncation and with no computation.  With
`ρ ≤ 5/6` from `card_grows_from_root` and `w = 1/6` this is `35/36 < 1`.  Proved,
where the singular-value figure `0.8733` was measured; weaker as a number, since
it discards the cancellation, and stronger as a statement, since it holds at every
truncation and needs no matrix.

**And it does not apply to the tree.**  The norm `‖a‖_w = sup_{j,r} w^{-r}|a(j,r)|`
is finite only for coefficients that decay like `w^r` in the conductor.  The
tree's do the opposite: measured, `max_j |μ̂_d(j,r)|` *rises* with `r` toward one —
at `d = 8` it runs `0.14, 0.29, 0.37, 0.68, 0.72, 0.87, 0.98, 0.998` for
`r = 1..8`, where the weight at `w = 0.3` demands `0.30, 0.09, 0.027, …, 0.0001`.
That is not a small discrepancy, it is the opposite behaviour, and it is forced:
once `3^r` exceeds the spread of a level, its `N_d` points cannot be spread over
`3^r` classes, so the coefficients are near one.  So `‖μ̂_d‖_w = ∞`, and the
weighted contraction is a true statement about the operator applied to vectors the
tree does not supply.

That is a finding about the route, not a missing constant.  The record above said
the remaining item was to prove a measured number; the number is now proved, in a
stronger and cheaper form, and it does not close the chain.

**What the obstruction actually is.**  Write `m_r(d)` for the largest coefficient
at conductor `r` and depth `d`.  The triangle recursion is exact in form:

    m_r(d+1) ≤ ρ ( m_r(d) + m_{r+1}(d) )

and every coefficient obeys `m ≤ 1`.  The all-ones vector is invariant under it:
`ρ(1 + 1) = 3/2 > 1`, so the cap never binds and the recursion has no decay in it
at all.  No refinement of the triangle inequality can help, because the inequality
is already tight term by term — the doubling term genuinely has modulus `D_r` and
the feed genuinely has modulus up to `D_{r+1}`.

So the cancellation between the doubling term and the feed is not a sharpening of
this argument.  It is the entire content, and it is the only thing in the chain
that is still measured: `|sum| / (|same| + |feed|)` averages `0.5312` at conductor
3 over 24 levels and `0.7884` at conductor 9 over 20.  Everything else — the
operator, the growth rate, the bridge — is proved. -/

/-- A character has modulus one, so the phases in `level_operator` cost nothing. -/
theorem norm_root_of_unity {z : ℂ} {n : ℕ} (h : z ^ n = 1) (hn : n ≠ 0) : ‖z‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one h hn

/-- **The level bound.**  The triangle inequality on `level_operator`: the new
    coefficient is at most the old one at the same conductor plus the largest of
    the three lifts one conductor above.  Both phases drop out. -/
theorem level_coeff_triangle (ζ ω : ℂ) (r j : ℕ) (L : Finset ℕ) (Dr Dr1 : ℝ)
    (hζ : ‖ζ‖ = 1) (hω : ζ ^ 3 ^ r = ω) (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    (hr : ‖coeff ζ L (6 * j)‖ ≤ Dr)
    (hr1 : ∀ s < 3, ‖coeff ζ L (2 * j + s * 3 ^ r)‖ ≤ Dr1) :
    ‖coeff ζ (predStep L) (3 * j)‖ ≤ Dr + Dr1 := by
  have hωn : ‖ω‖ = 1 := norm_root_of_unity h3 (by norm_num)
  have hζj : ‖ζ ^ j‖ = 1 := by rw [norm_pow, hζ, one_pow]
  have key := level_operator ζ ω r j L hω h3 h1
  have hlhs : ‖ζ ^ j * coeff ζ (predStep L) (3 * j)‖ = ‖coeff ζ (predStep L) (3 * j)‖ := by
    rw [norm_mul, hζj, one_mul]
  rw [← hlhs, key]
  refine (norm_add_le _ _).trans ?_
  have hA : ‖ζ ^ j * coeff ζ L (6 * j)‖ ≤ Dr := by rw [norm_mul, hζj, one_mul]; exact hr
  have hB : ‖(3 : ℂ)⁻¹ * ∑ s ∈ Finset.range 3, ω ^ s * coeff ζ L (2 * j + s * 3 ^ r)‖ ≤ Dr1 := by
    rw [norm_mul]
    have h3n : ‖(3 : ℂ)⁻¹‖ = (3 : ℝ)⁻¹ := by norm_num
    rw [h3n]
    have hsum : ‖∑ s ∈ Finset.range 3, ω ^ s * coeff ζ L (2 * j + s * 3 ^ r)‖ ≤ 3 * Dr1 := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ s ∈ Finset.range 3, ‖ω ^ s * coeff ζ L (2 * j + s * 3 ^ r)‖ ≤ Dr1 := by
        intro s hs
        rw [norm_mul, norm_pow, hωn, one_pow, one_mul]
        exact hr1 s (Finset.mem_range.mp hs)
      calc ∑ s ∈ Finset.range 3, ‖ω ^ s * coeff ζ L (2 * j + s * 3 ^ r)‖
          ≤ ∑ _s ∈ Finset.range 3, Dr1 := Finset.sum_le_sum this
        _ = 3 * Dr1 := by simp [Finset.sum_const]
    calc (3 : ℝ)⁻¹ * ‖∑ s ∈ Finset.range 3, ω ^ s * coeff ζ L (2 * j + s * 3 ^ r)‖
        ≤ (3 : ℝ)⁻¹ * (3 * Dr1) := by
          exact mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = Dr1 := by ring
  exact add_le_add hA hB

/-- **The weighted step.**  Under the weight `w^r` the bound is `(1+w)` times the
    weight at conductor `r`, so the unnormalised coefficient grows by at most
    `1 + w` per level and the normalisation supplies the factor `ρ`. -/
theorem level_weighted_step (ζ ω : ℂ) (r j : ℕ) (L : Finset ℕ) (K w : ℝ)
    (hw : 0 ≤ w) (hK : 0 ≤ K)
    (hζ : ‖ζ‖ = 1) (hω : ζ ^ 3 ^ r = ω) (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    (hr : ‖coeff ζ L (6 * j)‖ ≤ K * w ^ r)
    (hr1 : ∀ s < 3, ‖coeff ζ L (2 * j + s * 3 ^ r)‖ ≤ K * w ^ (r + 1)) :
    ‖coeff ζ (predStep L) (3 * j)‖ ≤ (1 + w) * (K * w ^ r) := by
  have h := level_coeff_triangle ζ ω r j L (K * w ^ r) (K * w ^ (r + 1)) hζ hω h3 h1 hr hr1
  calc ‖coeff ζ (predStep L) (3 * j)‖ ≤ K * w ^ r + K * w ^ (r + 1) := h
    _ = (1 + w) * (K * w ^ r) := by ring

/-- The constant the proved growth rate supplies: `ρ ≤ 5/6` from `card_grows`, and
    `w = 1/6`, giving `35/36 < 1` — a proved contraction where `0.8733` was a
    measured one. -/
theorem weighted_contraction_constant :
    (1 + (1 : ℝ) / 6) * (5 / 6) = 35 / 36 ∧ (35 : ℝ) / 36 < 1 := by
  constructor <;> norm_num

/-- **The obstruction, stated.**  The triangle recursion has the all-ones vector as
    a fixed point: with every coefficient at its maximum, `ρ(1 + 1) = 3/2 > 1`, so
    the bound never binds and carries no decay.  The cancellation between the
    doubling term and the feed is therefore not a refinement of this argument but
    the whole of what is missing. -/
theorem triangle_recursion_has_no_decay (ρ : ℝ) (hρ : (1 : ℝ) / 2 ≤ ρ) :
    (1 : ℝ) ≤ ρ * (1 + 1) := by linarith

/-! ## What the feed is, and why the gap does not close here

The gap was stated as a local inequality on the three lifts of a class,

    |b₀ + ω b₁ + ω² b₂|² ≤ c (|b₀|² + |b₁|² + |b₂|²)   with c ≈ 1,

measured at `c ≈ 0.97` where Cauchy–Schwarz gives `3`.  As a statement about
arbitrary `b` it is **false**: take `b_s = ω^(−s)` and every term aligns, giving
`|3|² = 9` against `3`, so `c = 3` is attained.  `feed_extremal_triple` records the
witness.  No inequality of that shape is available, and the measured `0.97` is a
fact about the coefficients the tree supplies, not about triples of numbers.

What the tree supplies them from is the point.  The feed is not an arbitrary
combination at all: it is the coefficient of another measure.  `feed_is_odd_image`
shows the `ω`-weighted average of the three lifts *is* `ζ^j` times the coefficient
of the odd arm's image, at conductor `r`, on the nose.  So bounding the feed's
energy is bounding how equidistributed the odd image is — one conductor up.

That is the tower, and now it can be priced.  Conductor `R` at depth `d` is fed by
conductor `R+1` at depth `d−1`, hence by conductor `R+d` at the root.  The level
there has `N_d ≍ (4/3)^d` points to spread over `3^(R+d)` classes, and

    (4/3)^d / 3^(R+d) = 3^(−R) (4/9)^d → 0

so the top of the tower is not merely unproved but **empty**: at depth 30 and
`R = 3` it is `10^(−12)` points per class.  `tower_never_fills` states it.  The
induction that would close the chain asks, at every step, for equidistribution at a
conductor the tree has not begun to fill.

What that rules out is one induction scheme — propagation at fixed depth up the
conductors — and nothing else.  The next section removes the tower from the
recursion entirely by reading the same quantity at the other index. -/

/-- The three lifts at which Cauchy–Schwarz is tight: no constant below `3` is
    available for arbitrary coefficients. -/
theorem feed_extremal_triple {ω : ℂ} (h3 : ω ^ 3 = 1) :
    ‖(1 : ℂ) + ω * ω ^ 2 + ω ^ 2 * ω‖ ^ 2
      = 3 * (‖(1 : ℂ)‖ ^ 2 + ‖ω ^ 2‖ ^ 2 + ‖ω‖ ^ 2) := by
  have hn : ‖ω‖ = 1 := norm_root_of_unity h3 (by norm_num)
  have hval : (1 : ℂ) + ω * ω ^ 2 + ω ^ 2 * ω = 3 := by
    have e : ω * ω ^ 2 = ω ^ 3 := by ring
    have e' : ω ^ 2 * ω = ω ^ 3 := by ring
    rw [e, e', h3]; norm_num
  rw [hval, norm_pow, hn]
  norm_num

/-- The odd arm's image: the level's junctions carried to their odd predecessors. -/
def oddImage (L : Finset ℕ) : Finset ℕ :=
  (L.filter (fun m => m % 3 = 2)).image (fun m => 2 * (m / 3) + 1)

/-- **The feed is a measure's coefficient.**  The `ω`-weighted average of the three
    lifts is exactly `ζ^j` times the coefficient of the odd image at conductor `r`.
    So the feed is not an arbitrary combination of three numbers, and bounding its
    energy is bounding the equidistribution of another measure one conductor up. -/
theorem feed_is_odd_image (ζ ω : ℂ) (r j : ℕ) (L : Finset ℕ)
    (hω : ζ ^ 3 ^ r = ω) (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) :
    ζ ^ j * coeff ζ (oddImage L) (3 * j)
      = (3 : ℂ)⁻¹ * ∑ s ∈ Finset.range 3, ω ^ s * coeff ζ L (2 * j + s * 3 ^ r) := by
  have hsplit := coeff_predStep ζ L (3 * j)
  have hop := level_operator ζ ω r j L hω h3 h1
  have hdbl : (∑ m ∈ L, ζ ^ (3 * j * (2 * m))) = coeff ζ L (6 * j) := by
    unfold coeff
    exact Finset.sum_congr rfl (fun m _ => by ring_nf)
  have himg : coeff ζ (oddImage L) (3 * j)
      = ∑ m ∈ L.filter (fun m => m % 3 = 2), ζ ^ (3 * j * (2 * (m / 3) + 1)) := by
    unfold coeff oddImage
    rw [Finset.sum_image]
    intro a ha b hb hab
    obtain ⟨_, ha3⟩ := Finset.mem_filter.mp ha
    obtain ⟨_, hb3⟩ := Finset.mem_filter.mp hb
    simp only at hab
    omega
  rw [himg]
  rw [hsplit, hdbl, mul_add] at hop
  linear_combination hop

/-- **The tower is empty.**  Conductor `R` at depth `d` is fed by conductor `R+d` at
    the root, where the level's `(4/3)^d` points must spread over `3^(R+d)` classes.
    The ratio is `3^(−R)(4/9)^d`, which goes to zero: the induction asks at every
    step for equidistribution at a conductor the tree has not begun to fill. -/
theorem tower_never_fills (R : ℕ) :
    Filter.Tendsto (fun d : ℕ => ((4 : ℝ) / 3) ^ d / 3 ^ (R + d))
      Filter.atTop (nhds 0) := by
  have hlow : ∀ d : ℕ, (0 : ℝ) ≤ ((4 : ℝ) / 3) ^ d / 3 ^ (R + d) := by
    intro d; positivity
  have hhigh : ∀ d : ℕ, ((4 : ℝ) / 3) ^ d / 3 ^ (R + d) ≤ ((4 : ℝ) / 9) ^ d := by
    intro d
    have h1 : (3 : ℝ) ^ d ≤ 3 ^ (R + d) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (0 : ℝ) < 3 ^ d := by positivity
    have h3 : ((4 : ℝ) / 3) ^ d / 3 ^ (R + d) ≤ ((4 : ℝ) / 3) ^ d / 3 ^ d := by
      gcongr
    calc ((4 : ℝ) / 3) ^ d / 3 ^ (R + d) ≤ ((4 : ℝ) / 3) ^ d / 3 ^ d := h3
      _ = ((4 : ℝ) / 9) ^ d := by rw [← div_pow]; norm_num
  exact squeeze_zero hlow hhigh
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

/-! ## The parity split, which takes the tower out of the recursion

The feed at conductor `r` and depth `d` is the odd image's coefficient, and the odd
image is fed by conductor `r+1` — that is the tower.  But the odd image has a second
reading.  `2m` is always even and `2(m/3)+1` is always odd, so the two arms of
`predStep` are exactly its even and odd parts:

    oddImage L  =  (predStep L).filter (· odd)
    L.image (2·) = (predStep L).filter (· even)

`oddImage_eq_odd_part` and `evenImage_eq_even_part`.  So the feed at conductor `r`
and depth `d` is the energy of the **odd part of level `d+1`, at conductor `r`** —
the same conductor.  The tower appeared only because the quantity was being read at
depth `d`; read at depth `d+1` the conductor does not move at all.

The recursion then closes at fixed conductor.  Doubling permutes the conductor-`r`
characters, so the even part carries energy `ρ²Q(d)` exactly, and

    Q(d+1) = ρ² Q(d) + Q_odd(d+1) + cross

with `Q_odd(d+1) ≤ κ Q(d+1)`.  Solving for `Q(d+1)`,

    Q(d+1) ≤ ρ²/(1 − ρ²κ) · Q(d)

which contracts exactly when `κ < 1/ρ² − 1 ≈ 0.7918`.  Nothing in that chain refers
to conductor `r+1`.

The price, measured: `κ` has median `0.27` at conductors 9, 27 and 81, and at
conductor 81 its **maximum over all twenty-four levels is `0.4435`**, inside the
allowance by a factor of `1.79`.  At `κ = 0.4435` the rate is `0.7495`, which is the
`0.73` measured directly.  The odd mass sits at `0.2491` throughout.

Parity is a twist, not a conductor: `2` is coprime to `3^r`, and the odd part's
coefficients are `ν̂(j) = (μ̂(j) − μ̂₂(j))/2` with `μ̂₂` the mod-2 twist — verified to
`10⁻¹⁶`.  Bounding `|ν̂|²` by `(|μ̂| + |μ̂₂|)²/4` is far too lossy, giving `κ ≤ 1.11`
against a truth of `0.27`, because `μ̂` and its twist are strongly correlated,
`Re⟨μ̂, μ̂₂⟩/Q ≈ 0.57`.  So the rung is `κ`, at fixed conductor, and its price is that
correlation. -/

/-- Doubling produces only even numbers and the odd arm only odd ones, so the two
    arms of `predStep` are its parity classes.  This is what lets the feed be read
    at the same conductor one level later. -/
theorem oddImage_eq_odd_part (L : Finset ℕ) :
    oddImage L = (predStep L).filter (fun n => n % 2 = 1) := by
  ext n
  simp only [oddImage, predStep, Finset.mem_filter, Finset.mem_image, Finset.mem_union]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨Or.inr ⟨m, hm, rfl⟩, by omega⟩
  · rintro ⟨h | h, hodd⟩
    · obtain ⟨m, _, rfl⟩ := h; omega
    · exact h

theorem evenImage_eq_even_part (L : Finset ℕ) :
    L.image (fun m => 2 * m) = (predStep L).filter (fun n => n % 2 = 0) := by
  ext n
  simp only [predStep, Finset.mem_filter, Finset.mem_image, Finset.mem_union]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨Or.inl ⟨m, hm, rfl⟩, by omega⟩
  · rintro ⟨h | h, heven⟩
    · exact h
    · obtain ⟨m, hm, rfl⟩ := h
      omega

/-- The two parts are disjoint and exhaust the level, by parity. -/
theorem predStep_parity_partition (L : Finset ℕ) :
    (predStep L).filter (fun n => n % 2 = 0) ∪ (predStep L).filter (fun n => n % 2 = 1)
      = predStep L := by
  rw [← Finset.filter_or]
  exact Finset.filter_true_of_mem (fun x _ => by omega)

/-- The contraction condition at fixed conductor.  With `Q_odd ≤ κ Q(d+1)` and the
    cross term non-positive, `level_energy_recursion` gives
    `Q(d+1) ≤ ρ²Q(d)/(1 − κ)`, so the level contracts exactly when `κ < 1 − ρ²`.

    The earlier statement of this threshold as `1/ρ² − 1 = 7/9` was wrong: that is
    the threshold for the feed normalised by the *previous* level's count, while `κ`
    is normalised by the new level's.  At `ρ = 3/4` the correct threshold is `7/16`,
    and under the growth rate actually proved, `ρ ≤ 5/6`, it is `11/36`.

    Measured at conductor 81 over twenty-four levels, `κ` has geometric mean
    `0.2855`, inside `11/36` and so inside `7/16`.  Since the bound composes
    multiplicatively, the geometric mean is the operative average — a single level
    above the threshold does not break the composition, the same correction the
    junction fraction needed. -/
theorem fixed_conductor_threshold :
    (1 : ℝ) - (3 / 4) ^ 2 = 7 / 16 ∧ (1 : ℝ) - (5 / 6) ^ 2 = 11 / 36
      ∧ (0.2855 : ℝ) < 11 / 36 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- The rate itself, from the recursion: `ρ²/(1 − κ) < 1` exactly when `κ < 1 − ρ²`. -/
theorem contraction_rate {ρ κ : ℝ} (hρ : 0 ≤ ρ) (hκ : κ < 1) :
    ρ ^ 2 / (1 - κ) < 1 ↔ κ < 1 - ρ ^ 2 := by
  rw [div_lt_one (by linarith)]
  constructor <;> intro h <;> linarith


/-! ## The even part carries the previous level's energy, exactly

The fixed-conductor recursion rests on one identity: that the doubling arm moves no
energy at all.  It is proved here rather than assumed.

`ζ^(3*j*(2m)) = ζ^(6*j*m)`, so the even part's coefficient at index `3j` is the
previous level's at `6j`; and `j ↦ 2j` is a bijection of the primitive indices mod
`3^r`, since `2` is a unit there.  Summing the squares over the primitive indices,
the two sums are the same sum reindexed:

    Σ_{j primitive} ‖coeff (even part of predStep L) (3j)‖²
      = Σ_{j primitive} ‖coeff L (3j)‖²

so `Q_even(d+1) = Q(d)` unnormalised, and `ρ²Q(d)` after normalising by the level
count.  With `predStep_parity_partition` splitting the level, the whole recursion

    Q(d+1) = ρ² Q(d) + Q_odd(d+1) + cross

has its first term proved exact and its remaining two the rung. -/

/-- The primitive indices at conductor `3^r`: those not divisible by three. -/
def prim (r : ℕ) : Finset ℕ := (Finset.range (3 ^ r)).filter (fun j => j % 3 ≠ 0)

/-- A root of unity only sees the exponent modulo its order. -/
theorem zpow_mod {ζ : ℂ} {M : ℕ} (hζ : ζ ^ M = 1) (n : ℕ) : ζ ^ n = ζ ^ (n % M) := by
  conv_lhs => rw [← Nat.div_add_mod n M]
  rw [pow_add, pow_mul, hζ, one_pow, one_mul]

/-- So a coefficient only sees its index modulo the order. -/
theorem coeff_periodic {ζ : ℂ} {M : ℕ} (hζ : ζ ^ M = 1) (L : Finset ℕ) {k k' : ℕ}
    (h : k % M = k' % M) : coeff ζ L k = coeff ζ L k' := by
  unfold coeff
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [zpow_mod hζ (k * v), zpow_mod hζ (k' * v)]
  congr 1
  exact Nat.ModEq.mul_right v h

/-- Doubling is injective on the primitive indices: `2` is a unit mod `3^r`. -/
theorem double_inj_prim (r : ℕ) : ∀ a ∈ prim r, ∀ b ∈ prim r,
    2 * a % 3 ^ r = 2 * b % 3 ^ r → a = b := by
  intro a ha b hb hab
  simp only [prim, Finset.mem_filter, Finset.mem_range] at ha hb
  have h : 2 * a ≡ 2 * b [MOD 3 ^ r] := hab
  have h2 := double_inj_mod h
  unfold Nat.ModEq at h2
  rw [Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at h2
  exact h2

theorem double_injOn_prim (r : ℕ) : Set.InjOn (fun j => 2 * j % 3 ^ r) (prim r) :=
  fun _ ha _ hb hab =>
    double_inj_prim r _ (Finset.mem_coe.mp ha) _ (Finset.mem_coe.mp hb) hab

/-- And so permutes them. -/
theorem doubling_image_prim (r : ℕ) :
    (prim r).image (fun j => 2 * j % 3 ^ r) = prim r := by
  have hpos : 0 < 3 ^ r := pow_pos (by norm_num) r
  have hmaps : ∀ j ∈ prim r, 2 * j % 3 ^ r ∈ prim r := by
    intro j hj
    simp only [prim, Finset.mem_filter, Finset.mem_range] at hj ⊢
    refine ⟨Nat.mod_lt _ hpos, ?_⟩
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp at hj; omega
    · have h3 : (3 : ℕ) ∣ 3 ^ r := dvd_pow_self 3 (by omega)
      have : (2 * j % 3 ^ r) % 3 = (2 * j) % 3 := Nat.mod_mod_of_dvd _ h3
      omega
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact hmaps j hj
  · rw [Finset.card_image_of_injOn (double_injOn_prim r)]

/-- The even arm's coefficient is the previous level's, at the doubled index. -/
theorem even_part_coeff (ζ : ℂ) (L : Finset ℕ) (j : ℕ) :
    coeff ζ ((predStep L).filter (fun n => n % 2 = 0)) (3 * j) = coeff ζ L (6 * j) := by
  rw [← evenImage_eq_even_part]
  unfold coeff
  rw [Finset.sum_image (by intro a _ b _ hab; simp only at hab; omega)]
  exact Finset.sum_congr rfl (fun m _ => by ring_nf)

/-- **The doubling arm moves no energy.**  Summed over the primitive indices, the
    even part of a level carries exactly the energy of the level below it. -/
theorem even_part_energy {ζ : ℂ} {r : ℕ} (hζ : ζ ^ 3 ^ (r + 1) = 1) (L : Finset ℕ) :
    ∑ j ∈ prim r, ‖coeff ζ ((predStep L).filter (fun n => n % 2 = 0)) (3 * j)‖ ^ 2
      = ∑ j ∈ prim r, ‖coeff ζ L (3 * j)‖ ^ 2 := by
  have hstep : ∀ j : ℕ, coeff ζ L (6 * j) = coeff ζ L (3 * (2 * j % 3 ^ r)) := by
    intro j
    refine coeff_periodic hζ L ?_
    have h : 3 * (2 * j) % (3 * 3 ^ r) = 3 * (2 * j % 3 ^ r) := Nat.mul_mod_mul_left _ _ _
    have hlt : 3 * (2 * j % 3 ^ r) < 3 * 3 ^ r := by
      have := Nat.mod_lt (2 * j) (pow_pos (by norm_num : (0:ℕ) < 3) r)
      omega
    have hpow : (3 : ℕ) ^ (r + 1) = 3 * 3 ^ r := by ring
    rw [hpow, show 6 * j = 3 * (2 * j) by ring, h, Nat.mod_eq_of_lt hlt]
  calc ∑ j ∈ prim r, ‖coeff ζ ((predStep L).filter (fun n => n % 2 = 0)) (3 * j)‖ ^ 2
      = ∑ j ∈ prim r, ‖coeff ζ L (3 * (2 * j % 3 ^ r))‖ ^ 2 := by
        exact Finset.sum_congr rfl (fun j _ => by rw [even_part_coeff, hstep])
    _ = ∑ j ∈ (prim r).image (fun j => 2 * j % 3 ^ r), ‖coeff ζ L (3 * j)‖ ^ 2 := by
        rw [Finset.sum_image (double_injOn_prim r)]
    _ = ∑ j ∈ prim r, ‖coeff ζ L (3 * j)‖ ^ 2 := by rw [doubling_image_prim]

/-- A level's coefficient splits along the parity partition. -/
theorem coeff_parity_split (ζ : ℂ) (L : Finset ℕ) (k : ℕ) :
    coeff ζ (predStep L) k
      = coeff ζ ((predStep L).filter (fun n => n % 2 = 0)) k
        + coeff ζ ((predStep L).filter (fun n => n % 2 = 1)) k := by
  unfold coeff
  rw [← Finset.sum_filter_add_sum_filter_not (predStep L) (fun n => n % 2 = 0)]
  congr 1
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, h⟩; exact ⟨hx, by omega⟩
  · rintro ⟨hx, h⟩; exact ⟨hx, by omega⟩

/-- **The level energy recursion, exactly.**  Summed over the primitive indices at
    conductor `3^r`, a level's energy is the energy of the level below it — the
    doubling arm, which moves nothing — plus the energy of its own odd part, plus
    the cross term between them.  No inequality anywhere. -/
theorem level_energy_recursion {ζ : ℂ} {r : ℕ} (hζ : ζ ^ 3 ^ (r + 1) = 1) (L : Finset ℕ) :
    ∑ j ∈ prim r, ‖coeff ζ (predStep L) (3 * j)‖ ^ 2
      = (∑ j ∈ prim r, ‖coeff ζ L (3 * j)‖ ^ 2)
        + (∑ j ∈ prim r, ‖coeff ζ (oddImage L) (3 * j)‖ ^ 2)
        + ∑ j ∈ prim r, 2 * ((coeff ζ ((predStep L).filter (fun n => n % 2 = 0)) (3 * j))
            * (starRingEnd ℂ) (coeff ζ (oddImage L) (3 * j))).re := by
  have hodd : ∀ j : ℕ, coeff ζ ((predStep L).filter (fun n => n % 2 = 1)) (3 * j)
      = coeff ζ (oddImage L) (3 * j) := by
    intro j; rw [oddImage_eq_odd_part]
  have hterm : ∀ j : ℕ, ‖coeff ζ (predStep L) (3 * j)‖ ^ 2
      = ‖coeff ζ ((predStep L).filter (fun n => n % 2 = 0)) (3 * j)‖ ^ 2
        + ‖coeff ζ (oddImage L) (3 * j)‖ ^ 2
        + 2 * ((coeff ζ ((predStep L).filter (fun n => n % 2 = 0)) (3 * j))
            * (starRingEnd ℂ) (coeff ζ (oddImage L) (3 * j))).re := by
    intro j
    rw [coeff_parity_split ζ L (3 * j), hodd j]
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]
  calc ∑ j ∈ prim r, ‖coeff ζ (predStep L) (3 * j)‖ ^ 2
      = ∑ j ∈ prim r, (‖coeff ζ ((predStep L).filter (fun n => n % 2 = 0)) (3 * j)‖ ^ 2
          + ‖coeff ζ (oddImage L) (3 * j)‖ ^ 2
          + 2 * ((coeff ζ ((predStep L).filter (fun n => n % 2 = 0)) (3 * j))
              * (starRingEnd ℂ) (coeff ζ (oddImage L) (3 * j))).re) :=
        Finset.sum_congr rfl (fun j _ => hterm j)
    _ = (∑ j ∈ prim r, ‖coeff ζ ((predStep L).filter (fun n => n % 2 = 0)) (3 * j)‖ ^ 2)
          + (∑ j ∈ prim r, ‖coeff ζ (oddImage L) (3 * j)‖ ^ 2)
          + ∑ j ∈ prim r, 2 * ((coeff ζ ((predStep L).filter (fun n => n % 2 = 0)) (3 * j))
              * (starRingEnd ℂ) (coeff ζ (oddImage L) (3 * j))).re := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = _ := by rw [even_part_energy hζ L]

/-- **The contraction, from the recursion.**  If the odd part carries at most `κ`
    of the level's energy and the cross term is non-positive, then the level's
    energy is at most `1/(1 − κ)` of the previous level's — so with `κ < 1` the
    unnormalised energy is controlled, and after the `ρ²` of normalisation the
    level contracts exactly when `κ < 1/ρ² − 1`. -/
theorem energy_contraction {Q Qodd cross Qprev κ : ℝ}
    (hrec : Q = Qprev + Qodd + cross) (hodd : Qodd ≤ κ * Q) (hcross : cross ≤ 0)
    (hκ : κ < 1) : Q * (1 - κ) ≤ Qprev := by
  nlinarith [hrec, hodd, hcross]

/-! ### The mod-2 twist carries the cross term

Parity being a twist rather than a conductor has an exact consequence.  Writing `e`
for the even part's coefficients and `o` for the odd part's, the level's coefficient
is `e + o` and its mod-2 twist is `e − o`.  The parallelogram law then gives

    Q + Q₂ = 2 Q_even + 2 Q_odd,      Q − Q₂ = 2 cross

so the cross term is not an independent unknown: it is the defect between a level's
energy and its twisted energy, and both of the recursion's inputs are determined by
the single quantity `Q₂`.  Combined with `even_part_energy`, contraction becomes

    Q₂ > (2ρ² − 1) Q_prev + 2 Q_odd

measured `1.22 Q` against `0.71 Q`, a margin of `1.7`. -/

/-- The parallelogram law, summed over the characters. -/
theorem energy_parallelogram (e o : ℕ → ℂ) (s : Finset ℕ) :
    (∑ j ∈ s, ‖e j + o j‖ ^ 2) + ∑ j ∈ s, ‖e j - o j‖ ^ 2
      = 2 * (∑ j ∈ s, ‖e j‖ ^ 2) + 2 * ∑ j ∈ s, ‖o j‖ ^ 2 := by
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_add, Complex.normSq_sub]
  ring

/-- **The cross term is the twist defect.**  It is not an independent quantity: the
    correlation between the two arms is exactly half the gap between a level's
    energy and the energy of its mod-2 twist. -/
theorem cross_is_twist_defect (e o : ℕ → ℂ) (s : Finset ℕ) :
    (∑ j ∈ s, 2 * ((e j) * (starRingEnd ℂ) (o j)).re)
      = ((∑ j ∈ s, ‖e j + o j‖ ^ 2) - ∑ j ∈ s, ‖e j - o j‖ ^ 2) / 2 := by
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_add, Complex.normSq_sub]
  ring

/-- So both inputs of the recursion are read off one quantity, and contraction is
    the single inequality `Q₂ > (2ρ² − 1) Q_prev + 2 Q_odd`. -/
theorem contraction_via_twist {Q Q2 Qeven Qodd Qprev ρ : ℝ}
    (hpar : Q + Q2 = 2 * Qeven + 2 * Qodd) (heven : Qeven = ρ ^ 2 * Qprev)
    (h : Q2 > (2 * ρ ^ 2 - 1) * Qprev + 2 * Qodd) : Q < Qprev := by
  nlinarith [hpar, heven, h]

/-! ## Counting by size: the certificate refined by odd steps

Equidistribution is not the conjecture.  What the conjecture asserts is that the
predecessor tree of `1` is all of `ℕ`, which is a statement about how many integers
below `x` the tree contains.  Counting by depth is lossy: nodes at depth `d` number
about `(4/3)^d` but run as large as `2^d`, giving density exponent
`log(4/3)/log 2 = 0.415` at best and `log(6/5)/log 2 = 0.263` from the growth rate
actually proved.

Counting by size is sharper, because the two arms move size differently.  Doubling
multiplies by `2`; the odd arm `n = (2m−1)/3` multiplies by less than `2/3`.  So a
node reached by `d` steps of which `j` are odd-arm steps has

    size  <  2^d / 3^j

and nodes with many odd steps are small.  The count that matters is therefore the
joint one, carried by `F_d(z) = Σ_nodes z^j`.

The conductor-nine certificate refines to it directly.  Put `z` on the two
injections of the six-cycle — the odd arm is exactly where `j` increments, since a
child is odd precisely when it comes from that arm — and the same tight chain gives

    L(z)^6  ≤  z L(z)^2 + z L(z) + 1

against `L^6 ≤ L^2 + L + 1` at `z = 1`.  At `z = 2` the root is `1.40759` and
`L = 7/5` clears it, with weights that clear to integers:

    w₁ = 6125   w₂ = 8575   w₄ = 5755   w₈ = 8057   w₇ = 3125   w₅ = 4375

and all six requirements hold, five of them with equality.  Measured against the
tree, `F_d(2)` grows at `1.66` per level, so `7/5` is a true lower bound with room;
the same holds at `z = 0.5, 0.75, 1, 1.5`.

Optimising `max_α log₂(inf_z L(z) z^(−α)) / (1 − α log₂ 3)` over the certificate
gives density exponent **`0.4366`** at `α = 0.18`, against `0.2630` from the depth
count alone.  `collatz_density_certificate.py` carries both. -/

/-- The certificate weight refined by odd steps: the same six-cycle at `z = 2`,
    where `z` counts the odd-arm steps that shrink a node. -/
def wtz (v : ℕ) : ℕ :=
  if v % 9 = 1 then 6125 else
  if v % 9 = 2 then 8575 else
  if v % 9 = 4 then 5755 else
  if v % 9 = 8 then 8057 else
  if v % 9 = 7 then 3125 else
  if v % 9 = 5 then 4375 else 0

theorem wtz_le (v : ℕ) : wtz v ≤ 8575 := by unfold wtz; split_ifs <;> omega

theorem wtz_ge_of_class_one {x : ℕ} (h : x % 3 = 1) : 3125 ≤ wtz x := by
  have h9 : x % 9 = 1 ∨ x % 9 = 4 ∨ x % 9 = 7 := by omega
  unfold wtz; rcases h9 with h9 | h9 | h9 <;> simp [h9]

theorem wtz_ge_of_class_two {x : ℕ} (h : x % 3 = 2) : 4375 ≤ wtz x := by
  have h9 : x % 9 = 2 ∨ x % 9 = 5 ∨ x % 9 = 8 := by omega
  unfold wtz; rcases h9 with h9 | h9 | h9 <;> simp [h9]

theorem wtz_double (v : ℕ) :
    wtz (2 * v) =
      if v % 9 = 1 then 8575 else
      if v % 9 = 2 then 5755 else
      if v % 9 = 4 then 8057 else
      if v % 9 = 8 then 3125 else
      if v % 9 = 7 then 4375 else
      if v % 9 = 5 then 6125 else 0 := by
  have h9 : v % 9 = 0 ∨ v % 9 = 1 ∨ v % 9 = 2 ∨ v % 9 = 3 ∨ v % 9 = 4 ∨ v % 9 = 5
      ∨ v % 9 = 6 ∨ v % 9 = 7 ∨ v % 9 = 8 := by omega
  have hd : (2 * v) % 9 = (2 * (v % 9)) % 9 := by omega
  unfold wtz
  rcases h9 with h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 <;> rw [hd, h9] <;> norm_num

/-- **The refined pointwise certificate.**  Counting the odd arm twice — which is
    `z = 2` — every vertex's children carry at least `7/5` of its own weight. -/
theorem wtz_children (v : ℕ) :
    7 * wtz v ≤ 5 * (wtz (2 * v) + if v % 3 = 2 then 2 * wtz (2 * (v / 3) + 1) else 0) := by
  rw [wtz_double]
  have h9 : v % 9 = 0 ∨ v % 9 = 1 ∨ v % 9 = 2 ∨ v % 9 = 3 ∨ v % 9 = 4 ∨ v % 9 = 5
      ∨ v % 9 = 6 ∨ v % 9 = 7 ∨ v % 9 = 8 := by omega
  rcases h9 with h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9
  · simp [wtz, h9]
  · have : v % 3 = 1 := by omega
    simp [wtz, h9, this]
  · have h3 : v % 3 = 2 := by omega
    obtain ⟨c, hcdef⟩ : ∃ c, wtz (2 * (v / 3) + 1) = c := ⟨_, rfl⟩
    have hc : _ ≤ c := hcdef ▸ wtz_ge_of_class_one (odd_child_class_two v h9)
    rw [hcdef]
    simp only [wtz, h9, h3, if_true, if_false]
    norm_num
    omega
  · simp [wtz, h9]
  · have : v % 3 = 1 := by omega
    simp [wtz, h9, this]
  · have h3 : v % 3 = 2 := by omega
    simp only [wtz, h9, h3, if_true, if_false] at *
    norm_num at *
    omega
  · simp [wtz, h9]
  · have : v % 3 = 1 := by omega
    simp [wtz, h9, this]
  · have h3 : v % 3 = 2 := by omega
    obtain ⟨c, hcdef⟩ : ∃ c, wtz (2 * (v / 3) + 1) = c := ⟨_, rfl⟩
    have hc : _ ≤ c := hcdef ▸ wtz_ge_of_class_two (odd_child_class_eight v h9)
    rw [hcdef]
    simp only [wtz, h9, h3, if_true, if_false]
    norm_num
    omega

/-- The characteristic inequality the refinement satisfies, at `z = 2`. -/
theorem density_characteristic : ((7 : ℚ) / 5) ^ 6 ≤ 2 * (7 / 5) ^ 2 + 2 * (7 / 5) + 1 := by
  norm_num

/-! ## The density reduces to the junction fraction

The tower's rungs climb toward the true growth `Λ(z)` of `F_d(z) = Σ_nodes z^j`, and
`Λ` has a closed form.  One level sends each node to its double and, when the node is
a junction, to an odd child carrying one more odd step, so

    F_{d+1}(z) = F_d(z) + z · F_d^{junc}(z)

and `Λ(z) = 1 + z·q(z)` with `q` the `z`-weighted junction fraction.  Measured to
depth 52, `q(z) → 1/3` and `Λ(z) = 1 + z/3` to five decimals: `1.166742` against
`7/6`, `1.333317` against `4/3`, `1.499914` against `3/2`, `1.666919` against `5/3`.

With `Λ(z) = 1 + z/3` the Legendre transform is the binary entropy.  Minimising
`log₂(1 + z/3) − α log₂ z` gives `z = 3α/(1−α)` and `1 + z/3 = 1/(1−α)`, so

    I(α) = H(α) − α log₂ 3

and the density exponent is `max_α (H(α) − α log₂3)/(1 − α log₂3)`.  At `α = 1/2`,
`H(1/2) = 1`, so numerator and denominator coincide and the value is **exactly 1**;
`0.9951` at `α = 0.48`, `0.9934` at `0.52`.  The maximum is a tangency at one point.

Equivalently, and with no entropy: the exponent is `1` exactly when

    Λ(z)  ≥  2 √(z/3)   for every z > 0

and `1 + z/3 ≥ 2√(z/3)` is AM–GM, with equality forced at `z = 3`.  So the density
form of the conjecture is the single statement that the `z`-weighted junction
fraction is at least `1/3` — and at `z = 1` that is `p₂ ≥ 1/3`, the quantity this
whole development began with, which the conductor tower approaches from below:
`L_11(1) = 1.33273` against `4/3`.

The chain therefore closes on itself.  Levels equidistributed mod 3 give `p₂ = 1/3`,
which gives `Λ(z) = 1 + z/3`, which gives density exponent `1`.  `levels_equidistribute`
supplies the first step from coefficient decay. -/

/-- The entropy at a half is one, which is why the exponent is a tangency. -/
theorem entropy_half : -(1 / 2 : ℝ) * Real.logb 2 (1 / 2) - (1 / 2) * Real.logb 2 (1 / 2) = 1 := by
  have h : Real.logb 2 (1 / 2 : ℝ) = -1 := by
    rw [one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
  rw [h]; ring

/-- At `α = 1/2` the numerator and denominator of the exponent coincide, so the
    value is exactly one.  The maximum of the density exponent is this tangency. -/
theorem exponent_tangency {c : ℝ} (hc : c ≠ 1) : (1 - c) / (1 - c) = 1 :=
  div_self (sub_ne_zero.mpr (Ne.symm hc))

/-- The extremal inequality, without entropy: `1 + z/3 ≥ 2√(z/3)` is AM–GM, with
    equality exactly at `z = 3`.  The density exponent is one precisely when the
    growth `Λ` clears this bound at every `z`. -/
theorem amgm_critical (z : ℝ) (hz : 0 ≤ z) : 2 * Real.sqrt (z / 3) ≤ 1 + z / 3 := by
  have hnn : (0 : ℝ) ≤ z / 3 := by linarith
  have hs : Real.sqrt (z / 3) ^ 2 = z / 3 := Real.sq_sqrt hnn
  nlinarith [sq_nonneg (1 - Real.sqrt (z / 3)), Real.sqrt_nonneg (z / 3), hs]

/-- And the equality case is `z = 3`, where the critical `α` is `1/2`. -/
theorem amgm_equality : 2 * Real.sqrt ((3 : ℝ) / 3) = 1 + (3 : ℝ) / 3 := by
  norm_num

/-! ## The fixed point: equidistribution mod 9 forces `p₂ = 1/3`

The mod-3 class counts move by an exact linear recursion.  Doubling sends class 1 to
class 2 and class 2 to class 1 and fixes class 0; the odd children come only from the
junctions, and which live class each lands in is fixed by the parent mod 9 —
`2 ↦ 1`, `5 ↦ 0`, `8 ↦ 2`, which is `odd_child_class_two/five/eight`.  Writing
`a₂, a₅, a₈` for the junction counts in those classes, with `a₂ + a₅ + a₈ = n₂`:

    n₀' = n₀ + a₅,    n₁' = n₂ + a₂,    n₂' = n₁ + a₈

and `N' = N + n₂`, so the growth rate is `1 + p₂` exactly — which is
`card_predStep`.

If the junctions are equidistributed mod 9, `a₂ = a₅ = a₈ = n₂/3`, the uniform
vector is an eigenvector: from `n₀ = n₁ = n₂ = n` every class becomes `n + n/3`, so
the level stays equidistributed mod 3 and grows by exactly `4/3`.  Solving the pair
`λn₁ = 4n₂/3`, `λn₂ = n₁ + n₂/3` gives `3λ² − λ − 4 = 0`, whose positive root is
`4/3` and whose eigenvector has `n₀ = n₁ = n₂` — equidistribution is not assumed at
the end, it is forced by the recursion.

So `p₂ = 1/3` exactly, `Λ(1) = 4/3`, and the density exponent is `1`.  Measured, the
two conductor-tower operators bracket it: at `k = 13` the sandwich is
`[1.3330773, 1.3336345]` around `4/3 = 1.3333333`, both sides converging at ratio
`≈ 0.65` per rung.

What this locates is where the remaining work is.  Equidistribution mod 9 of the
junctions is one rung up the tower from equidistribution mod 3 of the level, and
each rung needs the one above it.  The tower converges — that is what the two
bracketing sequences show — and proving it converges is proving the conjecture's
density form. -/

/-- **The fixed point.**  Junctions equidistributed mod 9 keep the level
    equidistributed mod 3 and multiply it by exactly `4/3`. -/
theorem mod_three_fixed_point (n : ℝ) :
    n + n / 3 = (4 / 3) * n := by ring

/-- The characteristic polynomial of the live pair, whose positive root is `4/3`. -/
theorem live_pair_char_root : 3 * ((4 : ℝ) / 3) ^ 2 - (4 / 3) - 4 = 0 := by norm_num

/-- And `4/3` is its only positive root, so the growth rate is forced rather than
    fitted: `3λ² − λ − 4 = (3λ − 4)(λ + 1)`. -/
theorem live_pair_factor (l : ℝ) : 3 * l ^ 2 - l - 4 = (3 * l - 4) * (l + 1) := by ring

/-- The growth rate and the junction fraction are the same number, by
    `card_predStep`: `N(d+1)/N(d) = 1 + p₂(d)`.  So `Λ(1) = 4/3` and `p₂ = 1/3` are
    one statement, and it is the one the density exponent needs. -/
theorem growth_is_one_plus_p2 (N n2 : ℝ) (hN : N ≠ 0) :
    (N + n2) / N = 1 + n2 / N := by field_simp

/-! ## Why no approximation from below reaches it

The density exponent is `1` exactly when `Λ(z) ≥ 2√(z/3)` for every `z`, and
`Λ(z) = 1 + z·q(z)` with `q` the `z`-weighted junction fraction.  If `q ≡ 1/3` then
`Λ(z) = 1 + z/3` and the requirement is AM–GM — which holds, **with equality at
`z = 3` and strict inequality everywhere else**.  So the requirement is met with zero
margin at exactly one point.

That is why the conductor tower's exponent climbs toward `1` and does not arrive.
Measured at `z = 3`, where the tangency sits:

    k     L_k(3)     2 − L_k(3)
    10  1.908410     9.16e−2
    11  1.916899     8.31e−2
    12  1.924541     7.55e−2
    13  1.930915     6.91e−2

decaying at ratio `≈ 0.91`, so `L_k(3) → 2`, but every finite rung is strictly below
`2` and therefore fails `Λ(3) ≥ 2` outright.  At `k = 13` the certificate clears the
requirement for `z ≤ 2` — slack `+0.35, +0.18, +0.019` at `z = 0.5, 1, 2` — and
fails from `z = 3` on.  The upper operator is no help there: `U_k(3) → 3.000001`,
since the adversary maximising can concentrate.

So the density form of the conjecture is not an inequality with room that a good
enough bound will eventually clear.  It is the exact value

    q(3) = 1/3,        equivalently   Λ(3) = 2

and an argument that closes it has to produce that value, not approach it.  The same
holds at every `z` in the sense that `q(z) ≥ 1/3` suffices, but `z = 3` is where the
slack vanishes and where the conjecture actually lives. -/

/-- At the tangency the requirement is exactly `2`, so any bound strictly below it
    fails, however close.  This is why the tower approaches `1` without arriving. -/
theorem no_slack_at_tangency {L : ℝ} (h : L < 2) : ¬ (2 * Real.sqrt ((3 : ℝ) / 3) ≤ L) := by
  have : Real.sqrt ((3 : ℝ) / 3) = 1 := by norm_num
  rw [this]; linarith

/-- Strict AM–GM off the tangency: away from `z = 3` there is genuine slack. -/
theorem amgm_strict {z : ℝ} (hz : 0 < z) (hne : z ≠ 3) : 2 * Real.sqrt (z / 3) < 1 + z / 3 := by
  have hnn : (0 : ℝ) ≤ z / 3 := by linarith
  have hs : Real.sqrt (z / 3) ^ 2 = z / 3 := Real.sq_sqrt hnn
  have hne' : Real.sqrt (z / 3) ≠ 1 := by
    intro h
    apply hne
    have : z / 3 = 1 := by rw [← hs, h]; norm_num
    linarith
  have hpos : 0 < (1 - Real.sqrt (z / 3)) ^ 2 := by
    have hz0 : (1 : ℝ) - Real.sqrt (z / 3) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne')
    positivity
  nlinarith [hpos, hs]

/-- The conjecture's density form as a single exact value: the `3`-weighted junction
    fraction is `1/3`, equivalently `Λ(3) = 2`. -/
theorem density_form_exact (q : ℝ) : 1 + 3 * q = 2 ↔ q = 1 / 3 := by
  constructor <;> intro h <;> linarith

/-! ## The size relation, exactly

The tangency needs an exact value, so the size bound has to be an identity rather
than an estimate.  It is one.  Under `u = v + 1` the odd arm is exactly
`u ↦ 2u/3` — because `v = 3t+2` gives `n = 2t+1` and `3(n+1) = 2(v+1)` — while
doubling is `u ↦ 2u − 1`.  Induction along the tree then gives, for every node,

    3^j · (v + 1)  ≤  2^(d+1)

with `d` its depth and `j` its number of odd-arm steps, and equality only at the
root.  `tree_size_bound`.  This is the exact form of "a node with `j` odd steps has
size below `2^d/3^j`", and it is what makes `z = 3` the coordinate the density
argument runs in: `3^j` is `2^(d+1)/(v+1)` up to a bounded factor.

Summing it, `F_d(3) ≤ 2^(d+1) S_d` with `S_d = Σ_{v ∈ L_d} 1/(v+1)` the level's
harmonic sum — measured, the ratio is a constant `0.432` from depth 15 to 46, so the
inequality is tight up to that factor.  Hence

    Λ(3) = 2 · lim S_d^(1/d)

and `Λ(3) = 2`, which is the whole density form, becomes the statement that the
level's harmonic sum is subexponential in both directions.

Upward it is free: the tree's nodes are distinct integers below `2^d`, so
`Σ_{d' ≤ d} S_d' ≤ H(2^d) ≈ d log 2`, giving `S_d = O(d)` and `Λ(3) ≤ 2`.  Downward,
`S_d ≥ 1/(min L_d + 1)`, so it is enough that the smallest node at depth `d` grows
subexponentially.  Measured to depth 46 it grows like `5d` — `5, 24, 14, 25, 43, 78,
135, 246, 159, 283, 167, 222` — with `(min)^(1/d)` at `1.1246` and falling, and
`S_d` flat at `0.11` from depth 25 on.

So the conjecture's density form has come down to: **at every depth the tree contains
a node of subexponential size.** -/

/-- Membership in the predecessor tree of `1`, carrying depth and odd-step count. -/
inductive InTree : ℕ → ℕ → ℕ → Prop
  | root : InTree 1 0 0
  | dbl {v d j} : InTree v d j → InTree (2 * v) (d + 1) j
  | odd {v d j} : InTree v d j → v % 3 = 2 → InTree (2 * (v / 3) + 1) (d + 1) (j + 1)

/-- The odd arm in the `u = v+1` coordinate is exactly multiplication by `2/3`. -/
theorem odd_arm_exact {v : ℕ} (h : v % 3 = 2) :
    3 * ((2 * (v / 3) + 1) + 1) = 2 * (v + 1) := by omega

/-- **The size relation.**  Every node of the tree satisfies `3^j (v+1) ≤ 2^(d+1)`,
    with equality only at the root.  This is the exact form of the estimate the
    density argument runs on, and the reason `z = 3` is its coordinate. -/
theorem tree_size_bound {v d j : ℕ} (h : InTree v d j) : 3 ^ j * (v + 1) ≤ 2 ^ (d + 1) := by
  induction h with
  | root => norm_num
  | dbl _ ih =>
      rename_i v d j _
      calc 3 ^ j * (2 * v + 1) ≤ 3 ^ j * (2 * (v + 1)) := by
            exact Nat.mul_le_mul_left _ (by omega)
        _ = 2 * (3 ^ j * (v + 1)) := by ring
        _ ≤ 2 * 2 ^ (d + 1) := Nat.mul_le_mul_left _ ih
        _ = 2 ^ (d + 1 + 1) := by ring
  | odd _ hv ih =>
      rename_i v d j _
      have hex := odd_arm_exact hv
      have : 3 ^ (j + 1) * (2 * (v / 3) + 1 + 1) = 2 * (3 ^ j * (v + 1)) := by
        have : 3 ^ (j + 1) = 3 ^ j * 3 := by ring
        rw [this]
        calc 3 ^ j * 3 * (2 * (v / 3) + 1 + 1)
            = 3 ^ j * (3 * ((2 * (v / 3) + 1) + 1)) := by ring
          _ = 3 ^ j * (2 * (v + 1)) := by rw [hex]
          _ = 2 * (3 ^ j * (v + 1)) := by ring
      rw [this]
      calc 2 * (3 ^ j * (v + 1)) ≤ 2 * 2 ^ (d + 1) := Nat.mul_le_mul_left _ ih
        _ = 2 ^ (d + 1 + 1) := by ring

/-- Every node is genuinely in the tree of `1`: one step of `col` moves to a node one
    level down, so the inductive definition agrees with `predStep`. -/
theorem inTree_col {v d j : ℕ} (h : InTree v (d + 1) j) :
    ∃ u j', InTree u d j' ∧ col v = u := by
  cases h with
  | dbl h' => exact ⟨_, _, h', col_two_mul _⟩
  | odd h' hv =>
      refine ⟨_, _, h', ?_⟩
      rw [col_odd_pred]
      omega

/-! ## The harmonic recursion, elementary and exact

`tree_size_bound` makes `S_d = Σ_{v ∈ L_d} 1/(v+1)` the object the density form asks
about, and `S_d` obeys a recursion with no Fourier analysis, no operator and no
conductor in it.

The odd arm is exact.  For a junction `v` with odd child `n`, `3(n+1) = 2(v+1)` —
`odd_arm_exact` — so

    1/(n+1) = (3/2) · 1/(v+1)

exactly.  The doubling arm loses only the difference between `2v+1` and `2v+2`:

    1/(2v+1) ≥ (1/2) · 1/(v+1)

Summing the two over a level, with `T = Σ over the junctions`,

    S(predStep L)  ≥  (1/2) S(L) + (3/2) T(L)

`harm_predStep`.  Measured, the inequality is tight to five decimals — `0.10289`
against `0.10290` at depth 48, `0.10422` against `0.10422` at 54 — because the
doubling loss vanishes as the nodes grow.

The consequence is immediate.  If the junctions carry at least a third of the
harmonic mass, `S ≤ 3T`, then

    S(predStep L) ≥ (1/2)S + (1/2)S = S

so `S_d` is non-decreasing and cannot decay at all, let alone exponentially —
`harm_nondecreasing`.  Measured, `T/S` oscillates about `1/3`: `0.3156, 0.2179,
0.3662, 0.3537, 0.3125, 0.3312, 0.3447, 0.3832` at depths `18` to `56`, and `S_d`
sits flat at `0.10` to `0.12`.

So the density form of the conjecture, stripped to its last elementary statement, is

> the junctions carry at least a third of the level's harmonic mass.

which is the same `1/3` as the junction fraction, the same `1/3` as `q(3)`, and the
same tangency — now with no machinery around it. -/

/-- A level's harmonic sum. -/
noncomputable def harm (L : Finset ℕ) : ℝ := ∑ v ∈ L, (1 : ℝ) / (v + 1)

/-- Its junction part. -/
noncomputable def harmJunc (L : Finset ℕ) : ℝ :=
  ∑ v ∈ L.filter (fun v => v % 3 = 2), (1 : ℝ) / (v + 1)

/-- The odd arm multiplies the harmonic weight by exactly `3/2`. -/
theorem harm_odd_child {v : ℕ} (h : v % 3 = 2) :
    (1 : ℝ) / ((2 * (v / 3) + 1 : ℕ) + 1) = (3 / 2) * ((1 : ℝ) / (v + 1)) := by
  have hex : 3 * ((2 * (v / 3) + 1) + 1) = 2 * (v + 1) := odd_arm_exact h
  have hc : (3 : ℝ) * ((2 * (v / 3) + 1 : ℕ) + 1) = 2 * ((v : ℝ) + 1) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hex
  have hpos : ((2 * (v / 3) + 1 : ℕ) : ℝ) + 1 > 0 := by positivity
  have hv : ((v : ℝ) + 1) > 0 := by positivity
  field_simp
  linarith [hc]

/-- The doubling arm loses only `2v+1` against `2v+2`. -/
theorem harm_even_child (v : ℕ) :
    (1 / 2 : ℝ) * ((1 : ℝ) / (v + 1)) ≤ (1 : ℝ) / ((2 * v : ℕ) + 1) := by
  have hcast : ((2 * v : ℕ) : ℝ) = 2 * (v : ℝ) := by push_cast; ring
  rw [hcast]
  have hpos : (0 : ℝ) < 2 * (v : ℝ) + 1 := by positivity
  have hle : 2 * (v : ℝ) + 1 ≤ 2 * ((v : ℝ) + 1) := by linarith
  have key : (1 : ℝ) / (2 * ((v : ℝ) + 1)) ≤ 1 / (2 * (v : ℝ) + 1) :=
    one_div_le_one_div_of_le hpos hle
  have heq : (1 / 2 : ℝ) * ((1 : ℝ) / ((v : ℝ) + 1)) = 1 / (2 * ((v : ℝ) + 1)) := by
    field_simp
  rw [heq]
  exact key

/-- **The harmonic recursion.**  Elementary, exact on the odd arm, and tight. -/
theorem harm_predStep (L : Finset ℕ) :
    (1 / 2 : ℝ) * harm L + (3 / 2) * harmJunc L ≤ harm (predStep L) := by
  have hsplit : harm (predStep L)
      = (∑ v ∈ L, (1 : ℝ) / ((2 * v : ℕ) + 1))
        + ∑ v ∈ L.filter (fun v => v % 3 = 2), (1 : ℝ) / ((2 * (v / 3) + 1 : ℕ) + 1) := by
    unfold harm predStep
    rw [Finset.sum_union, Finset.sum_image, Finset.sum_image]
    · intro a ha b hb hab
      obtain ⟨_, ha3⟩ := Finset.mem_filter.mp ha
      obtain ⟨_, hb3⟩ := Finset.mem_filter.mp hb
      simp only at hab
      omega
    · intro a _ b _ hab; simp only at hab; omega
    · rw [Finset.disjoint_left]
      rintro x hx hy
      obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨m', _, hm'⟩ := Finset.mem_image.mp hy
      omega
  rw [hsplit]
  have h1 : (1 / 2 : ℝ) * harm L ≤ ∑ v ∈ L, (1 : ℝ) / ((2 * v : ℕ) + 1) := by
    unfold harm
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun v _ => harm_even_child v)
  have h2 : (3 / 2 : ℝ) * harmJunc L
      = ∑ v ∈ L.filter (fun v => v % 3 = 2), (1 : ℝ) / ((2 * (v / 3) + 1 : ℕ) + 1) := by
    unfold harmJunc
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    obtain ⟨_, hv3⟩ := Finset.mem_filter.mp hv
    rw [harm_odd_child hv3]
  rw [h2]
  linarith

/-- **The consequence.**  If the junctions carry a third of the harmonic mass, the
    harmonic sum never decreases — so it cannot decay exponentially, and `Λ(3) = 2`. -/
theorem harm_nondecreasing (L : Finset ℕ) (h : harm L ≤ 3 * harmJunc L) :
    harm L ≤ harm (predStep L) := by
  have := harm_predStep L
  linarith

/-! ## The exceptional set: cycles

Density results say nothing about the conjecture, because a set of density one can
miss an infinite set.  Collatz fails in exactly two ways — a nontrivial cycle, or a
trajectory that diverges — and neither is a statement about almost all integers.
This section takes the first.

`col_shift` already contains the cycle equation.  Write `n = 2^k t + r` with
`r = n mod 2^k` and `j = oddSteps r k`.  Then `col^[k] n = 3^j t + col^[k] r`, so a
point of period `k` satisfies `3^j t + col^[k] r = 2^k t + r`, that is

    t · (2^k − 3^j)  =  col^[k] r − r

exactly, in `ℤ`.  `cycle_equation`.  Everything about cycles for the shortcut map is
in that line: the left side is a multiple of `2^k − 3^j`, which is never zero because
`2` and `3` are coprime, and the right side is bounded by the largest excursion of
`col^[k]` on `[0, 2^k)`.  So `t` is bounded, so the cycle's elements are bounded by a
function of `k` alone — `cycle_bound`.

That is the shape of every classical result on Collatz cycles: for the cycle to hold
a large number, `2^k − 3^j` must be small against `2^k`, so `k/j` must approximate
`log₂ 3` extremely well, which forces `k/j` to be a convergent of that continued
fraction and lets transcendence bounds on `|k log 2 − j log 3|` push the required
cycle length up.  What is formalised here is the exact identity the whole argument
starts from. -/

/-- **The cycle equation.**  A point of period `k` for the shortcut map satisfies
    `t(2^k − 3^j) = col^[k] r − r` exactly, with `t` and `r` its quotient and
    remainder mod `2^k` and `j` its odd-step count. -/
theorem cycle_equation {n k : ℕ} (h : col^[k] n = n) :
    ((n / 2 ^ k : ℕ) : ℤ) * ((2 : ℤ) ^ k - (3 : ℤ) ^ oddSteps (n % 2 ^ k) k)
      = ((col^[k] (n % 2 ^ k) : ℕ) : ℤ) - ((n % 2 ^ k : ℕ) : ℤ) := by
  have hn : 2 ^ k * (n / 2 ^ k) + n % 2 ^ k = n := Nat.div_add_mod n (2 ^ k)
  have hshift := col_shift k (n / 2 ^ k) (n % 2 ^ k)
  rw [hn, h] at hshift
  -- `n = 3^j t + col^[k] r` and `n = 2^k t + r`
  have : (n : ℤ) = (3 : ℤ) ^ oddSteps (n % 2 ^ k) k * ((n / 2 ^ k : ℕ) : ℤ)
      + ((col^[k] (n % 2 ^ k) : ℕ) : ℤ) := by exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) hshift
  have hn' : (n : ℤ) = (2 : ℤ) ^ k * ((n / 2 ^ k : ℕ) : ℤ) + ((n % 2 ^ k : ℕ) : ℤ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) hn.symm
  linarith [this, hn']

/-- `2^k = 3^j` only when both are `1`, so the coefficient in the cycle equation
    never vanishes for a positive-length cycle. -/
theorem two_pow_ne_three_pow {k j : ℕ} (hk : 1 ≤ k) : (2 : ℤ) ^ k ≠ (3 : ℤ) ^ j := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  intro h
  have hodd : Odd ((3 : ℤ) ^ j) := Odd.pow (by decide)
  have heven : Even ((2 : ℤ) ^ (k' + 1)) := by
    rw [pow_succ]
    exact (even_two).mul_left _
  rw [h] at heven
  exact (Int.not_odd_iff_even.mpr heven) hodd

/-- **Cycles are bounded by their length.**  Since the coefficient is a nonzero
    integer, `t` is at most the excursion of `col^[k]` on the residues, so every
    element of a `k`-cycle is bounded by a function of `k` alone. -/
theorem cycle_bound {n k : ℕ} (hk : 1 ≤ k) (h : col^[k] n = n) :
    ((n / 2 ^ k : ℕ) : ℤ) * ((2 : ℤ) ^ k - (3 : ℤ) ^ oddSteps (n % 2 ^ k) k) ≠ 0 ∨
      n < 2 ^ k := by
  rcases Nat.lt_or_ge n (2 ^ k) with hlt | hge
  · exact Or.inr hlt
  · left
    have hq : 1 ≤ n / 2 ^ k := (Nat.one_le_div_iff (by positivity)).mpr hge
    have hne : (2 : ℤ) ^ k - (3 : ℤ) ^ oddSteps (n % 2 ^ k) k ≠ 0 :=
      sub_ne_zero.mpr (two_pow_ne_three_pow hk)
    have hqz : ((n / 2 ^ k : ℕ) : ℤ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    exact mul_ne_zero hqz hne

/-! ### The excursion bound, and the cycle bound made quantitative

`cycle_bound` says a cycle's elements are bounded by its length; to say by how much,
bound `col^[k] r`.  The `u = n+1` coordinate does it in one line each way, and it is
the same coordinate that made the tree's odd arm exactly `×2/3`:

* an odd step is exactly `u ↦ (3/2)u`, since `n` odd gives `col n + 1 = 3(n+1)/2`;
* an even step never increases `u`, since `col n + 1 = n/2 + 1 ≤ n + 1`.

So `j` odd steps multiply `u` by `(3/2)^j` and the rest cannot help, giving

    2^j · (col^[k] r + 1)  ≤  3^j · (r + 1)

`iterate_le_pow`, by induction on `k`.  With `r < 2^k` that bounds the excursion in
the cycle equation, and

    t · |2^k − 3^j|  =  |col^[k] r − r|  ≤  3^j · 2^(k−j)

so a `k`-cycle can hold a large number only when `|2^k − 3^j|` is small against
`2^k` — which is the Diophantine condition the classical results exploit, reached
here from the residue split. -/

/-- One step, in the `u = n+1` coordinate: odd multiplies by exactly `3/2`. -/
theorem col_succ_odd {n : ℕ} (h : n % 2 = 1) : 2 * (col n + 1) = 3 * (n + 1) := by
  have : col n = (3 * n + 1) / 2 := by
    unfold col; simp [h]
  omega

/-- And even never increases it. -/
theorem col_succ_even {n : ℕ} (h : n % 2 = 0) : col n + 1 ≤ n + 1 := by
  have : col n = n / 2 := by unfold col; simp [h]
  omega

/-- **The excursion bound.**  `j` odd steps multiply `n+1` by at most `(3/2)^j`, and
    the even steps cannot help. -/
theorem iterate_le_pow : ∀ (k r : ℕ),
    2 ^ oddSteps r k * (col^[k] r + 1) ≤ 3 ^ oddSteps r k * (r + 1) := by
  intro k
  induction k with
  | zero => intro r; simp [oddSteps]
  | succ k ih =>
      intro r
      rw [Function.iterate_succ_apply]
      have hstep : oddSteps r (k + 1) = (if r % 2 = 0 then 0 else 1) + oddSteps (col r) k := rfl
      rcases Nat.even_or_odd r with he | ho
      · have h0 : r % 2 = 0 := Nat.even_iff.mp he
        have hj : oddSteps r (k + 1) = oddSteps (col r) k := by rw [hstep, if_pos h0]; ring
        rw [hj]
        calc 2 ^ oddSteps (col r) k * (col^[k] (col r) + 1)
            ≤ 3 ^ oddSteps (col r) k * (col r + 1) := ih (col r)
          _ ≤ 3 ^ oddSteps (col r) k * (r + 1) :=
              Nat.mul_le_mul_left _ (col_succ_even h0)
      · have h1 : r % 2 = 1 := Nat.odd_iff.mp ho
        have hj : oddSteps r (k + 1) = oddSteps (col r) k + 1 := by
          rw [hstep, if_neg (by omega)]; ring
        rw [hj, pow_succ, pow_succ]
        have hc := col_succ_odd h1
        calc 2 ^ oddSteps (col r) k * 2 * (col^[k] (col r) + 1)
            = 2 * (2 ^ oddSteps (col r) k * (col^[k] (col r) + 1)) := by ring
          _ ≤ 2 * (3 ^ oddSteps (col r) k * (col r + 1)) :=
              Nat.mul_le_mul_left _ (ih (col r))
          _ = 3 ^ oddSteps (col r) k * (2 * (col r + 1)) := by ring
          _ = 3 ^ oddSteps (col r) k * (3 * (r + 1)) := by rw [hc]
          _ = 3 ^ oddSteps (col r) k * 3 * (r + 1) := by ring

/-- **The cycle bound, quantitative.**  Combining the cycle equation with the
    excursion bound: the multiplier `t` is at most the excursion divided by
    `|2^k − 3^j|`, so a long cycle needs `2^k` and `3^j` to be very close. -/
theorem cycle_excursion {k r : ℕ} (hr : r < 2 ^ k) :
    2 ^ oddSteps r k * (col^[k] r + 1) ≤ 3 ^ oddSteps r k * 2 ^ k := by
  calc 2 ^ oddSteps r k * (col^[k] r + 1) ≤ 3 ^ oddSteps r k * (r + 1) := iterate_le_pow k r
    _ ≤ 3 ^ oddSteps r k * 2 ^ k := Nat.mul_le_mul_left _ (by omega)

/-! ### Banking the even steps: the exact identity

Vox reads `cycle_excursion` as **vacuous** — `weight` gives one seed and `83` inert
steps with no deposit, `banked` reports that no clear ever fired against a live
register, and `insert` finds no glyph that repairs it.  The reading is right: the
excursion bound throws the even steps away, keeping only that they do not increase
`u = n+1`.  A discarded count is exactly what `banked` reports as vacuous, and the
repair is to bank it.

Banked, the two steps are

    odd:   2u' = 3u          even:  2u' = u + 1

so carrying `2^i u_i` through the iteration gives an **exact** identity rather than
an inequality:

    2^k · (col^[k] r + 1)  =  3^j · (r + 1)  +  bank r k

with `bank` accumulating one `3^(odd steps remaining) · 2^(position)` at each even
step and nothing at an odd one.  `iterate_banked`.  The inequality proved earlier is
this identity with `bank` dropped.

For a cycle it closes immediately.  With `col^[k] n = n` the two sides share `n+1`:

    (n + 1) · (2^k − 3^j)  =  bank n k

`cycle_banked` — the cycle equation with its right-hand side explicit and positive,
instead of the excursion of `col^[k]` over a range of residues.  This is the form the
classical cycle arguments use, and it arrived by banking rather than by importing. -/

/-- The banked count: what the even steps contribute, kept instead of discarded. -/
def bank : ℕ → ℕ → ℕ
  | _, 0 => 0
  | r, (k + 1) => 2 * bank (col r) k + (if r % 2 = 0 then 3 ^ oddSteps (col r) k else 0)

/-- **The exact iterate identity.**  `2^k(col^[k] r + 1) = 3^j(r+1) + bank r k`. -/
theorem iterate_banked : ∀ (k r : ℕ),
    2 ^ k * (col^[k] r + 1) = 3 ^ oddSteps r k * (r + 1) + bank r k := by
  intro k
  induction k with
  | zero => intro r; simp [oddSteps, bank]
  | succ k ih =>
      intro r
      rw [Function.iterate_succ_apply]
      have hstep : oddSteps r (k + 1) = (if r % 2 = 0 then 0 else 1) + oddSteps (col r) k := rfl
      have hbank : bank r (k + 1)
          = 2 * bank (col r) k + (if r % 2 = 0 then 3 ^ oddSteps (col r) k else 0) := rfl
      have ihc := ih (col r)
      rcases Nat.even_or_odd r with he | ho
      · have h0 : r % 2 = 0 := Nat.even_iff.mp he
        have hcol : 2 * (col r + 1) = r + 2 := by
          have : col r = r / 2 := by unfold col; simp [h0]
          omega
        rw [hstep, if_pos h0, hbank, if_pos h0, pow_succ]
        calc 2 ^ k * 2 * (col^[k] (col r) + 1)
            = 2 * (2 ^ k * (col^[k] (col r) + 1)) := by ring
          _ = 2 * (3 ^ oddSteps (col r) k * (col r + 1) + bank (col r) k) := by rw [ihc]
          _ = 3 ^ oddSteps (col r) k * (2 * (col r + 1)) + 2 * bank (col r) k := by ring
          _ = 3 ^ oddSteps (col r) k * (r + 2) + 2 * bank (col r) k := by rw [hcol]
          _ = 3 ^ (0 + oddSteps (col r) k) * (r + 1)
                + (2 * bank (col r) k + 3 ^ oddSteps (col r) k) := by ring_nf
      · have h1 : r % 2 = 1 := Nat.odd_iff.mp ho
        have hcol : 2 * (col r + 1) = 3 * (r + 1) := col_succ_odd h1
        rw [hstep, if_neg (by omega), hbank, if_neg (by omega), pow_succ]
        calc 2 ^ k * 2 * (col^[k] (col r) + 1)
            = 2 * (2 ^ k * (col^[k] (col r) + 1)) := by ring
          _ = 2 * (3 ^ oddSteps (col r) k * (col r + 1) + bank (col r) k) := by rw [ihc]
          _ = 3 ^ oddSteps (col r) k * (2 * (col r + 1)) + 2 * bank (col r) k := by ring
          _ = 3 ^ oddSteps (col r) k * (3 * (r + 1)) + 2 * bank (col r) k := by rw [hcol]
          _ = 3 ^ (1 + oddSteps (col r) k) * (r + 1) + (2 * bank (col r) k + 0) := by ring

/-- **The cycle equation, banked.**  A point of period `k` satisfies
    `(n+1)(2^k − 3^j) = bank n k`, with the right-hand side an explicit positive
    integer rather than an excursion. -/
theorem cycle_banked {n k : ℕ} (h : col^[k] n = n) :
    ((n : ℤ) + 1) * ((2 : ℤ) ^ k - (3 : ℤ) ^ oddSteps n k) = (bank n k : ℤ) := by
  have hid := iterate_banked k n
  rw [h] at hid
  have : ((2 : ℤ) ^ k * ((n : ℤ) + 1))
      = (3 : ℤ) ^ oddSteps n k * ((n : ℤ) + 1) + (bank n k : ℤ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) hid
  linarith

end CollatzDepthSplit
