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

end CollatzDepthSplit
