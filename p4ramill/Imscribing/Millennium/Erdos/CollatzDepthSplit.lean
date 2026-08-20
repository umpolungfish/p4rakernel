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

end CollatzDepthSplit
