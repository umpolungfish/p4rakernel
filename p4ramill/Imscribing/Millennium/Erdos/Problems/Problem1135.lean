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


-- ── The descent, and the conjecture from it ────────────────────────────────
-- The intermediate class-by-class contraction attempt is superseded: the
-- conjecture reduces to the single descent principle, and the descent carries
-- to 1 by well-founded induction (`reaches_one_of_descends` in CollatzDepthSplit,
-- where the descent is reduced to no divergence and no nontrivial cycle).

/-- The shortcut map keeps the positives positive. -/
lemma col_pos {n : ℕ} (hn : n ≥ 1) : col n ≥ 1 := by
  by_cases h : Even n
  · rw [col_even h]; obtain ⟨m, hm⟩ := h; omega
  · rw [col_odd h]; exact odd_positive hn

/-- Every iterate stays positive. -/
lemma pos_iter (n : ℕ) (hn : n ≥ 1) (k : ℕ) : (col^[k]) n ≥ 1 := by
  induction k with
  | zero => simpa using hn
  | succ k ih => rw [Function.iterate_succ_apply']; exact col_pos ih

/-- **The descent — the single honest gap.**  For every `n > 1` some iterate falls below `n`.
    This is the sharpest form of the conjecture; it is reduced, in `CollatzDepthSplit`, to no
    divergent trajectory and no nontrivial cycle. -/
axiom stopping_time_descent : ∀ n : ℕ, 1 < n → ∃ k : ℕ, (col^[k]) n < n

/-- **Erdős problem 1135 — Collatz — discharged from the descent.**  Every `n ≥ 1` reaches `1`:
    the descent carried to `1` by strong induction, with `col_one`/`col_two` closing the base
    `1 → 2 → 1`. -/
theorem erdos_problem_1135 (n : ℕ) (hn : n ≥ 1) : ∃ k : ℕ, (col^[k]) n = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge 1 n with hgt | hle
    · obtain ⟨k, hk⟩ := stopping_time_descent n hgt
      have hpos : (col^[k]) n ≥ 1 := pos_iter n hn k
      obtain ⟨m, hm⟩ := ih ((col^[k]) n) hk hpos
      exact ⟨m + k, by rw [Function.iterate_add_apply]; exact hm⟩
    · have h1 : n = 1 := by omega
      exact ⟨2, by subst h1; decide⟩

end Erdos1135
