import Imscribing.ABC_Certificates
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Kernel-checked logarithm enclosures

These bounds use Mathlib's proved positive logarithm series and remainder.
The upper remainder deliberately uses the library's looser bound, without
the additional factor 2m+1 in the numerical reader's original formula.
-/
namespace Imscribing.ABC

noncomputable def logSeriesLower (x : ℝ) (m : ℕ) : ℝ :=
  2 * ∑ i ∈ Finset.range m, ((x - 1) / (x + 1)) ^ (2 * i + 1) / (2 * i + 1)

noncomputable def logSeriesUpper (x : ℝ) (m : ℕ) : ℝ :=
  logSeriesLower x m +
    2 * ((x - 1) / (x + 1)) ^ (2 * m + 1) / (1 - ((x - 1) / (x + 1)) ^ 2)

theorem log_series_enclosure {x : ℝ} (hx : 1 ≤ x) (m : ℕ) :
    logSeriesLower x m ≤ Real.log x ∧ Real.log x ≤ logSeriesUpper x m := by
  let z := (x - 1) / (x + 1)
  have hxp : 0 < x + 1 := by linarith
  have hz : 0 ≤ z := div_nonneg (sub_nonneg.mpr hx) hxp.le
  have hz1 : z < 1 := (div_lt_one hxp).mpr (by linarith)
  have hid : (1 + z) / (1 - z) = x := by
    dsimp [z]
    field_simp
    <;> nlinarith
  have hlo := Real.sum_range_le_log_div hz hz1 m
  have hhi := Real.log_div_le_sum_range_add hz hz1 m
  rw [hid] at hlo hhi
  constructor
  · convert mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 2) using 1 <;>
      dsimp [logSeriesLower, z] <;> ring
  · convert mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 2) using 1 <;>
      dsimp [logSeriesUpper, logSeriesLower, z] <;> ring

/-- A certificate may use binary range reduction without evaluating log. -/
theorem log_binary_enclosure {x n L₂ U₂ L U : ℝ} (k : ℕ)
    (hx : 0 < x) (hn : n = 2 ^ k * x)
    (h₂ : L₂ ≤ Real.log 2 ∧ Real.log 2 ≤ U₂)
    (h : L ≤ Real.log x ∧ Real.log x ≤ U) :
    (k : ℝ) * L₂ + L ≤ Real.log n ∧ Real.log n ≤ (k : ℝ) * U₂ + U := by
  rw [hn, Real.log_mul (ne_of_gt (pow_pos (by norm_num : (0 : ℝ) < 2) k))
    (ne_of_gt hx), Real.log_pow]
  constructor
  · exact add_le_add (mul_le_mul_of_nonneg_left h₂.1 (Nat.cast_nonneg k)) h.1
  · exact add_le_add (mul_le_mul_of_nonneg_left h₂.2 (Nat.cast_nonneg k)) h.2

/-- Proof-carrying bounds, with rational endpoints for certificate emission. -/
structure LogEnclosure (n : ℕ) where
  lower : ℚ
  upper : ℚ
  lower_le : (lower : ℝ) ≤ Real.log n
  le_upper : Real.log n ≤ (upper : ℝ)

theorem discrepancy_enclosure (ε : ℝ) (hε : 0 ≤ ε) (t : Triple)
    (height : LogEnclosure t.c) (support : LogEnclosure (radical (t.a * t.b * t.c))) :
    (height.lower : ℝ) - (1 + ε) * support.upper ≤ discrepancy ε t ∧
      discrepancy ε t ≤ (height.upper : ℝ) - (1 + ε) * support.lower := by
  have hp : 0 ≤ 1 + ε := by linarith
  have hl := mul_le_mul_of_nonneg_left support.lower_le hp
  have hu := mul_le_mul_of_nonneg_left support.le_upper hp
  have hhl := height.lower_le
  have hhu := height.le_upper
  unfold discrepancy logHeight logRadical rad
  constructor <;> linarith

end Imscribing.ABC
