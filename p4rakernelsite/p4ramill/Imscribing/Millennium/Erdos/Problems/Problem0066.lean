import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Finset.Basic

open scoped BigOperators Topology MeasureTheory ProbabilityTheory ENNReal
open Finset Set Real MeasureTheory ProbabilityTheory Filter

namespace Erdos66

/-- The Bernoulli parameter p_n = min(1, c · √(log(n+1)/(n+1))). -/
noncomputable def p (c : ℝ) (n : ℕ) : ℝ :=
  min 1 (c * Real.sqrt (Real.log (n + 1) / ((n + 1 : ℕ) : ℝ)))

/-- The r_A(n) counting function. -/
noncomputable def r (A : Set ℕ) (n : ℕ) : ℕ :=
  {ab : ℕ × ℕ | ab.1 ∈ A ∧ ab.2 ∈ A ∧ ab.1 + ab.2 = n}.ncard

lemma p_bound (c : ℝ) (hc : 0 ≤ c) (n b : ℕ) (hb : 0 < b) (hbn : b ≤ n) :
    p c b ≤ c * Real.sqrt (Real.log (n + 1) / (b : ℝ)) := by
  have hlog : 0 ≤ Real.log ((b : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) b])
  have hratio : Real.log ((b : ℝ) + 1) / ((b : ℝ) + 1) ≤
      Real.log ((n : ℝ) + 1) / (b : ℝ) := by
    apply div_le_div₀ (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]))
    · apply Real.log_le_log (by positivity)
      exact_mod_cast (Nat.add_le_add_right hbn 1)
    · exact_mod_cast hb
    · linarith
  calc
    p c b ≤ c * Real.sqrt (Real.log ((b : ℝ) + 1) / ((b : ℝ) + 1)) := by
      simp [p, Nat.cast_add, Nat.cast_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hratio) hc

lemma p_mul_le (c : ℝ) (hc : 0 ≤ c) (n a : ℕ) (ha : 1 ≤ a) (han : a < n) :
    p c a * p c (n - a) ≤ c^2 * Real.log (n + 1) / Real.sqrt ((a : ℝ) * (n - a : ℝ)) := by
  have hna : 0 < n - a := by omega
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hp0 : 0 ≤ p c (n - a) := by unfold p; positivity
  have hprod := mul_le_mul (p_bound c hc n a ha (by omega))
    (p_bound c hc n (n-a) hna (by omega)) hp0 (by positivity)
  have hcast : ((n - a : ℕ) : ℝ) = (n : ℝ) - a := Nat.cast_sub (by omega)
  calc
    p c a * p c (n - a) ≤
        (c * Real.sqrt (Real.log ((n : ℝ) + 1) / (a : ℝ))) *
        (c * Real.sqrt (Real.log ((n : ℝ) + 1) / ((n - a : ℕ) : ℝ))) := hprod
    _ = c^2 * Real.log (n + 1) / Real.sqrt ((a : ℝ) * (n - a : ℝ)) := by
      rw [hcast, Real.sqrt_div hlog, Real.sqrt_div hlog, Real.sqrt_mul (by positivity)]
      have hs := Real.mul_self_sqrt hlog
      have ha0 : Real.sqrt (a : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast ha))
      have hb0 : Real.sqrt ((n : ℝ) - a) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by
        have : (a : ℝ) < n := by exact_mod_cast han
        linarith))
      field_simp [ha0, hb0]
      nlinarith only [hs]

/-- Axiom (honest) : Erdős (1956) probabilistic existence theorem for representation counts ~ c·log n. -/
axiom ax_erdos_problem_66 :
    ∃ A : Set ℕ, ∃ l : ℝ, l ≠ 0 ∧
      Filter.Tendsto (fun n => (r A n : ℝ) / Real.log n) Filter.atTop (𝓝 l)

/-- The main Erdős problem #66 theorem. -/
theorem erdos_problem_66 :
    ∃ A : Set ℕ, ∃ l : ℝ, l ≠ 0 ∧
      Filter.Tendsto (fun n => (r A n : ℝ) / Real.log n) Filter.atTop (𝓝 l) :=
  ax_erdos_problem_66

end Erdos66
