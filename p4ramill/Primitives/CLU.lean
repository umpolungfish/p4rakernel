-- Imscribing/Primitives/CLU.lean
-- Formal definition of the Criticality-Lift Unit (CLU) = ln(10) nats.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription

open Imscribing.Primitives

namespace Imscribing.Primitives.CLUPrimitives

noncomputable abbrev CLU : ℝ := Real.log 10

theorem CLU_pos : CLU > 0 := by
  unfold CLU; apply Real.log_pos; norm_num

theorem CLU_gt_two : CLU > 2 := by
  unfold CLU
  have h : Real.exp (2 : ℝ) < (10 : ℝ) := by
    have h_sq : (Real.exp 1)^2 < (2.7182818286)^2 := by
      have hd : (2.7182818286 : ℝ) - Real.exp 1 > 0 := sub_pos.mpr Real.exp_one_lt_d9
      have hs : (2.7182818286 : ℝ) + Real.exp 1 > 0 :=
        add_pos (by norm_num : (0 : ℝ) < 2.7182818286) (Real.exp_pos 1)
      have h_diff_pos : (2.7182818286 : ℝ)^2 - (Real.exp 1)^2 > 0 := by
        calc
          (2.7182818286 : ℝ)^2 - (Real.exp 1)^2 = ((2.7182818286 : ℝ) - Real.exp 1) * ((2.7182818286 : ℝ) + Real.exp 1) := by ring
          _ > 0 := mul_pos hd hs
      linarith
    calc
      Real.exp (2 : ℝ) = Real.exp (1 + 1 : ℝ) := by norm_num
      _ = Real.exp 1 * Real.exp 1 := by rw [Real.exp_add]
      _ = (Real.exp 1) ^ 2 := by ring
      _ < (2.7182818286 : ℝ) ^ 2 := h_sq
      _ < (10 : ℝ) := by norm_num
  calc
    (2 : ℝ) = Real.log (Real.exp (2 : ℝ)) := by rw [Real.log_exp]
    _ < Real.log (10 : ℝ) := Real.log_lt_log (Real.exp_pos _) h
    _ = CLU := rfl

theorem CLU_lt_three : CLU < 3 := by
  unfold CLU
  have h_sq_gt : (Real.exp 1)^2 > (2.7182818283)^2 := by
    have hd : Real.exp 1 - (2.7182818283 : ℝ) > 0 := sub_pos.mpr Real.exp_one_gt_d9
    have hs : Real.exp 1 + (2.7182818283 : ℝ) > 0 :=
      add_pos (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2.7182818283)
    have h_diff_pos : (Real.exp 1)^2 - (2.7182818283 : ℝ)^2 > 0 := by
      calc
        (Real.exp 1)^2 - (2.7182818283 : ℝ)^2 = (Real.exp 1 - (2.7182818283 : ℝ)) * (Real.exp 1 + (2.7182818283 : ℝ)) := by ring
        _ > 0 := mul_pos hd hs
    linarith
  have h_cube : (Real.exp 1)^3 > (2.7182818283)^3 := by
    have hd : Real.exp 1 - (2.7182818283 : ℝ) > 0 := sub_pos.mpr Real.exp_one_gt_d9
    have hs : (Real.exp 1)^2 + Real.exp 1 * (2.7182818283 : ℝ) + (2.7182818283 : ℝ)^2 > 0 := by
      positivity
    have h_diff_pos : (Real.exp 1)^3 - (2.7182818283 : ℝ)^3 > 0 := by
      calc
        (Real.exp 1)^3 - (2.7182818283 : ℝ)^3 = (Real.exp 1 - (2.7182818283 : ℝ)) * ((Real.exp 1)^2 + Real.exp 1 * (2.7182818283 : ℝ) + (2.7182818283 : ℝ)^2) := by ring
        _ > 0 := mul_pos hd hs
    linarith
  have h : Real.exp (3 : ℝ) > (10 : ℝ) := by
    calc
      Real.exp (3 : ℝ) = Real.exp (1 + 1 + 1 : ℝ) := by norm_num
      _ = ((Real.exp 1 * Real.exp 1) * Real.exp 1) := by rw [Real.exp_add, Real.exp_add]
      _ = (Real.exp 1)^3 := by ring
      _ > (2.7182818283 : ℝ)^3 := h_cube
      _ > (10 : ℝ) := by norm_num
  calc
    CLU = Real.log (10 : ℝ) := rfl
    _ < Real.log (Real.exp (3 : ℝ)) := Real.log_lt_log (by norm_num : (0 : ℝ) < 10) h
    _ = 3 := Real.log_exp _

section Operators

/-- CLU-invariant scaling operator: multiplies by CLU. -/
noncomputable def cluScale (x : ℝ) : ℝ := CLU * x

theorem cluScale_pos (x : ℝ) (hx : x > 0) : cluScale x > 0 := by
  rw [cluScale]; exact mul_pos CLU_pos hx

/-- CLU division: x / CLU, the number of CLU-units in x. -/
noncomputable def cluDiv (x : ℝ) : ℝ := x / CLU

theorem cluDiv_pos (x : ℝ) (hx : x > 0) : cluDiv x > 0 := by
  rw [cluDiv]; exact div_pos hx CLU_pos

end Operators

section KTier

/-- The kTier index is the floor of energy / CLU, giving a discrete grade. -/
noncomputable def kTier (E : ℝ) : ℕ :=
  Int.toNat (⌊E / CLU⌋ : ℤ)

theorem kTier_zero_at_zero : kTier 0 = 0 := by
  unfold kTier; simp

theorem kTier_monotone (E₁ E₂ : ℝ) (h : E₁ ≤ E₂) : kTier E₁ ≤ kTier E₂ := by
  unfold kTier
  have hdiv : E₁ / CLU ≤ E₂ / CLU :=
    div_le_div_of_nonneg_right h (by positivity : 0 ≤ CLU)
  have hfloor : (⌊E₁ / CLU⌋ : ℤ) ≤ (⌊E₂ / CLU⌋ : ℤ) :=
    Int.floor_mono hdiv
  exact Int.toNat_le_toNat hfloor

end KTier

section EnergyBounds

/-- A CLU-bounded energy satisfies E < n*CLU for some natural n. -/
noncomputable def cluBounded (E : ℝ) (n : ℕ) : Prop :=
  E < (n : ℝ) * CLU

theorem bounded_zero_one : cluBounded 0 1 := by
  unfold cluBounded
  have hpos : (0 : ℝ) < ((1 : ℕ) : ℝ) * CLU := by
    simpa [Nat.cast_one] using CLU_pos
  exact hpos

theorem bounded_add (E₁ E₂ : ℝ) (n m : ℕ) (h₁ : cluBounded E₁ n) (h₂ : cluBounded E₂ m) :
    cluBounded (E₁ + E₂) (n + m) := by
  unfold cluBounded at *
  have hsum : E₁ + E₂ < (n : ℝ) * CLU + (m : ℝ) * CLU := by linarith
  have hcast : ((n : ℝ) * CLU + (m : ℝ) * CLU) = ((n + m : ℕ) : ℝ) * CLU := by
    simp [add_mul, Nat.cast_add]
  rw [hcast] at hsum
  exact hsum

end EnergyBounds

section CrossDomain

/-- Universal CLU scale: the ratio ln(10) as structural quantum. -/
noncomputable def cluUniversal : ℝ := CLU

theorem cluUniversal_pos : cluUniversal > 0 := CLU_pos

end CrossDomain

section Imscription

/-- The kTier index maps to K_slow as the relaxation class for CLU-bounded systems. -/
def kTierToChar (_n : ℕ) : KineticChar :=
  KineticChar.K_slow

/-- CLU's structural polarity assignment: P_asym — no intrinsic symmetry breaking. -/
def CLU_polarity : Polarity :=
  Polarity.P_asym

end Imscription

end Imscribing.Primitives.CLUPrimitives
