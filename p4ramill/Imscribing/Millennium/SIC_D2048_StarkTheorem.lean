import Mathlib
import Imscribing.Millennium.ClinkStarkBridge

/-!
# SIC_D2048_StarkTheorem — the Stark Theorem instance at d = 2048

The explicit Stark unit ε = (2047 + √4190205)/2 of K = ℚ(√4190205):
exact archimedean pinning of both embeddings, Galois-translate nonvanishing,
and the corrected mixed-signature clause. Builds on `ClinkStarkBridge`
(norm one, trace, regulator for all d ≥ 4) and pins d = 2048 exactly.
-/

namespace Imscribing.Millennium.StarkTheoremD2048

open Imscribing.Millennium.ClinkStarkBridge

open scoped Real

/-! ## §1 Exact bounds on √4190205 -/

/-- `√4190205 < 2047`: since 2047² = 4190209 > 4190205. -/
theorem sqrt_4190205_lt_2047 : Real.sqrt 4190205 < (2047 : ℝ) := by
  have hs : Real.sqrt ((4190205 : ℝ)) ^ 2 = (4190205 : ℝ) := Real.sq_sqrt (by norm_num)
  have hnpos : (0 : ℝ) ≤ Real.sqrt 4190205 := Real.sqrt_nonneg _
  nlinarith

/-- `2046 < √4190205`: since 2046² = 4186116 < 4190205. -/
theorem sqrt_4190205_gt_2046 : (2046 : ℝ) < Real.sqrt 4190205 := by
  have hs : Real.sqrt ((4190205 : ℝ)) ^ 2 = (4190205 : ℝ) := Real.sq_sqrt (by norm_num)
  have hnpos : (0 : ℝ) ≤ Real.sqrt 4190205 := Real.sqrt_nonneg _
  nlinarith

/-! ## §2 The dominant embedding σ₁(ε) -/

/-- The dominant embedding of the d = 2048 Stark unit lies in (2046, 2047). -/
theorem epsilonReal_2048_bounds :
    (2046 : ℝ) < epsilonReal 2048 ∧ epsilonReal 2048 < (2047 : ℝ) := by
  unfold epsilonReal
  constructor
  · linarith [sqrt_4190205_gt_2046]
  · linarith [sqrt_4190205_lt_2047]

/-! ## §3 The subdominant (contracting) embedding ε̄ -/

/-- The contracting embedding of the d = 2048 Stark unit lies in (1/2047, 1/2046). -/
theorem epsilonConjReal_2048_bounds :
    (1/2047 : ℝ) < epsilonConjReal 2048 ∧ epsilonConjReal 2048 < (1/2046 : ℝ) := by
  have h0 : epsilonReal 2048 * epsilonConjReal 2048 = 1 := epsilonReal_mul_conj 2048 (by norm_num)
  have hr := epsilonReal_2048_bounds
  have hεpos : (0 : ℝ) < epsilonConjReal 2048 := by
    have hnpos : (0 : ℝ) < epsilonReal 2048 * epsilonConjReal 2048 := by
      rw [h0]; norm_num
    nlinarith
  have hp1 : (0 : ℝ) < epsilonConjReal 2048 * (2047 - epsilonReal 2048) :=
    mul_pos hεpos (by linarith)
  have hp2 : epsilonConjReal 2048 * (2047 - epsilonReal 2048)
      = epsilonConjReal 2048 * 2047 - 1 := by rw [← h0]; ring
  have hp3 : (0 : ℝ) < epsilonConjReal 2048 * (epsilonReal 2048 - 2046) :=
    mul_pos hεpos (by linarith)
  have hp4 : epsilonConjReal 2048 * (epsilonReal 2048 - 2046)
      = 1 - epsilonConjReal 2048 * 2046 := by rw [← h0]; ring
  constructor
  · rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2047)]
    linarith
  · rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2046)]
    linarith

/-! ## §4 Galois-translate nonvanishing -/

/-- The identity translate never vanishes. -/
theorem epsilonReal_2048_ne_zero : epsilonReal 2048 ≠ 0 := by
  have := epsilonReal_2048_bounds.1
  linarith

/-- The conjugate translate never vanishes: it exceeds 1/2047. -/
theorem epsilonConjReal_2048_ne_zero : epsilonConjReal 2048 ≠ 0 := by
  have := epsilonConjReal_2048_bounds.1
  linarith

/-! ## §5 The wall: the smallness clause cannot hold for the true unit

The in-tree `MixedSignatureStarkConjecture` bounds every embedding by
`1 + 1/d`. A norm-one unit in a real quadratic field has one expanding and
one contracting conjugate; the contracting one meets the bound, the
expanding one cannot. -/

/-- The dominant embedding violates the smallness clause `‖σ(ε)‖ ≤ 1 + 1/d`. -/
theorem dominant_embedding_exceeds_smallness :
    (1 + 1/2048 : ℝ) < epsilonReal 2048 := by
  have hlo := epsilonReal_2048_bounds.1
  linarith

/-- The corrected mixed-signature clause: one expanding conjugate, one
    contracting conjugate, both nonvanishing. -/
theorem corrected_mixed_signature_2048 :
    (1 : ℝ) < epsilonReal 2048 ∧
    (1/2047 : ℝ) < epsilonConjReal 2048 ∧
    epsilonConjReal 2048 < (1/2046 : ℝ) ∧
    epsilonReal 2048 ≠ 0 ∧
    epsilonConjReal 2048 ≠ 0 := by
  refine ⟨?_, ?_, ?_, epsilonReal_2048_ne_zero, epsilonConjReal_2048_ne_zero⟩
  · have hlo := epsilonReal_2048_bounds.1
    linarith
  · exact epsilonConjReal_2048_bounds.1
  · exact epsilonConjReal_2048_bounds.2

/-! ## §6 Regulator -/

/-- The regulator identity 2·cosh(log ε) = 2047 at d = 2048. -/
theorem regulator_2048 :
    2 * Real.cosh (Real.log (epsilonReal 2048)) = (2048 : ℝ) - 1 :=
  regulator_identity 2048 (by norm_num)

/-- The regulator vector has zero total logarithm at d = 2048. -/
theorem log_signature_2048 :
    Real.log (epsilonReal 2048) + Real.log (epsilonConjReal 2048) = 0 :=
  log_epsilon_add_conj 2048 (by norm_num)

/-! ## §7 The Stark Theorem at d = 2048 -/

/-- **The Stark Theorem at d = 2048** (algebraic instance): the explicit unit
    ε = (2047 + √4190205)/2 has norm one, trace 2047, both Galois translates
    nonvanishing, dominant embedding in (2046, 2047), contracting embedding
    in (1/2047, 1/2046), regulator 2·cosh(log ε) = 2047, and the regulator
    vector sums to zero. All clauses are exact for the field
    K = ℚ(√4190205). -/
theorem stark_theorem_d2048 :
    epsilonReal 2048 * epsilonConjReal 2048 = 1 ∧
    epsilonReal 2048 + epsilonConjReal 2048 = (2047 : ℝ) ∧
    (2046 : ℝ) < epsilonReal 2048 ∧ epsilonReal 2048 < (2047 : ℝ) ∧
    (1/2047 : ℝ) < epsilonConjReal 2048 ∧ epsilonConjReal 2048 < (1/2046 : ℝ) ∧
    epsilonReal 2048 ≠ 0 ∧ epsilonConjReal 2048 ≠ 0 ∧
    2 * Real.cosh (Real.log (epsilonReal 2048)) = (2047 : ℝ) ∧
    Real.log (epsilonReal 2048) + Real.log (epsilonConjReal 2048) = 0 := by
  refine ⟨epsilonReal_mul_conj 2048 (by norm_num), ?_,
    epsilonReal_2048_bounds.1, epsilonReal_2048_bounds.2,
    epsilonConjReal_2048_bounds.1, epsilonConjReal_2048_bounds.2,
    epsilonReal_2048_ne_zero, epsilonConjReal_2048_ne_zero, ?_, log_signature_2048⟩
  · have h := epsilonReal_add_conj 2048
    rw [h]
    norm_num
  · have h := regulator_2048
    linarith

end Imscribing.Millennium.StarkTheoremD2048
