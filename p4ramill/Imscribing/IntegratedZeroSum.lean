import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

open scoped BigOperators

namespace Imscribing

/--
A reusable integration-by-parts form for one integrated zero term.

The derivative hypothesis is arranged so that `main` is the original
integrand and `correction` is the lower-order term left after differentiating
the proposed antiderivative.  This is the abstract identity used for
`Fρ(t) = t^ρ / (ρ log(t)^2)`.
-/
theorem integrated_zero_term_by_parts
    {a b : ℝ} (F main correction : ℝ → ℂ)
    (hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt F (main x - correction x) x)
    (hmain : IntervalIntegrable main MeasureTheory.volume a b)
    (hcorr : IntervalIntegrable correction MeasureTheory.volume a b) :
    (∫ x in a..b, main x ∂MeasureTheory.volume) =
      F b - F a + ∫ x in a..b, correction x ∂MeasureTheory.volume := by
  have hdiff :
      IntervalIntegrable (fun x => main x - correction x)
        MeasureTheory.volume a b :=
    hmain.sub hcorr
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hdiff
  have hsplit := intervalIntegral.integral_sub hmain hcorr
  calc
    (∫ x in a..b, main x ∂MeasureTheory.volume) =
        (∫ x in a..b, (main x - correction x) ∂MeasureTheory.volume) +
          ∫ x in a..b, correction x ∂MeasureTheory.volume := by
      rw [hsplit]
      exact (sub_add_cancel _ _).symm
    _ = F b - F a +
          ∫ x in a..b, correction x ∂MeasureTheory.volume := by
      rw [hFTC]

/-- The reciprocal-square weight attached to a complex zero. -/
noncomputable def reciprocalNormSquare {ι : Type*} (rho : ι → ℂ) (i : ι) : ℝ :=
  ((‖rho i‖) ^ 2)⁻¹

/--
Comparison principle for reciprocal-square weights.  The hypothesis `hmajorant`
is the summable majorant; in the zero-counting application it is supplied by
the Riemann--von Mangoldt estimate after ordering the zeros by height.
-/
theorem reciprocal_norm_square_summable_of_majorant
    {ι : Type*} [Countable ι] (rho : ι → ℂ) (majorant : ι → ℝ)
    (hmajorant_summable : Summable majorant)
    (hbound : ∀ i, reciprocalNormSquare rho i ≤ majorant i) :
    Summable (reciprocalNormSquare rho) := by
  exact Summable.of_nonneg_of_le
    (fun i => by simp [reciprocalNormSquare])
    hbound
    hmajorant_summable

/--
A convenient concrete comparison: an `(n+1)^(-3/2)` envelope is summable.
This is the exponent obtained from the zero-count estimate
`N(T) = O(T log T)` after ordering zeros by increasing height.
-/
theorem reciprocal_norm_square_summable_of_rpow_bound
    (rho : ℕ → ℂ) (C : ℝ)
    (hbound : ∀ n,
      reciprocalNormSquare rho n ≤
        C * (1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ))) :
    Summable (reciprocalNormSquare rho) := by
  have hp : Summable (fun n : ℕ =>
      1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ)) := by
    exact (Real.summable_one_div_nat_add_rpow 1 (3 / 2 : ℝ)).2 (by norm_num)
  have hmajorant : Summable (fun n : ℕ =>
      C * (1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ))) :=
    Summable.mul_left C hp
  exact Summable.of_nonneg_of_le
    (fun n => by simp [reciprocalNormSquare])
    hbound
    hmajorant

/--
The norm of one integrated zero term is bounded by the RH-sized numerator
and the reciprocal-square weight.  `hpower` is the pointwise consequence
`|X^ρ| = sqrt X` under RH for `X ≥ 0`.
-/
theorem norm_zero_term_le_reciprocal_square
    (B : ℝ) (z rho : ℂ)
    (hpower : ‖z‖ ≤ B) :
    ‖z / rho ^ 2‖ ≤ B * ((‖rho‖ ^ 2)⁻¹) := by
  rw [norm_div, norm_pow, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hpower
    (inv_nonneg.mpr (sq_nonneg (‖rho‖)))

/--
Finite truncated zero-sum estimate.  It is the exact inequality needed after
integrating each zero term by parts.  The separate summability theorem above
controls the right-hand side uniformly as the truncation grows.
-/
theorem finite_truncated_zero_sum_bound
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (S : Finset ι) (rho power : ι → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hpower : ∀ i ∈ S, ‖power i‖ ≤ B)
    (hweightSummable : Summable (reciprocalNormSquare rho)) :
    ‖∑ i ∈ S, power i / rho i ^ 2‖ ≤
      B * ∑' i, reciprocalNormSquare rho i := by
  have hweight_nonneg : ∀ i, 0 ≤ reciprocalNormSquare rho i := by
    intro i
    simp [reciprocalNormSquare]
  have hfinite_le_tsum :
      (∑ i ∈ S, reciprocalNormSquare rho i) ≤
        ∑' i, reciprocalNormSquare rho i := by
    exact sum_le_hasSum S (fun i hi => hweight_nonneg i) hweightSummable.hasSum
  calc
    ‖∑ i ∈ S, power i / rho i ^ 2‖ ≤
        ∑ i ∈ S, B * reciprocalNormSquare rho i := by
      apply norm_sum_le_of_le
      intro i hi
      exact norm_zero_term_le_reciprocal_square B (power i) (rho i)
        (hpower i hi)
    _ = B * ∑ i ∈ S, reciprocalNormSquare rho i := by
      rw [Finset.mul_sum]
    _ ≤ B * ∑' i, reciprocalNormSquare rho i :=
      mul_le_mul_of_nonneg_left hfinite_le_tsum hB

/--
If a truncated explicit formula has already been integrated and its remainder
is bounded by `E`, then the remaining finite zero sum is controlled by the
reciprocal-square mass.  This theorem is deliberately stated with the
integrated explicit-formula identity as an input: that analytic formula is
not part of Mathlib's current Chebyshev development.
-/
theorem integrated_formula_error_bound
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (S : Finset ι) (rho power : ι → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hpower : ∀ i ∈ S, ‖power i‖ ≤ B)
    (hweightSummable : Summable (reciprocalNormSquare rho))
    (R E : ℂ)
    (hformula : R = -(∑ i ∈ S, power i / rho i ^ 2) + E) :
    ‖R‖ ≤ B * ∑' i, reciprocalNormSquare rho i + ‖E‖ := by
  have hzero := finite_truncated_zero_sum_bound S rho power B hB hpower
    hweightSummable
  calc
    ‖R‖ = ‖-(∑ i ∈ S, power i / rho i ^ 2) + E‖ := by rw [hformula]
    _ ≤ ‖∑ i ∈ S, power i / rho i ^ 2‖ + ‖E‖ := by
      simpa only [norm_neg] using
        (norm_add_le (-(∑ i ∈ S, power i / rho i ^ 2)) E)
    _ ≤ B * ∑' i, reciprocalNormSquare rho i + ‖E‖ :=
      add_le_add hzero le_rfl

end Imscribing
