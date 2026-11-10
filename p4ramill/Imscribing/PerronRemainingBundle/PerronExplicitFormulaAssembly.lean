import Imscribing.IntegratedZeroSum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section

namespace Imscribing

open MeasureTheory Set

/-- Integrate a finite pointwise decomposition. -/
theorem intervalIntegral_integral_finite_decomposition
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f g : ℝ → ℂ) (hterm : ι → ℝ → ℂ)
    (a b : ℝ)
    (hg : IntervalIntegrable g MeasureTheory.volume a b)
    (hsum : IntervalIntegrable (fun x => ∑ i ∈ S, hterm i x)
      MeasureTheory.volume a b)
    (hterms : ∀ i ∈ S,
      IntervalIntegrable (hterm i) MeasureTheory.volume a b)
    (hpoint : ∀ x ∈ Set.uIcc a b,
      f x = g x + ∑ i ∈ S, hterm i x) :
    (∫ x in a..b, f x) =
      (∫ x in a..b, g x) +
        ∑ i ∈ S, (∫ x in a..b, hterm i x) := by
  calc
    (∫ x in a..b, f x) =
        ∫ x in a..b, (g x + ∑ i ∈ S, hterm i x) := by
          apply intervalIntegral.integral_congr
          intro x hx
          exact hpoint x hx
    _ = (∫ x in a..b, g x) +
        (∫ x in a..b, ∑ i ∈ S, hterm i x) :=
          intervalIntegral.integral_add hg hsum
    _ = (∫ x in a..b, g x) +
        ∑ i ∈ S, (∫ x in a..b, hterm i x) := by
          rw [intervalIntegral.integral_finset_sum]
          · rfl
          · exact hterms

/-- Integrate a finite explicit-formula decomposition and integrate every
zero term by parts. -/
theorem intervalIntegral_integrated_zero_decomposition
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f g : ℝ → ℂ)
    (main correction primitive : ι → ℝ → ℂ)
    (a b : ℝ)
    (hg : IntervalIntegrable g MeasureTheory.volume a b)
    (hsum : IntervalIntegrable (fun x => ∑ i ∈ S, main i x)
      MeasureTheory.volume a b)
    (hmain : ∀ i ∈ S,
      IntervalIntegrable (main i) MeasureTheory.volume a b)
    (hcorr : ∀ i ∈ S,
      IntervalIntegrable (correction i) MeasureTheory.volume a b)
    (hderiv : ∀ i ∈ S, ∀ x ∈ Set.uIcc a b,
      HasDerivAt (primitive i) (main i x - correction i x) x)
    (hpoint : ∀ x ∈ Set.uIcc a b,
      f x = g x + ∑ i ∈ S, main i x) :
    (∫ x in a..b, f x) =
      (∫ x in a..b, g x) +
        ∑ i ∈ S,
          (primitive i b - primitive i a +
            ∫ x in a..b, correction i x) := by
  have hdecomp := intervalIntegral_integral_finite_decomposition
    S f g main a b hg hsum hmain hpoint
  have hzero : ∀ i ∈ S,
      (∫ x in a..b, main i x) =
        primitive i b - primitive i a +
          ∫ x in a..b, correction i x := by
    intro i hi
    exact integrated_zero_term_by_parts (primitive i) (main i)
      (correction i) (hderiv i hi) (hmain i hi) (hcorr i hi)
  rw [hdecomp]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact hzero i hi

/-- Data for a pointwise truncated explicit formula on a finite interval. -/
structure TruncatedExplicitFormulaData
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a b : ℝ) where
  lhs : ℝ → ℂ
  remainder : ℝ → ℂ
  main : ι → ℝ → ℂ
  correction : ι → ℝ → ℂ
  primitive : ι → ℝ → ℂ
  lhs_integrable : IntervalIntegrable lhs MeasureTheory.volume a b
  remainder_integrable : IntervalIntegrable remainder MeasureTheory.volume a b
  main_sum_integrable :
    IntervalIntegrable (fun x => ∑ i ∈ S, main i x) MeasureTheory.volume a b
  main_integrable : ∀ i ∈ S,
    IntervalIntegrable (main i) MeasureTheory.volume a b
  correction_integrable : ∀ i ∈ S,
    IntervalIntegrable (correction i) MeasureTheory.volume a b
  primitive_deriv : ∀ i ∈ S, ∀ x ∈ Set.uIcc a b,
    HasDerivAt (primitive i) (main i x - correction i x) x
  pointwise_formula : ∀ x ∈ Set.uIcc a b,
    lhs x = remainder x + ∑ i ∈ S, main i x

/-- Integrate the packaged truncated explicit formula and integrate each
zero term by parts. -/
theorem integrate_truncated_formula_data
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a b : ℝ)
    (D : TruncatedExplicitFormulaData S a b) :
    (∫ x in a..b, D.lhs x) =
      (∫ x in a..b, D.remainder x) +
        ∑ i ∈ S,
          (D.primitive i b - D.primitive i a +
            ∫ x in a..b, D.correction i x) := by
  exact intervalIntegral_integrated_zero_decomposition
    S D.lhs D.remainder D.main D.correction D.primitive a b
    D.remainder_integrable D.main_sum_integrable D.main_integrable
    D.correction_integrable D.primitive_deriv D.pointwise_formula

end Imscribing
