import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential

open scoped BigOperators

namespace Imscribing

/--
The integrand on the vertical line `s = c + it` occurring in Perron's formula.
For a positive real ratio `u`, this is `u^s / s`, written using `exp(s * log u)`.
The definition is total; analytic applications supply `u > 0` and interval
integrability (the latter follows from `c > 0`).
-/
noncomputable def verticalPerronKernelIntegrand (u c t : ℝ) : ℂ :=
  Complex.exp (((c : ℂ) + (t : ℂ) * Complex.I) * (Real.log u : ℂ)) /
    ((c : ℂ) + (t : ℂ) * Complex.I)

/-- The real normalization `1 / (2π)`, regarded as a complex scalar. -/
noncomputable def perronScale : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ)

/-- One normalized, coefficient-weighted Perron summand. -/
noncomputable def perronSummand (a : ℂ) (u c t : ℝ) : ℂ :=
  (perronScale * a) • verticalPerronKernelIntegrand u c t

/-- A finite Dirichlet polynomial after multiplication by `x^s/s`,
parametrized by the ratios `u_i = x / n_i`. -/
noncomputable def finitePerronIntegrand {ι : Type*}
    (S : Finset ι) (a : ι → ℂ) (u : ι → ℝ) (c t : ℝ) : ℂ :=
  ∑ i ∈ S, perronSummand (a i) (u i) c t

/-- The contribution of one Dirichlet monomial to the truncated vertical integral. -/
noncomputable def perronTermContribution
    (a : ℂ) (u c T : ℝ) : ℂ :=
  ∫ t in -T..T, perronSummand a u c t ∂MeasureTheory.volume

/--
Pull a fixed complex coefficient and Perron normalization through the
vertical integral.  This is the scalar-linearity step for one monomial.
-/
theorem perron_summand_integral_factor
    (a : ℂ) (u c T : ℝ) :
    perronTermContribution a u c T =
      (perronScale * a) •
        (∫ t in -T..T,
          verticalPerronKernelIntegrand u c t ∂MeasureTheory.volume) := by
  change
    (∫ t in -T..T,
      (perronScale * a) • verticalPerronKernelIntegrand u c t
        ∂MeasureTheory.volume) =
      (perronScale * a) •
        (∫ t in -T..T,
          verticalPerronKernelIntegrand u c t ∂MeasureTheory.volume)
  exact intervalIntegral.integral_smul (perronScale * a)
    (fun t => verticalPerronKernelIntegrand u c t)

/--
Finite Perron interchange: the vertical integral of a finite Dirichlet
polynomial is the sum of the individual truncated Perron contributions.
This is the finite-sum step in Perron's method; no infinite series or limit
has been interchanged here.
-/
theorem finite_perron_interchange
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → ℂ) (u : ι → ℝ) (c T : ℝ)
    (hint : ∀ i ∈ S,
      IntervalIntegrable
        (fun t => perronSummand (a i) (u i) c t)
        MeasureTheory.volume (-T) T) :
    (∫ t in -T..T,
      finitePerronIntegrand S a u c t ∂MeasureTheory.volume) =
      ∑ i ∈ S, perronTermContribution (a i) (u i) c T := by
  simpa [finitePerronIntegrand, perronTermContribution] using
    (intervalIntegral.integral_finset_sum
      (a := -T) (b := T) (μ := MeasureTheory.volume) hint)

/--
Finite Perron interchange in kernel form.  This is the useful form for a
finite Dirichlet polynomial: each coefficient multiplies its own truncated
kernel integral.  The only analytic hypothesis is interval integrability of
each summand on the finite segment.
-/
theorem finite_perron_interchange_kernel_form
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → ℂ) (u : ι → ℝ) (c T : ℝ)
    (hint : ∀ i ∈ S,
      IntervalIntegrable
        (fun t => perronSummand (a i) (u i) c t)
        MeasureTheory.volume (-T) T) :
    (∫ t in -T..T,
      finitePerronIntegrand S a u c t ∂MeasureTheory.volume) =
      ∑ i ∈ S,
        (perronScale * a i) •
          (∫ t in -T..T,
            verticalPerronKernelIntegrand (u i) c t
            ∂MeasureTheory.volume) := by
  rw [finite_perron_interchange S a u c T hint]
  apply Finset.sum_congr rfl
  intro i hi
  exact perron_summand_integral_factor (a i) (u i) c T

/--
For a finite Dirichlet polynomial, the summand indexed by `i` uses the
Perron ratio `u i`.  In the arithmetic application, take `u i = x / n_i`.
-/
theorem finite_perron_integrand_eq_sum
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → ℂ) (u : ι → ℝ) (c t : ℝ) :
    finitePerronIntegrand S a u c t =
      ∑ i ∈ S,
        (perronScale * a i) •
          (Complex.exp
            (((c : ℂ) + (t : ℂ) * Complex.I) * (Real.log (u i) : ℂ)) /
            ((c : ℂ) + (t : ℂ) * Complex.I)) := by
  rfl

end Imscribing
