import Imscribing.PerronFinite

noncomputable section

open scoped BigOperators

namespace Imscribing

/-- The real part of the vertical Perron integrand, written explicitly in real
coordinates.  Here `y = log u`; the factor `exp (c*y)` is `u^c`. -/
noncomputable def verticalPerronRealIntegrand (u c t : ℝ) : ℝ :=
  Real.exp (c * Real.log u) *
    (c * Real.cos (t * Real.log u) + t * Real.sin (t * Real.log u)) /
      (c ^ 2 + t ^ 2)

/-- The imaginary part of the vertical Perron integrand, written explicitly in
real coordinates. -/
noncomputable def verticalPerronImagIntegrand (u c t : ℝ) : ℝ :=
  Real.exp (c * Real.log u) *
    (c * Real.sin (t * Real.log u) - t * Real.cos (t * Real.log u)) /
      (c ^ 2 + t ^ 2)

private theorem verticalPerronExponent_re (u c t : ℝ) :
    ((((c : ℂ) + (t : ℂ) * Complex.I) * (Real.log u : ℂ)).re) =
      c * Real.log u := by
  simp

private theorem verticalPerronExponent_im (u c t : ℝ) :
    ((((c : ℂ) + (t : ℂ) * Complex.I) * (Real.log u : ℂ)).im) =
      t * Real.log u := by
  simp

private theorem verticalPerronDenominator_re (c t : ℝ) :
    (((c : ℂ) + (t : ℂ) * Complex.I).re) = c := by
  simp

private theorem verticalPerronDenominator_im (c t : ℝ) :
    (((c : ℂ) + (t : ℂ) * Complex.I).im) = t := by
  simp

private theorem verticalPerronDenominator_normSq (c t : ℝ) :
    Complex.normSq ((c : ℂ) + (t : ℂ) * Complex.I) = c ^ 2 + t ^ 2 := by
  rw [Complex.normSq_apply]
  simp
  ring

/-- Explicit real-coordinate formula for the real part of `u^(c+it)/(c+it)`. -/
theorem verticalPerronKernelIntegrand_re (u c t : ℝ) :
    (verticalPerronKernelIntegrand u c t).re =
      verticalPerronRealIntegrand u c t := by
  change
    (Complex.exp
      (((c : ℂ) + (t : ℂ) * Complex.I) * (Real.log u : ℂ)) /
      ((c : ℂ) + (t : ℂ) * Complex.I)).re = _
  rw [Complex.div_re, Complex.exp_re, Complex.exp_im,
    verticalPerronExponent_re, verticalPerronExponent_im,
    verticalPerronDenominator_re, verticalPerronDenominator_im,
    verticalPerronDenominator_normSq]
  unfold verticalPerronRealIntegrand
  ring

/-- Explicit real-coordinate formula for the imaginary part of
`u^(c+it)/(c+it)`. -/
theorem verticalPerronKernelIntegrand_im (u c t : ℝ) :
    (verticalPerronKernelIntegrand u c t).im =
      verticalPerronImagIntegrand u c t := by
  change
    (Complex.exp
      (((c : ℂ) + (t : ℂ) * Complex.I) * (Real.log u : ℂ)) /
      ((c : ℂ) + (t : ℂ) * Complex.I)).im = _
  rw [Complex.div_im, Complex.exp_re, Complex.exp_im,
    verticalPerronExponent_re, verticalPerronExponent_im,
    verticalPerronDenominator_re, verticalPerronDenominator_im,
    verticalPerronDenominator_normSq]
  unfold verticalPerronImagIntegrand
  ring

/-- The complex vertical integrand is exactly its real-coordinate decomposition. -/
theorem verticalPerronKernelIntegrand_eq_re_add_im (u c t : ℝ) :
    verticalPerronKernelIntegrand u c t =
      (verticalPerronRealIntegrand u c t : ℂ) +
        (verticalPerronImagIntegrand u c t : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [verticalPerronKernelIntegrand_re]
  · simp [verticalPerronKernelIntegrand_im]

/-- The real-coordinate Perron integrand is even in the height variable. -/
theorem verticalPerronRealIntegrand_even (u c t : ℝ) :
    verticalPerronRealIntegrand u c (-t) =
      verticalPerronRealIntegrand u c t := by
  simp [verticalPerronRealIntegrand, Real.cos_neg, Real.sin_neg]

/-- The imaginary-coordinate Perron integrand is odd in the height variable. -/
theorem verticalPerronImagIntegrand_odd (u c t : ℝ) :
    verticalPerronImagIntegrand u c (-t) =
      -verticalPerronImagIntegrand u c t := by
  simp [verticalPerronImagIntegrand, Real.cos_neg, Real.sin_neg]
  ring

/-- On the diagonal `u = 1`, the real-coordinate integrand is the elementary
Cauchy kernel. -/
theorem verticalPerronRealIntegrand_one (c t : ℝ) :
    verticalPerronRealIntegrand 1 c t = c / (c ^ 2 + t ^ 2) := by
  simp [verticalPerronRealIntegrand]

/-- On the diagonal `u = 1`, the imaginary-coordinate integrand is odd and
has the elementary rational form. -/
theorem verticalPerronImagIntegrand_one (c t : ℝ) :
    verticalPerronImagIntegrand 1 c t = -t / (c ^ 2 + t ^ 2) := by
  simp [verticalPerronImagIntegrand]

/-- For a positive vertical line `c`, the original complex Perron integrand is
continuous, hence interval-integrable on every finite height interval. -/
theorem verticalPerronKernelIntegrand_intervalIntegrable
    (u c a b : ℝ) (hc : 0 < c) :
    IntervalIntegrable
      (fun t => verticalPerronKernelIntegrand u c t)
      MeasureTheory.volume a b := by
  have hnum : Continuous (fun t : ℝ =>
      Complex.exp (((c : ℂ) + (t : ℂ) * Complex.I) * (Real.log u : ℂ))) := by
    fun_prop
  have hden : Continuous (fun t : ℝ =>
      (c : ℂ) + (t : ℂ) * Complex.I) := by
    fun_prop
  have hden_ne : ∀ t : ℝ,
      (c : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro t ht
    have hc0 : c = 0 := by
      have h := congrArg Complex.re ht
      simpa using h
    exact (ne_of_gt hc) hc0
  change IntervalIntegrable
    (fun t => Complex.exp (((c : ℂ) + (t : ℂ) * Complex.I) * (Real.log u : ℂ)) /
      ((c : ℂ) + (t : ℂ) * Complex.I))
    MeasureTheory.volume a b
  exact (hnum.div hden hden_ne).intervalIntegrable _ _

/-- The real-coordinate integrand is interval-integrable on every finite
interval when `c` is positive. -/
theorem verticalPerronRealIntegrand_intervalIntegrable
    (u c a b : ℝ) (hc : 0 < c) :
    IntervalIntegrable (fun t => verticalPerronRealIntegrand u c t)
      MeasureTheory.volume a b := by
  have hnum : Continuous (fun t : ℝ =>
      Real.exp (c * Real.log u) *
        (c * Real.cos (t * Real.log u) + t * Real.sin (t * Real.log u))) := by
    fun_prop
  have hden : Continuous (fun t : ℝ => c ^ 2 + t ^ 2) := by
    fun_prop
  have hden_ne : ∀ t : ℝ, c ^ 2 + t ^ 2 ≠ 0 := by
    intro t ht
    have hpos : 0 < c ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
    exact (ne_of_gt hpos) ht
  unfold verticalPerronRealIntegrand
  exact (hnum.div hden hden_ne).intervalIntegrable _ _

/-- The imaginary-coordinate integrand is interval-integrable on every finite
interval when `c` is positive. -/
theorem verticalPerronImagIntegrand_intervalIntegrable
    (u c a b : ℝ) (hc : 0 < c) :
    IntervalIntegrable (fun t => verticalPerronImagIntegrand u c t)
      MeasureTheory.volume a b := by
  have hnum : Continuous (fun t : ℝ =>
      Real.exp (c * Real.log u) *
        (c * Real.sin (t * Real.log u) - t * Real.cos (t * Real.log u))) := by
    fun_prop
  have hden : Continuous (fun t : ℝ => c ^ 2 + t ^ 2) := by
    fun_prop
  have hden_ne : ∀ t : ℝ, c ^ 2 + t ^ 2 ≠ 0 := by
    intro t ht
    have hpos : 0 < c ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
    exact (ne_of_gt hpos) ht
  unfold verticalPerronImagIntegrand
  exact (hnum.div hden hden_ne).intervalIntegrable _ _

/-- The normalized real part of the finite vertical Perron kernel. -/
noncomputable def perronTruncatedRealKernel (u c T : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (∫ t in -T..T, verticalPerronRealIntegrand u c t)

/-- The normalized imaginary part of the finite vertical Perron kernel. -/
noncomputable def perronTruncatedImagKernel (u c T : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (∫ t in -T..T, verticalPerronImagIntegrand u c t)

/-- Exact diagonal reduction of the finite Perron kernel to the Cauchy integral.
The subsequent limit `T → ∞` is `1/2` when `c > 0`. -/
theorem perronTruncatedRealKernel_one (c T : ℝ) :
    perronTruncatedRealKernel 1 c T =
      (1 / (2 * Real.pi)) *
        (∫ t in -T..T, c / (c ^ 2 + t ^ 2)) := by
  simp [perronTruncatedRealKernel, verticalPerronRealIntegrand_one]

/-- Exact diagonal reduction of the imaginary kernel.  Its integral over a
symmetric interval vanishes because the integrand is odd; that integral
identity is kept separate from this pointwise theorem. -/
theorem perronDiagonalImagIntegrand (c t : ℝ) :
    verticalPerronImagIntegrand 1 c t = -t / (c ^ 2 + t ^ 2) :=
  verticalPerronImagIntegrand_one c t

end Imscribing
