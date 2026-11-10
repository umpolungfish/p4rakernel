import Imscribing.PerronKernelReal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section

namespace Imscribing

open Set MeasureTheory

/-- Finite-interval integration by parts for complex-valued functions. -/
theorem complex_interval_integral_by_parts
    {T U : ℝ} {F G F' G' : ℝ → ℂ}
    (hFcont : ContinuousOn F (Set.uIcc T U))
    (hGcont : ContinuousOn G (Set.uIcc T U))
    (hFderiv : ∀ x ∈ Set.Ioo (min T U) (max T U), HasDerivAt F (F' x) x)
    (hGderiv : ∀ x ∈ Set.Ioo (min T U) (max T U), HasDerivAt G (G' x) x)
    (hF' : IntervalIntegrable F' MeasureTheory.volume T U)
    (hG' : IntervalIntegrable G' MeasureTheory.volume T U)
    (hF'G : IntervalIntegrable (fun x => F' x * G x) MeasureTheory.volume T U)
    (hFG' : IntervalIntegrable (fun x => F x * G' x) MeasureTheory.volume T U) :
    (∫ x in T..U, F' x * G x) + (∫ x in T..U, F x * G' x) =
      F U * G U - F T * G T := by
  have h := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    hFcont hGcont hFderiv hGderiv hF' hG'
  rw [intervalIntegral.integral_add hF'G hFG'] at h
  exact h

/--
An oscillatory block bound obtained by one integration by parts.  On a block
`[T,U]` with `U ≤ 2T`, the endpoint terms contribute at most `2/(|a|T)`
and the differentiated-amplitude term contributes at most `1/(|a|T)`.
-/
theorem oscillatory_block_bound
    {T U a : ℝ} {F G F' G' : ℝ → ℂ}
    (ha : a ≠ 0)
    (hT : 0 < T)
    (hTU : T ≤ U)
    (hU : U ≤ 2 * T)
    (hFcont : ContinuousOn F (Set.uIcc T U))
    (hGcont : ContinuousOn G (Set.uIcc T U))
    (hFderiv : ∀ x ∈ Set.Ioo (min T U) (max T U), HasDerivAt F (F' x) x)
    (hGderiv : ∀ x ∈ Set.Ioo (min T U) (max T U), HasDerivAt G (G' x) x)
    (hF' : IntervalIntegrable F' MeasureTheory.volume T U)
    (hG' : IntervalIntegrable G' MeasureTheory.volume T U)
    (hF'G : IntervalIntegrable (fun x => F' x * G x) MeasureTheory.volume T U)
    (hFG' : IntervalIntegrable (fun x => F x * G' x) MeasureTheory.volume T U)
    (hFU : ‖F U‖ ≤ 1 / |a|)
    (hFT : ‖F T‖ ≤ 1 / |a|)
    (hGU : ‖G U‖ ≤ 1 / T)
    (hGT : ‖G T‖ ≤ 1 / T)
    (hFG'bound : ∀ x ∈ Set.Ioc T U,
      ‖F x * G' x‖ ≤ 1 / (|a| * T ^ 2)) :
    ‖∫ x in T..U, F' x * G x‖ ≤ 3 / (|a| * T) := by
  have hparts := complex_interval_integral_by_parts
    hFcont hGcont hFderiv hGderiv hF' hG' hF'G hFG'
  have hmain :
      (∫ x in T..U, F' x * G x) =
        F U * G U - F T * G T - (∫ x in T..U, F x * G' x) := by
    linear_combination hparts
  have hcorr :
      ‖∫ x in T..U, F x * G' x‖ ≤
        (1 / (|a| * T ^ 2)) * |U - T| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    apply hFG'bound x
    simpa [Set.uIoc, min_eq_left hTU, max_eq_right hTU] using hx
  have hlen : |U - T| ≤ T := by
    rw [abs_of_nonneg (sub_nonneg.mpr hTU)]
    linarith
  have haPos : 0 < |a| := abs_pos.mpr ha
  have ha0 : |a| ≠ 0 := ne_of_gt haPos
  have hT0 : T ≠ 0 := ne_of_gt hT
  have hUend : ‖F U * G U‖ ≤ 1 / (|a| * T) := by
    calc
      ‖F U * G U‖ = ‖F U‖ * ‖G U‖ := norm_mul _ _
      _ ≤ (1 / |a|) * (1 / T) :=
        mul_le_mul hFU hGU (norm_nonneg _) (by positivity)
      _ = 1 / (|a| * T) := by field_simp [ha0, hT0]
  have hTend : ‖F T * G T‖ ≤ 1 / (|a| * T) := by
    calc
      ‖F T * G T‖ = ‖F T‖ * ‖G T‖ := norm_mul _ _
      _ ≤ (1 / |a|) * (1 / T) :=
        mul_le_mul hFT hGT (norm_nonneg _) (by positivity)
      _ = 1 / (|a| * T) := by field_simp [ha0, hT0]
  have hcorr' :
      ‖∫ x in T..U, F x * G' x‖ ≤ 1 / (|a| * T) := by
    calc
      ‖∫ x in T..U, F x * G' x‖ ≤
          (1 / (|a| * T ^ 2)) * |U - T| := hcorr
      _ ≤ (1 / (|a| * T ^ 2)) * T := by
        exact mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = 1 / (|a| * T) := by field_simp [ha0, hT0]
  have hsum :
      ‖F U * G U‖ + ‖F T * G T‖ +
        ‖∫ x in T..U, F x * G' x‖ ≤ 3 / (|a| * T) := by
    calc
      ‖F U * G U‖ + ‖F T * G T‖ +
          ‖∫ x in T..U, F x * G' x‖
        ≤ 1 / (|a| * T) + 1 / (|a| * T) +
            1 / (|a| * T) := by
              exact add_le_add (add_le_add hUend hTend) hcorr'
      _ = 3 / (|a| * T) := by ring
  calc
    ‖∫ x in T..U, F' x * G x‖ =
        ‖F U * G U - F T * G T - (∫ x in T..U, F x * G' x)‖ := by
          rw [hmain]
    _ ≤ ‖F U * G U - F T * G T‖ +
        ‖∫ x in T..U, F x * G' x‖ := norm_sub_le _ _
    _ ≤ ‖F U * G U‖ + ‖F T * G T‖ +
        ‖∫ x in T..U, F x * G' x‖ := by
          exact add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ 3 / (|a| * T) := hsum

/-- The oscillatory phase `exp(i*a*t)` on a vertical Perron line. -/
noncomputable def perronOscillatoryPhase (a t : ℝ) : ℂ :=
  Complex.exp (((a * t : ℝ) : ℂ) * Complex.I)

/-- The reciprocal vertical-line amplitude `1/(c+i*t)`. -/
noncomputable def perronOscillatoryAmplitude (c t : ℝ) : ℂ :=
  1 / ((c : ℂ) + (t : ℂ) * Complex.I)

/-- An antiderivative of the phase when `a` is nonzero. -/
noncomputable def perronOscillatoryPrimitive (a t : ℝ) : ℂ :=
  perronOscillatoryPhase a t / (Complex.I * (a : ℂ))

/-- Derivative of the reciprocal vertical-line amplitude. -/
noncomputable def perronOscillatoryAmplitudeDeriv (c t : ℝ) : ℂ :=
  -Complex.I / (((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)

/-- Algebraic factorization of the off-diagonal Perron integrand. -/
theorem verticalPerronKernelIntegrand_factor (u c t : ℝ) :
    verticalPerronKernelIntegrand u c t =
      (Real.exp (c * Real.log u) : ℂ) *
        (perronOscillatoryPhase (Real.log u) t *
          perronOscillatoryAmplitude c t) := by
  have harg :
      (((c : ℂ) + (t : ℂ) * Complex.I) * (Real.log u : ℂ)) =
        (c * Real.log u : ℂ) +
          (((Real.log u * t : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  simp only [verticalPerronKernelIntegrand, perronOscillatoryPhase,
    perronOscillatoryAmplitude]
  have hcast :
      (c : ℂ) * (Real.log u : ℂ) = ((c * Real.log u : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [harg, Complex.exp_add, hcast, ← Complex.ofReal_exp]
  simp only [div_eq_mul_inv, one_mul]
  exact mul_assoc _ _ _

/--
The Perron off-diagonal block estimate, once the elementary derivative and
pointwise norm facts for the phase primitive and reciprocal amplitude are
supplied.  The interval is restricted to one dyadic block, `U ≤ 2T`.
-/
theorem perronOscillatoryBlock_bound
    (u c T U : ℝ)
    (hT : 0 < T)
    (hTU : T ≤ U)
    (hU : U ≤ 2 * T)
    (ha : Real.log u ≠ 0)
    (hFcont : ContinuousOn (perronOscillatoryPrimitive (Real.log u)) (Set.uIcc T U))
    (hGcont : ContinuousOn (perronOscillatoryAmplitude c) (Set.uIcc T U))
    (hFderiv : ∀ x ∈ Set.Ioo T U,
      HasDerivAt (perronOscillatoryPrimitive (Real.log u))
        (perronOscillatoryPhase (Real.log u) x) x)
    (hGderiv : ∀ x ∈ Set.Ioo T U,
      HasDerivAt (perronOscillatoryAmplitude c)
        (perronOscillatoryAmplitudeDeriv c x) x)
    (hF' : IntervalIntegrable (perronOscillatoryPhase (Real.log u))
      MeasureTheory.volume T U)
    (hG' : IntervalIntegrable (perronOscillatoryAmplitudeDeriv c)
      MeasureTheory.volume T U)
    (hF'G : IntervalIntegrable
      (fun x => perronOscillatoryPhase (Real.log u) x *
        perronOscillatoryAmplitude c x) MeasureTheory.volume T U)
    (hFG' : IntervalIntegrable
      (fun x => perronOscillatoryPrimitive (Real.log u) x *
        perronOscillatoryAmplitudeDeriv c x) MeasureTheory.volume T U)
    (hFU : ‖perronOscillatoryPrimitive (Real.log u) U‖ ≤ 1 / |Real.log u|)
    (hFT : ‖perronOscillatoryPrimitive (Real.log u) T‖ ≤ 1 / |Real.log u|)
    (hGU : ‖perronOscillatoryAmplitude c U‖ ≤ 1 / T)
    (hGT : ‖perronOscillatoryAmplitude c T‖ ≤ 1 / T)
    (hFG'bound : ∀ x ∈ Set.Ioc T U,
      ‖perronOscillatoryPrimitive (Real.log u) x *
        perronOscillatoryAmplitudeDeriv c x‖ ≤
          1 / (|Real.log u| * T ^ 2)) :
    ‖∫ x in T..U,
      perronOscillatoryPhase (Real.log u) x *
        perronOscillatoryAmplitude c x‖ ≤
      3 / (|Real.log u| * T) := by
  have hFderiv' : ∀ x ∈ Set.Ioo (min T U) (max T U),
      HasDerivAt (perronOscillatoryPrimitive (Real.log u))
        (perronOscillatoryPhase (Real.log u) x) x := by
    simpa [min_eq_left hTU, max_eq_right hTU] using hFderiv
  have hGderiv' : ∀ x ∈ Set.Ioo (min T U) (max T U),
      HasDerivAt (perronOscillatoryAmplitude c)
        (perronOscillatoryAmplitudeDeriv c x) x := by
    simpa [min_eq_left hTU, max_eq_right hTU] using hGderiv
  exact oscillatory_block_bound ha hT hTU hU
    hFcont hGcont hFderiv' hGderiv' hF' hG' hF'G hFG'
    hFU hFT hGU hGT hFG'bound

/--
The same block estimate for the original Perron integrand.  The factor
`exp(c*log u)` is constant in the height variable.
-/
theorem verticalPerronKernel_block_bound
    (u c T U : ℝ)
    (hT : 0 < T)
    (hTU : T ≤ U)
    (hU : U ≤ 2 * T)
    (ha : Real.log u ≠ 0)
    (hFcont : ContinuousOn (perronOscillatoryPrimitive (Real.log u)) (Set.uIcc T U))
    (hGcont : ContinuousOn (perronOscillatoryAmplitude c) (Set.uIcc T U))
    (hFderiv : ∀ x ∈ Set.Ioo T U,
      HasDerivAt (perronOscillatoryPrimitive (Real.log u))
        (perronOscillatoryPhase (Real.log u) x) x)
    (hGderiv : ∀ x ∈ Set.Ioo T U,
      HasDerivAt (perronOscillatoryAmplitude c)
        (perronOscillatoryAmplitudeDeriv c x) x)
    (hF' : IntervalIntegrable (perronOscillatoryPhase (Real.log u))
      MeasureTheory.volume T U)
    (hG' : IntervalIntegrable (perronOscillatoryAmplitudeDeriv c)
      MeasureTheory.volume T U)
    (hF'G : IntervalIntegrable
      (fun x => perronOscillatoryPhase (Real.log u) x *
        perronOscillatoryAmplitude c x) MeasureTheory.volume T U)
    (hFG' : IntervalIntegrable
      (fun x => perronOscillatoryPrimitive (Real.log u) x *
        perronOscillatoryAmplitudeDeriv c x) MeasureTheory.volume T U)
    (hFU : ‖perronOscillatoryPrimitive (Real.log u) U‖ ≤ 1 / |Real.log u|)
    (hFT : ‖perronOscillatoryPrimitive (Real.log u) T‖ ≤ 1 / |Real.log u|)
    (hGU : ‖perronOscillatoryAmplitude c U‖ ≤ 1 / T)
    (hGT : ‖perronOscillatoryAmplitude c T‖ ≤ 1 / T)
    (hFG'bound : ∀ x ∈ Set.Ioc T U,
      ‖perronOscillatoryPrimitive (Real.log u) x *
        perronOscillatoryAmplitudeDeriv c x‖ ≤
          1 / (|Real.log u| * T ^ 2)) :
    ‖∫ x in T..U, verticalPerronKernelIntegrand u c x‖ ≤
      3 * Real.exp (c * Real.log u) / (|Real.log u| * T) := by
  have hcore := perronOscillatoryBlock_bound u c T U hT hTU hU ha
    hFcont hGcont hFderiv hGderiv hF' hG' hF'G hFG'
    hFU hFT hGU hGT hFG'bound
  have hfactor :
      (∫ x in T..U, verticalPerronKernelIntegrand u c x) =
        (Real.exp (c * Real.log u) : ℂ) *
          (∫ x in T..U,
            perronOscillatoryPhase (Real.log u) x *
              perronOscillatoryAmplitude c x) := by
    calc
      (∫ x in T..U, verticalPerronKernelIntegrand u c x) =
          ∫ x in T..U,
            (Real.exp (c * Real.log u) : ℂ) *
              (perronOscillatoryPhase (Real.log u) x *
                perronOscillatoryAmplitude c x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact verticalPerronKernelIntegrand_factor u c x
      _ = (Real.exp (c * Real.log u) : ℂ) *
          (∫ x in T..U,
            perronOscillatoryPhase (Real.log u) x *
              perronOscillatoryAmplitude c x) := by
        rw [intervalIntegral.integral_const_mul]
  have hexpNorm :
      ‖(Real.exp (c * Real.log u) : ℂ)‖ = Real.exp (c * Real.log u) := by
    exact Complex.norm_of_nonneg (le_of_lt (Real.exp_pos _))
  calc
    ‖∫ x in T..U, verticalPerronKernelIntegrand u c x‖ =
        ‖(Real.exp (c * Real.log u) : ℂ) *
          (∫ x in T..U,
            perronOscillatoryPhase (Real.log u) x *
              perronOscillatoryAmplitude c x)‖ := by rw [hfactor]
    _ = Real.exp (c * Real.log u) *
        ‖∫ x in T..U,
          perronOscillatoryPhase (Real.log u) x *
            perronOscillatoryAmplitude c x‖ := by
          rw [norm_mul, hexpNorm]
    _ ≤ Real.exp (c * Real.log u) *
        (3 / (|Real.log u| * T)) :=
          mul_le_mul_of_nonneg_left hcore (le_of_lt (Real.exp_pos _))
    _ = 3 * Real.exp (c * Real.log u) / (|Real.log u| * T) := by ring

end Imscribing
