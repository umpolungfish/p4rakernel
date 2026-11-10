import Imscribing.PerronKernelReal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

namespace Imscribing

/-- Exact evaluation of the diagonal Cauchy-kernel integral. -/
theorem perronDiagonalCauchyIntegral (c T : ℝ) :
    (∫ t in -T..T, c / (c ^ 2 + t ^ 2)) =
      2 * Real.arctan (T / c) := by
  calc
    (∫ t in -T..T, c / (c ^ 2 + t ^ 2)) =
        Real.arctan (T / c) - Real.arctan ((-T) / c) :=
      integral_div_sq_add_sq
    _ = 2 * Real.arctan (T / c) := by
      rw [show (-T) / c = -(T / c) by ring, Real.arctan_neg]
      ring

/-- The normalized finite diagonal Perron kernel is an arctangent quotient. -/
theorem perronTruncatedRealKernel_one_eq_arctan (c T : ℝ) :
    perronTruncatedRealKernel 1 c T = Real.arctan (T / c) / Real.pi := by
  rw [perronTruncatedRealKernel_one, perronDiagonalCauchyIntegral]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi]
  <;> ring

/-- For a positive abscissa, the scaled height `T / c` tends to `+∞`. -/
theorem tendsto_div_const_atTop_of_pos (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun T : ℝ => T / c) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.2
  intro B
  exact Filter.eventually_atTop.2
    ⟨B * c, fun T hT => (le_div_iff₀ hc).2 hT⟩

/-- The diagonal finite Perron kernel converges to one half as the height
 tends to infinity. -/
theorem perronTruncatedRealKernel_one_tendsto_half (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun T : ℝ => perronTruncatedRealKernel 1 c T)
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
  have hdiv := tendsto_div_const_atTop_of_pos c hc
  have harc := Real.tendsto_arctan_atTop.comp hdiv
  have harc' : Filter.Tendsto (fun T : ℝ => Real.arctan (T / c))
      Filter.atTop (nhds (Real.pi / 2)) :=
    harc.mono_right nhdsWithin_le_nhds
  have hscaled := harc'.div_const Real.pi
  have hhalf : (Real.pi / 2) / Real.pi = (1 / 2 : ℝ) := by
    field_simp [Real.pi_ne_zero]
  simpa only [perronTruncatedRealKernel_one_eq_arctan, hhalf] using hscaled

end Imscribing
