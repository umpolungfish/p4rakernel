import Imscribing.PrimeWeightedAbel
import Mathlib.NumberTheory.Chebyshev

open scoped BigOperators

namespace Imscribing

/-- The prime-log prefix used by the Abel-summation development is exactly
Mathlib's Chebyshev theta function. -/
theorem primeThetaPrefix_eq_chebyshev_theta (x : ℝ) :
    primeThetaPrefix x = Chebyshev.theta x := by
  rw [primeThetaPrefix, weightedPrefix, Chebyshev.theta_eq_sum_Icc]
  simp [primeLogCoefficient, Finset.sum_filter]

/-- The PNT interface needed by the transfer estimates.  This is deliberately
stated as a theorem hypothesis here; the next bridge imports a PNT library and
proves this limit from its Chebyshev-psi theorem together with Mathlib's
psi-minus-theta bound. -/
def HasChebyshevThetaPNT : Prop :=
  Filter.Tendsto (fun x : ℝ => Chebyshev.theta x / x)
    Filter.atTop (nhds 1)

/-- A convenient eventual relative-error form of the Chebyshev theta PNT. -/
theorem theta_ratio_eventually_close
    (hPNT : HasChebyshevThetaPNT) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in Filter.atTop,
      |Chebyshev.theta x / x - 1| < ε := by
  have hdist := (Metric.tendsto_nhds.mp hPNT) ε hε
  filter_upwards [hdist] with x hx
  simpa [Real.dist_eq] using hx

end Imscribing
