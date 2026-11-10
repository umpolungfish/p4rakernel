import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev

open scoped BigOperators

namespace Imscribing

/-- Prefix sum of a coefficient sequence, written with a real cutoff. -/
noncomputable def weightedPrefix (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, c k

/--
The finite Abel-summation identity on a real interval.  The prime-harmonic
application takes `f t = 1/t` and `c k = if k is prime then log k else 0`.
The use of `Ioc` gives the convenient endpoint convention `A < k ≤ B`.
-/
theorem weightedPrefix_abel
    (c : ℕ → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B)
    (f : ℝ → ℝ)
    (hf_diff : ∀ t ∈ Set.Icc A B, DifferentiableAt ℝ f t)
    (hf_int : MeasureTheory.IntegrableOn (deriv f)
      (Set.Icc A B) MeasureTheory.volume) :
    (∑ k ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, f (k : ℝ) * c k)
      = f B * weightedPrefix c B
        - f A * weightedPrefix c A
        - ∫ t in Set.Ioc A B, deriv f t * weightedPrefix c t := by
  simpa [weightedPrefix] using
    (sum_mul_eq_sub_sub_integral_mul c hA hAB hf_diff hf_int)

/-- Logarithmic prime coefficient used in the Chebyshev theta function. -/
noncomputable def primeLogCoefficient (k : ℕ) : ℝ :=
  if Nat.Prime k then Real.log (k : ℝ) else 0

/-- Finite prime prefix `sum_{p ≤ x} log p`, in a form suited to Abel summation. -/
noncomputable def primeThetaPrefix (x : ℝ) : ℝ :=
  weightedPrefix primeLogCoefficient x

/--
Abel summation for the prime-harmonic interval.  This is the exact identity
that converts `sum_{A < p ≤ B} log(p)/p` into a theta-prefix expression.
-/
theorem primeHarmonic_abel
    {A B : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B)
    (hf_diff : ∀ t ∈ Set.Icc A B,
      DifferentiableAt ℝ (fun u : ℝ => u⁻¹) t)
    (hf_int : MeasureTheory.IntegrableOn
      (deriv (fun u : ℝ => u⁻¹))
      (Set.Icc A B) MeasureTheory.volume) :
    (∑ k ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊,
      (k : ℝ)⁻¹ * primeLogCoefficient k)
      = B⁻¹ * primeThetaPrefix B
        - A⁻¹ * primeThetaPrefix A
        - ∫ t in Set.Ioc A B,
          deriv (fun u : ℝ => u⁻¹) t * primeThetaPrefix t := by
  simpa [primeThetaPrefix, weightedPrefix] using
    (sum_mul_eq_sub_sub_integral_mul
      primeLogCoefficient hA hAB hf_diff hf_int)

end Imscribing
