import Mathlib

/-! One carried complex return supplies both the fixed-point equation and its
zero mechanical residual. This does not assert that a particular source map
has already attained zero, or discard its source scale or conflict evidence. -/
namespace Imscribing.Biochem.RetainedReturnClosure

def residual {n : ℕ} (returned carried : Fin n → ℂ) : ℝ :=
  ∑ i, Complex.normSq (returned i-carried i)

theorem residual_nonnegative {n : ℕ} (returned carried : Fin n → ℂ) :
    0 ≤ residual returned carried := by
  exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)

theorem zero_iff_same_return {n : ℕ} (returned carried : Fin n → ℂ) :
    residual returned carried=0 ↔ returned=carried := by
  simp only [residual, Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Complex.normSq_nonneg (returned i-carried i)),
    Finset.mem_univ, forall_const, Complex.normSq_eq_zero, sub_eq_zero]
  exact funext_iff.symm

theorem fixed_point_is_mechanical_zero {n : ℕ}
    (step : (Fin n → ℂ) → (Fin n → ℂ)) (carried : Fin n → ℂ) :
    residual (step carried) carried=0 ↔ step carried=carried :=
  zero_iff_same_return _ _

#print axioms residual_nonnegative
#print axioms zero_iff_same_return
#print axioms fixed_point_is_mechanical_zero
end Imscribing.Biochem.RetainedReturnClosure
