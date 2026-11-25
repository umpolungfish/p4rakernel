import Mathlib
import Imscribing.Millennium.Erdos.Proofs.MontgomeryVaughan220.Fourier
open Erdos220
open scoped ComplexConjugate
namespace Imscribing.Millennium.WKExpand
noncomputable section

variable (d : ℕ) [NeZero d]
local notation "w" => fourierRoot d

def nu (N : ZMod d → ℝ) (b : ZMod d) : ℂ :=
  ∑ k : ZMod d, (N k : ℂ) * w ^ (b * k).val

/-- The product star(nu_b)*nu_b expanded as a double sum - the algebraic
    first half of Wiener-Khinchin. -/
theorem wk_expand (N : ZMod d → ℝ) (b : ZMod d) :
    star (nu d N b) * nu d N b =
      ∑ k : ZMod d, ∑ l : ZMod d,
        ((N l : ℝ) : ℂ) * (star w) ^ (b*l).val * ((N k : ℝ) : ℂ) * w ^ (b*k).val := by
  simp [nu, star_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- The Fourier root has unit modulus: ‖fourierRoot q‖ = 1. -/
theorem fourierRoot_norm (q : ℕ) (hq : 0 < q) : ‖fourierRoot q‖ = 1 := by
  rw [fourierRoot, Complex.norm_exp]
  simp

/-- star w * w = normSq w = ‖w‖^2 = 1. -/
theorem fourierRoot_star_mul (q : ℕ) (hq : 0 < q) :
    star (fourierRoot q) * fourierRoot q = 1 := by
  have h := Complex.mul_conj (fourierRoot q)
  -- mul_conj: z * conj z = normSq z
  have hn : Complex.normSq (fourierRoot q) = 1 := by
    rw [Complex.normSq_eq_norm_sq, fourierRoot_norm q hq]
    ring
  change conj (fourierRoot q) * fourierRoot q = 1
  rw [mul_comm]
  rw [h, hn]
  norm_num


end
end WKExpand
