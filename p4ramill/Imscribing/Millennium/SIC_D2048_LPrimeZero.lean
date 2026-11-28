import Mathlib
import Imscribing.Millennium.SIC_D2048_StarkCharacter

/-!
# SIC_D2048_LPrimeZero — the L-side at the even-Hurwitz level

The first rung of the analytic wall (§3.3): for an even congruence function
`Φ : ZMod N → ℂ` with `Φ 0 = 0`, the odd part of the Hurwitz combination cancels
identically by the reindex `j ↦ -j`, and differentiating at `s = 0` the `log N`
term drops by the boundary value `hurwitzZetaEven_apply_zero`:

* `lfunction_eq_evenPart` :
  `LFunction Φ s = N ^ (-s) * ∑ j, Φ j * hurwitzZetaEven (ZMod.toAddCircle j) s`;
* `lfunction_even_deriv_zero` :
  `deriv (LFunction Φ) 0 = ∑ j, Φ j * deriv (hurwitzZetaEven (ZMod.toAddCircle j)) 0`.

Instance corollary for the Stark character of `F₂₀₄₈ = ℚ(√4190205)`:

* `qchar_lfunction_deriv_zero` : `L'(0, χ)` is a finite sum of boundary
  derivatives of the even Hurwitz zeta at the residue classes `j / 4190205`.

This is the classical Dirichlet position: no poles, no conditionally convergent
series, no digamma.
-/

open Complex Real Finset HurwitzZeta ZMod

noncomputable section

namespace Imscribing.Millennium.LPrimeZero

open Imscribing.Millennium.StarkCharacterD2048

variable {N : ℕ} [NeZero N]

theorem lfunction_eq_evenPart {Φ : ZMod N → ℂ} (hΦ : Φ.Even) (s : ℂ) :
    ZMod.LFunction Φ s = N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaEven (ZMod.toAddCircle j) s := by
  have hodd : ∑ j : ZMod N, Φ j * hurwitzZetaOdd (ZMod.toAddCircle j) s = 0 := by
    have hkey : ∑ j : ZMod N, Φ (-j) * hurwitzZetaOdd (ZMod.toAddCircle (-j)) s
        = ∑ j : ZMod N, Φ j * hurwitzZetaOdd (ZMod.toAddCircle j) s :=
      Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ fun j => rfl
    have hterm : ∑ j : ZMod N, Φ (-j) * hurwitzZetaOdd (ZMod.toAddCircle (-j)) s
        = ∑ j : ZMod N, -(Φ j * hurwitzZetaOdd (ZMod.toAddCircle j) s) :=
      Finset.sum_congr rfl fun j _ => by rw [hΦ j, map_neg, hurwitzZetaOdd_neg, mul_neg]
    have hre := Finset.sum_neg_distrib
      (f := fun (j : ZMod N) => Φ j * hurwitzZetaOdd (ZMod.toAddCircle j) s)
      (s := (Finset.univ : Finset (ZMod N)))
    have hpair : (∑ j : ZMod N, Φ (-j) * hurwitzZetaOdd (ZMod.toAddCircle (-j)) s)
        + (∑ j : ZMod N, Φ j * hurwitzZetaOdd (ZMod.toAddCircle j) s) = 0 := by
      rw [hterm, hre]
      exact neg_add_cancel _
    have hcoef : (2:ℂ) * (∑ j : ZMod N, Φ j * hurwitzZetaOdd (ZMod.toAddCircle j) s)
        = (∑ j : ZMod N, Φ (-j) * hurwitzZetaOdd (ZMod.toAddCircle (-j)) s)
        + (∑ j : ZMod N, Φ j * hurwitzZetaOdd (ZMod.toAddCircle j) s) := by
      rw [← hkey]
      ring
    have h2 : (2:ℂ) * (∑ j : ZMod N, Φ j * hurwitzZetaOdd (ZMod.toAddCircle j) s) = 0 := by
      rw [hcoef]
      exact hpair
    rcases mul_eq_zero.mp h2 with h | h
    · norm_num at h
    · exact h
  simp only [ZMod.LFunction, hurwitzZeta, mul_add, Finset.sum_add_distrib]
  rw [hodd, mul_zero, add_zero]

theorem lfunction_even_deriv_zero {Φ : ZMod N → ℂ} (hΦ : Φ.Even) (hΦ0 : Φ 0 = 0) :
    deriv (ZMod.LFunction Φ) 0 =
      ∑ j : ZMod N, Φ j * deriv (hurwitzZetaEven (ZMod.toAddCircle j)) 0 := by
  rw [show deriv (ZMod.LFunction Φ) 0 = deriv (fun s : ℂ => ZMod.LFunction Φ s) 0 from rfl]
  have hfun : (fun s : ℂ => ZMod.LFunction Φ s)
      = fun s : ℂ => (N:ℂ) ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaEven (ZMod.toAddCircle j) s :=
    funext fun s => lfunction_eq_evenPart hΦ s
  rw [hfun]
  have hcpow : (fun s : ℂ => (N:ℂ) ^ (-s)) = fun s : ℂ => cexp (-(log (N:ℂ) * s)) := by
    funext s
    rw [Complex.cpow_def_of_ne_zero (NeZero.ne (N : ℂ)) (-s)]
    congr 1
    ring
  have hA : HasDerivAt (fun s : ℂ => (N:ℂ) ^ (-s)) (-(log (N:ℂ))) 0 := by
    have hpos : HasDerivAt (fun s : ℂ => (log (N:ℂ)) * s) (log (N:ℂ)) 0 := by
      simpa using HasDerivAt.const_mul (log (N:ℂ)) (hasDerivAt_id (0:ℂ))
    have hA0 : HasDerivAt (fun s : ℂ => cexp (-(log (N:ℂ) * s)))
        (cexp (-(log (N:ℂ) * 0)) * (-(log (N:ℂ)))) 0 := hpos.neg.cexp
    rw [← hcpow] at hA0
    simpa using hA0
  have hE0 : ∑ j : ZMod N, Φ j * hurwitzZetaEven (ZMod.toAddCircle j) 0 = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rcases eq_or_ne j 0 with rfl | hj
    · rw [hΦ0, zero_mul]
    · rw [hurwitzZetaEven_apply_zero, if_neg (ZMod.toAddCircle_eq_zero.not.mpr hj), mul_zero]
  have hE : HasDerivAt (fun s : ℂ => ∑ j : ZMod N, Φ j * hurwitzZetaEven (ZMod.toAddCircle j) s)
      (∑ j : ZMod N, Φ j * deriv (hurwitzZetaEven (ZMod.toAddCircle j)) 0) 0 := by
    refine HasDerivAt.fun_sum (u := (Finset.univ : Finset (ZMod N))) fun j _ => ?_
    exact (differentiableAt_hurwitzZetaEven (ZMod.toAddCircle j)
      (by norm_num : (0:ℂ) ≠ 1)).hasDerivAt.const_mul (Φ j)
  simpa [hE0] using (hA.mul hE).deriv

/-- The Stark character's L-function derivative at zero, expressed as a finite sum of
even-Hurwitz boundary derivatives. -/
theorem qchar_lfunction_deriv_zero :
    deriv (ZMod.LFunction qchar) 0 =
      ∑ j : ZMod con, qchar j * deriv (hurwitzZetaEven (ZMod.toAddCircle j)) 0 :=
  lfunction_even_deriv_zero qchar_even qchar_zero

end Imscribing.Millennium.LPrimeZero

end
