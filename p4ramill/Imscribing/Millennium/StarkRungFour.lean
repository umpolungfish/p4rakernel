import Mathlib
import Imscribing.Millennium.StarkRungOne
import Imscribing.Millennium.SIC_D2048_Moduli

/-!
# StarkRungFour: rung 4 — the L-side meets the unit side

Rung 1 (registered as `StarkRungOne`) gives the L-side of the Stark track:

* `2 · L′(0, χ) = τ(χ) · L(1, χ)` (`two_lprime_zero_eq_tau`),
* `Re(τ(χ) · L(1, χ)) = −∑_j χ(j)·log(2·sin(π·j/con))` (`re_tau_mul_L_one_eq_log_sum`).

Rung 4 chains these into the real-quadratic regulator form of the Stark
Theorem. The unconditional piece:

* `two_re_lprime_zero_eq_neg_log_sum`: **2 · Re L′(0, χ) = −∑_j χ(j)·log(2·sin(π·j/con))**.

The deep input is the Kronecker class-number relation — the analytic class
number formula for `F = ℚ(√4190205)` in its product form, `ε^h = ∏ (2sin)⁻χ`
— which is not formalized here; it enters as the explicit hypothesis `hKNR`:

* `re_lprime_zero_eq_hRegulator`: given the class-number relation,
  **Re L′(0, χ) = h · log ε** — the Stark form `log|ε^σ| = L′(0,χ)` with the
  Stark unit `ε^σ = ε^h` (`h = hilbert_class_degree = 64`, the registered
  class number of `F`), i.e. the identification into
  `ClinkStarkBridge.regulator_identity`'s `ε = epsilonReal 2048`.

* `moduli_regulator_eq_log_epsilonReal`: the registered regulator
  `SIC.D2048.Moduli.regulator = log((2047 + √4190205)/2)` is exactly
  `log(epsilonReal 2048)` — the same unit.
-/

open Complex Real Filter Finset
open ZMod
open Imscribing.Millennium.StarkCharacterD2048
open Imscribing.Millennium.StarkGaussSum
open Imscribing.Millennium.StarkRungOne
open Imscribing.Millennium.ClinkStarkBridge

noncomputable section

namespace Imscribing.Millennium.StarkRungFour

/-- The real part of twice a complex number is twice its real part. -/
private theorem reCLM_two_mul (z : ℂ) : Complex.reCLM (2 * z) = 2 * Complex.reCLM z := by
  have h : ∀ w : ℂ, Complex.reCLM w = w.re := fun _ => rfl
  rw [h, h, Complex.mul_re]
  norm_num

/-- **Rung 4, L-side corollary.** `2 · Re L′(0, χ) = −∑_j χ(j)·log(2·sin(π·j/con))`
for the Stark character of conductor 4190205 — the real form of rung 1,
obtained by taking real parts of the two registered rung-1 identities. -/
theorem two_re_lprime_zero_eq_neg_log_sum :
    2 * Complex.reCLM (deriv (ZMod.LFunction qchar) 0)
      = ∑ j : ZMod con, qcharR j
          * -(Real.log (2 * Real.sin (Real.pi * (j.val : ℝ) / (con : ℝ)))) := by
  calc 2 * Complex.reCLM (deriv (ZMod.LFunction qchar) 0)
      = Complex.reCLM (2 * deriv (ZMod.LFunction qchar) 0) := (reCLM_two_mul _).symm
    _ = Complex.reCLM (gaussSum qchar' stdAddChar * ZMod.LFunction qchar 1) := by
        rw [two_lprime_zero_eq_tau]
    _ = ∑ j : ZMod con, qcharR j
          * -(Real.log (2 * Real.sin (Real.pi * (j.val : ℝ) / (con : ℝ)))) :=
        re_tau_mul_L_one_eq_log_sum

/-- The registered class number of `F = ℚ(√4190205)`. -/
abbrev hField : ℕ := SIC.D2048.Moduli.hilbert_class_degree

theorem hField_val : hField = 64 := SIC.D2048.Moduli.hilbert_class_degree_val

/-- The registered regulator `R_F = log((2047 + √4190205)/2)` is exactly
`log(epsilonReal 2048)` — the two files name the same unit. -/
theorem moduli_regulator_eq_log_epsilonReal :
    SIC.D2048.Moduli.regulator = Real.log (epsilonReal 2048) := by
  have h : epsilonReal 2048 = ((2047 : ℝ) + Real.sqrt 4190205) / 2 := by
    unfold epsilonReal
    have hc : ((((2048 : ℕ) : ℝ) - 3) * (((2048 : ℕ) : ℝ) + 1)) = 4190205 := by
      norm_num
    rw [hc]
    norm_num
  unfold SIC.D2048.Moduli.regulator
  rw [h]

/-- **Rung 4, the identification.** Given the Kronecker class-number relation
`−∑_j χ(j)·log(2·sin(π·j/con)) = 2h·log ε` (the analytic class number formula
for `F = ℚ(√4190205)` in product form — the deep input, hypothesis `hKNR`),
the L-side matches the unit side: `Re L′(0, χ) = h · log ε`. This is the
Stark Theorem in its real-quadratic form `log|ε^σ| = L′(0,χ)`, with the Stark
unit `ε^σ = ε^h`, `h = 64`, and `ε = epsilonReal 2048` the unit of
`ClinkStarkBridge.regulator_identity`. -/
theorem re_lprime_zero_eq_hRegulator
    (hKNR : ∑ j : ZMod con, qcharR j
        * -(Real.log (2 * Real.sin (Real.pi * (j.val : ℝ) / (con : ℝ))))
      = 2 * ((hField : ℕ) : ℝ) * Real.log (epsilonReal 2048)) :
    Complex.reCLM (deriv (ZMod.LFunction qchar) 0)
      = ((hField : ℕ) : ℝ) * Real.log (epsilonReal 2048) := by
  have h1 := two_re_lprime_zero_eq_neg_log_sum
  rw [hKNR] at h1
  linarith

/-- **Rung 4, Stark form.** The same identification written with the Stark
unit `ε^σ = ε^h` itself: `Re L′(0, χ) = log(ε^h)` — `log|ε^σ| = L′(0,χ)`. -/
theorem re_lprime_zero_eq_log_stark_unit
    (hKNR : ∑ j : ZMod con, qcharR j
        * -(Real.log (2 * Real.sin (Real.pi * (j.val : ℝ) / (con : ℝ))))
      = 2 * ((hField : ℕ) : ℝ) * Real.log (epsilonReal 2048)) :
    Complex.reCLM (deriv (ZMod.LFunction qchar) 0)
      = Real.log (epsilonReal 2048 ^ hField) := by
  rw [Real.log_pow]
  exact re_lprime_zero_eq_hRegulator hKNR

end Imscribing.Millennium.StarkRungFour

end
