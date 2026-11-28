import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Imscribing.Millennium.StarkRungFourGaussSign

/-!
# StarkRungFiveTheta — the theta-transformation brick (foundation of the
Schur / Dirichlet staircase)

The two remaining named inputs on the Stark ladder are the Gauss-sign
positivity `0 < (τ(χ)).re` (K3b's last kernel) and the Dirichlet class number
formula (K4).  Classically both are consequences of the *same* analytic
engine: the Jacobi theta transformation applied to the quadratic chirp, in
the form of the Landsberg–Schaar reciprocity (for the sign) and Dirichlet's
theta series with the quadratic character (for the class number formula).

This module lays the foundation: Mathlib's theta transformation
`Complex.tsum_exp_neg_mul_int_sq` (which is Poisson summation for the complex
Gaussian) specialized to the conductor `con = 4190205`.  For `t > 0` it
regularizes the divergent chirp `∑_n exp(2πi·n²/con)` by the heat-kernel
factor `exp(−π·t·n²/con)` and transforms it into a second theta series with
reciprocal parameter.  The `t ↦ 0⁺` asymptotics of both sides are the
Landsberg–Schaar computation whose constant term is `±√con`; the parity of
the primes `3, 683 ≡ 3 (mod 4)` (two of them) conspires with the half-phase
`e^{iπ/4}` factors to select the `+` sign, i.e. `τ(χ) = +√con` — this is the
Schur staircase proper, built on top of this brick.
-/

open Complex Real
open Imscribing.Millennium.StarkCharacterD2048

namespace Imscribing.Millennium.StarkTheta

/-- **Theta transformation specialized to the conductor.**  For real `t > 0`,
with complex parameter `a = (t − 2i)/con` (so `0 < a.re`), Mathlib's theta
transformation reads: the Abel-regularized chirp
`∑_n exp(−π·((t−2i)/con)·n²)` equals `(con/(t−2i))^{1/2}` times the dual
theta series `∑_n exp(−π·(con/(t−2i))·n²)`.  Note
`−π·((t−2i)/con)·n² = 2πi·n²/con − π·t·n²/con`, so the left side is the
heat-kernel regularization of the quadratic chirp. -/
theorem chirp_theta (t : ℝ) (ht : 0 < t) :
    (∑' n : ℤ, cexp (-↑π * (((t : ℂ) - 2 * I) / (con : ℂ)) * ((n : ℂ) ^ 2)))
      = 1 / (((t : ℂ) - 2 * I) / (con : ℂ)) ^ ((1 : ℂ) / 2) *
        ∑' n : ℤ, cexp (-↑π / (((t : ℂ) - 2 * I) / (con : ℂ)) * ((n : ℂ) ^ 2)) := by
  have ha : 0 < (((t : ℂ) - 2 * I) / (con : ℂ)).re := by
    have hre : (((t : ℂ) - 2 * I) / (con : ℂ)).re = t / (con : ℝ) := by
      rw [Complex.div_natCast_re, sub_re, ofReal_re, Complex.mul_I_re]
      simp
    rw [hre]
    exact div_pos ht (by norm_num : (0 : ℝ) < (con : ℝ))
  exact Complex.tsum_exp_neg_mul_int_sq ha

/-! ## Brick B0: even/odd split of a summable even function on `ℤ`

For the dual theta series `T(t) = ∑'_n exp(−c·n²)` the parity split is the
combinatorial core of the Landsberg–Schaar computation: the even terms carry
phase `1` and the odd terms carry phase `−i` (for `con ≡ 1 mod 4`), and the
two half-strength sums combine to the full-strength factor `(1 − i)`.  This
brick reduces the `ℤ`-indexed split to Mathlib's `ℕ`-indexed
`tsum_even_add_odd` via `tsum_nat_add_neg_add_one`. -/

/-- For summable `g : ℤ → ℂ` with `g(−k) = g(k)`, the full `ℤ`-sum equals
twice the sum of the `ℕ`-indexed even and odd parts, minus the `n = 0` term
(which the twice-counting double-charges). -/
theorem tsum_int_even_odd (g : ℤ → ℂ) (hg : Summable g) (hgeven : ∀ k : ℤ, g (-k) = g k) :
    (∑' k : ℤ, g k)
      = 2 * ((∑' n : ℕ, g ((2 * n : ℕ) : ℤ)) + (∑' n : ℕ, g ((2 * n + 1 : ℕ) : ℤ))) - g 0 := by
  have hcast : Summable (fun n : ℕ => g ((n : ℕ) : ℤ)) := hg.comp_injective Nat.cast_injective
  have hsucc : Summable (fun n : ℕ => g ((n : ℤ) + 1)) := by
    have hinj : Function.Injective (fun n : ℕ => (n : ℤ) + 1) := by
      intro a b hab
      push_cast at hab
      linarith
    exact hg.comp_injective hinj
  have h2 : Summable (fun k : ℕ => g ((2 * k : ℕ) : ℤ)) := by
    have hinj : Function.Injective (fun n : ℕ => ((2 * n : ℕ) : ℤ)) := by
      intro a b hab
      push_cast at hab
      linarith
    exact hg.comp_injective hinj
  have h3 : Summable (fun k : ℕ => g ((2 * k + 1 : ℕ) : ℤ)) := by
    have hinj : Function.Injective (fun n : ℕ => ((2 * n + 1 : ℕ) : ℤ)) := by
      intro a b hab
      push_cast at hab
      linarith
    exact hg.comp_injective hinj
  -- the ℕ-level even/odd split
  have hall : (∑' k : ℕ, g ((2 * k : ℕ) : ℤ)) + (∑' k : ℕ, g ((2 * k + 1 : ℕ) : ℤ))
      = ∑' k : ℕ, g ((k : ℕ) : ℤ) :=
    tsum_even_add_odd (f := fun n : ℕ => g ((n : ℕ) : ℤ)) h2 h3
  -- the shift: ∑'_ℕ g(↑n + 1) = ∑'_ℕ g(↑n) − g 0
  have hshift : (∑' n : ℕ, g ((n : ℤ) + 1)) = (∑' n : ℕ, g ((n : ℕ) : ℤ)) - g 0 := by
    have h := Summable.tsum_eq_zero_add hcast
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at h
    rw [add_comm (g 0)] at h
    exact eq_sub_of_add_eq h.symm
  -- the ℤ-split into nonnegative and negative parts
  have hz := tsum_nat_add_neg_add_one hg
  rw [← hz]
  have hneg : ∀ n : ℕ, g (-(↑n + 1)) = g (↑n + 1) := fun n => hgeven (↑n + 1)
  simp only [hneg]
  rw [hcast.tsum_add hsucc, hshift, ← hall]
  ring

/-- **Chirp form of the theta brick.**  The regularized sum is termwise the
chirp under the heat kernel: `exp(−π·((t−2i)/con)·n²) =
exp(2πi·n²/con)·exp(−π·t·n²/con)`. -/
theorem chirp_theta' (t : ℝ) (ht : 0 < t) :
    (∑' n : ℤ, cexp (2 * ↑π * I * ((n : ℂ) ^ 2 / (con : ℂ))
        - ↑π * (t : ℂ) * ((n : ℂ) ^ 2 / (con : ℂ))))
      = 1 / (((t : ℂ) - 2 * I) / (con : ℂ)) ^ ((1 : ℂ) / 2) *
        ∑' n : ℤ, cexp (-↑π / (((t : ℂ) - 2 * I) / (con : ℂ)) * ((n : ℂ) ^ 2)) := by
  have hterm : ∀ n : ℤ,
      cexp (2 * ↑π * I * ((n : ℂ) ^ 2 / (con : ℂ))
          - ↑π * (t : ℂ) * ((n : ℂ) ^ 2 / (con : ℂ)))
        = cexp (-↑π * (((t : ℂ) - 2 * I) / (con : ℂ)) * ((n : ℂ) ^ 2)) := by
    intro n
    exact congrArg cexp (by ring)
  have key := chirp_theta t ht
  rw [← key]
  simp only [hterm]

end Imscribing.Millennium.StarkTheta
