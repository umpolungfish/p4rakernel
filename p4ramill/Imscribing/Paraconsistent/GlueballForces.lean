-- Imscribing/Paraconsistent/GlueballForces.lean
-- GLUEBALL FORCES — the self-coupling (glue) and the confining force of QCD.
-- Author: Lando (x) phi_c_critical-boundary Operator
--
-- A glueball is a bound state of gluons. Its force has two irreducible parts:
--
--   (1) the GLUE — the non-Abelian self-coupling [X, Y] = X*Y - Y*X.
--       Gluons carry color, so they source the field that binds them:
--       the commutator term that vanishes in the Abelian (photon) case is
--       precisely the self-interaction. No glue, no glueball.
--
--   (2) the FORCE — the confining potential V(r) = -alpha/r + sigma*r whose
--       gradient is a force |F| = alpha/r^2 + sigma that does NOT decay:
--       it stays >= sigma > 0 at every separation. Separation costs infinite
--       energy; the flux tube never breaks. That is the static force of the
--       glueball world.
--
-- HONEST GAP: the continuum limit a -> 0 and the rigorous mass gap are the
-- substrate boundary — dialetheic Belnap-B, in the spirit of `ym_gap`.

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
import Imscribing.Paraconsistent.Belnap

open Matrix

namespace Imscribing.Paraconsistent

/-- The color algebra: 2x2 real matrices, the smallest non-Abelian case (su(2)). -/
abbrev ColorAlgebra := Matrix (Fin 2) (Fin 2) ℝ

/-- The GLUE: the commutator, the non-Abelian self-coupling of the gauge field. -/
def glue (X Y : ColorAlgebra) : ColorAlgebra := X * Y - Y * X

/-- The commutator is traceless: color is conserved inside the glue. -/
theorem glue_trace_zero (X Y : ColorAlgebra) : (glue X Y).trace = 0 := by
  simp [glue]
  rw [trace_mul_comm X Y]
  ring

/-- Vanishing of the glue is exactly commutativity: Abelian = no self-coupling. -/
theorem glue_zero_iff_commute (X Y : ColorAlgebra) : glue X Y = 0 ↔ X * Y = Y * X := by
  constructor
  · intro h
    have h0 : X * Y - Y * X = 0 := by simpa [glue] using h
    exact sub_eq_zero.mp h0
  · intro h
    rw [glue, h]
    exact sub_self (Y * X)

/-- The GLUE is real: two color matrices fail to commute, so gluons self-interact. -/
theorem glue_nonzero : ∃ (X Y : ColorAlgebra), glue X Y ≠ 0 := by
  let X : ColorAlgebra := of fun i j => if i = 0 ∧ j = 1 then 1 else 0
  let Y : ColorAlgebra := of fun i j => if i = 1 ∧ j = 0 then 1 else 0
  refine ⟨X, Y, ?_⟩
  have hxy : X * Y = of fun i j => if i = 0 ∧ j = 0 then 1 else 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X, Y, Matrix.mul_apply, Fin.sum_univ_two]
    <;> aesop
  have hyx : Y * X = of fun i j => if i = 1 ∧ j = 1 then 1 else 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X, Y, Matrix.mul_apply, Fin.sum_univ_two]
    <;> aesop
  intro h
  have h00 := congr_arg (fun M => M 0 0) h
  simp [glue, hxy, hyx] at h00

/-! Scalar (Abelian) color carries no glue: the photon case. A scalar field is a
    multiple of the identity, and all multiples of the identity commute, so the
    commutator (the glue) vanishes. -/
theorem abelian_no_glue (a b : ℝ) : glue (a • (1 : ColorAlgebra)) (b • (1 : ColorAlgebra)) = 0 := by
  have h : (a • (1 : ColorAlgebra)) * (b • (1 : ColorAlgebra)) = (b • (1 : ColorAlgebra)) * (a • (1 : ColorAlgebra)) := by
    simp [smul_smul, mul_comm]
  rw [glue, h]
  exact sub_self _

/-- The flux tube: static quark-antiquark potential = Coulomb + linear confinement. -/
noncomputable def fluxTube (α σ : ℝ) (r : ℝ) : ℝ := -α / r + σ * r

/-- The confining force: negative gradient of the flux tube. -/
noncomputable def glueballForce (α σ : ℝ) (r : ℝ) : ℝ := -α / r ^ 2 - σ

/-- The force IS the negative gradient of the flux tube (for r > 0). -/
theorem force_is_negative_gradient (α σ r : ℝ) (hr : 0 < r) :
    glueballForce α σ r = -(deriv (fun r => fluxTube α σ r) r) := by
  have hcoul : HasDerivAt (fun r => -α / r) (α * (r ^ 2)⁻¹) r := by
    simpa [div_eq_mul_inv] using (hasDerivAt_inv hr.ne').const_mul (-α)
  have hlin : HasDerivAt (fun r => σ * r) σ r := by
    simpa using (hasDerivAt_id r).const_mul σ
  have hsum : HasDerivAt (fun r => -α / r + σ * r) (α * (r ^ 2)⁻¹ + σ) r :=
    hcoul.add hlin
  have hder : deriv (fun r => -α / r + σ * r) r = α * (r ^ 2)⁻¹ + σ :=
    hsum.deriv
  dsimp only [glueballForce, fluxTube]
  rw [hder]
  field_simp [hr.ne']
  ring

/-- Non-decay: the force magnitude never drops below the string tension sigma. -/
theorem force_nondecaying (α σ r : ℝ) (hα : 0 < α) (hσ : 0 < σ) (hr : 0 < r) :
    σ ≤ α / r ^ 2 + σ := by
  have hpos : 0 ≤ α / r ^ 2 := by
    apply div_nonneg hα.le
    exact pow_nonneg hr.le 2
  linarith

/-- Confinement: the potential is unbounded above — separation costs infinite energy. -/
theorem confinement (α σ : ℝ) (hσ : 0 < σ) :
    ∀ (M : ℝ), ∃ (r : ℝ), 0 < r ∧ M < fluxTube α σ r := by
  intro M
  let r := max 1 ((M + abs α) / σ + 1)
  have hr : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left (1 : ℝ) ((M + abs α) / σ + 1))
  have hr1 : r ≥ 1 := le_max_left (1 : ℝ) ((M + abs α) / σ + 1)
  use r
  constructor
  · exact hr
  · dsimp only [fluxTube]
    have hbound : -α / r ≥ -abs α := by
      by_cases hα : 0 ≤ α
      · have h : α / r ≤ α := by
          calc
            α / r = α * (1 / r) := by field_simp [hr.ne']
            _ ≤ α * 1 := mul_le_mul_of_nonneg_left ((div_le_one hr).mpr hr1) hα
            _ = α := by ring
        have hn : -α / r ≥ -α := by
          calc
            -α / r = -(α / r) := by field_simp [hr.ne']
            _ ≥ -α := neg_le_neg h
        simpa [abs_of_nonneg hα] using hn
      · have habs : abs α = -α := abs_of_nonpos (le_of_not_ge hα)
        have hneg : 0 ≤ -α / r := by
          apply div_nonneg (by simpa [habs] using abs_nonneg α) hr.le
        calc
          -α / r ≥ 0 := hneg
          _ ≥ -abs α := by rw [habs]; linarith
    have hlin : σ * r > M + abs α := by
      have hge : r ≥ (M + abs α) / σ + 1 := le_max_right (1 : ℝ) ((M + abs α) / σ + 1)
      have hgt : r > (M + abs α) / σ := by
        calc
          r ≥ (M + abs α) / σ + 1 := hge
          _ > (M + abs α) / σ := by linarith
      have hmul : σ * r > M + abs α := by
        calc
          σ * r > σ * ((M + abs α) / σ) := by
            apply mul_lt_mul_of_pos_left hgt hσ
          _ = M + abs α := by field_simp [hσ.ne']
      exact hmul
    calc
      M < σ * r - abs α := by linarith [hlin]
      _ ≤ -α / r + σ * r := by linarith [hbound]

/-- The Coulomb force alone decays to zero: only the linear term confines. -/
theorem coulomb_decays (α : ℝ) (hα : 0 < α) :
    ∀ (ε : ℝ) (hε : 0 < ε), ∃ (r : ℝ), 0 < r ∧ α / r ^ 2 < ε := by
  intro ε hε
  let r := max 1 (Real.sqrt (α / ε) + 1)
  have hr : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left (1 : ℝ) (Real.sqrt (α / ε) + 1))
  have hr2 : r ≥ Real.sqrt (α / ε) + 1 := le_max_right (1 : ℝ) (Real.sqrt (α / ε) + 1)
  have hspos : 0 < Real.sqrt (α / ε) := Real.sqrt_pos.mpr (div_pos hα hε)
  have hsq : (Real.sqrt (α / ε) + 1) ^ 2 > (Real.sqrt (α / ε)) ^ 2 := by
    nlinarith [Real.sq_sqrt (le_of_lt (div_pos hα hε)), hspos]
  have hstrict : r ^ 2 > (Real.sqrt (α / ε)) ^ 2 := by
    have hmono : r ^ 2 ≥ (Real.sqrt (α / ε) + 1) ^ 2 := by
      gcongr
    have hgap : (Real.sqrt (α / ε) + 1) ^ 2 > (Real.sqrt (α / ε)) ^ 2 + 0 := by
      nlinarith [hsq]
    nlinarith [hmono, hsq]
  use r
  constructor
  · exact hr
  · have hden : (Real.sqrt (α / ε)) ^ 2 = α / ε := by
      rw [Real.sq_sqrt (le_of_lt (div_pos hα hε))]
    have hstrict2 : α / r ^ 2 < α / (Real.sqrt (α / ε)) ^ 2 := by
      have hsqpos : 0 < (Real.sqrt (α / ε)) ^ 2 := by positivity
      have hnpos : 0 < r ^ 2 := by positivity
      have hinv : 1 / r ^ 2 < 1 / (Real.sqrt (α / ε)) ^ 2 :=
        (one_div_lt_one_div hnpos hsqpos).mpr hstrict
      calc
        α / r ^ 2 = α * (1 / r ^ 2) := by rw [div_eq_mul_one_div]
        _ < α * (1 / (Real.sqrt (α / ε)) ^ 2) := mul_lt_mul_of_pos_left hinv hα
        _ = α / (Real.sqrt (α / ε)) ^ 2 := by rw [← div_eq_mul_one_div]
    have hsimp : α / (Real.sqrt (α / ε)) ^ 2 = ε := by
      rw [hden]
      have hεn : ε ≠ 0 := by positivity
      have hsq : (Real.sqrt (α / ε)) ^ 2 = α / ε := by
        rw [Real.sq_sqrt (le_of_lt (div_pos hα hε))]
      field_simp [hεn, hsq]
    calc
      α / r ^ 2 < α / (Real.sqrt (α / ε)) ^ 2 := hstrict2
      _ = ε := hsimp

/-- GAP: continuum limit a -> 0 and the rigorous mass gap are the
    substrate boundary of the glueball force — dialetheic Belnap-B. -/
def glueball_gap : Belnap := .B

theorem glueball_gap_dialetheic : band glueball_gap (bnot glueball_gap) = glueball_gap := rfl

theorem glueball_gap_non_explosion : band glueball_gap (bnot glueball_gap) ≠ .F := by
  decide

/-- The glueball word: the same twelve-mark tuple the catalog carries for this class. -/
def glueball_shavian : String := "⟨𐑦·𐑸·𐑾·𐑹·𐑐·𐑧·𐑲·𐑠·⊙·𐑫·𐑳·𐑭⟩"

end Imscribing.Paraconsistent
