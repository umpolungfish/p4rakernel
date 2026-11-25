import Mathlib
import Imscribing.Millennium.WKExpand
open Imscribing.Millennium.WKExpand
open Erdos220
open scoped ComplexConjugate
noncomputable section

variable (d : ℕ) [NeZero d]
local notation "w" => fourierRoot d

def corr (N : ZMod d → ℝ) (m : ZMod d) : ℝ :=
  ∑ l : ZMod d, N (m + l) * N l

/-- Wiener-Khinchin: star(nu_b)*nu_b = sum_m corr(m) w^{bm}. -/
theorem wk_full (N : ZMod d → ℝ) (b : ZMod d) :
    star (nu d N b) * nu d N b =
      ∑ m : ZMod d, ((corr d N m : ℝ) : ℂ) * w ^ (b * m).val := by
  rw [wk_expand]
  -- reindex the double sum (k,l) -> (m = k - l, l)
  let e : (ZMod d × ZMod d) ≃ (ZMod d × ZMod d) :=
    { toFun := fun kl => (kl.1 - kl.2, kl.2)
      invFun := fun ml => (ml.1 + ml.2, ml.2)
      left_inv := by intro kl; simp
      right_inv := by intro ml; simp }
  change (∑ p : ZMod d × ZMod d, ((N p.2 : ℝ) : ℂ) * (star w) ^ (b*p.2).val * ((N p.1 : ℝ) : ℂ) * w ^ (b*p.1).val) = _
  rw [Fintype.sum_equiv e]
  apply Finset.sum_congr rfl
  intro m hm
  -- need: sum_l N l (star w)^{b l} N (m+l) w^{b(m+l)} = corr(m) w^{bm}
  have hpow : ∀ l : ZMod d, (star w) ^ (b*l).val * w ^ (b*(m+l)).val = w ^ (b*m).val := by
    intro l
    have hs : star w * w = 1 := fourierRoot_star_mul d (NeZero.pos d)
    have hsp : (star w) ^ (b*l).val * w ^ (b*l).val = 1 := by
      rw [← mul_pow, hs, one_pow]
    -- w^{b(m+l)} = w^{bm} * w^{bl}
    have hadd : w ^ (b*(m+l)).val = w ^ (b*m).val * w ^ (b*l).val := by
      rw [← pow_add]
      congr 1
      simp [mul_add]
    rw [hadd]
    rw [← mul_assoc, hsp, one_mul]
  simp [corr, mul_assoc, hpow]
  ring
