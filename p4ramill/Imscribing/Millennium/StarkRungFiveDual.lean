/-
Copyright (c) 2026 Imscribing. All rights reserved.
-/
import Imscribing.Millennium.StarkRungFiveAsympt

/-!
# StarkRungFiveDual — dual-side limits of the Landsberg–Schaar mechanism

This module runs the K3b campaign's dual-side analysis (state file `stark-ladder-state.md`,
"Stage 1-4" plan). Stage 1 collects the Gaussian second-moment estimates:

* `wsq_exp_le` — the global bound `w²·e^{−w²/2} ≤ 4` (from `u/2 + 1 ≤ e^{u/2}`,
  which gives `u·e^{−u/2} ≤ 2` outright);
* `sqMoment_pointwise` — `x²·e^{−cx²} ≤ (4/c)·e^{−cx²/2}` for `c > 0`
  (from `wsq_exp_le` at `√c·x`);
* `summable_gaussNat_shift` — summability of the shifted half-line Gaussian;
* `tsum_int_even_symm` — the symmetric ℤ-split `∑'ℤ f = ∑'ℕ f + ∑'ℕ f(n+1)`;
* `tsum_exp_pi_le` — the self-dual ℤ-Gaussian sum `∑' n, e^{−πn²} ≤ 21/19`
  (geometric tail, using `e^π > 20` via `π > 3` and `e > 2.7182818283`);
* `tsum_exp_half_le` — the half-line sum `∑'_{k∈ℕ} e^{−π(a/2)k²} ≤ (21/19)·√(2/a)`
  for `0 < a ≤ 2`, via `thetaReal_poisson` at `a/2`;
* `sqMoment_le`, `sqMoment_int_le` — the **sharpened second moments**
  `∑' k, k²·e^{−πak²} ≤ 2/(a·√a)` over ℕ (doubled over ℤ) for `0 < a ≤ 1`,
  with the sharp `a^{-3/2}` growth rate; the final numerical check is `42·√2 ≤ 19·π`
  (from `√2 < 17/12` and `π > 3.14`).

Stage 1 is the input to Stage 2 (the dual-limit brick R3-R5), which turns the deviation
bound `|E(t) − gI(4qt/(t²+4))| ≤ (2πqt²/(t²+4))·∑' k² e^{−πβk²}` with `β = 4qt/(t²+4)`
into the limits `E(t)·√(tq) → 1`, `O(t)·√(tq) → −i`, `T(t)·√(tq) → 1−i` as `t → 0⁺`.
-/

open Real Filter
open scoped Real Topology

open Imscribing.Millennium.StarkAsympt

noncomputable section

namespace Imscribing.Millennium.StarkDual

/-! ## The Gaussian second moment -/

/-- The Gaussian second moment is globally bounded: `w²·e^{−w²/2} ≤ 4` for all real `w`.
(The true maximum is `2/e ≈ 0.54`; `u/2 + 1 ≤ e^{u/2}` already gives `u·e^{−u/2} ≤ 2`.) -/
theorem wsq_exp_le (w : ℝ) : w ^ 2 * exp (-(w ^ 2) / 2) ≤ 4 := by
  have h1 := Real.add_one_le_exp (w ^ 2 / 2)
  have hu : w ^ 2 ≤ 2 * exp (w ^ 2 / 2) := by linarith
  have hmerge : exp (w ^ 2 / 2) * exp (-(w ^ 2) / 2) = 1 := by
    rw [← Real.exp_add, ← Real.exp_zero]
    congr 1
    ring
  have hm : w ^ 2 * exp (-(w ^ 2) / 2) ≤ 2 := by
    have h2 := mul_le_mul_of_nonneg_right hu (exp_nonneg (-(w ^ 2) / 2))
    rw [mul_assoc, hmerge, mul_one] at h2
    exact h2
  linarith

/-- The real second moment admits the Gaussian majorant
`x²·e^{−cx²} ≤ (4/c)·e^{−cx²/2}` for every `c > 0` (from `wsq_exp_le` at `√c·x`). -/
theorem sqMoment_pointwise {c : ℝ} (hc : 0 < c) (x : ℝ) :
    x ^ 2 * exp (-c * x ^ 2) ≤ (4 / c) * exp (-(c / 2) * x ^ 2) := by
  have hsqrt : c * x ^ 2 = (Real.sqrt c * x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc.le]
  have hkey0 := wsq_exp_le (Real.sqrt c * x)
  rw [← hsqrt] at hkey0
  have hkey : c * x ^ 2 * exp (-(c / 2) * x ^ 2) ≤ 4 := by
    have hconv : exp (-(c * x ^ 2) / 2) = exp (-(c / 2) * x ^ 2) := by
      congr 1; ring
    rwa [hconv] at hkey0
  have hsplit2 : exp (-c * x ^ 2)
      = exp (-(c / 2) * x ^ 2) * exp (-(c / 2) * x ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : (4 : ℝ) / c * exp (-(c / 2) * x ^ 2)
      = 4 * exp (-(c / 2) * x ^ 2) / c := by ring
  have hexp : x ^ 2 * exp (-c * x ^ 2) * c
      = (c * x ^ 2 * exp (-(c / 2) * x ^ 2)) * exp (-(c / 2) * x ^ 2) := by
    rw [hsplit2]; ring
  rw [h4, le_div_iff₀ hc, hexp]
  exact mul_le_mul_of_nonneg_right hkey (exp_nonneg _)

/-- Scaling a summable real-valued function by a constant (multiplicative form). -/
theorem summable_const_mul {ι : Type*} {f : ι → ℝ} (hf : Summable f) (b : ℝ) :
    Summable (fun i => b * f i) :=
  (hf.const_smul b).congr fun _ => smul_eq_mul _ _

/-- The shifted half-line Gaussian is summable, dominated by a geometric series. -/
theorem summable_gaussNat_shift (s : ℝ) (hs : 0 < s) :
    Summable (fun n : ℕ => exp (-π * s * (((n : ℕ) + 1 : ℕ) : ℝ) ^ 2)) := by
  have hneg : -π * s < 0 := by linarith [mul_pos Real.pi_pos hs]
  have hr1 : exp (-π * s) < 1 := by simpa using exp_lt_exp.mpr hneg
  have hg := (summable_geometric_of_lt_one (exp_nonneg _) hr1).comp_injective
    Nat.succ_injective
  refine Summable.of_nonneg_of_le (fun n => exp_nonneg _) (fun n => ?_) hg
  have hpos : 0 < π * s := mul_pos Real.pi_pos hs
  have hA : (((n : ℕ) + 1 : ℕ) : ℝ) = ((n : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  have hq : ((n : ℕ) : ℝ) + 1 ≤ (((n : ℕ) : ℝ) + 1) ^ 2 := by
    have hn : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hkey := mul_le_mul_of_nonneg_left hq hpos.le
  have h2 : -π * s * (((n : ℕ) + 1 : ℕ) : ℝ) ^ 2
      ≤ -π * s * (((n : ℕ) + 1 : ℕ) : ℝ) := by
    rw [hA]
    nlinarith [hkey]
  calc exp (-π * s * (((n : ℕ) + 1 : ℕ) : ℝ) ^ 2)
      ≤ exp (-π * s * (((n : ℕ) + 1 : ℕ) : ℝ)) := exp_le_exp.mpr h2
    _ = exp (-π * s) ^ (((n : ℕ) + 1 : ℕ)) := by
        rw [mul_comm (-π * s) (((n : ℕ) + 1 : ℕ) : ℝ)]
        exact Real.exp_nat_mul _ _

/-- Symmetric ℤ-split of an even series:
`∑'_{m∈ℤ} f m = ∑'_{n∈ℕ} f n + ∑'_{n∈ℕ} f (n+1)`. -/
theorem tsum_int_even_symm {f : ℤ → ℝ} (hf : Summable f)
    (hfa : Summable (fun n : ℕ => f (n : ℤ)))
    (hev : ∀ n : ℕ, f (-(↑n + 1 : ℤ)) = f (↑n + 1)) :
    ∑' m : ℤ, f m = ∑' n : ℕ, f ↑n + ∑' n : ℕ, f (↑n + 1) := by
  have hz := tsum_nat_add_neg_add_one hf
  have hfs : Summable (fun n : ℕ => f (↑n + 1)) := hfa.comp_injective Nat.succ_injective
  have hfb : Summable (fun n : ℕ => f (-(↑n + 1 : ℤ))) := hfs.congr fun n => (hev n).symm
  rw [← hz, Summable.tsum_add hfa hfb, tsum_congr hev]

/-! ## The self-dual ℤ-Gaussian sum -/

/-- The self-dual ℤ-Gaussian sum: `∑' n, e^{−πn²} ≤ 21/19`.
(The exact value `θ₃(e^{−π}) ≈ 1.08643`; the geometric tail with `e^π > 20` gives `21/19`.) -/
theorem tsum_exp_pi_le : ∑' n : ℤ, exp (-(π : ℝ) * ((n : ℤ) : ℝ) ^ 2) ≤ 21 / 19 := by
  have hr1 : exp (-(π : ℝ)) < 1 := by
    simpa using exp_lt_exp.mpr (show -(π : ℝ) < 0 by linarith [Real.pi_pos])
  have h20 : (20 : ℝ) < exp π := by
    have h3 := Real.pi_gt_three
    have hp : exp 3 < exp π := exp_lt_exp.mpr h3
    have he := Real.exp_one_gt_d9
    have he3 : exp 3 = exp 1 * exp 1 * exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      norm_num
    calc (20 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
      _ ≤ exp 1 * exp 1 * exp 1 := by nlinarith [he]
      _ = exp 3 := he3.symm
      _ < exp π := hp
  have hr0 : 0 ≤ exp (-(π : ℝ)) := exp_nonneg _
  have hgeom : ∑' n : ℕ, exp (-(π : ℝ) * ((n : ℕ) + 1 : ℝ)) ≤ 1 / 19 := by
    have hgeo := tsum_geometric_of_lt_one hr0 hr1
    have hfn : ∀ n : ℕ, exp (-(π : ℝ) * ((n : ℕ) + 1 : ℝ))
        = (exp (-(π : ℝ))) ^ (n + 1) := by
      intro n
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast; ring
    have hsh : ∑' n : ℕ, (exp (-(π : ℝ))) ^ (n + 1)
        = exp (-(π : ℝ)) * ∑' n : ℕ, (exp (-(π : ℝ))) ^ n := by
      rw [tsum_congr (fun n => pow_succ' (exp (-(π : ℝ))) n)]
      exact Summable.tsum_mul_left _ (summable_geometric_of_lt_one hr0 hr1)
    rw [tsum_congr hfn, hsh, hgeo, ← div_eq_mul_inv, div_le_iff₀ (sub_pos.mpr hr1)]
    have hx : exp (-(π : ℝ)) ≤ 1 / 20 := by
      rw [Real.exp_neg, one_div,
        inv_le_inv₀ (exp_pos _) (by norm_num : (0 : ℝ) < 20)]
      exact le_of_lt h20
    linarith
  have hgeom1 : ∑' n : ℕ, exp (-(π : ℝ) * 1 * (((n : ℕ) + 1 : ℕ) : ℝ))
      ≤ 1 / 19 := by
    have hc1 : ∑' n : ℕ, exp (-(π : ℝ) * 1 * (((n : ℕ) + 1 : ℕ) : ℝ))
        = ∑' n : ℕ, exp (-(π : ℝ) * ((n : ℕ) + 1 : ℝ)) :=
      tsum_congr fun _ => by congr 1; push_cast; ring
    rw [hc1]
    exact hgeom
  have htail : ∑' n : ℕ, exp (-(π : ℝ) * 1 * (((n : ℕ) + 1 : ℕ) : ℝ) ^ 2)
      ≤ 1 / 19 := by
    have hgeo1 : Summable (fun n : ℕ =>
        exp (-(π : ℝ) * 1 * (((n : ℕ) + 1 : ℕ) : ℝ))) := by
      have hg1 := (summable_geometric_of_lt_one hr0 hr1).comp_injective
        Nat.succ_injective
      refine hg1.congr fun n => ?_
      show exp (-(π : ℝ)) ^ ((n : ℕ) + 1)
          = exp (-(π : ℝ) * 1 * (((n : ℕ) + 1 : ℕ) : ℝ))
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast; ring
    refine le_trans (Summable.tsum_le_tsum (fun n => ?_)
      (summable_gaussNat_shift 1 (by norm_num)) hgeo1) hgeom1
    refine exp_le_exp.mpr ?_
    have hA : (((n : ℕ) + 1 : ℕ) : ℝ) = ((n : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    have hq : ((n : ℕ) : ℝ) + 1 ≤ (((n : ℕ) : ℝ) + 1) ^ 2 := by
      have hn : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hpos : 0 < π * 1 := mul_pos Real.pi_pos one_pos
    have hkey := mul_le_mul_of_nonneg_left hq hpos.le
    rw [hA]
    nlinarith [hkey]
  have hconv : ∑' n : ℤ, exp (-(π : ℝ) * ((n : ℤ) : ℝ) ^ 2)
      = ∑' n : ℤ, exp (-(π : ℝ) * 1 * ((n : ℤ) : ℝ) ^ 2) :=
    tsum_congr fun _ => by congr 1; ring
  rw [hconv]
  have hsplit := tsum_int_even_symm (summable_gaussReal 1 (by norm_num))
    (summable_gaussNat 1 (by norm_num)) (fun n => by push_cast; ring_nf)
  rw [hsplit]
  have hz2 := (summable_gaussNat 1 (by norm_num)).tsum_eq_zero_add
  have hf0 : exp (-(π : ℝ) * 1 * ((0 : ℕ) : ℝ) ^ 2) = 1 := by simp
  rw [hf0] at hz2
  have hcon : ∑' n : ℕ, exp (-(π : ℝ) * 1 * (((↑n + 1 : ℤ) : ℤ) : ℝ) ^ 2)
      = ∑' n : ℕ, exp (-(π : ℝ) * 1 * (((n : ℕ) + 1 : ℕ) : ℝ) ^ 2) :=
    tsum_congr fun n => by push_cast; ring
  have hcon2 : ∑' n : ℕ, exp (-(π : ℝ) * 1 * (((↑n : ℤ) : ℤ) : ℝ) ^ 2)
      = ∑' n : ℕ, exp (-(π : ℝ) * 1 * ((n : ℕ) : ℝ) ^ 2) :=
    tsum_congr fun n => by push_cast; ring
  rw [hcon2, hcon, hz2]
  linarith [htail]

/-! ## The half-line Gaussian sum through the self-dual point -/

/-- The half-line Gaussian sum, bounded through the self-dual point:
`∑'_{k∈ℕ} e^{−π(a/2)k²} ≤ (21/19)·√(2/a)` for `0 < a ≤ 2`. -/
theorem tsum_exp_half_le (a : ℝ) (ha : 0 < a) (hle : a ≤ 2) :
    ∑' k : ℕ, exp (-((π * a) / 2) * ((k : ℕ) : ℝ) ^ 2)
      ≤ (21 / 19) * (2 / a) ^ ((1 : ℝ) / 2) := by
  have hconv1 : ∑' k : ℕ, exp (-((π * a) / 2) * ((k : ℕ) : ℝ) ^ 2)
      = ∑' k : ℕ, exp (-(π : ℝ) * (a / 2) * ((k : ℕ) : ℝ) ^ 2) :=
    tsum_congr fun _ => by congr 1; ring
  have hconv2 : ∑' n : ℤ, exp (-((π * a) / 2) * ((n : ℤ) : ℝ) ^ 2)
      = ∑' n : ℤ, exp (-(π : ℝ) * (a / 2) * ((n : ℤ) : ℝ) ^ 2) :=
    tsum_congr fun _ => by congr 1; ring
  have hsplit := tsum_int_even_symm (summable_gaussReal (a / 2) (by positivity))
    (summable_gaussNat (a / 2) (by positivity)) (fun n => by push_cast; ring_nf)
  have hnat2 : ∑' k : ℕ, exp (-(π : ℝ) * (a / 2) * ((k : ℕ) : ℝ) ^ 2)
      ≤ ∑' n : ℤ, exp (-(π : ℝ) * (a / 2) * ((n : ℤ) : ℝ) ^ 2) := by
    calc ∑' k : ℕ, exp (-(π : ℝ) * (a / 2) * ((k : ℕ) : ℝ) ^ 2)
        ≤ ∑' k : ℕ, exp (-(π : ℝ) * (a / 2) * ((k : ℕ) : ℝ) ^ 2)
            + ∑' n : ℕ, exp (-(π : ℝ) * (a / 2) * (((↑n + 1 : ℤ) : ℤ) : ℝ) ^ 2) :=
          le_add_of_nonneg_right (tsum_nonneg fun _ => exp_nonneg _)
      _ = ∑' n : ℤ, exp (-(π : ℝ) * (a / 2) * ((n : ℤ) : ℝ) ^ 2) := hsplit.symm
  have hnat := (le_of_eq hconv1).trans (hnat2.trans (le_of_eq hconv2.symm))
  have hmono : ∑' n : ℤ, exp (-(π : ℝ) / (a / 2) * ((n : ℤ) : ℝ) ^ 2)
      ≤ ∑' n : ℤ, exp (-(π : ℝ) * ((n : ℤ) : ℝ) ^ 2) := by
    have h21 : (1 : ℝ) ≤ 2 / a := by rw [le_div_iff₀ ha, one_mul]; linarith
    rw [show ∑' n : ℤ, exp (-(π : ℝ) / (a / 2) * ((n : ℤ) : ℝ) ^ 2)
        = ∑' n : ℤ, exp (-(π : ℝ) * (2 / a) * ((n : ℤ) : ℝ) ^ 2) from
      tsum_congr fun _ => by congr 1; field_simp]
    refine Summable.tsum_le_tsum (fun n => ?_) ?_ ?_
    · have hq : (0 : ℝ) ≤ ((n : ℤ) : ℝ) ^ 2 := sq_nonneg _
      have hkey := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left h21 Real.pi_pos.le) hq
      exact exp_le_exp.mpr (by nlinarith [hkey])
    · exact summable_gaussReal (2 / a) (by positivity)
    · exact (summable_gaussReal 1 (by norm_num)).congr fun n => by congr 1; ring
  have hpois := thetaReal_poisson (a / 2) (by positivity)
  have hkey : (a / 2) ^ ((1 : ℝ) / 2)
      * ∑' n : ℤ, exp (-(π : ℝ) * (a / 2) * ((n : ℤ) : ℝ) ^ 2) ≤ 21 / 19 := by
    rw [hpois]
    exact hmono.trans tsum_exp_pi_le
  have hpos2 : 0 < (a / 2) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hinv : (2 / a) ^ ((1 : ℝ) / 2) = ((a / 2) ^ ((1 : ℝ) / 2))⁻¹ := by
    have h1 : (2 / a) ^ ((1 : ℝ) / 2) * (a / 2) ^ ((1 : ℝ) / 2) = 1 := by
      rw [← Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 / a)
        (by positivity : (0 : ℝ) ≤ a / 2),
        show (2 / a) * (a / 2) = (1 : ℝ) from by field_simp]
      simp
    exact eq_inv_of_mul_eq_one_left h1
  have hconv3 : ∑' n : ℤ, exp (-((π * a) / 2) * ((n : ℤ) : ℝ) ^ 2)
      = ∑' n : ℤ, exp (-(π : ℝ) * (a / 2) * ((n : ℤ) : ℝ) ^ 2) :=
    tsum_congr fun _ => by congr 1; ring
  calc ∑' k : ℕ, exp (-((π * a) / 2) * ((k : ℕ) : ℝ) ^ 2)
      ≤ ∑' n : ℤ, exp (-((π * a) / 2) * ((n : ℤ) : ℝ) ^ 2) := hnat
    _ = ((a / 2) ^ ((1 : ℝ) / 2))⁻¹ * ((a / 2) ^ ((1 : ℝ) / 2)
          * ∑' n : ℤ, exp (-(π : ℝ) * (a / 2) * ((n : ℤ) : ℝ) ^ 2)) := by
        rw [inv_mul_cancel_left₀ hpos2.ne', hconv3]
    _ ≤ ((a / 2) ^ ((1 : ℝ) / 2))⁻¹ * (21 / 19) := by
        exact mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (21 / 19) * (2 / a) ^ ((1 : ℝ) / 2) := by
        rw [hinv, mul_comm]

/-! ## The sharpened second moment -/

set_option maxHeartbeats 800000 in
/-- **Stage 1: the sharpened second moment.** For `0 < a ≤ 1`,
`∑' k, k²·e^{−πak²} ≤ 2/(a·√a)` — the sharp `a^{-3/2}` growth rate.
(The pointwise bound `sqMoment_pointwise` against the geometric half-Gaussian majorant,
with the half-line sum bounded via the self-dual point; the final numerical check is
`42·√2 ≤ 19·π`, i.e. `√2 < 17/12` and `π > 3.14`.) -/
theorem sqMoment_le (a : ℝ) (ha : 0 < a) (hle : a ≤ 1) :
    ∑' k : ℕ, ((k : ℕ) : ℝ) ^ 2 * exp (-(π * a) * ((k : ℕ) : ℝ) ^ 2)
      ≤ 2 / (a * Real.sqrt a) := by
  have hc : 0 < π * a := mul_pos Real.pi_pos ha
  have hpt : ∀ k : ℕ, ((k : ℕ) : ℝ) ^ 2 * exp (-(π * a) * ((k : ℕ) : ℝ) ^ 2)
      ≤ (4 / (π * a)) * exp (-(π * a / 2) * ((k : ℕ) : ℝ) ^ 2) :=
    fun k => sqMoment_pointwise hc ((k : ℕ) : ℝ)
  have hgsum : Summable (fun k : ℕ => exp (-(π * a / 2) * ((k : ℕ) : ℝ) ^ 2)) :=
    (summable_gaussNat (a / 2) (by positivity)).congr fun k => by congr 1; ring
  have hscaled : Summable (fun k : ℕ =>
      (4 / (π * a)) * exp (-(π * a / 2) * ((k : ℕ) : ℝ) ^ 2)) :=
    summable_const_mul hgsum (4 / (π * a))
  have hl : Summable (fun k : ℕ => ((k : ℕ) : ℝ) ^ 2 * exp (-(π * a) * ((k : ℕ) : ℝ) ^ 2)) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sq_nonneg _) (exp_nonneg _)) hpt hscaled
  have hval : ∑' k : ℕ, (4 / (π * a)) * exp (-(π * a / 2) * ((k : ℕ) : ℝ) ^ 2)
      = (4 / (π * a)) * ∑' k : ℕ, exp (-(π * a / 2) * ((k : ℕ) : ℝ) ^ 2) :=
    Summable.tsum_mul_left _ hgsum
  have hstep := (Summable.tsum_le_tsum hpt hl hscaled).trans (le_of_eq hval)
  have hhalf := tsum_exp_half_le a ha (by linarith)
  have hsqrt2 : (Real.sqrt 2 : ℝ) < 17 / 12 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 17 / 12)]
    norm_num
  have hconst : (42 : ℝ) * Real.sqrt 2 ≤ 19 * π := by nlinarith [hsqrt2, Real.pi_gt_d2]
  have hpi0 : (π : ℝ) ≠ 0 := Real.pi_pos.ne'
  have hconv : (4 / (π * a)) * ((21 / 19) * (2 / a) ^ ((1 : ℝ) / 2))
      = (84 * Real.sqrt 2 / (19 * π)) / (a * Real.sqrt a) := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp [hpi0]
    ring
  calc ∑' k : ℕ, ((k : ℕ) : ℝ) ^ 2 * exp (-(π * a) * ((k : ℕ) : ℝ) ^ 2)
      ≤ (4 / (π * a)) * ∑' k : ℕ, exp (-(π * a / 2) * ((k : ℕ) : ℝ) ^ 2) := hstep
    _ ≤ (4 / (π * a)) * ((21 / 19) * (2 / a) ^ ((1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
    _ = (84 * Real.sqrt 2 / (19 * π)) / (a * Real.sqrt a) := hconv
    _ ≤ 2 / (a * Real.sqrt a) := by
        have hpos : (0 : ℝ) < a * Real.sqrt a := by positivity
        rw [le_div_iff₀ hpos,
          show (84 * Real.sqrt 2 / (19 * π)) / (a * Real.sqrt a)
              * (a * Real.sqrt a) = 84 * Real.sqrt 2 / (19 * π) from by field_simp,
          div_le_iff₀ (by positivity : (0 : ℝ) < 19 * π)]
        linarith [hconst]

set_option maxHeartbeats 800000 in
/-- Stage 1 over ℤ: doubling the half-line second moment. -/
theorem sqMoment_int_le (a : ℝ) (ha : 0 < a) (hle : a ≤ 1) :
    ∑' m : ℤ, ((m : ℤ) : ℝ) ^ 2 * exp (-(π * a) * ((m : ℤ) : ℝ) ^ 2)
      ≤ 4 / (a * Real.sqrt a) := by
  have hc : 0 < π * a := mul_pos Real.pi_pos ha
  have hpt : ∀ x : ℝ, x ^ 2 * exp (-(π * a) * x ^ 2)
      ≤ (4 / (π * a)) * exp (-(π * a / 2) * x ^ 2) := fun x => sqMoment_pointwise hc x
  have hgsumZ : Summable (fun m : ℤ => exp (-(π * a / 2) * ((m : ℤ) : ℝ) ^ 2)) :=
    (summable_gaussReal (a / 2) (by positivity)).congr fun m => by congr 1; ring
  have hmajor : Summable (fun m : ℤ => (4 / (π * a)) * exp (-(π * a / 2) * ((m : ℤ) : ℝ) ^ 2)) :=
    summable_const_mul hgsumZ (4 / (π * a))
  have hs : Summable (fun m : ℤ => ((m : ℤ) : ℝ) ^ 2 * exp (-(π * a) * ((m : ℤ) : ℝ) ^ 2)) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (sq_nonneg _) (exp_nonneg _))
      (fun m => hpt ((m : ℤ) : ℝ)) hmajor
  have hgsumN : Summable (fun n : ℕ => exp (-(π * a / 2) * ((n : ℕ) : ℝ) ^ 2)) :=
    (summable_gaussNat (a / 2) (by positivity)).congr fun n => by congr 1; ring
  have hfa : Summable (fun n : ℕ => ((n : ℕ) : ℝ) ^ 2 * exp (-(π * a) * ((n : ℕ) : ℝ) ^ 2)) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (exp_nonneg _))
      (fun n => hpt ((n : ℕ) : ℝ))
      (summable_const_mul hgsumN (4 / (π * a)))
  have hsplit := tsum_int_even_symm hs hfa (fun n => by push_cast; ring_nf)
  rw [hsplit]
  have hz2 := hfa.tsum_eq_zero_add
  have hf0 : ((0 : ℕ) : ℝ) ^ 2 * exp (-(π * a) * ((0 : ℕ) : ℝ) ^ 2) = 0 := by simp
  rw [hf0] at hz2
  have hcon : ∑' n : ℕ, (((↑n + 1 : ℤ) : ℤ) : ℝ) ^ 2
        * exp (-(π * a) * (((↑n + 1 : ℤ) : ℤ) : ℝ) ^ 2)
      = ∑' n : ℕ, (((n : ℕ) + 1 : ℕ) : ℝ) ^ 2
        * exp (-(π * a) * (((n : ℕ) + 1 : ℕ) : ℝ) ^ 2) :=
    tsum_congr fun n => by push_cast; ring
  have hcon2 : ∑' n : ℕ, (((n : ℕ) : ℤ) : ℝ) ^ 2
        * exp (-(π * a) * (((n : ℕ) : ℤ) : ℝ) ^ 2)
      = ∑' n : ℕ, ((n : ℕ) : ℝ) ^ 2 * exp (-(π * a) * ((n : ℕ) : ℝ) ^ 2) :=
    tsum_congr fun n => by push_cast; ring
  have hrhs : (4 : ℝ) / (a * Real.sqrt a) = 2 * (2 / (a * Real.sqrt a)) := by ring
  rw [hcon2, hcon, hrhs]
  nlinarith [hz2, sqMoment_le a ha hle]

end Imscribing.Millennium.StarkDual
