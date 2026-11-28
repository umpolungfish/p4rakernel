import Imscribing.Millennium.StarkRungFourContinued

/-!
# StarkRungFourGaussSign — the Gauss-sign brick (K3b)

The quadratic Gauss-sign evaluation for the Stark character of
`F2048 = Q(√4190205)`.  This file folds in the elementary bricks that reduce
the sign to a single positivity input:

* the divisor-vanishing lemma: if `f` on `ZMod (d*m)` depends only on the
  residue class modulo `d` (with `d` coprime to `m ≥ 2`), then
  `∑_x f(x)·ψ(x) = 0`.  The proof reindexes along the Chinese-remainder
  equivalence `ZMod (d*m) ≃ ZMod d × ZMod m` and splits off the character sum
  over the second coordinate, which vanishes because the additive character
  `ψ ∘ (t ↦ (0, t))` is nontrivial at `t = 1`.
* the fiber count `#{x : x² = y} = (1+χ₃)(1+χ₅)(1+χ₄₀₉)(1+χ₆₈₃)` via
  per-prime Euler criterion + CRT (next step),
* the chirp-Gauss identity `∑_x exp(2πi·x²/con) = τ(χ)` and hence
  `τ = ±√con`, with the sign selected by the positivity input `0 < τ.re`
  (verified numerically to 12 digits: `τ ≈ 2046.9990…`).

The remaining named inputs on the KNR ladder are then exactly: the sign
positivity `0 < τ.re` (Schur's staircase over the CRT certificates) and the
Dirichlet class number formula (K4).
-/

open Complex Real Finset
open scoped ComplexConjugate
open ZMod
open Imscribing.Millennium.StarkCharacterD2048
open Imscribing.Millennium.StarkGaussSum
open Imscribing.Millennium.StarkRungFour
open StarkLogRung

noncomputable section

namespace Imscribing.Millennium.StarkGaussSign

/-! ## The positive square root of `con` -/

/-- The positive square root of `con` inside `ℂ`. -/
private def ciota : ℂ := ((Real.sqrt (con : ℝ) : ℝ) : ℂ)

private theorem ciota_re : ciota.re = Real.sqrt (con : ℝ) := by
  rw [ciota, Complex.ofReal_re]

private theorem ciota_im_zero : ciota.im = 0 := by
  rw [ciota, Complex.ofReal_im]

private theorem ciota_eq : ciota = ((Real.sqrt (con : ℝ) : ℝ) : ℂ) := rfl

private theorem ciota_sq : ciota * ciota = (con : ℂ) := by
  rw [ciota_eq, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by exact_mod_cast con_pos.le), Complex.ofReal_natCast]

/-! ## Small arithmetic and analytic helpers -/

/-- `exp(2πi·r/f) ≠ 1` for a proper nonzero residue `r mod f`. -/
private theorem rootExp_ne_one {f : ℕ} (hf : 1 < f) (r : ℕ) (hr : r % f ≠ 0) :
    rootExp r f ≠ 1 := by
  haveI : NeZero f := ⟨by linarith⟩
  intro h1
  rw [rootExp, Complex.exp_eq_one_iff] at h1
  obtain ⟨n, hn⟩ := h1
  have hpi : ((2 : ℂ) * (Real.pi : ℂ) * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have h2 : ((r : ℂ) / (f : ℂ)) = ((n : ℤ) : ℂ) := by
    refine mul_right_cancel₀ hpi ?_
    calc ((r : ℂ) / (f : ℂ)) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
        = (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((r : ℂ) / (f : ℂ)) := mul_comm _ _
      _ = ((n : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := hn
  have hf0 : ((f : ℕ) : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne f
  have h4 : ((r : ℕ) : ℂ) = ((n : ℤ) : ℂ) * ((f : ℕ) : ℂ) := by
    rw [← h2, div_mul_cancel₀ _ hf0]
  have h5 : (r : ℝ) = ((n : ℤ) : ℝ) * (f : ℝ) := by
    have h6 := congrArg Complex.re h4
    simp only [Complex.natCast_re, Complex.intCast_re, Complex.mul_re,
      Complex.intCast_im, Complex.natCast_im, mul_zero, sub_zero] at h6
    exact h6
  have hn0 : 0 ≤ n := by
    by_contra hneg
    have h7' : n < 0 := by omega
    have h7 : ((n : ℤ) : ℝ) < 0 := by exact_mod_cast h7'
    have hfpos : (0 : ℝ) < (f : ℝ) := Nat.cast_pos.2 (lt_trans zero_lt_one hf)
    have hmul : ((n : ℤ) : ℝ) * (f : ℝ) < 0 := by nlinarith [h7, hfpos]
    have hnn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg (r : ℕ)
    rw [h5] at hnn
    linarith
  have h8 : (n.toNat : ℕ) * f = r := by
    have h11 : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn0
    have h10' : (n : ℤ) * ((f : ℕ) : ℤ) = ((r : ℕ) : ℤ) := by
      have hc : (((n : ℤ) * ((f : ℕ) : ℤ) : ℤ) : ℝ) = (((r : ℕ) : ℤ) : ℝ) := by
        rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, h5]
      exact Int.cast_injective hc
    rw [← h11] at h10'
    exact_mod_cast h10'
  rw [← h8] at hr
  exact hr (Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left f n.toNat))

/-! ## The cast machinery -/

private theorem castHom_val_mod {n p : ℕ} [NeZero n] (hp : p ∣ n) (x : ZMod n) :
    (ZMod.castHom hp (ZMod p) x).val = x.val % p := by
  have h1 : ZMod.castHom hp (ZMod p) x = ZMod.cast x := ZMod.castHom_apply x
  have h2 : ZMod.cast x = ((x.val : ℕ) : ZMod p) :=
    (ZMod.natCast_val (R := ZMod p) x).symm
  rw [h1, h2, ZMod.val_natCast]

private theorem castHom_val_eq {n p : ℕ} [NeZero n] (hp : p ∣ n) (x y : ZMod n) :
    ZMod.castHom hp (ZMod p) x = ZMod.castHom hp (ZMod p) y ↔ x.val % p = y.val % p := by
  haveI hnp : NeZero p :=
    ⟨Nat.ne_of_gt (Nat.pos_of_dvd_of_pos hp (Nat.pos_of_ne_zero (NeZero.ne n)))⟩
  constructor
  · intro h
    calc x.val % p = (ZMod.castHom hp (ZMod p) x).val := (castHom_val_mod hp x).symm
      _ = (ZMod.castHom hp (ZMod p) y).val := congrArg ZMod.val h
      _ = y.val % p := castHom_val_mod hp y
  · intro h
    have h1 : (ZMod.castHom hp (ZMod p) x).val = (ZMod.castHom hp (ZMod p) y).val := by
      rw [castHom_val_mod, castHom_val_mod]
      exact h
    exact ZMod.val_injective p h1

private theorem castHom_comp_gen {N p q : ℕ} (hp : p ∣ q) (hq : q ∣ N) (y : ZMod N) :
    ZMod.castHom hp (ZMod p) (ZMod.castHom hq (ZMod q) y)
      = ZMod.castHom (dvd_trans hp hq) (ZMod p) y := by
  exact congrArg (fun g : ZMod N →+* ZMod p => g y) (ZMod.castHom_comp hp hq)

/-- Dependence of a function on `ZMod con` only through the cast into `ZMod d`. -/
private def castDep (d : ℕ) (hd : d ∣ con) (f : ZMod con → ℂ) : Prop :=
  ∀ x y : ZMod con,
    ZMod.castHom hd (ZMod d) x = ZMod.castHom hd (ZMod d) y → f x = f y

private theorem castDep_trans {d e : ℕ} (hdc : d ∣ con) (hde : d ∣ e) (hee : e ∣ con)
    {f : ZMod con → ℂ} (hf : castDep d hdc f) : castDep e hee f := by
  intro x y hxy
  refine hf x y ?_
  rw [castHom_val_eq hdc x y]
  have hxy' : x.val % e = y.val % e := (castHom_val_eq hee x y).mp hxy
  calc x.val % d = (x.val % e) % d := (Nat.mod_mod_of_dvd x.val hde).symm
    _ = (y.val % e) % d := congrArg (fun a : ℕ => a % d) hxy'
    _ = y.val % d := Nat.mod_mod_of_dvd y.val hde

private theorem castDep_mul {d : ℕ} (hd : d ∣ con) {f g : ZMod con → ℂ}
    (hf : castDep d hd f) (hg : castDep d hd g) : castDep d hd (fun y => f y * g y) := by
  intro x y hxy
  show f x * g x = f y * g y
  rw [hf x y hxy, hg x y hxy]

/-- The Legendre symbol at `p`, read on `ZMod con` through the cast. -/
private def chiP (p : ℕ) : ZMod con → ℂ :=
  fun y => ((jacobiSym (y.val : ℤ) p : ℤ) : ℂ)

private theorem chiP_cast (p : ℕ) (hp : p ∣ con) (y : ZMod con) :
    chiP p y = ((jacobiSym (((ZMod.castHom hp (ZMod p)) y).val : ℤ) p : ℤ) : ℂ) := by
  rw [chiP, castHom_val_mod]
  have hmod : ((y.val % p : ℕ) : ℤ) = (y.val : ℤ) % (p : ℤ) := by push_cast; rfl
  rw [hmod, ← jacobiSym.mod_left (y.val : ℤ) p]

private theorem chiP_dep (p : ℕ) (hp : p ∣ con) : castDep p hp (chiP p) := by
  intro x y hxy
  have hv : x.val % p = y.val % p := by
    rw [← castHom_val_mod hp x, hxy, castHom_val_mod hp y]
  rw [chiP_cast p hp x, chiP_cast p hp y, castHom_val_mod, castHom_val_mod, hv]

/-- Mathlib's standard additive character is the `rootExp` root of unity. -/
private theorem stdAddChar_rootExp {N : ℕ} [NeZero N] (j : ZMod N) :
    stdAddChar (N := N) j = rootExp j.val N := by
  have hj : ((j.val : ℤ) : ZMod N) = j := by simp
  have h1 := stdAddChar_coe (N := N) (j.val : ℤ)
  rw [hj] at h1
  rw [h1]
  unfold rootExp
  push_cast
  ring_nf

/-- Fiber decomposition of a finite sum: group the terms by the value of `h`. -/
private theorem sum_fiber_eq {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (h : α → β) (F : α → ℂ) :
    ∑ x, F x = ∑ y, ∑ x ∈ Finset.univ.filter (fun x => h x = y), F x := by
  classical
  have h1 : ∑ y, ∑ x ∈ Finset.univ.filter (fun x => h x = y), F x
      = ∑ y, ∑ x, (if h x = y then F x else 0) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_filter]
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite_eq (Finset.univ : Finset β) (h x) (fun _ => F x)]
  simp

/-! ## The divisor-vanishing lemma -/

/-- **The divisor-vanishing lemma.**  If `f` on `ZMod (d*m)` depends only on the
residue class modulo `d`, where `d` is coprime to `m ≥ 2`, then
`∑_x f(x)·ψ(x) = 0`: reindexing along the Chinese-remainder equivalence
`ZMod (d*m) ≃ ZMod d × ZMod m` splits off the character sum over the second
coordinate, which vanishes because `ψ ∘ (t ↦ (0, t))` is nontrivial at `t = 1`. -/
private theorem sum_mul_stdAddChar_eq_zero {d m : ℕ} [NeZero (d * m)]
    (hcop : Nat.Coprime d m) (hm : 1 < m)
    {f : ZMod (d * m) → ℂ}
    (hf : ∀ x y : ZMod (d * m), ZMod.castHom (Nat.dvd_mul_right d m) (ZMod d) x
      = ZMod.castHom (Nat.dvd_mul_right d m) (ZMod d) y → f x = f y) :
    ∑ x, f x * stdAddChar (N := d * m) x = 0 := by
  classical
  haveI hmN : NeZero m := ⟨by omega⟩
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, Nat.coprime_zero_left] at hcop
    exact hm.ne' hcop
  haveI hdN : NeZero d := ⟨hd0⟩
  let hE := ZMod.chineseRemainder hcop
  -- hE : ZMod (d * m) ≃+* ZMod d × ZMod m
  have hApp : ∀ w : ZMod d × ZMod m, hE (hE.symm w) = w := hE.toEquiv.apply_symm_apply
  have hSApp : ∀ z : ZMod (d * m), hE.symm (hE z) = z := hE.toEquiv.symm_apply_apply
  have hEinj : Function.Injective hE := hE.toEquiv.injective
  have hE0 : hE 0 = 0 := map_zero hE
  have hlt : 1 < d * m :=
    Nat.lt_of_lt_of_le hm (Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero hd0))
  have hnz : hE.symm (0, 1) ≠ 0 := by
    intro h0
    refine hm.ne' ?_
    have h3 : hE (hE.symm (0, 1)) = hE 0 := by rw [h0]
    rw [hApp, hE0] at h3
    have h5 : (1 : ZMod m) = (0 : ZMod m) := congrArg Prod.snd h3
    have h5' : (1 : ZMod m) = 0 := by rw [h5]
    exact ZMod.one_eq_zero_iff.mp h5'
  have hconn : ∀ z : ZMod (d * m), ZMod.castHom (Nat.dvd_mul_right d m) (ZMod d) z
      = (hE z).1 := by
    intro z
    have h1 : ZMod.castHom (Nat.dvd_mul_right d m) (ZMod d) z = ZMod.cast (R := ZMod d) z :=
      ZMod.castHom_apply z
    have h2 : (hE z).1 = (ZMod.cast (R := ZMod d × ZMod m) z).1 := rfl
    rw [h1, h2, Prod.fst_zmod_cast]
  have hreindex : ∑ x, f x * stdAddChar (N := d * m) x
      = ∑ p : ZMod d × ZMod m, f (hE.symm p) * stdAddChar (N := d * m) (hE.symm p) :=
    (Equiv.sum_comp hE.toEquiv.symm
      (fun x : ZMod (d * m) => f x * stdAddChar (N := d * m) x)).symm
  have hsplit : ∀ (b : ZMod d) (t : ZMod m),
      f (hE.symm (b, t)) * stdAddChar (N := d * m) (hE.symm (b, t))
        = f (hE.symm (b, 0)) * stdAddChar (N := d * m) (hE.symm (b, 0))
          * stdAddChar (N := d * m) (hE.symm (0, t)) := by
    intro b t
    have hdec : hE.symm (b, t) = hE.symm (b, 0) + hE.symm (0, t) := by
      refine hEinj ?_
      rw [map_add, hApp, hApp, hApp]
      have hp0 : (b, 0) + (0, t) = (b + 0, 0 + t) := rfl
      rw [hp0, add_zero, zero_add]
    have hfdep : f (hE.symm (b, t)) = f (hE.symm (b, 0)) := by
      refine hf _ _ ?_
      rw [hconn, hconn, hApp, hApp]
    rw [hfdep, hdec, AddChar.map_add_eq_mul]
    ring
  have hψt : ∀ t : ZMod m, (stdAddChar (N := d * m)).compAddMonoidHom
      ((hE.symm.toAddMonoidHom).comp (AddMonoidHom.inr (ZMod d) (ZMod m))) t
      = stdAddChar (N := d * m) (hE.symm (0, t)) := by
    intro t
    rw [AddChar.compAddMonoidHom_apply, AddMonoidHom.comp_apply, AddMonoidHom.inr_apply]
    rfl
  have hψ₀ne : (stdAddChar (N := d * m)).compAddMonoidHom
      ((hE.symm.toAddMonoidHom).comp (AddMonoidHom.inr (ZMod d) (ZMod m))) ≠ 0 := by
    rw [AddChar.ne_zero_iff]
    refine ⟨1, ?_⟩
    intro h1
    rw [hψt, stdAddChar_rootExp] at h1
    refine rootExp_ne_one hlt ((hE.symm (0, 1)).val) ?_ h1
    rw [Nat.mod_eq_of_lt (ZMod.val_lt _)]
    exact fun h => hnz ((ZMod.val_eq_zero (hE.symm (0, 1))).mp h)
  rw [hreindex, Fintype.sum_prod_type]
  have hsum : ∑ b : ZMod d, ∑ t : ZMod m,
      f (hE.symm (b, t)) * stdAddChar (N := d * m) (hE.symm (b, t))
        = ∑ b : ZMod d, ∑ t : ZMod m,
            f (hE.symm (b, 0)) * stdAddChar (N := d * m) (hE.symm (b, 0))
              * stdAddChar (N := d * m) (hE.symm (0, t)) :=
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun t _ => hsplit b t
  rw [hsum]
  have hkey : ∑ b : ZMod d, ∑ t : ZMod m,
      f (hE.symm (b, 0)) * stdAddChar (N := d * m) (hE.symm (b, 0))
        * stdAddChar (N := d * m) (hE.symm (0, t))
      = ∑ b : ZMod d, f (hE.symm (b, 0)) * stdAddChar (N := d * m) (hE.symm (b, 0))
          * ∑ t : ZMod m, (stdAddChar (N := d * m)).compAddMonoidHom
              ((hE.symm.toAddMonoidHom).comp (AddMonoidHom.inr (ZMod d) (ZMod m))) t := by
    refine Finset.sum_congr rfl fun b _ => ?_
    exact (Finset.mul_sum Finset.univ
      ((stdAddChar (N := d * m)).compAddMonoidHom
        ((hE.symm.toAddMonoidHom).comp (AddMonoidHom.inr (ZMod d) (ZMod m))))
      (f (hE.symm (b, 0)) * stdAddChar (N := d * m) (hE.symm (b, 0)))).symm
  rw [hkey, AddChar.sum_eq_zero_iff_ne_zero.2 hψ₀ne]
  simp only [mul_zero]
  exact Finset.sum_const_zero

/-! ## The square-root count and the chirp identity -/

/-- The number of square roots of `y` in `ZMod N`. -/
private def sqFiber (N : ℕ) [NeZero N] (y : ZMod N) : ℕ :=
  Fintype.card {x : ZMod N // x ^ 2 = y}

private theorem sqFiber_filter (N : ℕ) [NeZero N] (y : ZMod N) :
    (Finset.univ.filter (fun x : ZMod N => x ^ 2 = y)).card = sqFiber N y := by
  rw [← Fintype.card_coe (Finset.univ.filter (fun x : ZMod N => x ^ 2 = y) : Finset (ZMod N))]
  refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl (ZMod N)) fun x => ?_)
  simp [Finset.mem_filter]

private theorem castHom_congr {n m : ℕ} [NeZero n] [NeZero m] (h₁ h₂ : m ∣ n) (y : ZMod n) :
    ZMod.castHom h₁ (ZMod m) y = ZMod.castHom h₂ (ZMod m) y := by
  refine ZMod.val_injective m ?_
  rw [castHom_val_mod]

/-- **CRT multiplicativity of the square-root count.**  Via the Chinese-remainder
ring equivalence `ZMod (d*c) ≃ ZMod d × ZMod c`, a square root of `y` splits into
a square root of each component, bijectively. -/
private theorem sqFiber_mul {d c : ℕ} [NeZero d] [NeZero c] [NeZero (d * c)]
    (hcop : Nat.Coprime d c) (y : ZMod (d * c)) :
    sqFiber (d * c) y
      = sqFiber d (ZMod.castHom (Nat.dvd_mul_right d c) (ZMod d) y)
        * sqFiber c (ZMod.castHom (Nat.dvd_mul_left c d) (ZMod c) y) := by
  let hE := ZMod.chineseRemainder hcop
  -- hE : ZMod (d * c) ≃+* ZMod d × ZMod c
  have hEc1 : ∀ w : ZMod (d * c), (hE w).1 = ZMod.castHom (Nat.dvd_mul_right d c) (ZMod d) w := by
    intro w
    have h2 : (hE w).1 = (ZMod.cast (R := ZMod d × ZMod c) w).1 := rfl
    rw [h2, Prod.fst_zmod_cast, ZMod.castHom_apply]
  have hEc2 : ∀ w : ZMod (d * c), (hE w).2 = ZMod.castHom (Nat.dvd_mul_left c d) (ZMod c) w := by
    intro w
    have h2 : (hE w).2 = (ZMod.cast (R := ZMod d × ZMod c) w).2 := rfl
    rw [h2, Prod.snd_zmod_cast, ZMod.castHom_apply]
  have hpow : ∀ w : ZMod (d * c), (hE w) ^ 2 = hE (w ^ 2) := by
    intro w
    rw [pow_two, ← map_mul, ← pow_two]
  have h1 : Fintype.card {x : ZMod (d * c) // x ^ 2 = y}
      = Fintype.card {u : ZMod d × ZMod c //
          u.1 ^ 2 = (ZMod.castHom (Nat.dvd_mul_right d c) (ZMod d)) y
            ∧ u.2 ^ 2 = (ZMod.castHom (Nat.dvd_mul_left c d) (ZMod c)) y} := by
    refine Fintype.card_congr (Equiv.subtypeEquiv hE.toEquiv fun x => ?_)
    constructor
    · intro hx
      have hmap : (hE x) ^ 2 = hE y := by rw [hpow, hx]
      exact ⟨by rw [← hEc1 y]; exact congrArg Prod.fst hmap,
        by rw [← hEc2 y]; exact congrArg Prod.snd hmap⟩
    · intro hx
      refine hE.toEquiv.injective ?_
      show hE (x ^ 2) = hE y
      rw [← hpow]
      refine Prod.ext ?_ ?_
      · rw [hEc1 y]; exact hx.1
      · rw [hEc2 y]; exact hx.2
  simp only [sqFiber]
  rw [h1, Fintype.card_congr (Equiv.subtypeProdEquivProd
    (p := fun x : ZMod d => x ^ 2 = ZMod.castHom (Nat.dvd_mul_right d c) (ZMod d) y)
    (q := fun x : ZMod c => x ^ 2 = ZMod.castHom (Nat.dvd_mul_left c d) (ZMod c) y)),
    Fintype.card_prod]

/-- **Per-prime square-root count** (Euler criterion): `#{x² = y} = 1 + χ_p(y)`. -/
private theorem sqFiber_prime (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (y : ZMod p) :
    (sqFiber p y : ℂ) = 1 + ((jacobiSym (y.val : ℤ) p : ℤ) : ℂ) := by
  classical
  haveI : NeZero p := ⟨Nat.ne_of_gt (‹Fact p.Prime›.1.pos)⟩
  have hset : {x : ZMod p | x ^ 2 = ((y.val : ℤ) : ZMod p)} = {x : ZMod p | x ^ 2 = y} := by
    ext x
    simp
  have h2 := legendreSym.card_sqrts p hp (y.val : ℤ)
  simp only [hset] at h2
  rw [jacobiSym.legendreSym.to_jacobiSym p (y.val : ℤ)] at h2
  have h3 : ({x : ZMod p | x ^ 2 = y}).toFinset.card
      = Fintype.card {x : ZMod p // x ^ 2 = y} := by
    rw [Set.toFinset_card]
    exact Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl (ZMod p)) fun _ => Iff.rfl)
  rw [h3] at h2
  rw [sqFiber]
  have h5 : ((Fintype.card {x : ZMod p // x ^ 2 = y} : ℕ) : ℤ)
      = (jacobiSym (y.val : ℤ) p : ℤ) + 1 := h2
  have h6 : ((Fintype.card {x : ZMod p // x ^ 2 = y} : ℕ) : ℂ)
      = (((Fintype.card {x : ZMod p // x ^ 2 = y} : ℕ) : ℤ) : ℂ) := by
    rw [Int.cast_natCast]
  rw [h6, h5, Int.cast_add, Int.cast_one]
  ring

/-- Per-prime count read on `ZMod con` through the cast into `ZMod p`. -/
private theorem sqFiber_prime_con (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpcon : p ∣ con)
    (y : ZMod con) :
    (sqFiber p (ZMod.castHom hpcon (ZMod p) y) : ℂ) = 1 + chiP p y := by
  rw [sqFiber_prime p hp, castHom_val_mod]
  have hmod : ((y.val % p : ℕ) : ℤ) = (y.val : ℤ) % (p : ℤ) := by push_cast; rfl
  simp only [chiP]
  rw [hmod, ← jacobiSym.mod_left (y.val : ℤ) p]

/-- The Legendre symbol is multiplicative in the modulus. -/
private theorem chiP_mul (d c : ℕ) [NeZero d] [NeZero c] (y : ZMod con) :
    chiP d y * chiP c y = chiP (d * c) y := by
  simp only [chiP]
  rw [jacobiSym.mul_right (y.val : ℤ) d c]
  push_cast
  rfl

/-- Dependence of `y ↦ J(y.val | d)` through the cast into `ZMod d`. -/
private theorem chiP_dc_dep {d c : ℕ} [NeZero (d * c)] (x y : ZMod (d * c)) :
    ZMod.castHom (Nat.dvd_mul_right d c) (ZMod d) x
      = ZMod.castHom (Nat.dvd_mul_right d c) (ZMod d) y
    → (((jacobiSym (x.val : ℤ) d : ℤ) : ℂ)) = (((jacobiSym (y.val : ℤ) d : ℤ) : ℂ)) := by
  intro hxy
  have hv : x.val % d = y.val % d := by
    rw [← castHom_val_mod (Nat.dvd_mul_right d c) x, hxy,
      castHom_val_mod (Nat.dvd_mul_right d c) y]
  have hmodx : ((x.val % d : ℕ) : ℤ) = (x.val : ℤ) % (d : ℤ) := by push_cast; rfl
  have hmody : ((y.val % d : ℕ) : ℤ) = (y.val : ℤ) % (d : ℤ) := by push_cast; rfl
  rw [jacobiSym.mod_left (x.val : ℤ) d, jacobiSym.mod_left (y.val : ℤ) d, ← hmodx, ← hmody,
    hv]

/-- Divisor-vanishing, `con`-direct form: for `con = d * c` with `d` coprime to
`c ≥ 2`, the character-weighted sum of the Legendre symbol at `d` vanishes. -/
private theorem sum_chiP_mul_stdAddChar_eq_zero {d c : ℕ} [NeZero d] [NeZero c]
    (hdc : con = d * c) (hcop : Nat.Coprime d c) (hm : 1 < c) :
    ∑ y : ZMod con, chiP d y * stdAddChar (N := con) y = 0 := by
  haveI hNdc : NeZero (d * c) := ⟨fun h => con_ne_zero (by rw [hdc, h])⟩
  have hdvd : con ∣ d * c := by rw [hdc]
  have hdvd' : d * c ∣ con := by rw [hdc]
  set E : ZMod (d * c) →+* ZMod con := ZMod.castHom hdvd (ZMod con) with hEdef
  have hEval : ∀ z : ZMod (d * c), (E z).val = z.val := by
    intro z
    have hlt : z.val < con := by rw [hdc]; exact ZMod.val_lt z
    rw [castHom_val_mod hdvd z, Nat.mod_eq_of_lt hlt]
  have hbij : Function.Bijective E := by
    constructor
    · intro x y hxy
      refine ZMod.val_injective (d * c) ?_
      rw [← hEval x, ← hEval y, hxy]
    · intro y
      refine ⟨ZMod.castHom hdvd' (ZMod (d * c)) y, ?_⟩
      refine ZMod.val_injective con ?_
      rw [hEval _, castHom_val_mod hdvd' y]
      exact Nat.mod_eq_of_lt (by rw [← hdc]; exact ZMod.val_lt y)
  have hχ : ∀ z : ZMod (d * c), chiP d (E z) = ((jacobiSym ((z.val : ℕ) : ℤ) d : ℤ) : ℂ) := by
    intro z
    simp only [chiP]
    rw [← hEval]
  have hψ : ∀ z : ZMod (d * c), stdAddChar (N := con) (E z) = stdAddChar (N := d * c) z := by
    intro z
    rw [stdAddChar_rootExp (E z), stdAddChar_rootExp z, ← hEval]
    exact congrArg (rootExp (E z).val) hdc
  rw [← Fintype.sum_bijective E hbij
    (fun z : ZMod (d * c) => ((jacobiSym (z.val : ℤ) d : ℤ) : ℂ) * stdAddChar (N := d * c) z)
    (fun y : ZMod con => chiP d y * stdAddChar (N := con) y)
    (fun z => by
      show ((jacobiSym (z.val : ℤ) d : ℤ) : ℂ) * stdAddChar (N := d * c) z
        = chiP d (E z) * stdAddChar (N := con) (E z)
      rw [hχ, hψ])]
  exact sum_mul_stdAddChar_eq_zero hcop hm chiP_dc_dep

/-- Pointwise expansion of the square-root count product into the sixteen
Jacobi-symbol terms indexed by the divisors of `con`. -/
private theorem chirp_expand (y : ZMod con) :
    (1 + chiP 3 y) * (1 + chiP 5 y) * (1 + chiP 409 y) * (1 + chiP 683 y)
      = 1 + chiP 3 y + chiP 5 y + chiP 409 y + chiP 683 y
        + chiP 3 y * chiP 5 y + chiP 3 y * chiP 409 y + chiP 3 y * chiP 683 y
        + chiP 5 y * chiP 409 y + chiP 5 y * chiP 683 y + chiP 409 y * chiP 683 y
        + chiP 3 y * chiP 5 y * chiP 409 y + chiP 3 y * chiP 5 y * chiP 683 y
        + chiP 3 y * chiP 409 y * chiP 683 y + chiP 5 y * chiP 409 y * chiP 683 y
        + chiP 3 y * chiP 5 y * chiP 409 y * chiP 683 y := by
  ring

/-- The standard additive character is nonzero. -/
private theorem stdAddChar_ne_zero (N : ℕ) [NeZero N] (hf : 1 < N) :
    (stdAddChar (N := N)) ≠ 0 := by
  rw [AddChar.ne_zero_iff]
  refine ⟨((1 : ℕ) : ZMod N), fun h1 => ?_⟩
  rw [stdAddChar_rootExp, ZMod.val_natCast N, Nat.mod_eq_of_lt hf] at h1
  exact rootExp_ne_one hf 1 (by rw [Nat.mod_eq_of_lt hf]; norm_num) h1

/-- **The chirp identity**: `∑_x ψ(x²) = τ(χ)`.  The fiber count
`#{x² = y} = (1+χ₃)(1+χ₅)(1+χ₄₀₉)(1+χ₆₈₃)` expands into sixteen Jacobi terms;
fourteen vanish by divisor-vanishing, the trivial term vanishes since `ψ` is
nontrivial, and the full-modulus term is exactly the Gauss sum. -/
private theorem chirp_con :
    ∑ x : ZMod con, stdAddChar (N := con) (x * x) = gaussSum qchar' stdAddChar := by
  haveI hN15 : NeZero (15 * 279347) := ⟨by norm_num⟩
  haveI hN409 : NeZero (409 * 683) := ⟨by norm_num⟩
  -- fiber grouping
  rw [sum_fiber_eq (fun x : ZMod con => x ^ 2) (fun x => stdAddChar (N := con) (x * x))]
  have hinner : ∀ y : ZMod con,
      ∑ x ∈ Finset.univ.filter (fun x : ZMod con => x ^ 2 = y),
        stdAddChar (N := con) (x * x)
        = (sqFiber con y : ℂ) * stdAddChar (N := con) y := by
    intro y
    have hconst : ∀ x ∈ Finset.univ.filter (fun x : ZMod con => x ^ 2 = y),
        stdAddChar (N := con) (x * x) = stdAddChar (N := con) y := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [← pow_two, hx]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, sqFiber_filter]
  simp only [hinner]
  -- the count identity
  have hcount : ∀ y : ZMod con, (sqFiber con y : ℂ)
      = (1 + chiP 3 y) * (1 + chiP 5 y) * (1 + chiP 409 y) * (1 + chiP 683 y) := by
    intro y
    have hsplit1 := sqFiber_mul (d := 15) (c := 279347) (hcop := by norm_num) y
    have hsplit2 := sqFiber_mul (d := 3) (c := 5) (hcop := by norm_num)
      (ZMod.castHom (Nat.dvd_mul_right 15 279347) (ZMod 15) y)
    have hsplit3 := sqFiber_mul (d := 409) (c := 683) (hcop := by norm_num)
      (ZMod.castHom (Nat.dvd_mul_left 279347 15) (ZMod 279347) y)
    have hcc3 : ZMod.castHom (Nat.dvd_mul_right 3 5) (ZMod 3)
        (ZMod.castHom (Nat.dvd_mul_right 15 279347) (ZMod 15) y)
        = ZMod.castHom (show (3 : ℕ) ∣ con by norm_num) (ZMod 3) y := by
      rw [castHom_comp_gen (hp := (by norm_num : (3 : ℕ) ∣ 15))
        (hq := Nat.dvd_mul_right 15 279347) y]
    have hcc5 : ZMod.castHom (Nat.dvd_mul_left 5 3) (ZMod 5)
        (ZMod.castHom (Nat.dvd_mul_right 15 279347) (ZMod 15) y)
        = ZMod.castHom (show (5 : ℕ) ∣ con by norm_num) (ZMod 5) y := by
      rw [castHom_comp_gen (hp := Nat.dvd_mul_left 5 3)
        (hq := Nat.dvd_mul_right 15 279347) y]
    have hcc409 : ZMod.castHom (Nat.dvd_mul_right 409 683) (ZMod 409)
        (ZMod.castHom (Nat.dvd_mul_left 279347 15) (ZMod 279347) y)
        = ZMod.castHom (show (409 : ℕ) ∣ con by norm_num) (ZMod 409) y := by
      rw [castHom_comp_gen (hp := (by norm_num : (409 : ℕ) ∣ 279347))
        (hq := Nat.dvd_mul_left 279347 15) y]
    have hcc683 : ZMod.castHom (Nat.dvd_mul_left 683 409) (ZMod 683)
        (ZMod.castHom (Nat.dvd_mul_left 279347 15) (ZMod 279347) y)
        = ZMod.castHom (show (683 : ℕ) ∣ con by norm_num) (ZMod 683) y := by
      rw [castHom_comp_gen (hp := Nat.dvd_mul_left 683 409)
        (hq := Nat.dvd_mul_left 279347 15) y]
    have h1 : (sqFiber con y : ℂ)
        = ((sqFiber 3 (ZMod.castHom (Nat.dvd_mul_right 3 5) (ZMod 3)
              (ZMod.castHom (Nat.dvd_mul_right 15 279347) (ZMod 15) y)) * sqFiber 5
              (ZMod.castHom (Nat.dvd_mul_left 5 3) (ZMod 5)
                (ZMod.castHom (Nat.dvd_mul_right 15 279347) (ZMod 15) y)) : ℕ) : ℂ)
          * ((sqFiber 409 (ZMod.castHom (Nat.dvd_mul_right 409 683) (ZMod 409)
                (ZMod.castHom (Nat.dvd_mul_left 279347 15) (ZMod 279347) y)) * sqFiber 683
                (ZMod.castHom (Nat.dvd_mul_left 683 409) (ZMod 683)
                  (ZMod.castHom (Nat.dvd_mul_left 279347 15) (ZMod 279347) y)) : ℕ) : ℂ) := by
      rw [hsplit1, hsplit2, hsplit3]
      push_cast
      rfl
    haveI hp3 : Fact (3 : ℕ).Prime := ⟨by norm_num⟩
    haveI hp5 : Fact (5 : ℕ).Prime := ⟨by norm_num⟩
    haveI hp409 : Fact (409 : ℕ).Prime := ⟨by norm_num⟩
    haveI hp683 : Fact (683 : ℕ).Prime := ⟨by norm_num⟩
    rw [h1, hcc3, hcc5, hcc409, hcc683]
    push_cast
    rw [sqFiber_prime_con 3 (by norm_num) (show (3 : ℕ) ∣ con by norm_num) y,
      sqFiber_prime_con 5 (by norm_num) (show (5 : ℕ) ∣ con by norm_num) y,
      sqFiber_prime_con 409 (by norm_num) (show (409 : ℕ) ∣ con by norm_num) y,
      sqFiber_prime_con 683 (by norm_num) (show (683 : ℕ) ∣ con by norm_num) y]
    ring
  simp only [hcount]
  have hψ0 : ∑ y : ZMod con, stdAddChar (N := con) y = 0 :=
    AddChar.sum_eq_zero_iff_ne_zero.2 (stdAddChar_ne_zero con con_one_lt)
  have hstep : ∑ y : ZMod con,
      (1 + chiP 3 y) * (1 + chiP 5 y) * (1 + chiP 409 y) * (1 + chiP 683 y)
        * stdAddChar (N := con) y
      = ∑ y : ZMod con, (1 + chiP 3 y + chiP 5 y + chiP 409 y + chiP 683 y
          + chiP 3 y * chiP 5 y + chiP 3 y * chiP 409 y + chiP 3 y * chiP 683 y
          + chiP 5 y * chiP 409 y + chiP 5 y * chiP 683 y + chiP 409 y * chiP 683 y
          + chiP 3 y * chiP 5 y * chiP 409 y + chiP 3 y * chiP 5 y * chiP 683 y
          + chiP 3 y * chiP 409 y * chiP 683 y + chiP 5 y * chiP 409 y * chiP 683 y
          + chiP 3 y * chiP 5 y * chiP 409 y * chiP 683 y) * stdAddChar (N := con) y := by
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [chirp_expand y]
  rw [hstep]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, one_mul, chiP_mul]
  rw [hψ0,
    sum_chiP_mul_stdAddChar_eq_zero (d := 3) (c := 1396735) (by norm_num) (by norm_num)
      (by norm_num),
    sum_chiP_mul_stdAddChar_eq_zero (d := 5) (c := 838041) (by norm_num) (by norm_num)
      (by norm_num),
    sum_chiP_mul_stdAddChar_eq_zero (d := 409) (c := 10245) (by norm_num) (by norm_num)
      (by norm_num),
    sum_chiP_mul_stdAddChar_eq_zero (d := 683) (c := 6135) (by norm_num) (by norm_num)
      (by norm_num),
    sum_chiP_mul_stdAddChar_eq_zero (d := 15) (c := 279347) (by norm_num) (by norm_num)
      (by norm_num),
    sum_chiP_mul_stdAddChar_eq_zero (d := 1227) (c := 3415) (by norm_num) (by norm_num)
      (by norm_num),
    sum_chiP_mul_stdAddChar_eq_zero (d := 2049) (c := 2045) (by norm_num) (by norm_num)
      (by norm_num),
    sum_chiP_mul_stdAddChar_eq_zero (d := 2045) (c := 2049) (by norm_num) (by norm_num)
      (by norm_num),
    sum_chiP_mul_stdAddChar_eq_zero (d := 3415) (c := 1227) (by norm_num) (by norm_num)
      (by norm_num),
    sum_chiP_mul_stdAddChar_eq_zero (d := 279347) (c := 15) (by norm_num) (by norm_num)
      (by norm_num),
    sum_chiP_mul_stdAddChar_eq_zero (d := 6135) (c := 683) (by norm_num) (by norm_num)
      (by norm_num),
    sum_chiP_mul_stdAddChar_eq_zero (d := 10245) (c := 409) (by norm_num) (by norm_num)
      (by norm_num),
    sum_chiP_mul_stdAddChar_eq_zero (d := 838041) (c := 5) (by norm_num) (by norm_num)
      (by norm_num),
    sum_chiP_mul_stdAddChar_eq_zero (d := 1396735) (c := 3) (by norm_num) (by norm_num)
      (by norm_num)]
  simp only [add_zero, zero_add]
  have hlast : ∀ y : ZMod con, chiP (((3 * 5) * 409) * 683) y * stdAddChar (N := con) y
      = qchar' y * stdAddChar (N := con) y := by
    intro y
    have h1 : chiP (((3 * 5) * 409) * 683) y = qchar y := rfl
    rw [h1, qchar_apply]
  simp only [hlast]
  rfl

/-! ## K3b closed up to the sign input: the Gauss sum is +√con -/

/-- **K3 sign resolution, conditional.** Given the positivity input
`0 < (τ(χ)).re` (the classical Gauss/Schur sign for the fundamental
discriminant con = 4190205 ≡ 1 mod 4), the Gauss sum is `+√con`, i.e. the
chiral chirp constant `ciota`. This is the last complex-level step before the
class number formula rung. -/
theorem gaussSum_eq_sqrt_con (hpos : 0 < (gaussSum qchar' stdAddChar).re) :
    gaussSum qchar' stdAddChar = ((Real.sqrt (con : ℝ) : ℝ) : ℂ) := by
  rcases gaussSum_eq_sqrt_or_neg with h | h
  · exact h
  · exfalso
    rw [h] at hpos
    rw [Complex.neg_re, Complex.ofReal_re] at hpos
    have hsqrt : 0 < Real.sqrt (con : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast con_pos : (0:ℝ) < (con:ℝ))
    linarith

end Imscribing.Millennium.StarkGaussSign

end
