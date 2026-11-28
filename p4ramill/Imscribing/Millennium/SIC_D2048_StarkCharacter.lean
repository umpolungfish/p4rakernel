import Mathlib
import Imscribing.Millennium.SIC_D2048_StarkGaloisCard
import Imscribing.Millennium.ClinkStarkBridge

/-!
# SIC_D2048_StarkCharacter — the quadratic character of F₂₀₄₈ and its L-function footing

The L-side of the Stark track for `F₂₀₄₈ = ℚ(√4190205)`: the quadratic Dirichlet
character of conductor `4190205` (the absolute discriminant already certified in
`SIC_D2048_StarkTheorem`), its character laws, its evenness, and the analytic
footing of its L-function through Mathlib's `ZMod.LFunction` API.

The evenness of the character is the entry ticket to the completed-L functional
equation; differentiability at `s = 1` follows from the vanishing of the character
sum. Together with the algebraic regulator identity
(`2 * cosh (log ε) = 2047` in `ClinkStarkBridge`), these are the exact symmetries
that the Kronecker class-number relation folds into `L'(0, χ) = -log ε`.
-/

namespace Imscribing.Millennium.StarkCharacterD2048

open scoped NumberTheorySymbols

/-! ## Arithmetic of the conductor -/

/-- The conductor: the absolute discriminant of `F₂₀₄₈ = ℚ(√4190205)`. -/
abbrev con : ℕ := 4190205

theorem con_pos : 0 < con := by norm_num

theorem con_one_lt : 1 < con := by norm_num

theorem con_ne_zero : con ≠ 0 := by norm_num

instance conNeZero : NeZero con := ⟨con_ne_zero⟩

theorem con_odd : Odd con := ⟨2095102, by norm_num⟩

theorem con_mod_four : con % 4 = 1 := by norm_num

theorem con_mod_eight : con % 8 = 5 := by norm_num

/-! ## The quadratic character -/

/-- The quadratic character of `F₂₀₄₈` at the residue class `x`:
the Jacobi/Kronecker symbol `(x | 4190205)` on the canonical representative. -/
def qchar (x : ZMod con) : ℂ :=
  ((jacobiSym (x.val : ℤ) con : ℤ) : ℂ)

theorem qchar_mul (a b : ZMod con) : qchar (a * b) = qchar a * qchar b := by
  have hval : (((a * b : ZMod con).val : ℕ) : ℤ) = ((a.val : ℤ) * (b.val : ℤ)) % con := by
    rw [ZMod.val_mul]
    push_cast
    rfl
  simp only [qchar]
  rw [hval, ← jacobiSym.mod_left]
  push_cast
  rw [jacobiSym.mul_left]
  norm_num

theorem qchar_eq_zero_iff (x : ZMod con) : qchar x = 0 ↔ ¬IsUnit x := by
  have hxcast : (↑x.val : ZMod con) = x :=
    (ZMod.natCast_val x).trans (ZMod.cast_id _ x)
  constructor
  · intro h hu
    have hu' : IsUnit (↑x.val : ZMod con) := by rw [hxcast]; exact hu
    have hcop : x.val.Coprime con := (ZMod.isUnit_iff_coprime _ _).mp hu'
    rw [Nat.coprime_iff_gcd_eq_one] at hcop
    simp only [qchar, Int.cast_eq_zero] at h
    rw [jacobiSym.eq_zero_iff_not_coprime] at h
    exact absurd hcop h
  · intro hu
    have hcop : ¬x.val.Coprime con :=
      fun hc => hu (by rw [← hxcast]; exact (ZMod.isUnit_iff_coprime _ _).mpr hc)
    rw [Nat.coprime_iff_gcd_eq_one] at hcop
    simp only [qchar, Int.cast_eq_zero]
    rw [jacobiSym.eq_zero_iff_not_coprime]
    exact hcop

theorem qchar_one : qchar 1 = 1 := by
  have hv1 : ((1 : ZMod con).val : ℤ) = 1 := by
    have h := ZMod.val_natCast con 1
    norm_num [h]
    rfl
  simp only [qchar, hv1]
  exact_mod_cast jacobiSym.one_left con

theorem qchar_zero : qchar 0 = 0 := by
  simp only [qchar, ZMod.val_zero]
  push_cast
  exact_mod_cast jacobiSym.zero_left con_one_lt

/-! ## The character as a `MulChar` -/

/-- The character in bundled `MulChar` form, the input shape of the
`ZMod.LFunction` analytic API. -/
def qchar' : MulChar (ZMod con) ℂ where
  toFun := qchar
  map_one' := qchar_one
  map_mul' := qchar_mul
  map_nonunit' := fun a ha => (qchar_eq_zero_iff a).mpr ha

theorem qchar_apply (x : ZMod con) : qchar' x = qchar x := rfl

/-- Nontriviality: `χ(2) = -1`, from `4190205 ≡ 5 (mod 8)`. -/
theorem qchar_two : qchar 2 = -1 := by
  have hv2 : ((2 : ZMod con).val : ℤ) = 2 := by
    have h := ZMod.val_natCast con 2
    norm_num [h]
    rfl
  have h2 : jacobiSym (2 : ℤ) con = (-1 : ℤ) := by
    rw [jacobiSym.at_two con_odd]
    have h8 : ((con : ℕ) : ZMod 8) = 5 := by
      rw [← ZMod.natCast_mod, con_mod_eight]
      rfl
    rw [h8]
    decide
  simp only [qchar, hv2]
  exact_mod_cast h2

/-- Evenness at `-1`: `χ(-1) = 1`, from `4190205 ≡ 1 (mod 4)`. -/
theorem qchar_neg_one : qchar (-1 : ZMod con) = 1 := by
  have hvn : ((-1 : ZMod con).val : ℤ) % con = (-1 : ℤ) % con := by
    have hve : ((-1 : ZMod con).val : ℤ) = (con - 1 : ℕ) := by norm_num
    rw [hve]
    push_cast
    norm_num
  calc qchar (-1 : ZMod con)
      _ = ((jacobiSym (((-1 : ZMod con).val : ℤ)) con : ℤ) : ℂ) := rfl
      _ = ((jacobiSym ((-1 : ℤ)) con : ℤ) : ℂ) := by rw [jacobiSym.mod_left' hvn]
      _ = ((ZMod.χ₄ ((con : ℕ)) : ℤ) : ℂ) := by rw [jacobiSym.at_neg_one con_odd]
      _ = 1 := by
          rw [ZMod.χ₄_nat_one_mod_four con_mod_four]
          norm_num

/-- Full evenness: `χ(-x) = χ(x)` — the entry ticket to the completed-L
functional equation. -/
theorem qchar_even : (qchar : ZMod con → ℂ).Even := by
  intro x
  have hsplit : (-x : ZMod con) = (-1 : ZMod con) * x := by
    rw [neg_one_mul]
  rw [hsplit, qchar_mul, qchar_neg_one, one_mul]

/-! ## The character sums -/

/-- The negation equivalence on the residue classes. -/
def negEquiv : ZMod con ≃ ZMod con where
  toFun := fun x => -x
  invFun := fun x => -x
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/-- Nontriviality of the bundled character. -/
theorem qchar'_ne_one : qchar' ≠ 1 := by
  intro h1
  have h2 : qchar' ((2 : ℕ) : ZMod con) = (1 : MulChar (ZMod con) ℂ) ((2 : ℕ) : ZMod con) :=
    DFunLike.congr_fun h1 ((2 : ℕ) : ZMod con)
  rw [qchar_apply, MulChar.one_apply
    ((ZMod.isUnit_iff_coprime 2 con).mpr (by decide : Nat.Coprime 2 4190205)),
    show qchar ((2 : ℕ) : ZMod con) = qchar 2 from rfl, qchar_two] at h2
  norm_num at h2

/-- The full character sum vanishes: `∑ χ = 0`. -/
theorem sum_qchar_eq_zero : ∑ j : ZMod con, qchar j = 0 := by
  have h := qchar'.sum_eq_zero_of_ne_one qchar'_ne_one
  simpa [qchar_apply] using h

set_option maxRecDepth 4000 in
/-- The first Bernoulli moment `∑ j · χ(j)` vanishes: pair each `j` with `-j`;
the identity `χ(-j) = χ(j)` and `(-j).val + j.val = 4190205` on the unit classes
do the pairing uniformly, including at `j = 0` where `χ` vanishes. -/
theorem sum_val_mul_qchar_eq_zero :
    ∑ j : ZMod con, ((j.val : ℤ) : ℂ) * qchar j = 0 := by
  have hterm : ∀ j : ZMod con,
      (((j.val : ℤ) : ℂ) * qchar j) + ((((-j).val : ℤ) : ℂ) * qchar (-j))
        = ((con : ℤ) : ℂ) * qchar j := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simp only [neg_zero, neg_neg, qchar_zero, mul_zero, zero_mul, zero_add, add_zero]
    · haveI hnz : NeZero (j : ZMod con) := ⟨hj⟩
      have hev : qchar (-j) = qchar j := by
        have h := qchar_even (-j)
        simpa using h.symm
      have hjlt : (j.val : ℕ) < con := ZMod.val_lt j
      rw [hev, ZMod.val_neg_of_ne_zero j, Nat.cast_sub (le_of_lt hjlt)]
      push_cast
      ring
  have h1 : (∑ j : ZMod con, ((j.val : ℤ) : ℂ) * qchar j)
      = ∑ j : ZMod con, (((-j).val : ℤ) : ℂ) * qchar (-j) := by
    refine Fintype.sum_equiv negEquiv
      (fun j => ((j.val : ℤ) : ℂ) * qchar j)
      (fun k => (((-k).val : ℤ) : ℂ) * qchar (-k))
      (fun x => by simp [negEquiv])
  have hS2 : (∑ j : ZMod con, ((j.val : ℤ) : ℂ) * qchar j)
      + (∑ j : ZMod con, (((-j).val : ℤ) : ℂ) * qchar (-j)) = 0 := by
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    rw [← Finset.mul_sum, sum_qchar_eq_zero, mul_zero]
  rw [← h1] at hS2
  have hdone : (2 : ℂ) * (∑ j : ZMod con, ((j.val : ℤ) : ℂ) * qchar j) = 0 := by
    rw [two_mul]
    exact hS2
  exact ((mul_eq_zero.mp hdone).resolve_left (by norm_num))

/-! ## The L-function footing -/

/-- The L-function of the quadratic character is differentiable at `s = 1`,
because the character sum vanishes. -/
theorem lFunction_differentiable_at_one :
    DifferentiableAt ℂ (ZMod.LFunction qchar) 1 :=
  ZMod.differentiableAt_LFunction qchar 1 (Or.inr sum_qchar_eq_zero)

theorem lFunction_zero : ZMod.LFunction qchar 0 = -qchar 0 / 2 :=
  ZMod.LFunction_apply_zero_of_even qchar_even

end Imscribing.Millennium.StarkCharacterD2048
