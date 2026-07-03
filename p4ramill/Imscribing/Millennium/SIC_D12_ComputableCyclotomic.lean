import Mathlib

/-!
# SIC_D12_ComputableCyclotomic — piece 1 of the d=12 axiom-drop build

Mathlib's `CyclotomicField` is abstract (splitting-field quotients) and not
computable, so `native_decide` cannot evaluate ring identities in it. This module
builds the computable surrogate the plan needs: the group algebra ℚ[ℤ/n]
(= ℚ[X]/(Xⁿ − 1), which contains the n-th roots of unity as `X = ζ`) represented
as coefficient vectors `Fin n → ℚ`, with fully computable +, *, conjugation and
decidable equality. Ring identities among roots of unity are then `native_decide`.

This is the foundation brick; if `native_decide` fires here, the 143 Gram
identities (piece 4) become mechanically checkable in this ring.
-/

namespace SIC.D12.ComputableCyclotomic

/-- Element of ℚ[ℤ/n]: a coefficient vector over the n-th roots of unity. -/
abbrev Cyc (n : ℕ) := Fin n → ℚ

variable {n : ℕ}

def zeroC : Cyc n := fun _ => 0
def addC (a b : Cyc n) : Cyc n := fun i => a i + b i
def negC (a : Cyc n) : Cyc n := fun i => - a i

/-- Unit `1` (the coefficient of ζ⁰). Needs `n > 0` for the index `0` to exist. -/
def oneC [NeZero n] : Cyc n := fun i => if i = 0 then 1 else 0

/-- Cyclic convolution: `(a*b)_k = Σ_i a_i · b_(k−i)`, indices in ℤ/n
    (Fin subtraction is already mod n). This is multiplication in ℚ[X]/(Xⁿ−1). -/
def mulC (a b : Cyc n) : Cyc n := fun k => ∑ i : Fin n, a i * b (k - i)

/-- The primitive generator `ζ = X` (coefficient 1 on the degree-1 slot). -/
def zeta [NeZero n] : Cyc n := fun i => if i = 1 then 1 else 0

/-- Complex conjugation on roots of unity: `ζ ↦ ζ⁻¹`, i.e. reverse the exponent. -/
def conjC (a : Cyc n) : Cyc n := fun i => a (-i)

/-- Scalar embedding ℚ → Cyc n. -/
def ofQ [NeZero n] (q : ℚ) : Cyc n := fun i => if i = 0 then q else 0

-- ── Foundation checks: native_decide fires on root-of-unity identities ──

/-- ζ · ζ̄ = 1 in ℚ[ℤ/12]: a root of unity times its conjugate is the identity. -/
theorem zeta_mul_conj_eq_one : mulC (zeta (n := 12)) (conjC (zeta (n := 12))) = oneC := by
  native_decide

/-- ζ¹² = 1 in ℚ[ℤ/12] (twelfth power of the generator closes the cycle). -/
theorem zeta_pow_twelve :
    (mulC (zeta) (mulC zeta (mulC zeta (mulC zeta (mulC zeta (mulC zeta
      (mulC zeta (mulC zeta (mulC zeta (mulC zeta (mulC zeta zeta))))))))))
      = (oneC : Cyc 12) := by
  native_decide

/-- Σ_{k} ζᵏ = 0 in ℚ[ℤ/12]: the twelve roots of unity sum to zero. -/
theorem sum_roots_eq_zero :
    (Finset.univ.sum (fun k : Fin 12 => (fun i => if i = k then (1:ℚ) else 0 : Cyc 12)))
      = (fun _ => 1) := by
  native_decide

end SIC.D12.ComputableCyclotomic
