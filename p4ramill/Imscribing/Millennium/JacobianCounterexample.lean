import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
An explicit dimension-three counterexample to the Jacobian injectivity claim.

The polynomial map and rational collision are due to Levent Alpöge and Claude
Fable 5 (announced July 2026). This file formalizes the determinant and the
collision calculation over `ℚ`; it does not formalize the wider geometric
analysis of the map.
-/

open MvPolynomial

noncomputable section

namespace Millennium.JacobianCounterexample

/-- The injectivity consequence of the Jacobian conjecture, stated for
polynomial self-maps of affine `n`-space over a characteristic-zero field.
This is a necessary consequence of polynomial invertibility, not a definition
of a polynomial inverse. -/
def JacobianConjecture (k : Type) (n : ℕ) [Field k] [CharZero k] : Prop :=
  ∀ F : Fin n → MvPolynomial (Fin n) k,
    (∃ c : k, c ≠ 0 ∧
      (Matrix.of fun i j => MvPolynomial.pderiv j (F i)).det = MvPolynomial.C c) →
    Function.Injective (fun p i => MvPolynomial.eval p (F i))

def xVar : MvPolynomial (Fin 3) ℚ := X 0
def yVar : MvPolynomial (Fin 3) ℚ := X 1
def zVar : MvPolynomial (Fin 3) ℚ := X 2

def F1 : MvPolynomial (Fin 3) ℚ :=
  (C 1 + xVar * yVar) ^ 3 * zVar
    + yVar ^ 2 * (C 1 + xVar * yVar) * (C 4 + C 3 * xVar * yVar)

def F2 : MvPolynomial (Fin 3) ℚ :=
  yVar
    + C 3 * xVar * (C 1 + xVar * yVar) ^ 2 * zVar
    + C 3 * xVar * yVar ^ 2 * (C 4 + C 3 * xVar * yVar)

def F3 : MvPolynomial (Fin 3) ℚ :=
  C 2 * xVar - C 3 * xVar ^ 2 * yVar - xVar ^ 3 * zVar

def jacobianMatrix : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℚ) :=
  !![pderiv 0 F1, pderiv 1 F1, pderiv 2 F1;
     pderiv 0 F2, pderiv 1 F2, pderiv 2 F2;
     pderiv 0 F3, pderiv 1 F3, pderiv 2 F3]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
theorem jacobian_det_eq_neg_two :
    jacobianMatrix.det = C (-2 : ℚ) := by
  unfold jacobianMatrix F1 F2 F3 xVar yVar zVar
  simp [Matrix.det_fin_three, pderiv_mul, pderiv_pow, pderiv_X, pderiv_C,
        Pi.single_eq_same, Pi.single_eq_of_ne]
  simp only [map_ofNat]
  ring

def p1 : Fin 3 → ℚ := ![0, 0, -1/4]
def p2 : Fin 3 → ℚ := ![1, -3/2, 13/2]
def p3 : Fin 3 → ℚ := ![-1, 3/2, 13/2]

set_option maxHeartbeats 1000000 in
theorem points_collide :
    (eval p1 F1, eval p1 F2, eval p1 F3) = (-1/4, 0, 0) ∧
    (eval p2 F1, eval p2 F2, eval p2 F3) = (-1/4, 0, 0) ∧
    (eval p3 F1, eval p3 F2, eval p3 F3) = (-1/4, 0, 0) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp [F1, F2, F3, xVar, yVar, zVar, p1, p2, p3]
    try norm_num

theorem points_pairwise_distinct : p1 ≠ p2 ∧ p1 ≠ p3 ∧ p2 ≠ p3 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · intro h
    have := congrFun h 0
    simp only [p1, p2, p3] at this
    try norm_num at this

def polynomialMap (p : Fin 3 → ℚ) : Fin 3 → ℚ :=
  ![eval p F1, eval p F2, eval p F3]

theorem map_collision : polynomialMap p1 = polynomialMap p2 := by
  rcases points_collide with ⟨h1, h2, _⟩
  have h12 := h1.trans h2.symm
  have h1' : eval p1 F1 = eval p2 F1 ∧
      eval p1 F2 = eval p2 F2 ∧ eval p1 F3 = eval p2 F3 := by
    simpa only [Prod.mk.injEq] using h12
  funext i
  fin_cases i
  · simpa [polynomialMap] using h1'.1
  · simpa [polynomialMap] using h1'.2.1
  · simpa [polynomialMap] using h1'.2.2

theorem polynomialMap_not_injective : ¬ Function.Injective polynomialMap := by
  intro hinj
  have h12 : p1 = p2 := hinj map_collision
  exact points_pairwise_distinct.1 h12

theorem counterexample_certificate :
    jacobianMatrix.det = C (-2 : ℚ) ∧ ¬ Function.Injective polynomialMap :=
  ⟨jacobian_det_eq_neg_two, polynomialMap_not_injective⟩

theorem jacobianConjecture_false : ¬ JacobianConjecture ℚ 3 := by
  intro hJC
  let F : Fin 3 → MvPolynomial (Fin 3) ℚ := ![F1, F2, F3]
  have hdet : (Matrix.of fun i j => pderiv j (F i)).det = C (-2 : ℚ) := by
    have hmatrix : (Matrix.of fun i j => pderiv j (F i)) = jacobianMatrix := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [hmatrix, jacobian_det_eq_neg_two]
  have hinj := hJC F ⟨-2, by norm_num, hdet⟩
  have h12 := points_collide.1.trans points_collide.2.1.symm
  have h12' : eval p1 F1 = eval p2 F1 ∧
      eval p1 F2 = eval p2 F2 ∧ eval p1 F3 = eval p2 F3 := by
    simpa only [Prod.mk.injEq] using h12
  have hcollision : (fun p i => eval p (F i)) p1 = (fun p i => eval p (F i)) p2 := by
    funext i
    fin_cases i
    · simpa [F] using h12'.1
    · simpa [F] using h12'.2.1
    · simpa [F] using h12'.2.2
  have hp : p1 = p2 := hinj hcollision
  exact points_pairwise_distinct.1 hp

end Millennium.JacobianCounterexample
