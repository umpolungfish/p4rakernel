import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Imscribing.Millennium.ZetaSICDualFrame

namespace Imscribing.Paraconsistent.SICInverse

open Matrix
open scoped BigOperators
open Imscribing.Millennium.ZetaSICDualFrame

def J (n : Nat) : Matrix (Fin n) (Fin n) Real := fun _ _ => 1

lemma J_apply (n : Nat) (i j : Fin n) : J n i j = 1 := rfl

lemma J_sq (n : Nat) : (J n) * (J n) = (n : Real) • J n := by
  ext i j
  simp only [Matrix.mul_apply, J_apply, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp [Matrix.smul_apply, J_apply]

noncomputable def sicGramReal (d : ℕ+) :
    Matrix (Fin ((d : Nat) ^ 2)) (Fin ((d : Nat) ^ 2)) Real :=
  (((d : Nat) : Real) / (((d : Nat) : Real) + 1)) • 1 +
    (1 / (((d : Nat) : Real) + 1)) • J ((d : Nat) ^ 2)

noncomputable def sicDualReal (d : ℕ+) :
    Matrix (Fin ((d : Nat) ^ 2)) (Fin ((d : Nat) ^ 2)) Real :=
  (1 - 12 / ((d : Nat) : Real) * (-1 / 12)) • 1 +
    (12 / (((d : Nat) : Real) ^ 2) * (-1 / 12)) • J ((d : Nat) ^ 2)

theorem sicDualReal_eq (d : ℕ+) :
    sicDualReal d =
      ((((d : Nat) : Real) + 1) / ((d : Nat) : Real)) • 1 +
        (-1 / (((d : Nat) : Real) ^ 2)) • J ((d : Nat) ^ 2) := by
  have hd : ((d : Nat) : Real) ≠ 0 := by exact_mod_cast d.ne_zero
  have h1 : (1 - 12 / ((d : Nat) : Real) * (-1 / 12))
      = (((d : Nat) : Real) + 1) / ((d : Nat) : Real) := by
    field_simp [hd] <;> ring
  have h2 : (12 / (((d : Nat) : Real) ^ 2) * (-1 / 12))
      = -1 / (((d : Nat) : Real) ^ 2) := by
    field_simp [hd] <;> ring
  dsimp [sicDualReal]
  rw [h1, h2]

private theorem affine_product_real (n : Nat) (a b c e : Real) :
    (a • (1 : Matrix (Fin n) (Fin n) Real) + b • J n) *
      (c • (1 : Matrix (Fin n) (Fin n) Real) + e • J n) =
    (a * c) • (1 : Matrix (Fin n) (Fin n) Real) +
      (a * e + b * c + b * e * (n : Real)) • J n := by
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.one_mul, Matrix.mul_one, J_sq]
  module

theorem sic_inverse_general (d : ℕ+) :
    sicDualReal d * sicGramReal d = 1 ∧
    sicGramReal d * sicDualReal d = 1 := by
  let D : Real := (d : Nat)
  let n : Nat := (d : Nat) ^ 2
  have hD : D ≠ 0 := by dsimp [D]; exact_mod_cast d.ne_zero
  have hD1 : D + 1 ≠ 0 := by positivity
  have hn : (n : Real) = D ^ 2 := by simp [n, D, Nat.cast_pow]
  have hD_eq : sicDualReal d =
      ((D + 1) / D) • (1 : Matrix (Fin n) (Fin n) Real) + (-1 / D ^ 2) • J n := by
    rw [sicDualReal_eq d]
  have hG_eq : sicGramReal d =
      (D / (D + 1)) • (1 : Matrix (Fin n) (Fin n) Real) + (1 / (D + 1)) • J n := rfl
  rw [hD_eq, hG_eq]
  have hdiag : ((D + 1) / D) * (D / (D + 1)) = 1 := by field_simp [hD, hD1]
  have hoff : ((D + 1) / D) * (1 / (D + 1)) + (-1 / D ^ 2) * (D / (D + 1))
      + (-1 / D ^ 2) * (1 / (D + 1)) * (n : Real) = 0 := by
    rw [hn]; field_simp [hD, hD1]; ring
  have hdiag' : (D / (D + 1)) * ((D + 1) / D) = 1 := by field_simp [hD, hD1]
  have hoff' : (D / (D + 1)) * (-1 / D ^ 2) + (1 / (D + 1)) * ((D + 1) / D)
      + (1 / (D + 1)) * (-1 / D ^ 2) * (n : Real) = 0 := by
    rw [hn]; field_simp [hD, hD1]; ring
  have hp1 := affine_product_real n ((D + 1) / D) (-1 / D ^ 2) (D / (D + 1)) (1 / (D + 1))
  have hp2 := affine_product_real n (D / (D + 1)) (1 / (D + 1)) ((D + 1) / D) (-1 / D ^ 2)
  constructor
  · rw [hp1, hdiag, hoff]; simp
  · rw [hp2, hdiag', hoff']; simp

theorem sic_reconstruction_trace {d : ℕ+} {K : Type*} [Fintype K]
    (hcard : Fintype.card K = (d : Nat) ^ 2)
    (p : K → Real) (hp : ∑ k, p k = 1)
    (proj : K → Matrix (Fin ((d : Nat) ^ 2)) (Fin ((d : Nat) ^ 2)) Real)
    (hproj : ∀ k, Matrix.trace (proj k) = 1) :
    Matrix.trace (∑ k, ((((d : Nat) : Real) + 1) * p k - 1 / (d : Nat)) • proj k) = 1 := by
  have hd : ((d : Nat) : Real) ≠ 0 := by exact_mod_cast d.ne_zero
  rw [Matrix.trace_sum]
  have hterm : ∀ k,
      Matrix.trace (((((d : Nat) : Real) + 1) * p k - 1 / (d : Nat)) • proj k)
        = (((d : Nat) : Real) + 1) * p k - 1 / (d : Nat) := by
    intro k
    rw [Matrix.trace_smul, hproj k, smul_eq_mul, mul_one]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hp, mul_one]
  rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  push_cast
  field_simp [hd]
  ring

theorem uniformMatrix_eq_map_J (n : Nat) :
    uniformMatrix n = (J n).map (algebraMap Real Complex) := by
  ext i j
  simp [uniformMatrix, J, Matrix.map_apply]

theorem sicGramGeneral_eq_map (d : ℕ+) :
    sicGramGeneral d = (sicGramReal d).map (algebraMap Real Complex) := by
  ext i j
  simp only [sicGramGeneral, sicGramReal, Matrix.add_apply, Matrix.smul_apply,
    Matrix.map_apply, uniformMatrix, J, Matrix.one_apply]
  push_cast
  by_cases h : i = j <;> simp [h] <;> ring

theorem sicDualGeneral_eq_map (d : ℕ+) :
    sicDualGeneral d = (sicDualReal d).map (algebraMap Real Complex) := by
  have hz := zeta_neg_one
  ext i j
  simp only [sicDualGeneral, sicDualReal, Matrix.add_apply, Matrix.smul_apply,
    Matrix.map_apply, uniformMatrix, J, Matrix.one_apply, hz]
  push_cast
  by_cases h : i = j <;> simp [h] <;> ring

theorem sic_inverse_general_via_real (d : ℕ+) :
    sicDualGeneral d * sicGramGeneral d = 1 ∧
    sicGramGeneral d * sicDualGeneral d = 1 := by
  obtain ⟨hleft, hright⟩ := sic_inverse_general d
  constructor
  · rw [sicDualGeneral_eq_map d, sicGramGeneral_eq_map d, ← Matrix.map_mul, hleft]
    ext i j
    simp only [Matrix.map_apply, Matrix.one_apply]
    by_cases h : i = j
    · simp [h, map_one]
    · simp [h, map_zero]
  · rw [sicDualGeneral_eq_map d, sicGramGeneral_eq_map d, ← Matrix.map_mul, hright]
    ext i j
    simp only [Matrix.map_apply, Matrix.one_apply]
    by_cases h : i = j
    · simp [h, map_one]
    · simp [h, map_zero]

end Imscribing.Paraconsistent.SICInverse