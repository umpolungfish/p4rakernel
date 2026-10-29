import Imscribing.Millennium.SourceBraidSquareCollision

/-! Full joint SIC contraction, with all source-correlated labels retained.
No marginalization or probabilistic branch selection occurs in these maps. -/
namespace Imscribing.SourceBraidSICContraction

open Imscribing.Millennium.ZetaSICDualFrame

abbrev JointLabel (k : ℕ) := Fin k → Fin 16

noncomputable def joint (k : ℕ) (A : Matrix (Fin 16) (Fin 16) ℂ) :
    Matrix (JointLabel k) (JointLabel k) ℂ :=
  fun i j => ∏ n : Fin k, A (i n) (j n)

theorem joint_mul (k : ℕ) (A B : Matrix (Fin 16) (Fin 16) ℂ) :
    joint k (A*B) = joint k A * joint k B := by
  classical
  ext i j
  simp only [joint, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

theorem joint_one (k : ℕ) : joint k (1 : Matrix (Fin 16) (Fin 16) ℂ) = 1 := by
  classical
  ext i j
  simp only [joint, Matrix.one_apply]
  by_cases h : i = j
  · subst j
    simp
  · rw [if_neg h]
    have hex : ∃ n, i n ≠ j n := by
      by_contra hn
      push_neg at hn
      exact h (funext hn)
    obtain ⟨n, hn⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ n)
    simp [hn]

noncomputable def jointGram (k : ℕ) := joint k ququartGram
noncomputable def jointDual (k : ℕ) := joint k ququartDualGram

theorem joint_dual_left_inverse (k : ℕ) : jointDual k * jointGram k = 1 := by
  rw [jointDual, jointGram, ← joint_mul, ququart_dual_left_inverse, joint_one]

theorem joint_dual_right_inverse (k : ℕ) : jointGram k * jointDual k = 1 := by
  rw [jointDual, jointGram, ← joint_mul, ququart_dual_right_inverse, joint_one]

theorem joint_coordinate_return (k : ℕ) (c : JointLabel k → ℂ) :
    (jointDual k).mulVec ((jointGram k).mulVec c) = c := by
  rw [Matrix.mulVec_mulVec, joint_dual_left_inverse, Matrix.one_mulVec]

theorem ququart_kernel (i j : Fin 16) :
    ququartDualGram i j = (if i=j then (5/4 : ℂ) else 0) - 1/16 := by
  simp only [ququartDualGram, zeta_neg_one, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, uniformMatrix]
  split_ifs <;> norm_num

theorem joint_kernel (k : ℕ) (i j : JointLabel k) :
    jointDual k i j =
      ∏ n : Fin k, ((if i n=j n then (5/4 : ℂ) else 0) - 1/16) := by
  simp only [jointDual, joint, ququart_kernel]

/-- The contraction is bilinear trace pairing, not a probability expectation. -/
theorem quadratic_return (k : ℕ) (c : JointLabel k → ℂ) :
    dotProduct ((jointGram k).mulVec c)
      ((jointDual k).mulVec ((jointGram k).mulVec c)) =
    dotProduct c ((jointGram k).mulVec c) := by
  rw [joint_coordinate_return]
  exact dotProduct_comm _ _

theorem mass_quadratic_kernel (k : ℕ) (m : JointLabel k → ℂ) :
    (∑ i : JointLabel k, ∑ j : JointLabel k,
      m i * m j * ∏ n : Fin k,
        ((if i n=j n then (5/4 : ℂ) else 0) - 1/16)) =
      dotProduct m ((jointDual k).mulVec m) := by
  simp only [dotProduct, Matrix.mulVec, dotProduct, Finset.mul_sum, joint_kernel]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadratic_kernel (k : ℕ) (c : JointLabel k → ℂ) :
    let m := (jointGram k).mulVec c
    (∑ i : JointLabel k, ∑ j : JointLabel k,
      m i * m j * ∏ n : Fin k,
        ((if i n=j n then (5/4 : ℂ) else 0) - 1/16)) =
      dotProduct c ((jointGram k).mulVec c) := by
  exact (mass_quadratic_kernel k ((jointGram k).mulVec c)).trans (quadratic_return k c)

#print axioms joint_coordinate_return
#print axioms quadratic_kernel

end Imscribing.SourceBraidSICContraction
