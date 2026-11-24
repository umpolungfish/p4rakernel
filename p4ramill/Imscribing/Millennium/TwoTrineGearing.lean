import Imscribing.Millennium.FamilyWeylFrobenius

namespace Imscribing.Millennium.TwoTrineGearing

open Imscribing.Millennium.FamilyWeylFrobenius

/-! ## Part 1: Inner Evaluator Bloch Trine in M₂(E3) -/

/-- Scaled evaluator Bloch operators 2·B_j in E3 = Zsqrtd (-3):
    BH2 = 2σₓ, BT2 = -σₓ + √3 σ_y, BF2 = -σₓ - √3 σ_y. -/
def BH2 : Matrix (Fin 2) (Fin 2) E3 := !![0, 2; 2, 0]
def BT2 : Matrix (Fin 2) (Fin 2) E3 := !![0, w2b; w2, 0]
def BF2 : Matrix (Fin 2) (Fin 2) E3 := !![0, w2; w2b, 0]

def sigmaZ2 : Matrix (Fin 2) (Fin 2) E3 := !![2, 0; 0, -2]

theorem inner_trine_identities :
    BH2 + BT2 + BF2 = 0 ∧
    BH2 * BH2 = (4 : E3) • 1 ∧
    BT2 * BT2 = (4 : E3) • 1 ∧
    BF2 * BF2 = (4 : E3) • 1 ∧
    BH2 * BT2 + BT2 * BH2 = (-4 : E3) • 1 ∧
    BT2 * BF2 + BF2 * BT2 = (-4 : E3) • 1 ∧
    BF2 * BH2 + BH2 * BF2 = (-4 : E3) • 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

theorem inner_trine_d3_group :
    BH2 * BT2 = BT2 * BF2 ∧
    BT2 * BF2 = BF2 * BH2 ∧
    (BH2 * BT2) ^ 3 = (64 : E3) • 1 ∧
    BH2 * (BH2 * BT2) * BH2 = (4 : E3) • (BT2 * BH2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-- The evaluator trine generates the full su(2) Pauli frame:
    [2σₓ, 2√3 σ_y] = 4√(-3) · (2σ_z), etc. -/
theorem inner_trine_generates_su2 :
    BH2 * (BT2 - BF2) - (BT2 - BF2) * BH2 = ((4 : E3) * sRoot) • sigmaZ2 ∧
    (BT2 - BF2) * sigmaZ2 - sigmaZ2 * (BT2 - BF2) = ((4 : E3) * sRoot) • BH2 ∧
    (3 : E3) • (sigmaZ2 * BH2 - BH2 * sigmaZ2) = (4 : E3) • (sRoot • (BT2 - BF2)) := by
  refine ⟨?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-! ## Part 2: Sixfold Spinor Lift and Negation Reflection -/

/-- Scaled spinor rotation UB2 = 2 · exp(-iπ/3 · σ_z) = diag(1 - √(-3), 1 + √(-3)). -/
def UB2 : Matrix (Fin 2) (Fin 2) E3 := !![1 - sRoot, 0; 0, 1 + sRoot]
def UB2_conj : Matrix (Fin 2) (Fin 2) E3 := !![1 + sRoot, 0; 0, 1 - sRoot]
def sigmaX1 {α : Type*} [Zero α] [One α] : Matrix (Fin 2) (Fin 2) α := !![0, 1; 1, 0]

theorem spinor_sixfold_lift :
    UB2 * UB2_conj = (4 : E3) • 1 ∧
    UB2 ^ 3 = (-8 : E3) • 1 ∧
    UB2 ^ 6 = (64 : E3) • 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-- Adjoint action of UB2 cycles HOLD PARADOX → EVALUATE TRUE → EVALUATE FALSE → HOLD PARADOX. -/
theorem spinor_cycles_evaluator_trine :
    UB2 * BH2 * UB2_conj = (4 : E3) • BT2 ∧
    UB2 * BT2 * UB2_conj = (4 : E3) • BF2 ∧
    UB2 * BF2 * UB2_conj = (4 : E3) • BH2 := by
  refine ⟨?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-- Negation reflection fixes HOLD PARADOX, swaps TRUE ↔ FALSE, and inverts UB2. -/
theorem spinor_reflection_fixes_paradox :
    (sigmaX1 : Matrix (Fin 2) (Fin 2) E3) * BH2 * sigmaX1 = BH2 ∧
    (sigmaX1 : Matrix (Fin 2) (Fin 2) E3) * BT2 * sigmaX1 = BF2 ∧
    (sigmaX1 : Matrix (Fin 2) (Fin 2) E3) * BF2 * sigmaX1 = BT2 ∧
    (sigmaX1 : Matrix (Fin 2) (Fin 2) E3) * UB2 * sigmaX1 = UB2_conj := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-! ## Part 3: 3D Major–Bloch Gearing Map G_int and Trace Fork (§§127–128) -/

/-- Unnormalized integer 3D gearing map:
    row 0 = (2, -1, -1) (norm² = 6), row 1 = (0, 1, -1) (norm² = 2), row 2 = (1, 1, 1) (norm² = 3). -/
def G_int : Matrix (Fin 3) (Fin 3) ℤ :=
  !![2, -1, -1;
     0,  1, -1;
     1,  1,  1]

def R_B_int : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-1, -3, 0;
      1, -1, 0;
      0,  0, 2]

def S_B_K : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 0, -1, 0; 0, 0, 1]
def S_B_U : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 0, -1, 0; 0, 0, -1]

theorem major_bloch_gearing_intertwiner :
    G_int * G_int.transpose = !![6, 0, 0; 0, 2, 0; 0, 0, 3] ∧
    (2 : ℤ) • (G_int * (R : Matrix (Fin 3) (Fin 3) ℤ)) = R_B_int * G_int ∧
    G_int * (S : Matrix (Fin 3) (Fin 3) ℤ) = S_B_K * G_int := by
  refine ⟨?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-- Trace fork (§128): major S_M has trace +1, matching antiunitary conjugation S_B^(K) (+1),
    whereas unitary σ_x conjugation S_B^(U) has trace -1. -/
theorem reflection_trace_fork :
    Matrix.trace (S : Matrix (Fin 3) (Fin 3) ℤ) = 1 ∧
    Matrix.trace S_B_K = 1 ∧
    Matrix.trace S_B_U = -1 ∧
    Matrix.trace S_B_K ≠ Matrix.trace S_B_U := by
  decide

/-! ## Part 4: Coupled 5D Gear on V = V₃ ⊕ V₂ and Hypercharge Compatibility (§114) -/

def blockDiag5 {α : Type*} [Zero α]
    (A : Matrix (Fin 3) (Fin 3) α) (B : Matrix (Fin 2) (Fin 2) α) :
    Matrix (Fin 5) (Fin 5) α := fun i j =>
  if hi : i.val < 3 then
    if hj : j.val < 3 then A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
  else
    if hj : j.val < 3 then 0 else B ⟨i.val - 3, by omega⟩ ⟨j.val - 3, by omega⟩

theorem blockDiag5_mul {α : Type*} [CommRing α]
    (A C : Matrix (Fin 3) (Fin 3) α) (B D : Matrix (Fin 2) (Fin 2) α) :
    blockDiag5 A B * blockDiag5 C D = blockDiag5 (A * C) (B * D) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [blockDiag5, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_three, Fin.sum_univ_two]

def R_hat2 : Matrix (Fin 5) (Fin 5) E3 := blockDiag5 ((2 : E3) • R) UB2
def S_hat : Matrix (Fin 5) (Fin 5) E3 := blockDiag5 S sigmaX1
def S_hat_Z : Matrix (Fin 5) (Fin 5) ℤ := blockDiag5 S sigmaX1
def Y6_5 : Matrix (Fin 5) (Fin 5) E3 := blockDiag5 ((-2 : E3) • 1) ((3 : E3) • 1)

private lemma r_hat2_cube :
    R_hat2 ^ 3 = blockDiag5 ((8 : E3) • 1) ((-8 : E3) • 1) := by
  have hR : ((2 : E3) • (R : Matrix (Fin 3) (Fin 3) E3)) ^ 3 = (8 : E3) • 1 := by
    apply Matrix.ext; intro i j; revert i j; decide
  have hU : UB2 ^ 3 = (-8 : E3) • 1 := spinor_sixfold_lift.2.1
  rw [R_hat2, pow_three, blockDiag5_mul, blockDiag5_mul, ← pow_three, ← pow_three, hR, hU]

theorem coupled_5d_gear_relations :
    R_hat2 ^ 3 = blockDiag5 ((8 : E3) • 1) ((-8 : E3) • 1) ∧
    R_hat2 ^ 6 = (64 : E3) • 1 ∧
    S_hat ^ 2 = 1 ∧
    S_hat * R_hat2 * S_hat * R_hat2 = (4 : E3) • 1 := by
  refine ⟨r_hat2_cube, ?_, ?_, ?_⟩
  · have h33 : ((8 : E3) • (1 : Matrix (Fin 3) (Fin 3) E3)) * ((8 : E3) • 1) = (64 : E3) • 1 := by
      apply Matrix.ext; intro i j; revert i j; decide
    have h22 : ((-8 : E3) • (1 : Matrix (Fin 2) (Fin 2) E3)) * ((-8 : E3) • 1) = (64 : E3) • 1 := by
      apply Matrix.ext; intro i j; revert i j; decide
    have hs : blockDiag5 ((64 : E3) • (1 : Matrix (Fin 3) (Fin 3) E3))
        ((64 : E3) • (1 : Matrix (Fin 2) (Fin 2) E3)) =
        (64 : E3) • (1 : Matrix (Fin 5) (Fin 5) E3) := by
      apply Matrix.ext; intro i j; revert i j; decide
    rw [show (6 : ℕ) = 3 + 3 from rfl, pow_add, r_hat2_cube, blockDiag5_mul, h33, h22, hs]
  · have hS3 : (S : Matrix (Fin 3) (Fin 3) E3) * S = 1 := by
      apply Matrix.ext; intro i j; revert i j; decide
    have hS2 : (sigmaX1 : Matrix (Fin 2) (Fin 2) E3) * sigmaX1 = 1 := by
      apply Matrix.ext; intro i j; revert i j; decide
    have h1 : blockDiag5 (1 : Matrix (Fin 3) (Fin 3) E3) (1 : Matrix (Fin 2) (Fin 2) E3) = 1 := by
      apply Matrix.ext; intro i j; revert i j; decide
    rw [S_hat, pow_two, blockDiag5_mul, hS3, hS2, h1]
  · have h3 : (S : Matrix (Fin 3) (Fin 3) E3) * ((2 : E3) • R) * S * ((2 : E3) • R) = (4 : E3) • 1 := by
      apply Matrix.ext; intro i j; revert i j; decide
    have h2 : (sigmaX1 : Matrix (Fin 2) (Fin 2) E3) * UB2 * sigmaX1 * UB2 = (4 : E3) • 1 := by
      apply Matrix.ext; intro i j; revert i j; decide
    have h4 : blockDiag5 ((4 : E3) • (1 : Matrix (Fin 3) (Fin 3) E3))
        ((4 : E3) • (1 : Matrix (Fin 2) (Fin 2) E3)) =
        (4 : E3) • (1 : Matrix (Fin 5) (Fin 5) E3) := by
      apply Matrix.ext; intro i j; revert i j; decide
    rw [S_hat, R_hat2, blockDiag5_mul, blockDiag5_mul, blockDiag5_mul, h3, h2, h4]

private lemma det_S_hat_Z_eq_one : Matrix.det S_hat_Z = 1 := by
  let S4 : Matrix (Fin 4) (Fin 4) ℤ := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  let S3 : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 0, 0, 1; 0, 1, 0]
  let S2 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]
  have h5r : S_hat_Z 0 0 = 1 ∧ S_hat_Z 0 1 = 0 ∧ S_hat_Z 0 2 = 0 ∧
      S_hat_Z 0 3 = 0 ∧ S_hat_Z 0 4 = 0 := by decide
  have h5sub : S_hat_Z.submatrix Fin.succ (0 : Fin 5).succAbove = S4 := by
    apply Matrix.ext; intro i j; revert i j; decide
  have h4r : S4 0 0 = 0 ∧ S4 0 1 = 1 ∧ S4 0 2 = 0 ∧ S4 0 3 = 0 := by decide
  have h4sub : S4.submatrix Fin.succ (1 : Fin 4).succAbove = S3 := by
    apply Matrix.ext; intro i j; revert i j; decide
  have h3r : S3 0 0 = 1 ∧ S3 0 1 = 0 ∧ S3 0 2 = 0 := by decide
  have h3sub : S3.submatrix Fin.succ (0 : Fin 3).succAbove = S2 := by
    apply Matrix.ext; intro i j; revert i j; decide
  have h2det : Matrix.det S2 = -1 := by
    rw [Matrix.det_fin_two]; decide
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_five,
      h5r.1, h5r.2.1, h5r.2.2.1, h5r.2.2.2.1, h5r.2.2.2.2, h5sub]
  simp only [Fin.val_zero, pow_zero, one_mul, mul_zero, zero_mul, add_zero]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four,
      h4r.1, h4r.2.1, h4r.2.2.1, h4r.2.2.2, h4sub]
  simp only [Fin.val_one, pow_one, mul_one, mul_zero, zero_mul, zero_add, add_zero]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_three,
      h3r.1, h3r.2.1, h3r.2.2, h3sub]
  simp only [Fin.val_zero, pow_zero, one_mul, mul_zero, zero_mul, add_zero]
  rw [h2det]
  norm_num

/-- Coupled gear preserves the 3+2 traceless hypercharge Y₆ and lies in SL(5) (det S_hat = +1). -/
theorem coupled_5d_gear_compatible_with_hypercharge :
    Matrix.trace Y6_5 = 0 ∧
    Y6_5 * R_hat2 = R_hat2 * Y6_5 ∧
    Y6_5 * S_hat = S_hat * Y6_5 ∧
    Matrix.det S_hat_Z = 1 := by
  refine ⟨?_, ?_, ?_, det_S_hat_Z_eq_one⟩
  · decide
  · rw [Y6_5, R_hat2, blockDiag5_mul, blockDiag5_mul]
    congr 1 <;> (apply Matrix.ext; intro i j; revert i j; decide)
  · rw [Y6_5, S_hat, blockDiag5_mul, blockDiag5_mul]
    congr 1 <;> (apply Matrix.ext; intro i j; revert i j; decide)

end Imscribing.Millennium.TwoTrineGearing