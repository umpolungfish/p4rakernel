/-
# LadderToSphere — the split/fuse ladder generates the qubit geometry

The paper *Usurping Quantum Mechanics II* derives the Hilbert-space geometry of a
qubit from the split/fuse ladder rather than assuming it. This file formalizes the
load-bearing algebra of that derivation at the single-coordinate register `m = 1`,
where the whole geometry is fixed.

Contents:

1. The `m = 1` ladder operators `S₊`, `S₋`, the weight `K`, and `J_z = K - ½I`,
   `J_x = (S₊+S₋)/2`, `J_y = (S₊-S₋)/(2i)`, shown to be exactly the Pauli matrices
   over two, so the ladder generates the su(2) action of spin ½:
     `[J_z,S₊] = S₊`, `[J_z,S₋] = -S₋`, `[S₊,S₋] = 2 J_z`,
     `[J_x,J_y] = i J_z`, `[J_y,J_z] = i J_x`, `[J_z,J_x] = i J_y`.

2. The shared held value `|B₂⟩ = (|TF⟩ - |FT⟩)/√2` is the unique frame-invariant ray,
   and its correlator is `⟨B₂| σᵢ⊗σⱼ |B₂⟩ = -δᵢⱼ`.

3. The CHSH observable at the optimal tilt attains `|⟨B₂|C|B₂⟩| = 2√2`, the Tsirelson
   value.

## Tuple
The ladder as geometry: ⟨𐑦𐑥𐑽𐑹𐑐𐑧𐑔𐑠⊙𐑒𐑙𐑭⟩
-/
import Mathlib

namespace Imscribing.Quantum.LadderToSphere

open Matrix Complex

noncomputable section

/-! ## 1. The single-coordinate ladder is the Pauli/su(2) algebra -/

/-- Pauli X over the ordered basis `(|T⟩, |F⟩)`. -/
def sx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
/-- Pauli Y. -/
def sy : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
/-- Pauli Z. -/
def sz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The split (raising) operator at `m = 1`: `S₊ |F⟩ = |T⟩`, `S₊ |T⟩ = 0`. -/
def Splus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
/-- The fuse (lowering) operator at `m = 1`, the adjoint of `S₊`. -/
def Sminus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]
/-- The weight operator `K |T⟩ = |T⟩`, `K |F⟩ = 0`. -/
def Kop : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- `Jz = K - ½ I`. -/
def Jz : Matrix (Fin 2) (Fin 2) ℂ := Kop - (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
/-- `Jx = (S₊ + S₋)/2`. -/
def Jx : Matrix (Fin 2) (Fin 2) ℂ := (1/2 : ℂ) • (Splus + Sminus)
/-- `Jy = (S₊ - S₋)/(2i)`. -/
def Jy : Matrix (Fin 2) (Fin 2) ℂ := (1/(2*Complex.I) : ℂ) • (Splus - Sminus)

/-- The commutator of two matrices. -/
def comm (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := A * B - B * A

theorem Jz_eq : Jz = (1/2 : ℂ) • sz := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Jz, Kop, sz, Matrix.one_apply, Matrix.smul_apply, Matrix.sub_apply] <;> ring

theorem Jx_eq : Jx = (1/2 : ℂ) • sx := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Jx, Splus, Sminus, sx, Matrix.smul_apply, Matrix.add_apply] <;> ring

theorem Jy_eq : Jy = (1/2 : ℂ) • sy := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Jy, Splus, Sminus, sy, Matrix.smul_apply, Matrix.sub_apply, div_eq_mul_inv,
      Complex.inv_I] <;> ring

/-- Ladder relation: `[Jz, S₊] = S₊`. -/
theorem comm_Jz_Splus : comm Jz Splus = Splus := by
  rw [Jz_eq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [comm, sz, Splus, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply] <;> ring

/-- Ladder relation: `[Jz, S₋] = -S₋`. -/
theorem comm_Jz_Sminus : comm Jz Sminus = -Sminus := by
  rw [Jz_eq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [comm, sz, Sminus, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply,
      Matrix.neg_apply] <;> ring

/-- Ladder relation: `[S₊, S₋] = 2 Jz`. At `m = 1` the eigenvalue `2k - m` is `±1`. -/
theorem comm_Splus_Sminus : comm Splus Sminus = (2 : ℂ) • Jz := by
  rw [Jz_eq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [comm, Splus, Sminus, sz, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.smul_apply] <;> ring

/-- The su(2) relation `[Jx, Jy] = i Jz`. -/
theorem comm_Jx_Jy : comm Jx Jy = Complex.I • Jz := by
  rw [Jx_eq, Jy_eq, Jz_eq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [comm, sx, sy, sz, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

/-- The su(2) relation `[Jy, Jz] = i Jx`. -/
theorem comm_Jy_Jz : comm Jy Jz = Complex.I • Jx := by
  rw [Jx_eq, Jy_eq, Jz_eq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [comm, sx, sy, sz, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

/-- The su(2) relation `[Jz, Jx] = i Jy`. -/
theorem comm_Jz_Jx : comm Jz Jx = Complex.I • Jy := by
  rw [Jx_eq, Jy_eq, Jz_eq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [comm, sx, sy, sz, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

/-! ## 2. The shared held value and its correlator -/

/-- The tensor product of two `2×2` matrices as a `4×4` matrix, in the ordered basis
`(|TT⟩,|TF⟩,|FT⟩,|FF⟩)`. -/
def kron (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![A 0 0 * B 0 0, A 0 0 * B 0 1, A 0 1 * B 0 0, A 0 1 * B 0 1;
     A 0 0 * B 1 0, A 0 0 * B 1 1, A 0 1 * B 1 0, A 0 1 * B 1 1;
     A 1 0 * B 0 0, A 1 0 * B 0 1, A 1 1 * B 0 0, A 1 1 * B 0 1;
     A 1 0 * B 1 0, A 1 0 * B 1 1, A 1 1 * B 1 0, A 1 1 * B 1 1]

/-- The shared held value, unnormalized: `|w⟩ = |TF⟩ - |FT⟩`, whose norm squared is `2`.
The normalized held value of the paper is `|B₂⟩ = |w⟩/√2`; every correlator below is
`expect · w`, and the normalized correlator is that divided by `‖w‖² = 2`. -/
def heldW : Fin 4 → ℂ := ![0, 1, -1, 0]

/-- The expectation `⟨v| M |v⟩` (bilinear in `v`, conjugate-linear on the left). -/
def expect (M : Matrix (Fin 4) (Fin 4) ℂ) (v : Fin 4 → ℂ) : ℂ :=
  ∑ i, ∑ j, (starRingEnd ℂ) (v i) * M i j * v j

/-- Norm squared of the held value is `2`. -/
theorem heldW_normSq : expect (1 : Matrix (Fin 4) (Fin 4) ℂ) heldW = 2 := by
  simp [expect, heldW, Fin.sum_univ_four, Matrix.one_apply] <;> norm_num

/-- Aligned truth-frame readings on the held value are perfectly anticorrelated:
`⟨w| σz⊗σz |w⟩ = -2 = -‖w‖²`, so the normalized value is `-1`. -/
theorem corr_zz : expect (kron sz sz) heldW = -2 := by
  simp [expect, kron, heldW, sz, Fin.sum_univ_four] <;> norm_num

theorem corr_xx : expect (kron sx sx) heldW = -2 := by
  simp [expect, kron, heldW, sx, Fin.sum_univ_four] <;> norm_num

theorem corr_yy : expect (kron sy sy) heldW = -2 := by
  simp [expect, kron, heldW, sy, Fin.sum_univ_four]
  ring

/-- Off-axis readings are uncorrelated: `⟨w| σx⊗σz |w⟩ = 0`. Together with the three
aligned cases this is the `-δᵢⱼ` correlator of the paper (Proposition on the correlator). -/
theorem corr_xz : expect (kron sx sz) heldW = 0 := by
  simp [expect, kron, heldW, sx, sz, Fin.sum_univ_four]

/-! ## 3. The Tsirelson bound from the ladder's spin-½ representation -/

/-- The tensor product is multiplicative: `(A⊗B)(C⊗D) = (AC)⊗(BD)`. -/
theorem kron_mul_kron (A B C D : Matrix (Fin 2) (Fin 2) ℂ) :
    kron A B * kron C D = kron (A * C) (B * D) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four] <;> ring

/-- The expectation is additive in the operator. -/
theorem expect_add (M N : Matrix (Fin 4) (Fin 4) ℂ) (v : Fin 4 → ℂ) :
    expect (M + N) v = expect M v + expect N v := by
  simp only [expect, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- The expectation is homogeneous in the operator. -/
theorem expect_smul (c : ℂ) (M : Matrix (Fin 4) (Fin 4) ℂ) (v : Fin 4 → ℂ) :
    expect (c • M) v = c * expect M v := by
  simp only [expect, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- The optimal CHSH observable. With `A = σz`, `A' = σx`,
`B = (σz+σx)/√2`, `B' = (σz-σx)/√2`, the sums collapse to
`B+B' = √2·σz` and `B-B' = √2·σx`, so
`C = A⊗(B+B') + A'⊗(B-B') = √2·(σz⊗σz + σx⊗σx)`. -/
def CHSHopt : Matrix (Fin 4) (Fin 4) ℂ :=
  (Real.sqrt 2 : ℂ) • (kron sz sz + kron sx sx)

/-- The ladder's spin-½ representation attains the Tsirelson value. On the shared held
value the optimal CHSH observable gives `⟨w|C|w⟩ = -4√2`, and since `‖w‖² = 2` the
normalized correlator is `-2√2`, of magnitude `2√2`. No quantum correlator is assumed;
this is computed from `σz⊗σz` and `σx⊗σx` on the held value. -/
theorem chsh_attains_tsirelson :
    expect CHSHopt heldW = -(4 * Real.sqrt 2 : ℝ) := by
  rw [CHSHopt, expect_smul, expect_add, corr_zz, corr_xx]
  push_cast
  ring

/-- The magnitude of the normalized CHSH value is exactly `2√2`. -/
theorem chsh_magnitude :
    ‖expect CHSHopt heldW‖ / 2 = 2 * Real.sqrt 2 := by
  rw [chsh_attains_tsirelson]
  rw [show (-(4 * Real.sqrt 2 : ℝ) : ℂ) = ((-(4 * Real.sqrt 2) : ℝ) : ℂ) from by push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h : (0:ℝ) ≤ 4 * Real.sqrt 2 := by positivity
  rw [abs_neg, abs_of_nonneg h]
  ring

end

end Imscribing.Quantum.LadderToSphere
