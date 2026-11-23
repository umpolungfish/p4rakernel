import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Imscribing.Millennium.TrineOperatorAlgebra

open Matrix

/-! ## Part 1: Tensor Carrier V = V_T ⊗ V_F ⊗ V_t ⊗ V_f (Fin 16) -/

/-- Basis state x : Fin 16 encodes (x_T, x_F, x_t, x_f) at bits 3, 2, 1, 0. -/
def bitT (x : Fin 16) : ℤ := ((x.val >>> 3) % 2 : ℕ)
def bitF (x : Fin 16) : ℤ := ((x.val >>> 2) % 2 : ℕ)
def bitt (x : Fin 16) : ℤ := ((x.val >>> 1) % 2 : ℕ)
def bitf (x : Fin 16) : ℤ := (x.val % 2 : ℕ)

def rank_i (x : Fin 16) : ℤ := bitT x + bitF x + bitt x + bitf x
def rank_t (x : Fin 16) : ℤ := bitT x + (1 - bitF x) + bitt x + (1 - bitf x)
def rank_c (x : Fin 16) : ℤ := bitT x + bitF x + (1 - bitt x) + (1 - bitf x)

def rankTriple (x : Fin 16) : ℤ × ℤ × ℤ := (rank_i x, rank_t x, rank_c x)

/-- Exactly two states share rank triple (2,2,2): |0110⟩ = 6 ({F,t}) and |1001⟩ = 9 ({T,f}).
    All other 14 states have unique rank triples. -/
theorem rankTriple_222_doublet :
    Finset.univ.filter (fun x : Fin 16 => rankTriple x = (2, 2, 2)) = {6, 9} := by
  decide

theorem rankTriple_other_singleton (x : Fin 16) (hx : rankTriple x ≠ (2, 2, 2)) :
    (Finset.univ.filter (fun y : Fin 16 => rankTriple y = rankTriple x)).card = 1 := by
  revert x hx
  decide

/-! ## Part 2: Directed Order Operators U_i, U_t, U_c (Kernel-Reducible, Zero Nat.bitwise) -/

def sigmaPlusAt (bit : Fin 16 → ℤ) (stride : ℕ) : Matrix (Fin 16) (Fin 16) ℤ :=
  fun y x => if bit x == 0 && y.val == x.val + stride then 1 else 0

def sigmaMinusAt (bit : Fin 16 → ℤ) (stride : ℕ) : Matrix (Fin 16) (Fin 16) ℤ :=
  fun y x => if bit x == 1 && x.val == y.val + stride then 1 else 0

def sigmaPlusT : Matrix (Fin 16) (Fin 16) ℤ := sigmaPlusAt bitT 8
def sigmaPlusF : Matrix (Fin 16) (Fin 16) ℤ := sigmaPlusAt bitF 4
def sigmaPlust : Matrix (Fin 16) (Fin 16) ℤ := sigmaPlusAt bitt 2
def sigmaPlusf : Matrix (Fin 16) (Fin 16) ℤ := sigmaPlusAt bitf 1

def sigmaMinusF : Matrix (Fin 16) (Fin 16) ℤ := sigmaMinusAt bitF 4
def sigmaMinust : Matrix (Fin 16) (Fin 16) ℤ := sigmaMinusAt bitt 2
def sigmaMinusf : Matrix (Fin 16) (Fin 16) ℤ := sigmaMinusAt bitf 1

def U_i : Matrix (Fin 16) (Fin 16) ℤ :=
  sigmaPlusT + sigmaPlusF + sigmaPlust + sigmaPlusf

def U_t : Matrix (Fin 16) (Fin 16) ℤ :=
  sigmaPlusT + sigmaMinusF + sigmaPlust + sigmaMinusf

def U_c : Matrix (Fin 16) (Fin 16) ℤ :=
  sigmaPlusT + sigmaPlusF + sigmaMinust + sigmaMinusf

def hsPairZ (A B : Matrix (Fin 16) (Fin 16) ℤ) : ℤ :=
  ∑ i : Fin 16, ∑ j : Fin 16, A i j * B i j

/-- Gram matrix G = 16 * (I_3 + J_3) on {U_i, U_t, U_c}. -/
theorem order_gram_matrix :
    hsPairZ U_i U_i = 32 ∧ hsPairZ U_t U_t = 32 ∧ hsPairZ U_c U_c = 32 ∧
    hsPairZ U_i U_t = 16 ∧ hsPairZ U_i U_c = 16 ∧ hsPairZ U_t U_c = 16 := by
  decide

/-- Scaled mean 3*Ū and scaled centered trine 3*Ũ_a = 3*U_a - 3*Ū (exact integer matrices). -/
def barU3 : Matrix (Fin 16) (Fin 16) ℤ := U_i + U_t + U_c
def tildeUi3 : Matrix (Fin 16) (Fin 16) ℤ := 3 • U_i - barU3
def tildeUt3 : Matrix (Fin 16) (Fin 16) ℤ := 3 • U_t - barU3
def tildeUc3 : Matrix (Fin 16) (Fin 16) ℤ := 3 • U_c - barU3

theorem centered_trine_sum_zero :
    ∀ i j : Fin 16, (tildeUi3 + tildeUt3 + tildeUc3) i j = 0 := by
  decide

/-- Centered trine inner products (scaled by 9):
    ‖Ũ_a‖² = 96/9 = 32/3 and ⟨Ũ_a, Ũ_b⟩ = -48/9 = -16/3 (cosine = -1/2). -/
theorem centered_trine_gram :
    hsPairZ tildeUi3 tildeUi3 = 96 ∧
    hsPairZ tildeUt3 tildeUt3 = 96 ∧
    hsPairZ tildeUc3 tildeUc3 = 96 ∧
    hsPairZ tildeUi3 tildeUt3 = -48 ∧
    hsPairZ tildeUi3 tildeUc3 = -48 ∧
    hsPairZ tildeUt3 tildeUc3 = -48 := by
  decide

/-! ## Part 3: Hadamard Inversion and Local 2×2 Exceptional-Point Triangle -/

def H4 : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1,  1,  1,  1;
     1, -1,  1, -1;
     1,  1, -1, -1;
     1, -1, -1,  1]

theorem hadamard_orthogonality : H4 * H4ᵀ = 4 • (1 : Matrix (Fin 4) (Fin 4) ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H4, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four] <;>
    norm_num

/-- Local 2×2 operator M(p, q) = [[0, q], [p, 0]] on a tensor factor.
    Its square is (p*q) • I_2: EP2 Jordan block whenever p*q = 0,
    real-split for p*q > 0, complex-conjugate monodromy for p*q < 0. -/
def localM {R : Type*} [CommRing R] (p q : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, q; p, 0]

theorem localM_sq {R : Type*} [CommRing R] (p q : R) :
    localM p q * localM p q = (p * q) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [localM, Matrix.mul_apply] <;> ring

theorem localM_ep2_jordan {R : Type*} [CommRing R] (p : R) :
    localM p 0 * localM p 0 = 0 ∧ localM 0 p * localM 0 p = 0 := by
  rw [localM_sq, localM_sq]
  simp

/-! ## Part 4: Induced Singlet-Doublet Jordan Block on gr_{(2,2,2)}(V) -/

/-- The (1,1,1)-homogeneous part of Ū is purely σ_T⁺ = sigmaPlusT. -/
def barU111 : Matrix (Fin 16) (Fin 16) ℤ := sigmaPlusT

/-- Projection onto the unique 2D graded sector gr_{(2,2,2)}(V) = span{|6⟩, |9⟩}. -/
def P222 : Matrix (Fin 16) (Fin 16) ℤ :=
  fun i j => if (i = 6 ∨ i = 9) ∧ i = j then 1 else 0

/-- Scaled graded singlet-doublet coupling 27 * Ω_{(0,0,0)} =
    P222 * (barU_{(1,1,1)} * 3Ũ_i * 3Ũ_t * 3Ũ_c) * P222. -/
def omegaRaw27 : Matrix (Fin 16) (Fin 16) ℤ :=
  barU111 * tildeUi3 * tildeUt3 * tildeUc3

def omegaEntry (i j : Fin 16) : ℤ :=
  ∑ a : Fin 16, ∑ b : Fin 16, ∑ c : Fin 16,
    barU111 i a * tildeUi3 a b * tildeUt3 b c * tildeUc3 c j

lemma omegaRaw27_eq_entry (i j : Fin 16) : omegaRaw27 i j = omegaEntry i j := by
  unfold omegaRaw27 omegaEntry
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

lemma p222_sandwich (M : Matrix (Fin 16) (Fin 16) ℤ) (i j : Fin 16) :
    (P222 * M * P222) i j =
      if (i = 6 ∨ i = 9) ∧ (j = 6 ∨ j = 9) then M i j else 0 := by
  rw [Matrix.mul_apply]
  have hright : ∀ k1 : Fin 16, k1 ≠ j → (P222 * M) i k1 * P222 k1 j = 0 := by
    intro k1 hk1
    simp [P222, hk1]
  rw [Finset.sum_eq_single j (fun k1 _ hk1 => hright k1 hk1)
    (fun hj => absurd (Finset.mem_univ j) hj)]
  rw [Matrix.mul_apply]
  have hleft : ∀ k2 : Fin 16, k2 ≠ i → P222 i k2 * M k2 j = 0 := by
    intro k2 hk2
    simp [P222, hk2.symm]
  rw [Finset.sum_eq_single i (fun k2 _ hk2 => hleft k2 hk2)
    (fun hi => absurd (Finset.mem_univ i) hi)]
  by_cases hi : i = 6 ∨ i = 9 <;> by_cases hj : j = 6 ∨ j = 9 <;> simp [P222, hi, hj]

/-- On gr_{(2,2,2)}(V) = span{|9⟩, |6⟩}, Ω_{(0,0,0)} has exact matrix
    [[0, 12/27], [0, 0]] = (4/9) * [[0, 1], [0, 0]], and vanishes everywhere else. -/
theorem omega_graded_jordan_block :
    omegaRaw27 9 6 = 12 ∧
    omegaRaw27 6 6 = 0 ∧
    omegaRaw27 6 9 = 0 ∧
    omegaRaw27 9 9 = 0 := by
  simp only [omegaRaw27_eq_entry]
  decide

theorem omega_jordan_nilpotent :
    (P222 * omegaRaw27 * P222) * (P222 * omegaRaw27 * P222) = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  have hblk := omega_graded_jordan_block
  have hsub : ∀ k : Fin 16,
      (P222 * omegaRaw27 * P222) i k * (P222 * omegaRaw27 * P222) k j = 0 := by
    intro k
    rw [p222_sandwich, p222_sandwich]
    by_cases hi : i = 6 ∨ i = 9 <;> by_cases hk : k = 6 ∨ k = 9 <;> by_cases hj : j = 6 ∨ j = 9
    · rcases hi with rfl | rfl <;> rcases hk with rfl | rfl <;> rcases hj with rfl | rfl <;>
        simp [hblk.1, hblk.2.1, hblk.2.2.1, hblk.2.2.2]
    all_goals simp [hi, hk, hj]
  simp [hsub]

end Imscribing.Millennium.TrineOperatorAlgebra