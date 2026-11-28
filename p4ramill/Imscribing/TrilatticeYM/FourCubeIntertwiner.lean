import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Imscribing.TrilatticeYM



open Matrix

def G6 : Matrix (Fin 5) (Fin 5) ℚ :=
  !![ 8, -4, -4,  2, -4;
     -4,  8,  2, -4,  2;
     -4,  2,  8, -4,  2;
      2, -4, -4,  8, -4;
     -4,  2,  2, -4,  8]

def G6Inv : Matrix (Fin 5) (Fin 5) ℚ :=
  !![ 1/3,  1/6,  1/6, 1/6,  1/6;
      1/6,  1/4, 1/12, 1/6, 1/12;
      1/6, 1/12,  1/4, 1/6, 1/12;
      1/6,  1/6,  1/6, 1/3,  1/6;
      1/6, 1/12, 1/12, 1/6,  1/4]

theorem G6_mul_inv : G6 * G6Inv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [G6, G6Inv, Matrix.mul_apply, Fin.sum_univ_five] <;> norm_num

theorem G6_inv_mul : G6Inv * G6 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [G6, G6Inv, Matrix.mul_apply, Fin.sum_univ_five] <;> norm_num

theorem G6_trace : G6.trace = 40 := by
  simp [G6, Matrix.trace, Fin.sum_univ_five]; norm_num

def G6_L : Matrix (Fin 5) (Fin 5) ℚ :=
  !![    1,    0,    0,    0, 0;
      -1/2,    1,    0,    0, 0;
      -1/2,    0,    1,    0, 0;
       1/4, -1/2, -1/2,    1, 0;
      -1/2,    0,    0, -2/3, 1]

def G6_D : Fin 5 → ℚ
  | 0 => 8 | 1 => 6 | 2 => 6 | 3 => 9 / 2 | 4 => 4

theorem G6_LDL : G6 = G6_L * Matrix.diagonal G6_D * G6_Lᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [G6, G6_L, G6_D, Matrix.mul_apply, Matrix.diagonal, Matrix.transpose,
          Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_five] <;> norm_num

theorem G6_det : G6.det = 5184 := by
  rw [G6_LDL, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hL : G6_L.det = 1 := by
    have htri : ∀ i j : Fin 5, i < j → G6_L i j = 0 := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp only [Fin.lt_def, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue] at hij <;>
        first | omega | (simp [G6_L])
    rw [Matrix.det_of_lowerTriangular G6_L htri]
    simp [G6_L, Fin.prod_univ_five]
  have hD : (Matrix.diagonal G6_D).det = 5184 := by
    rw [Matrix.det_diagonal]
    simp [G6_D, Fin.prod_univ_five]
    norm_num
  rw [hL, hD]
  norm_num

def R12 : Matrix (Fin 5) (Fin 5) ℚ :=
  !![-1,  0, 1, 0, 1;
      0, -1, 0, 1, 0;
      0,  0, 1, 0, 0;
      0,  0, 0, 1, 0;
      0,  0, 0, 0, 1]

def R23 : Matrix (Fin 5) (Fin 5) ℚ :=
  !![ 1, 0,  0,  0, 0;
      0, 1,  0,  0, 0;
      1, 0, -1,  0, 0;
      0, 1,  0, -1, 1;
      0, 0,  0,  0, 1]

theorem R12_R23_relations :
    R12 * R12 = 1 ∧ R23 * R23 = 1 ∧
    R12 * R23 * R12 = R23 * R12 * R23 ∧
    R12ᵀ * G6 * R12 = G6 ∧ R23ᵀ * G6 * R23 = G6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [R12, R23, G6, Matrix.mul_apply, Fin.sum_univ_five] <;> norm_num)

def P_triv : Matrix (Fin 5) (Fin 5) ℚ :=
  !![1,   0,   0,   0, 0;
     0, 1/3, 1/3, 1/3, 0;
     0, 1/3, 1/3, 1/3, 0;
     0, 1/3, 1/3, 1/3, 0;
     0,   0,   0,   0, 0]

def P_std : Matrix (Fin 5) (Fin 5) ℚ :=
  !![0,    0,    0,    0, 0;
     0,  2/3, -1/3, -1/3, 0;
     0, -1/3,  2/3, -1/3, 0;
     0, -1/3, -1/3,  2/3, 0;
     0,    0,    0,    0, 0]

def P_sign : Matrix (Fin 5) (Fin 5) ℚ :=
  !![0, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 0, 0, 0, 1]

theorem S3_projectors_complete :
    P_triv + P_std + P_sign = 1 ∧
    P_triv * P_triv = P_triv ∧
    P_std * P_std = P_std ∧
    P_sign * P_sign = P_sign ∧
    P_triv * P_std = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [P_triv, P_std, P_sign, Matrix.mul_apply, Fin.sum_univ_five] <;> norm_num)

noncomputable def uChannel : Fin 5 → ℝ
  | 0 => Real.sqrt 3 / Real.sqrt 6
  | 1 => -1 / Real.sqrt 6
  | 2 => -1 / Real.sqrt 6
  | 3 => -1 / Real.sqrt 6
  | 4 => 0

noncomputable def T32 : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => uChannel i * uChannel j

noncomputable def Tlocal : Matrix (Fin 5) (Fin 5) ℝ :=
  1 - (3 / 4 : ℝ) • T32

theorem uChannel_norm_one : ∑ i : Fin 5, uChannel i * uChannel i = 1 := by
  rw [Fin.sum_univ_five]
  simp [uChannel]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h6 : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
  calc (Real.sqrt 3 / Real.sqrt 6) * (Real.sqrt 3 / Real.sqrt 6) +
        (-1 / Real.sqrt 6) * (-1 / Real.sqrt 6) +
        (-1 / Real.sqrt 6) * (-1 / Real.sqrt 6) +
        (-1 / Real.sqrt 6) * (-1 / Real.sqrt 6)
      = (Real.sqrt 3 * Real.sqrt 3 + 3) / (Real.sqrt 6 * Real.sqrt 6) := by ring
    _ = (3 + 3) / 6 := by rw [h3, h6]
    _ = 1 := by norm_num

theorem T32_idem : T32 * T32 = T32 := by
  ext i j
  simp only [T32, Matrix.mul_apply]
  calc ∑ k : Fin 5, uChannel i * uChannel k * (uChannel k * uChannel j)
      = uChannel i * uChannel j * ∑ k : Fin 5, uChannel k * uChannel k := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by ring
    _ = uChannel i * uChannel j := by rw [uChannel_norm_one, mul_one]

theorem Tlocal_spectrum_action :
    Tlocal *ᵥ uChannel = (1 / 4 : ℝ) • uChannel ∧
    ∀ w : Fin 5 → ℝ, (∑ i : Fin 5, uChannel i * w i = 0) → Tlocal *ᵥ w = w := by
  constructor
  · rw [Tlocal, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    ext i
    simp only [T32, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    have hsum : ∑ j : Fin 5, uChannel i * uChannel j * uChannel j = uChannel i := by
      calc ∑ j : Fin 5, uChannel i * uChannel j * uChannel j
          = uChannel i * ∑ j : Fin 5, uChannel j * uChannel j := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
        _ = uChannel i := by rw [uChannel_norm_one, mul_one]
    rw [hsum]; ring
  · intro w hw
    rw [Tlocal, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    ext i
    simp only [T32, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    have hsum : ∑ j : Fin 5, uChannel i * uChannel j * w j = 0 := by
      calc ∑ j : Fin 5, uChannel i * uChannel j * w j
          = uChannel i * ∑ j : Fin 5, uChannel j * w j := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hw, mul_zero]
    rw [hsum]; ring

@[inline] def vBit (x : Fin 16) (k : Fin 4) : ℕ := (x.val / 2 ^ k.val) % 2

abbrev CubeEdge := { e : Fin 4 × Fin 16 // vBit e.2 e.1 = 0 }

def planeDirs : Fin 6 → Fin 4 × Fin 4
  | 0 => (0, 1) | 1 => (0, 2) | 2 => (0, 3)
  | 3 => (1, 2) | 4 => (1, 3) | 5 => (2, 3)

def remDirs : Fin 6 → Fin 4 × Fin 4
  | 0 => (2, 3) | 1 => (1, 3) | 2 => (1, 2)
  | 3 => (0, 3) | 4 => (0, 2) | 5 => (0, 1)

abbrev CubeFace := Fin 6 × Fin 4

theorem card_cube_edges_faces :
    Fintype.card CubeEdge = 32 ∧ Fintype.card CubeFace = 24 := by
  constructor
  · first | decide | norm_num | ring
  · first | decide | norm_num | ring

def faceBase (p : Fin 6) (t : Fin 4) : ℕ :=
  let (ρ, σ) := remDirs p
  (t.val % 2) * 2 ^ ρ.val + (t.val / 2) * 2 ^ σ.val

def edgeInFace (e : CubeEdge) (f : CubeFace) : Bool :=
  let (μ, ν) := planeDirs f.1
  let y := faceBase f.1 f.2
  (e.1.1 == μ && (e.1.2.val == y || e.1.2.val == y + 2 ^ ν.val)) ||
  (e.1.1 == ν && (e.1.2.val == y || e.1.2.val == y + 2 ^ μ.val))

def kerVec1 (p : Fin 6) : ℤ :=
  match p.val with
  | 0 => 0 | 1 => 1 | 2 => -1 | 3 => -1 | 4 => 1 | 5 => 0 | _ => 0

def kerVec2 (p : Fin 6) : ℤ :=
  match p.val with
  | 0 => 1 | 1 => 0 | 2 => -1 | 3 => -1 | 4 => 0 | 5 => 1 | _ => 0

theorem incidence_ker_exact :
    (∀ e : CubeEdge, (∑ f : CubeFace, if edgeInFace e f then (1 : ℤ) else 0) = 3) ∧
    (∀ e : CubeEdge, (∑ f : CubeFace, if edgeInFace e f then kerVec1 f.1 else 0) = 0) ∧
    (∀ e : CubeEdge, (∑ f : CubeFace, if edgeInFace e f then kerVec2 f.1 else 0) = 0) ∧
    (∀ p : Fin 6, ∀ ab ∈ ([(0,0), (-1,0), (-1,1), (0,-1), (0,1), (1,-1), (1,0)] : List (ℤ × ℤ)),
      ab.1 * kerVec1 p + ab.2 * kerVec2 p ∈ ([-1, 0, 1] : List ℤ)) := by
  first | decide | norm_num | ring

end Imscribing.TrilatticeYM
