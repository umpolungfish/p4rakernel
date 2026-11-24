import Imscribing.Millennium.CurvatureLieAlgebra
import Imscribing.Millennium.FamilyWeylFrobenius

namespace Imscribing.Millennium.TwoTrineGearing

open Imscribing.Millennium.CurvatureLieAlgebra
open Imscribing.Millennium.FamilyWeylFrobenius

/-! ## Part 1: Major Trine (Ui, Ut, Uc), Exact Gram Geometry, and Commuting Warning -/

def hsInner (A B : Matrix (Fin 16) (Fin 16) ℤ) : ℤ :=
  ∑ i : Fin 16, ∑ j : Fin 16, A i j * B i j

theorem major_raw_gram :
    hsInner Ui Ui = 32 ∧ hsInner Ut Ut = 32 ∧ hsInner Uc Uc = 32 ∧
    hsInner Ui Ut = 16 ∧ hsInner Ut Uc = 16 ∧ hsInner Uc Ui = 16 := by
  decide

/-- Scaled centered major operators 3·Ũ_a = 3·U_a - (Ui + Ut + Uc). -/
def Utilde_i : Matrix (Fin 16) (Fin 16) ℤ := (3 : ℤ) • Ui - (Ui + Ut + Uc)
def Utilde_t : Matrix (Fin 16) (Fin 16) ℤ := (3 : ℤ) • Ut - (Ui + Ut + Uc)
def Utilde_c : Matrix (Fin 16) (Fin 16) ℤ := (3 : ℤ) • Uc - (Ui + Ut + Uc)

theorem major_trine_sum_zero : Utilde_i + Utilde_t + Utilde_c = 0 := by
  apply Matrix.ext; intro i j; revert i j; decide

/-- Centered Gram inner products: 96 on diagonal, -48 off-diagonal (cos θ = -48/96 = -1/2). -/
theorem major_trine_equilateral_gram :
    hsInner Utilde_i Utilde_i = 96 ∧
    hsInner Utilde_t Utilde_t = 96 ∧
    hsInner Utilde_c Utilde_c = 96 ∧
    hsInner Utilde_i Utilde_t = -48 ∧
    hsInner Utilde_t Utilde_c = -48 ∧
    hsInner Utilde_c Utilde_i = -48 := by
  decide

/-- §97 Algebraic Warning: because K_{it} + K_{tc} + K_{ci} = 0, the centered major
    trine operators commute pairwise under the matrix commutator. -/
theorem centered_major_trine_commutes :
    lieBracket Utilde_i Utilde_t = 0 ∧
    lieBracket Utilde_t Utilde_c = 0 ∧
    lieBracket Utilde_c Utilde_i = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-! ## Part 2: Internal Bloch-Sphere Evaluator Trine (E_T, E_F, H_P) over E3 = Zsqrtd (-3) -/

/-- Scaled centered Bloch operators B_j = 2(2P_j - I) for EVAL TRUE, EVAL FALSE, HOLD PARADOX. -/
def BT2 : Matrix (Fin 2) (Fin 2) E3 := fun i j =>
  match i.val, j.val with
  | 0, 1 => 2 | 1, 0 => 2 | _, _ => 0

def BF2 : Matrix (Fin 2) (Fin 2) E3 := fun i j =>
  match i.val, j.val with
  | 0, 1 => w2b | 1, 0 => w2 | _, _ => 0

def BH2 : Matrix (Fin 2) (Fin 2) E3 := fun i j =>
  match i.val, j.val with
  | 0, 1 => w2 | 1, 0 => w2b | _, _ => 0

def sz2 : Matrix (Fin 2) (Fin 2) E3 := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1 | 1, 1 => -1 | _, _ => 0

def trace2 (A : Matrix (Fin 2) (Fin 2) E3) : E3 := A 0 0 + A 1 1

theorem bloch_trine_sum_zero : BT2 + BF2 + BH2 = 0 := by
  apply Matrix.ext; intro i j; revert i j; decide

/-- Isometric equilateral Bloch trine: Tr(B_j B_j) = 8, Tr(B_j B_k) = -4 (cos θ = -1/2). -/
theorem bloch_trine_equilateral_gram :
    trace2 (BT2 * BT2) = 8 ∧ trace2 (BF2 * BF2) = 8 ∧ trace2 (BH2 * BH2) = 8 ∧
    trace2 (BT2 * BF2) = -4 ∧ trace2 (BF2 * BH2) = -4 ∧ trace2 (BH2 * BT2) = -4 := by
  decide

/-- Unlike the commuting centered major operators, the Bloch trine is noncommuting and
    generates the orthogonal σ_z axis (closing su(2) on V₂). -/
theorem bloch_trine_generates_su2 :
    BT2 * BF2 - BF2 * BT2 = ((4 : E3) * sRoot) • sz2 ∧
    sRoot • (sz2 * BT2 - BT2 * sz2) = (2 : E3) • (BH2 - BF2) := by
  refine ⟨?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-! ## Part 3: Cyclic & Reflection Gear Intertwiners, 2D₃ Spinor Lift, and 5D Gauge Compatibility -/

/-- Scaled unitary cyclic gear UB2 = 2 U_B = diag(1 - √(-3), 1 + √(-3)) and its adjoint. -/
def UB2 : Matrix (Fin 2) (Fin 2) E3 := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1 - sRoot
  | 1, 1 => 1 + sRoot
  | _, _ => 0

def UB2_adj : Matrix (Fin 2) (Fin 2) E3 := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1 + sRoot
  | 1, 1 => 1 - sRoot
  | _, _ => 0

def conjE3 (z : E3) : E3 := ⟨z.re, -z.im⟩
def conjMat2 (A : Matrix (Fin 2) (Fin 2) E3) : Matrix (Fin 2) (Fin 2) E3 :=
  fun i j => conjE3 (A i j)

/-- Spinorial 6-fold lift: U_B is unitary, U_B³ = -I₂, and U_B⁶ = I₂. -/
theorem gear_unitary_and_sixfold_spinor :
    UB2 * UB2_adj = (4 : E3) • 1 ∧
    UB2^3 = (-8 : E3) • 1 ∧
    UB2^6 = (64 : E3) • 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-- §99 Cyclic Gear Intertwiner: Ad_{U_B} cycles BT2 → BF2 → BH2 → BT2. -/
theorem gear_cyclic_intertwiner :
    UB2 * BT2 * UB2_adj = (4 : E3) • BF2 ∧
    UB2 * BF2 * UB2_adj = (4 : E3) • BH2 ∧
    UB2 * BH2 * UB2_adj = (4 : E3) • BT2 := by
  refine ⟨?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-- §100 Reflection Gear Intertwiner: complex conjugation fixes BT2, swaps BF2 ↔ BH2,
    and inverts U_B ↦ U_B⁻¹. -/
theorem gear_reflection_intertwiner :
    conjMat2 BT2 = BT2 ∧
    conjMat2 BF2 = BH2 ∧
    conjMat2 BH2 = BF2 ∧
    conjMat2 UB2 = UB2_adj := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-- Binary dihedral 2D₃ (order 12) spinor relations on V₂: r³ = -I, s² = -I, s r s⁻¹ = r⁻¹. -/
def sSpinor : Matrix (Fin 2) (Fin 2) E3 := fun i j =>
  match i.val, j.val with
  | 0, 1 => -1 | 1, 0 => 1 | _, _ => 0

theorem binary_dihedral_2d3_relations :
    sSpinor * sSpinor = (-1 : E3) • 1 ∧
    UB2^3 = (-8 : E3) • 1 ∧
    sSpinor * UB2 * (-sSpinor) = UB2_adj := by
  refine ⟨?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-- §101 5D Geared Lift R̂ = diag(R_M, U_B) (scaled by 2) on V₃ ⊕ V₂, and 6Y = diag(-2,-2,-2,3,3). -/
def Rhat2 : Matrix (Fin 5) (Fin 5) E3 := fun i j =>
  match i.val, j.val with
  | 1, 0 => 2 | 2, 1 => 2 | 0, 2 => 2
  | 3, 3 => 1 - sRoot | 4, 4 => 1 + sRoot
  | _, _ => 0

def Y6_5 : Matrix (Fin 5) (Fin 5) E3 := fun i j =>
  if i = j then (if i.val < 3 then (-2 : E3) else 3) else 0

theorem geared_5d_lift_and_hypercharge :
    Rhat2^3 = (fun i j => if i = j then (if i.val < 3 then (8 : E3) else -8) else 0) ∧
    Rhat2^6 = (64 : E3) • 1 ∧
    Y6_5 * Rhat2 = Rhat2 * Y6_5 := by
  refine ⟨?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

end Imscribing.Millennium.TwoTrineGearing