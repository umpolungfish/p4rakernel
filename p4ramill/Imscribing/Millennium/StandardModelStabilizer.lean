import Imscribing.Millennium.Spin10Intertwiner

namespace Imscribing.Millennium.StandardModelStabilizer

open Imscribing.Millennium.Spin10ChiralFock
open Imscribing.Millennium.Spin10Intertwiner
open Imscribing.Millennium.CurvatureLieAlgebra

/-! ## Part 1: Fermionic Bilinears c_a† c_b as Exact Spin(10) Clifford Bilinears -/

def flipBit32 (k : ℕ) (y : Fin 32) : Fin 32 :=
  ⟨(y.val ^^^ (1 <<< k)) % 32, Nat.mod_lt _ (by decide)⟩

def hop32Coeff (a b : Fin 5) (y : Fin 32) : GaussianInt :=
  if bitAt y b.val = 1 ∧ bitAt y a.val = 0 then
    ⟨jwSign y b.val * jwSign (flipBit32 b.val y) a.val, 0⟩
  else 0

def hop32G (a b : Fin 5) : Matrix (Fin 32) (Fin 32) GaussianInt :=
  monomialMatrix (fun y => flipBit32 a.val (flipBit32 b.val y)) (hop32Coeff a b)

def caDag2 (a : Fin 5) : Matrix (Fin 32) (Fin 32) GaussianInt :=
  monomialMatrix (flipBit32 a.val)
    (fun y => if bitAt y a.val = 0 then ⟨2 * jwSign y a.val, 0⟩ else 0)

def cb2 (b : Fin 5) : Matrix (Fin 32) (Fin 32) GaussianInt :=
  monomialMatrix (flipBit32 b.val)
    (fun y => if bitAt y b.val = 1 then ⟨2 * jwSign y b.val, 0⟩ else 0)

private lemma gammaFlip_even (a : Fin 5) (y : Fin 32) :
    gammaFlip ⟨2 * a.val, by omega⟩ y = flipBit32 a.val y := by
  revert a y; decide

private lemma gammaFlip_odd (a : Fin 5) (y : Fin 32) :
    gammaFlip ⟨2 * a.val + 1, by omega⟩ y = flipBit32 a.val y := by
  revert a y; decide

private lemma caDag_coeff_eq (a : Fin 5) (y : Fin 32) :
    gammaCoeff ⟨2 * a.val, by omega⟩ y - ⟨0, 1⟩ * gammaCoeff ⟨2 * a.val + 1, by omega⟩ y =
    (if bitAt y a.val = 0 then ⟨2 * jwSign y a.val, 0⟩ else 0) := by
  revert a y; decide

private lemma cb_coeff_eq (b : Fin 5) (y : Fin 32) :
    gammaCoeff ⟨2 * b.val, by omega⟩ y + ⟨0, 1⟩ * gammaCoeff ⟨2 * b.val + 1, by omega⟩ y =
    (if bitAt y b.val = 1 then ⟨2 * jwSign y b.val, 0⟩ else 0) := by
  revert b y; decide

theorem caDag2_eq_clifford (a : Fin 5) :
    gammaMatrix ⟨2 * a.val, by omega⟩ - (⟨0, 1⟩ : GaussianInt) • gammaMatrix ⟨2 * a.val + 1, by omega⟩ =
    caDag2 a := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, gammaMatrix, monomialMatrix,
    caDag2, gammaFlip_even, gammaFlip_odd]
  by_cases hij : i = flipBit32 a.val j
  · simp [hij, caDag_coeff_eq]
  · simp [hij]

theorem cb2_eq_clifford (b : Fin 5) :
    gammaMatrix ⟨2 * b.val, by omega⟩ + (⟨0, 1⟩ : GaussianInt) • gammaMatrix ⟨2 * b.val + 1, by omega⟩ =
    cb2 b := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, gammaMatrix, monomialMatrix,
    cb2, gammaFlip_even, gammaFlip_odd]
  by_cases hij : i = flipBit32 b.val j
  · simp [hij, cb_coeff_eq]
  · simp [hij]

private lemma hop_coeff_mul_eq (a b : Fin 5) (hab : a ≠ b) (j : Fin 32) :
    (if bitAt (flipBit32 b.val j) a.val = 0 then ⟨2 * jwSign (flipBit32 b.val j) a.val, 0⟩ else 0) *
    (if bitAt j b.val = 1 then ⟨2 * jwSign j b.val, 0⟩ else 0) =
    (4 : GaussianInt) * hop32Coeff a b j := by
  revert a b hab j; decide

/-- Every fermionic hopping bilinear 4·c_a† c_b (a ≠ b) equals the Clifford product
    (γ_{2a} - i γ_{2a+1})(γ_{2b} + i γ_{2b+1}) inside so(10)_ℂ. -/
theorem hop32_in_clifford_bilinear (a b : Fin 5) (hab : a ≠ b) :
    (4 : GaussianInt) • hop32G a b =
      (gammaMatrix ⟨2 * a.val, by omega⟩ - (⟨0, 1⟩ : GaussianInt) • gammaMatrix ⟨2 * a.val + 1, by omega⟩) *
      (gammaMatrix ⟨2 * b.val, by omega⟩ + (⟨0, 1⟩ : GaussianInt) • gammaMatrix ⟨2 * b.val + 1, by omega⟩) := by
  rw [caDag2_eq_clifford, cb2_eq_clifford, caDag2, cb2, monomialMatrix_mul]
  apply Matrix.ext
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul, hop32G, monomialMatrix, Function.comp_apply]
  by_cases hij : i = flipBit32 a.val (flipBit32 b.val j)
  · simp [hij, hop_coeff_mul_eq a b hab j]
  · simp [hij]

/-! ## Part 2: Integer Restriction to L (Fin 16) and SU(3)_C Chevalley-Serre Closure -/

def hop16 (a b : Fin 5) : Matrix (Fin 16) (Fin 16) ℤ :=
  fun i j =>
    let yj := lToFockEven j
    let yi := flipBit32 a.val (flipBit32 b.val yj)
    if parity5 yi = 0 ∧ fockEvenToL yi = i then
      (hop32Coeff a b yj).re
    else 0

theorem hop16_intertwines_hop32 (a b : Fin 5) (i j : Fin 16) :
    ((hop16 a b i j : ℤ) : GaussianInt) = hop32G a b (lToFockEven i) (lToFockEven j) := by
  revert a b i j; decide

/-- The weak-isospin generators of Spin10Intertwiner are literally c₃† c₄ and c₄† c₃. -/
theorem weak_su2_from_fock_bilinears :
    T_plus_weak = hop16 3 4 ∧ T_minus_weak = hop16 4 3 := by
  refine ⟨?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-- Color SU(3)_C Chevalley generators acting on modes 0, 1, 2 ∈ V₃. -/
def C_a1 : Matrix (Fin 16) (Fin 16) ℤ := hop16 0 1
def C_a2 : Matrix (Fin 16) (Fin 16) ℤ := hop16 1 2
def C_m1 : Matrix (Fin 16) (Fin 16) ℤ := hop16 1 0
def C_m2 : Matrix (Fin 16) (Fin 16) ℤ := hop16 2 1

def C_a3 : Matrix (Fin 16) (Fin 16) ℤ := lieBracket C_a1 C_a2
def C_m3 : Matrix (Fin 16) (Fin 16) ℤ := lieBracket C_m2 C_m1

def HC1_diag : Matrix (Fin 16) (Fin 16) ℤ := fun i j =>
  if i = j then
    let y := lToFockEven i
    (bitAt y 0 : ℤ) - (bitAt y 1 : ℤ)
  else 0

def HC2_diag : Matrix (Fin 16) (Fin 16) ℤ := fun i j =>
  if i = j then
    let y := lToFockEven i
    (bitAt y 1 : ℤ) - (bitAt y 2 : ℤ)
  else 0

def HC1 : Matrix (Fin 16) (Fin 16) ℤ := lieBracket C_a1 C_m1
def HC2 : Matrix (Fin 16) (Fin 16) ℤ := lieBracket C_a2 C_m2

private lemma hc1_eq_diag : HC1 = HC1_diag := by
  apply Matrix.ext; intro i j; revert i j; decide

private lemma hc2_eq_diag : HC2 = HC2_diag := by
  apply Matrix.ext; intro i j; revert i j; decide

private lemma ca3_eq_hop : C_a3 = hop16 0 2 := by
  apply Matrix.ext; intro i j; revert i j; decide

private lemma cm3_eq_hop : C_m3 = hop16 2 0 := by
  apply Matrix.ext; intro i j; revert i j; decide

theorem su3_color_cartan_comm : lieBracket HC1 HC2 = 0 := by
  rw [hc1_eq_diag, hc2_eq_diag]
  apply Matrix.ext; intro i j; revert i j; decide

theorem su3_color_cartan_pos_roots :
    lieBracket HC1 C_a1 = (2 : ℤ) • C_a1 ∧
    lieBracket HC1 C_a2 = (-1 : ℤ) • C_a2 ∧
    lieBracket HC2 C_a1 = (-1 : ℤ) • C_a1 ∧
    lieBracket HC2 C_a2 = (2 : ℤ) • C_a2 := by
  rw [hc1_eq_diag, hc2_eq_diag]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

theorem su3_color_cartan_neg_roots :
    lieBracket HC1 C_m1 = (-2 : ℤ) • C_m1 ∧
    lieBracket HC1 C_m2 = C_m2 ∧
    lieBracket HC2 C_m1 = C_m1 ∧
    lieBracket HC2 C_m2 = (-2 : ℤ) • C_m2 := by
  rw [hc1_eq_diag, hc2_eq_diag]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

theorem su3_color_chevalley_pairing :
    lieBracket C_a1 C_m1 = HC1 ∧
    lieBracket C_a2 C_m2 = HC2 ∧
    lieBracket C_a1 C_m2 = 0 ∧
    lieBracket C_a2 C_m1 = 0 ∧
    lieBracket C_a3 C_m3 = HC1 + HC2 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · apply Matrix.ext; intro i j; revert i j; decide
  · apply Matrix.ext; intro i j; revert i j; decide
  · rw [ca3_eq_hop, cm3_eq_hop, hc1_eq_diag, hc2_eq_diag]
    apply Matrix.ext; intro i j; revert i j; decide

theorem su3_color_serre_relations :
    lieBracket C_a1 C_a3 = 0 ∧
    lieBracket C_a2 (lieBracket C_a2 C_a1) = 0 ∧
    lieBracket C_m1 (lieBracket C_m1 C_m2) = 0 ∧
    lieBracket C_m2 C_m3 = 0 := by
  rw [ca3_eq_hop, cm3_eq_hop]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-! ## Part 3: Full S(U(3) × U(2)) Mutual Decoupling and Color-Singlet Leptons -/

/-- Complete mutual commutativity of SU(3)_C, SU(2)_L, and U(1)_Y across all 16 Weyl states. -/
theorem gsm_factors_mutually_commute :
    lieBracket C_a1 Y6_16 = 0 ∧ lieBracket C_a2 Y6_16 = 0 ∧
    lieBracket C_m1 Y6_16 = 0 ∧ lieBracket C_m2 Y6_16 = 0 ∧
    lieBracket C_a1 T_plus_weak = 0 ∧ lieBracket C_a2 T_plus_weak = 0 ∧
    lieBracket C_a1 T_minus_weak = 0 ∧ lieBracket C_a2 T_minus_weak = 0 ∧
    lieBracket C_m1 T_plus_weak = 0 ∧ lieBracket C_m2 T_plus_weak = 0 ∧
    lieBracket C_m1 T_minus_weak = 0 ∧ lieBracket C_m2 T_minus_weak = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply Matrix.ext; intro i j; revert i j; decide)

/-- All 4 leptonic states (0=νᶜ, 8=eᶜ, 15=ν, 7=e) are annihilated by all SU(3)_C generators. -/
theorem leptons_are_color_singlets :
    ∀ s ∈ ({0, 7, 8, 15} : Finset (Fin 16)), ∀ i : Fin 16,
      C_a1 i s = 0 ∧ C_a2 i s = 0 ∧ C_m1 i s = 0 ∧ C_m2 i s = 0 := by
  decide

/-- Color-neutral electric charge Q_em_6 commutes with all SU(3)_C color generators. -/
theorem electric_charge_commutes_with_color :
    lieBracket C_a1 Q_em_6 = 0 ∧ lieBracket C_a2 Q_em_6 = 0 ∧
    lieBracket C_m1 Q_em_6 = 0 ∧ lieBracket C_m2 Q_em_6 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

end Imscribing.Millennium.StandardModelStabilizer