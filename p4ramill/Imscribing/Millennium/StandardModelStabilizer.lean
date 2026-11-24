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

private def C_a1_fast : Matrix (Fin 16) (Fin 16) ℤ := fun i j =>
  if (j.val / 2) % 2 = 1 ∧ j.val % 2 = 0 ∧ i.val + 1 = j.val then 1 else 0

private def C_a2_fast : Matrix (Fin 16) (Fin 16) ℤ := fun i j =>
  if (j.val / 4) % 2 = 1 ∧ (j.val / 2) % 2 = 0 ∧ i.val + 2 = j.val then 1 else 0

private def C_m1_fast : Matrix (Fin 16) (Fin 16) ℤ := fun i j =>
  if j.val % 2 = 1 ∧ (j.val / 2) % 2 = 0 ∧ i.val = j.val + 1 then 1 else 0

private def C_m2_fast : Matrix (Fin 16) (Fin 16) ℤ := fun i j =>
  if (j.val / 2) % 2 = 1 ∧ (j.val / 4) % 2 = 0 ∧ i.val = j.val + 2 then 1 else 0

private def C_a3_fast : Matrix (Fin 16) (Fin 16) ℤ := fun i j =>
  if (j.val / 4) % 2 = 1 ∧ j.val % 2 = 0 ∧ i.val + 3 = j.val then
    (if (j.val / 2) % 2 = 0 then 1 else -1)
  else 0

private def C_m3_fast : Matrix (Fin 16) (Fin 16) ℤ := fun i j =>
  if j.val % 2 = 1 ∧ (j.val / 4) % 2 = 0 ∧ i.val = j.val + 3 then
    (if (j.val / 2) % 2 = 0 then 1 else -1)
  else 0

private def T_plus_fast : Matrix (Fin 16) (Fin 16) ℤ := fun i j =>
  if (j.val / 8) % 2 = 0 ∧
     (j.val % 2 + (j.val / 2) % 2 + (j.val / 4) % 2) % 2 = 1 ∧
     i.val = j.val + 8 then 1 else 0

private def T_minus_fast : Matrix (Fin 16) (Fin 16) ℤ := fun i j =>
  if (j.val / 8) % 2 = 1 ∧
     (j.val % 2 + (j.val / 2) % 2 + (j.val / 4) % 2) % 2 = 1 ∧
     i.val + 8 = j.val then 1 else 0

private def Y6_fast : Matrix (Fin 16) (Fin 16) ℤ := fun i j =>
  if i = j then
    let b0 := j.val % 2;
    let b1 := (j.val / 2) % 2;
    let b2 := (j.val / 4) % 2;
    let b3 := (j.val / 8) % 2;
    let b4 := (b0 + b1 + b2 + b3) % 2;
    (-2 : ℤ) * ((b0 : ℤ) + b1 + b2) + 3 * ((b3 : ℤ) + b4)
  else 0

private lemma ca1_fast_eq : C_a1 = C_a1_fast := by
  apply Matrix.ext; intro i j; revert i j; decide

private lemma ca2_fast_eq : C_a2 = C_a2_fast := by
  apply Matrix.ext; intro i j; revert i j; decide

private lemma cm1_fast_eq : C_m1 = C_m1_fast := by
  apply Matrix.ext; intro i j; revert i j; decide

private lemma cm2_fast_eq : C_m2 = C_m2_fast := by
  apply Matrix.ext; intro i j; revert i j; decide

private lemma ca3_fast_eq : C_a3 = C_a3_fast := by
  rw [C_a3, ca1_fast_eq, ca2_fast_eq]
  apply Matrix.ext; intro i j; revert i j; decide

private lemma cm3_fast_eq : C_m3 = C_m3_fast := by
  rw [C_m3, cm2_fast_eq, cm1_fast_eq]
  apply Matrix.ext; intro i j; revert i j; decide

private lemma tplus_fast_eq : T_plus_weak = T_plus_fast := by
  apply Matrix.ext; intro i j; revert i j; decide

private lemma tminus_fast_eq : T_minus_weak = T_minus_fast := by
  apply Matrix.ext; intro i j; revert i j; decide

private lemma y6_fast_eq : Y6_16 = Y6_fast := by
  apply Matrix.ext; intro i j; revert i j; decide

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
  rw [HC1, ca1_fast_eq, cm1_fast_eq]
  apply Matrix.ext; intro i j; revert i j; decide

private lemma hc2_eq_diag : HC2 = HC2_diag := by
  rw [HC2, ca2_fast_eq, cm2_fast_eq]
  apply Matrix.ext; intro i j; revert i j; decide

theorem su3_color_cartan_comm : lieBracket HC1 HC2 = 0 := by
  rw [hc1_eq_diag, hc2_eq_diag]
  apply Matrix.ext; intro i j; revert i j; decide

theorem su3_color_cartan_pos_roots :
    lieBracket HC1 C_a1 = (2 : ℤ) • C_a1 ∧
    lieBracket HC1 C_a2 = (-1 : ℤ) • C_a2 ∧
    lieBracket HC2 C_a1 = (-1 : ℤ) • C_a1 ∧
    lieBracket HC2 C_a2 = (2 : ℤ) • C_a2 := by
  rw [hc1_eq_diag, hc2_eq_diag, ca1_fast_eq, ca2_fast_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

theorem su3_color_cartan_neg_roots :
    lieBracket HC1 C_m1 = (-2 : ℤ) • C_m1 ∧
    lieBracket HC1 C_m2 = C_m2 ∧
    lieBracket HC2 C_m1 = C_m1 ∧
    lieBracket HC2 C_m2 = (-2 : ℤ) • C_m2 := by
  rw [hc1_eq_diag, hc2_eq_diag, cm1_fast_eq, cm2_fast_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

theorem su3_color_chevalley_pairing :
    lieBracket C_a1 C_m1 = HC1 ∧
    lieBracket C_a2 C_m2 = HC2 ∧
    lieBracket C_a1 C_m2 = 0 ∧
    lieBracket C_a2 C_m1 = 0 ∧
    lieBracket C_a3 C_m3 = HC1 + HC2 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · rw [ca1_fast_eq, cm2_fast_eq]; apply Matrix.ext; intro i j; revert i j; decide
  · rw [ca2_fast_eq, cm1_fast_eq]; apply Matrix.ext; intro i j; revert i j; decide
  · rw [ca3_fast_eq, cm3_fast_eq, hc1_eq_diag, hc2_eq_diag]
    apply Matrix.ext; intro i j; revert i j; decide

private lemma lieBracket_swap {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℤ) : lieBracket A B = -lieBracket B A := by
  simp [lieBracket, neg_sub]

private lemma lieBracket_neg_right {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℤ) : lieBracket A (-B) = -lieBracket A B := by
  simp [lieBracket, Matrix.mul_neg, Matrix.neg_mul]
  abel

theorem su3_color_serre_relations :
    lieBracket C_a1 C_a3 = 0 ∧
    lieBracket C_a2 (lieBracket C_a2 C_a1) = 0 ∧
    lieBracket C_m1 (lieBracket C_m1 C_m2) = 0 ∧
    lieBracket C_m2 C_m3 = 0 := by
  have h21 : lieBracket C_a2 C_a1 = -C_a3 := lieBracket_swap C_a2 C_a1
  have h12 : lieBracket C_m1 C_m2 = -C_m3 := lieBracket_swap C_m1 C_m2
  rw [h21, h12, lieBracket_neg_right, lieBracket_neg_right, neg_eq_zero, neg_eq_zero]
  rw [ca1_fast_eq, ca2_fast_eq, ca3_fast_eq, cm1_fast_eq, cm2_fast_eq, cm3_fast_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-! ## Part 3: Full S(U(3) × U(2)) Mutual Decoupling and Color-Singlet Leptons -/

private lemma su3_comm_u1Y :
    lieBracket C_a1 Y6_16 = 0 ∧ lieBracket C_a2 Y6_16 = 0 ∧
    lieBracket C_m1 Y6_16 = 0 ∧ lieBracket C_m2 Y6_16 = 0 := by
  rw [ca1_fast_eq, ca2_fast_eq, cm1_fast_eq, cm2_fast_eq, y6_fast_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

private lemma su3_comm_Tplus :
    lieBracket C_a1 T_plus_weak = 0 ∧ lieBracket C_a2 T_plus_weak = 0 ∧
    lieBracket C_m1 T_plus_weak = 0 ∧ lieBracket C_m2 T_plus_weak = 0 := by
  rw [ca1_fast_eq, ca2_fast_eq, cm1_fast_eq, cm2_fast_eq, tplus_fast_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

private lemma su3_comm_Tminus :
    lieBracket C_a1 T_minus_weak = 0 ∧ lieBracket C_a2 T_minus_weak = 0 ∧
    lieBracket C_m1 T_minus_weak = 0 ∧ lieBracket C_m2 T_minus_weak = 0 := by
  rw [ca1_fast_eq, ca2_fast_eq, cm1_fast_eq, cm2_fast_eq, tminus_fast_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-- Complete mutual commutativity of SU(3)_C, SU(2)_L, and U(1)_Y across all 16 Weyl states. -/
theorem gsm_factors_mutually_commute :
    lieBracket C_a1 Y6_16 = 0 ∧ lieBracket C_a2 Y6_16 = 0 ∧
    lieBracket C_m1 Y6_16 = 0 ∧ lieBracket C_m2 Y6_16 = 0 ∧
    lieBracket C_a1 T_plus_weak = 0 ∧ lieBracket C_a2 T_plus_weak = 0 ∧
    lieBracket C_a1 T_minus_weak = 0 ∧ lieBracket C_a2 T_minus_weak = 0 ∧
    lieBracket C_m1 T_plus_weak = 0 ∧ lieBracket C_m2 T_plus_weak = 0 ∧
    lieBracket C_m1 T_minus_weak = 0 ∧ lieBracket C_m2 T_minus_weak = 0 :=
  ⟨su3_comm_u1Y.1, su3_comm_u1Y.2.1, su3_comm_u1Y.2.2.1, su3_comm_u1Y.2.2.2,
   su3_comm_Tplus.1, su3_comm_Tplus.2.1, su3_comm_Tminus.1, su3_comm_Tminus.2.1,
   su3_comm_Tplus.2.2.1, su3_comm_Tplus.2.2.2, su3_comm_Tminus.2.2.1, su3_comm_Tminus.2.2.2⟩

/-- All 4 leptonic states (0=νᶜ, 8=eᶜ, 15=ν, 7=e) are annihilated by all SU(3)_C generators. -/
theorem leptons_are_color_singlets :
    ∀ s ∈ ({0, 7, 8, 15} : Finset (Fin 16)), ∀ i : Fin 16,
      C_a1 i s = 0 ∧ C_a2 i s = 0 ∧ C_m1 i s = 0 ∧ C_m2 i s = 0 := by
  rw [ca1_fast_eq, ca2_fast_eq, cm1_fast_eq, cm2_fast_eq]
  decide

private lemma lieBracket_comm_of_comm {n : Type*} [Fintype n] [DecidableEq n]
    {X A B : Matrix n n ℤ} (hA : lieBracket X A = 0) (hB : lieBracket X B = 0) :
    lieBracket X (lieBracket A B) = 0 := by
  have hXA : X * A = A * X := sub_eq_zero.mp hA
  have hXB : X * B = B * X := sub_eq_zero.mp hB
  apply sub_eq_zero.mpr
  simp only [lieBracket, Matrix.mul_sub, Matrix.sub_mul]
  calc X * (A * B) - X * (B * A)
      = (X * A) * B - (X * B) * A := by simp only [Matrix.mul_assoc]
    _ = (A * X) * B - (B * X) * A := by rw [hXA, hXB]
    _ = A * (X * B) - B * (X * A) := by simp only [Matrix.mul_assoc]
    _ = A * (B * X) - B * (A * X) := by rw [hXB, hXA]
    _ = (A * B) * X - (B * A) * X := by simp only [Matrix.mul_assoc]

private lemma lieBracket_comm_smul_add {n : Type*} [Fintype n] [DecidableEq n]
    {X A B : Matrix n n ℤ} (c : ℤ) (hA : lieBracket X A = 0) (hB : lieBracket X B = 0) :
    lieBracket X (c • A + B) = 0 := by
  have hXA : X * A = A * X := sub_eq_zero.mp hA
  have hXB : X * B = B * X := sub_eq_zero.mp hB
  apply sub_eq_zero.mpr
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hXA, hXB]

/-- Color-neutral electric charge Q_em_6 commutes with all SU(3)_C color generators. -/
theorem electric_charge_commutes_with_color :
    lieBracket C_a1 Q_em_6 = 0 ∧ lieBracket C_a2 Q_em_6 = 0 ∧
    lieBracket C_m1 Q_em_6 = 0 ∧ lieBracket C_m2 Q_em_6 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact lieBracket_comm_smul_add 3
      (lieBracket_comm_of_comm su3_comm_Tplus.1 su3_comm_Tminus.1) su3_comm_u1Y.1
  · exact lieBracket_comm_smul_add 3
      (lieBracket_comm_of_comm su3_comm_Tplus.2.1 su3_comm_Tminus.2.1) su3_comm_u1Y.2.1
  · exact lieBracket_comm_smul_add 3
      (lieBracket_comm_of_comm su3_comm_Tplus.2.2.1 su3_comm_Tminus.2.2.1) su3_comm_u1Y.2.2.1
  · exact lieBracket_comm_smul_add 3
      (lieBracket_comm_of_comm su3_comm_Tplus.2.2.2 su3_comm_Tminus.2.2.2) su3_comm_u1Y.2.2.2

end Imscribing.Millennium.StandardModelStabilizer