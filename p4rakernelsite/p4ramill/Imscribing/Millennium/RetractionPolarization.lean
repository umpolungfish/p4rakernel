import Imscribing.Millennium.CurvatureLieAlgebra

namespace Imscribing.Millennium.RetractionPolarization

open Imscribing.Millennium.CurvatureLieAlgebra

/-! ## Part 1: Support Retraction ρ : L → B ⇄ ι : B → L and Fiber Multiplicities (1, 3, 3, 9) -/

private def bitOf (x : Fin 16) (a : ℕ) : ℕ := (x.val / 2^a) % 2

/-- Positive support p(x) = 1 iff T or t is occupied; negative support n(x) = 1 iff F or f is occupied. -/
def posSupp (x : Fin 16) : Bool := bitOf x 3 = 1 || bitOf x 1 = 1
def negSupp (x : Fin 16) : Bool := bitOf x 2 = 1 || bitOf x 0 = 1

/-- Support retraction ρ : L → B = {0=N, 1=T, 2=F, 3=B}. -/
def rho (x : Fin 16) : Fin 4 :=
  match posSupp x, negSupp x with
  | false, false => 0
  | true,  false => 1
  | false, true  => 2
  | true,  true  => 3

/-- Canonical Boolean section ι : B ↪ L using {∅, {T}, {F}, {T, F}}. -/
def iota : Fin 4 → Fin 16
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 8
  | ⟨2, _⟩ => 4
  | ⟨3, _⟩ => 12

theorem rho_iota_id : ∀ b : Fin 4, rho (iota b) = b := by
  decide

/-- Fiber multiplicities |ρ⁻¹(N, T, F, B)| = (1, 3, 3, 9), splitting 16 = 4 + 12. -/
theorem fiber_multiplicities_1_3_3_9 :
    (Finset.univ.filter fun x : Fin 16 => rho x = 0).card = 1 ∧
    (Finset.univ.filter fun x : Fin 16 => rho x = 1).card = 3 ∧
    (Finset.univ.filter fun x : Fin 16 => rho x = 2).card = 3 ∧
    (Finset.univ.filter fun x : Fin 16 => rho x = 3).card = 9 := by
  decide

/-! ## Part 2: Linearized Retraction, Core Operators A_a, and Retraction Curvature R_{ab} -/

def rhoMat : Matrix (Fin 4) (Fin 16) ℤ := fun b x => if rho x = b then 1 else 0
def iotaMat : Matrix (Fin 16) (Fin 4) ℤ := fun x b => if iota b = x then 1 else 0

def Pret : Matrix (Fin 16) (Fin 16) ℤ := iotaMat * rhoMat
def Qret : Matrix (Fin 16) (Fin 16) ℤ := 1 - Pret

theorem retraction_projector_laws :
    rhoMat * iotaMat = 1 ∧ Pret * Pret = Pret ∧ Pret * Qret = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-- Retracted core order operators A_a = ρ U_a ι on (N, T, F, B). -/
def Ai : Matrix (Fin 4) (Fin 4) ℤ := rhoMat * Ui * iotaMat
def At : Matrix (Fin 4) (Fin 4) ℤ := rhoMat * Ut * iotaMat
def Ac : Matrix (Fin 4) (Fin 4) ℤ := rhoMat * Uc * iotaMat

def Ai_explicit : Matrix (Fin 4) (Fin 4) ℤ := fun i j =>
  match i.val, j.val with
  | 1, 0 => 2 | 1, 1 => 1
  | 2, 0 => 2 | 2, 2 => 1
  | 3, 1 => 2 | 3, 2 => 2 | 3, 3 => 2
  | _, _ => 0

def At_explicit : Matrix (Fin 4) (Fin 4) ℤ := fun i j =>
  match i.val, j.val with
  | 0, 2 => 1
  | 1, 0 => 2 | 1, 1 => 1 | 1, 3 => 1
  | 3, 2 => 2 | 3, 3 => 1
  | _, _ => 0

def Ac_explicit : Matrix (Fin 4) (Fin 4) ℤ := fun i j =>
  match i.val, j.val with
  | 1, 0 => 1
  | 2, 0 => 1
  | 3, 1 => 1 | 3, 2 => 1
  | _, _ => 0

theorem core_operators_exact :
    Ai = Ai_explicit ∧ At = At_explicit ∧ Ac = Ac_explicit := by
  refine ⟨?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-- Retraction curvature R_{ab} = ρ [U_a, U_b] ι - [A_a, A_b] = ρ U_a Q U_b ι - ρ U_b Q U_a ι. -/
def Rit : Matrix (Fin 4) (Fin 4) ℤ := rhoMat * Kit * iotaMat - lieBracket Ai At
def Rtc : Matrix (Fin 4) (Fin 4) ℤ := rhoMat * Ktc * iotaMat - lieBracket At Ac
def Rci : Matrix (Fin 4) (Fin 4) ℤ := rhoMat * Kci * iotaMat - lieBracket Ac Ai

def Rit_explicit : Matrix (Fin 4) (Fin 4) ℤ := fun i j =>
  match i.val, j.val with
  | 0, 2 => 1 | 1, 3 => 1 | 2, 2 => -2 | 3, 3 => -2 | _, _ => 0

def Rtc_explicit : Matrix (Fin 4) (Fin 4) ℤ := fun i j =>
  match i.val, j.val with
  | 0, 0 => -1 | 1, 0 => -1 | 1, 1 => -1 | 2, 2 => -1 | 3, 2 => -1 | 3, 3 => -1 | _, _ => 0

def Rci_explicit : Matrix (Fin 4) (Fin 4) ℤ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 2 | 1, 0 => 1 | 1, 1 => 2 | 2, 0 => 1 | 2, 2 => 2 | 3, 1 => 1 | 3, 2 => 1 | 3, 3 => 2 | _, _ => 0

theorem retraction_curvatures_exact :
    Rit = Rit_explicit ∧ Rtc = Rtc_explicit ∧ Rci = Rci_explicit := by
  refine ⟨?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

theorem retraction_curvature_fiber_formula :
    Rit = rhoMat * Ui * Qret * Ut * iotaMat - rhoMat * Ut * Qret * Ui * iotaMat ∧
    Rtc = rhoMat * Ut * Qret * Uc * iotaMat - rhoMat * Uc * Qret * Ut * iotaMat ∧
    Rci = rhoMat * Uc * Qret * Ui * iotaMat - rhoMat * Ui * Qret * Uc * iotaMat := by
  refine ⟨?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-- Cyclic retraction residue C_ρ = R_{it} + R_{tc} + R_{ci} and exact polarization C_ρ² = 2 I₄. -/
def C_rho : Matrix (Fin 4) (Fin 4) ℤ := Rit + Rtc + Rci

def C_rho_explicit : Matrix (Fin 4) (Fin 4) ℤ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1 | 0, 2 => 1
  | 1, 1 => 1 | 1, 3 => 1
  | 2, 0 => 1 | 2, 2 => -1
  | 3, 1 => 1 | 3, 3 => -1
  | _, _ => 0

theorem core_polarization_law :
    C_rho = C_rho_explicit ∧ C_rho * C_rho = (2 : ℤ) • 1 := by
  refine ⟨?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-! ## Part 3: Primitive sl₂⁴ Lie Closure of {U_i, U_t, U_c, U_i†, U_t†, U_c†} & A₂ Obstruction -/

def Xop (a : ℕ) : Matrix (Fin 16) (Fin 16) ℤ := EPlus a + EMinus a
def Yop (a : ℕ) : Matrix (Fin 16) (Fin 16) ℤ := EPlus a - EMinus a
def Zop (a : ℕ) : Matrix (Fin 16) (Fin 16) ℤ := lieBracket (EPlus a) (EMinus a)

def Zdiag (a : ℕ) : Matrix (Fin 16) (Fin 16) ℤ :=
  fun i j => if i = j then (if (i.val / 2^a) % 2 = 1 then 1 else -1) else 0

private lemma fin4_cases {P : Fin 4 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) :
    ∀ a : Fin 4, P a
  | ⟨0, _⟩ => h0 | ⟨1, _⟩ => h1 | ⟨2, _⟩ => h2 | ⟨3, _⟩ => h3

private lemma zop_eq_zdiag : ∀ a : Fin 4, Zop a.val = Zdiag a.val := by
  refine fin4_cases ?_ ?_ ?_ ?_ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-- Sign-weighted generators extracted directly from U_i, U_t, U_c and their transposes. -/
def X1 : Matrix (Fin 16) (Fin 16) ℤ := Ui + Ui.transpose
def Y1 : Matrix (Fin 16) (Fin 16) ℤ := Ui - Ui.transpose
def Yp : Matrix (Fin 16) (Fin 16) ℤ := Ut - Ut.transpose
def Yq : Matrix (Fin 16) (Fin 16) ℤ := Uc - Uc.transpose

theorem sl2_local_XY (a : Fin 4) :
    lieBracket (Xop a.val) (Yop a.val) = (-2 : ℤ) • Zop a.val := by
  rw [zop_eq_zdiag a]
  revert a
  refine fin4_cases ?_ ?_ ?_ ?_ <;> (apply Matrix.ext; intro i j; revert i j; decide)

theorem sl2_local_ZY (a : Fin 4) :
    lieBracket (Zop a.val) (Yop a.val) = (2 : ℤ) • Xop a.val := by
  rw [zop_eq_zdiag a]
  revert a
  refine fin4_cases ?_ ?_ ?_ ?_ <;> (apply Matrix.ext; intro i j; revert i j; decide)

theorem sl2_local_ZX (a : Fin 4) :
    lieBracket (Zop a.val) (Xop a.val) = (2 : ℤ) • Yop a.val := by
  rw [zop_eq_zdiag a]
  revert a
  refine fin4_cases ?_ ?_ ?_ ?_ <;> (apply Matrix.ext; intro i j; revert i j; decide)

private lemma lieBracket_anticomm (A B : Matrix (Fin 16) (Fin 16) ℤ) :
    lieBracket A B = 0 → lieBracket B A = 0 := by
  intro h
  have h1 : A * B = B * A := sub_eq_zero.mp h
  exact sub_eq_zero.mpr h1.symm

private lemma eplus_eplus_comm_lt :
    ∀ a b : Fin 4, a < b → lieBracket (EPlus a.val) (EPlus b.val) = 0 := by
  decide

private lemma eplus_eminus_comm_lt :
    ∀ a b : Fin 4, a < b → lieBracket (EPlus a.val) (EMinus b.val) = 0 := by
  decide

private lemma eminus_eplus_comm_lt :
    ∀ a b : Fin 4, a < b → lieBracket (EMinus a.val) (EPlus b.val) = 0 := by
  decide

private lemma zop_comm (a b : Fin 4) : lieBracket (Zop a.val) (Zop b.val) = 0 := by
  rw [zop_eq_zdiag a, zop_eq_zdiag b]
  apply Matrix.ext
  intro i j
  simp only [lieBracket, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply, Zdiag]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
  · by_cases hij : i = j
    · subst hij; ring
    · simp [hij]
  · intro k _ hk; simp [hk.symm]
  · intro h; exact absurd (Finset.mem_univ i) h
  · intro k _ hk; simp [hk.symm]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem sl2_cross_commute {a b : Fin 4} (hab : a ≠ b) :
    lieBracket (EPlus a.val) (EPlus b.val) = 0 ∧
    lieBracket (EPlus a.val) (EMinus b.val) = 0 ∧
    lieBracket (Zop a.val) (Zop b.val) = 0 := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact ⟨eplus_eplus_comm_lt a b hlt, eplus_eminus_comm_lt a b hlt, zop_comm a b⟩
  · exact ⟨lieBracket_anticomm _ _ (eplus_eplus_comm_lt b a hgt),
           lieBracket_anticomm _ _ (eminus_eplus_comm_lt b a hgt),
           zop_comm a b⟩

private lemma x1_eq : X1 = Xop 3 + Xop 2 + Xop 1 + Xop 0 := by
  apply Matrix.ext; intro i j; revert i j; decide

private lemma zp_eq : lieBracket Yp X1 = (2 : ℤ) • (Zop 3 - Zop 2 + Zop 1 - Zop 0) := by
  apply Matrix.ext; intro i j; revert i j; decide

private lemma zq_eq : lieBracket Yq X1 = (2 : ℤ) • (Zop 3 + Zop 2 - Zop 1 - Zop 0) := by
  apply Matrix.ext; intro i j; revert i j; decide

private lemma xp_eq :
    lieBracket (lieBracket Yp X1) Y1 = (4 : ℤ) • (Xop 3 - Xop 2 + Xop 1 - Xop 0) := by
  rw [zp_eq]
  apply Matrix.ext; intro i j; revert i j; decide

private lemma xq_eq :
    lieBracket (lieBracket Yq X1) Y1 = (4 : ℤ) • (Xop 3 + Xop 2 - Xop 1 - Xop 0) := by
  rw [zq_eq]
  apply Matrix.ext; intro i j; revert i j; decide

private lemma xr_eq :
    lieBracket (lieBracket Yp X1) Yq = (4 : ℤ) • (Xop 3 - Xop 2 - Xop 1 + Xop 0) := by
  rw [zp_eq]
  apply Matrix.ext; intro i j; revert i j; decide

/-- Hadamard recovery of all four individual X_a from {Ui, Ut, Uc, Uiᵀ, Utᵀ, Ucᵀ} brackets. -/
theorem hadamard_recovers_local_sl2 :
    let Zp := lieBracket Yp X1
    let Zq := lieBracket Yq X1
    let Xp := lieBracket Zp Y1
    let Xq := lieBracket Zq Y1
    let Xr := lieBracket Zp Yq
    (16 : ℤ) • Xop 3 = (4 : ℤ) • X1 + Xp + Xq + Xr ∧
    (16 : ℤ) • Xop 2 = (4 : ℤ) • X1 - Xp + Xq - Xr ∧
    (16 : ℤ) • Xop 1 = (4 : ℤ) • X1 + Xp - Xq - Xr ∧
    (16 : ℤ) • Xop 0 = (4 : ℤ) • X1 - Xp - Xq + Xr := by
  dsimp
  rw [xp_eq, xq_eq, xr_eq, x1_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply Matrix.ext
    intro i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring

/-- §73 Obstruction: primitive transverse flips have the A₂ weight projections under H₁, H₂,
    yet commute with one another ([E_F⁺, E_t⁺] = 0), and H₀ = Z_F + Z_t - Z_f separates the two
    zero-weight states |001⟩ (-3) and |110⟩ (+3). -/
theorem primitive_flips_are_su2_cubed_not_su3 :
    lieBracket (EPlus 2) (EPlus 1) = 0 ∧
    (Zop 2 + Zop 1 - Zop 0) 1 1 = -3 ∧
    (Zop 2 + Zop 1 - Zop 0) 6 6 = 3 := by
  refine ⟨?_, ?_, ?_⟩
  · apply Matrix.ext; intro i j; revert i j; decide
  · decide
  · decide

end Imscribing.Millennium.RetractionPolarization