import Imscribing.Millennium.Spin10ChiralFock
import Imscribing.Millennium.CurvatureLieAlgebra

namespace Imscribing.Millennium.Spin10Intertwiner

open Imscribing.Millennium.Spin10ChiralFock
open Imscribing.Millennium.CurvatureLieAlgebra

/-! ## Part 1: Explicit Intertwiner Φ : ℂ¹⁶ → S⁺₁₀ ⊂ ℂ³² (§95) -/

def phiMat : Matrix (Fin 32) (Fin 16) ℤ :=
  fun y x => if lToFockEven x = y then 1 else 0

def phiInvMat : Matrix (Fin 16) (Fin 32) ℤ :=
  fun x y => if lToFockEven x = y then 1 else 0

def P_even : Matrix (Fin 32) (Fin 32) ℤ :=
  fun y₁ y₂ => if y₁ = y₂ ∧ parity5 y₁ = 0 then 1 else 0

def conj32 (O : Matrix (Fin 16) (Fin 16) ℤ) : Matrix (Fin 32) (Fin 32) ℤ :=
  phiMat * O * phiInvMat

theorem phiInv_mul_phi : phiInvMat * phiMat = 1 := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, phiInvMat, phiMat, Matrix.one_apply]
  rw [Finset.sum_eq_single (lToFockEven i)]
  · simp only [ite_true, one_mul]
    by_cases hij : i = j
    · subst hij; simp
    · have hne : lToFockEven j ≠ lToFockEven i := by
        intro heq; apply hij
        calc i = fockEvenToL (lToFockEven i) := (fock_bijection_left i).symm
             _ = fockEvenToL (lToFockEven j) := by rw [heq]
             _ = j := fock_bijection_left j
      simp [hij, hne]
  · intro y _ hy
    simp [hy.symm]
  · intro hm; exact absurd (Finset.mem_univ _) hm

theorem phi_mul_phiInv : phiMat * phiInvMat = P_even := by
  apply Matrix.ext
  intro y₁ y₂
  simp only [Matrix.mul_apply, phiMat, phiInvMat, P_even]
  by_cases h1 : parity5 y₁ = 0
  · have hy1 : lToFockEven (fockEvenToL y₁) = y₁ := fock_bijection_right y₁ h1
    rw [Finset.sum_eq_single (fockEvenToL y₁)]
    · by_cases heq : y₁ = y₂
      · subst heq; simp [hy1, h1]
      · have hne : lToFockEven (fockEvenToL y₁) ≠ y₂ := by rw [hy1]; exact heq
        simp [heq, h1, hne]
    · intro x _ hx
      have hne : lToFockEven x ≠ y₁ := by
        intro heq; apply hx
        calc x = fockEvenToL (lToFockEven x) := (fock_bijection_left x).symm
             _ = fockEvenToL y₁ := by rw [heq]
      simp [hne]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · have hzero : ∀ x : Fin 16, lToFockEven x ≠ y₁ := by
      intro x heq
      have hp := fock_even_parity x
      rw [heq] at hp
      exact h1 hp
    simp [h1, hzero]

theorem conj32_entry (O : Matrix (Fin 16) (Fin 16) ℤ) (y₁ y₂ : Fin 32) :
    conj32 O y₁ y₂ =
      if parity5 y₁ = 0 ∧ parity5 y₂ = 0 then O (fockEvenToL y₁) (fockEvenToL y₂) else 0 := by
  simp only [conj32, Matrix.mul_apply, phiMat, phiInvMat]
  by_cases h2 : parity5 y₂ = 0
  · have hy2 : lToFockEven (fockEvenToL y₂) = y₂ := fock_bijection_right y₂ h2
    rw [Finset.sum_eq_single (fockEvenToL y₂)]
    · simp only [hy2, ite_true, mul_one]
      by_cases h1 : parity5 y₁ = 0
      · have hy1 : lToFockEven (fockEvenToL y₁) = y₁ := fock_bijection_right y₁ h1
        rw [Finset.sum_eq_single (fockEvenToL y₁)]
        · simp [hy1, h1, h2]
        · intro x _ hx
          have hne : lToFockEven x ≠ y₁ := by
            intro heq; apply hx
            calc x = fockEvenToL (lToFockEven x) := (fock_bijection_left x).symm
                 _ = fockEvenToL y₁ := by rw [heq]
          simp [hne]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      · have hzero : ∀ x : Fin 16, lToFockEven x ≠ y₁ := by
          intro x heq
          have hp := fock_even_parity x
          rw [heq] at hp
          exact h1 hp
        simp [h1, hzero]
    · intro x _ hx
      have hne : lToFockEven x ≠ y₂ := by
        intro heq; apply hx
        calc x = fockEvenToL (lToFockEven x) := (fock_bijection_left x).symm
             _ = fockEvenToL y₂ := by rw [heq]
      simp [hne]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · have hzero : ∀ x : Fin 16, lToFockEven x ≠ y₂ := by
      intro x heq
      have hp := fock_even_parity x
      rw [heq] at hp
      exact h2 hp
    simp [h2, hzero]

theorem conj32_mul (A B : Matrix (Fin 16) (Fin 16) ℤ) :
    conj32 A * conj32 B = conj32 (A * B) := by
  simp only [conj32]
  calc phiMat * A * phiInvMat * (phiMat * B * phiInvMat)
      = phiMat * A * (phiInvMat * phiMat) * B * phiInvMat := by
          simp only [Matrix.mul_assoc]
    _ = phiMat * (A * B) * phiInvMat := by
          rw [phiInv_mul_phi, Matrix.mul_one]
          simp only [Matrix.mul_assoc]

theorem conj32_bracket (A B : Matrix (Fin 16) (Fin 16) ℤ) :
    lieBracket (conj32 A) (conj32 B) = conj32 (lieBracket A B) := by
  have hsub : conj32 (A * B - B * A) = conj32 (A * B) - conj32 (B * A) := by
    simp only [conj32, Matrix.mul_sub, Matrix.sub_mul]
  simp only [lieBracket, conj32_mul, hsub]

/-! ## Part 2: Hypercharge Commutator Test [6Y, Φ O Φ⁻¹] (§97) -/

def Y6_32 : Matrix (Fin 32) (Fin 32) ℤ := fun i j => if i = j then y6State i else 0
def Y6_16 : Matrix (Fin 16) (Fin 16) ℤ := fun i j => if i = j then y6State (lToFockEven i) else 0

theorem Y6_intertwine (O : Matrix (Fin 16) (Fin 16) ℤ) :
    lieBracket Y6_32 (conj32 O) = conj32 (lieBracket Y6_16 O) := by
  apply Matrix.ext
  intro y₁ y₂
  simp only [lieBracket, Matrix.sub_apply, Matrix.mul_apply, Y6_32]
  rw [Finset.sum_eq_single y₁, Finset.sum_eq_single y₂]
  · simp only [ite_true, one_mul, mul_one, conj32_entry]
    by_cases h : parity5 y₁ = 0 ∧ parity5 y₂ = 0
    · have hy1 : lToFockEven (fockEvenToL y₁) = y₁ := fock_bijection_right y₁ h.1
      have hy2 : lToFockEven (fockEvenToL y₂) = y₂ := fock_bijection_right y₂ h.2
      rw [if_pos h, if_pos h]
      simp only [Matrix.sub_apply, Matrix.mul_apply, Y6_16]
      rw [Finset.sum_eq_single (fockEvenToL y₁), Finset.sum_eq_single (fockEvenToL y₂)]
      · simp [hy1, hy2]
      · intro k _ hk; simp [hk]
      · intro hm; exact absurd (Finset.mem_univ _) hm
      · intro k _ hk; simp [hk.symm]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · simp [h]
  · intro k _ hk; simp [hk]
  · intro hm; exact absurd (Finset.mem_univ _) hm
  · intro k _ hk; simp [hk.symm]
  · intro hm; exact absurd (Finset.mem_univ _) hm

/-- The raw trilattice cover operators Ui, Ut, Uc do NOT commute with 6Y:
    all three shift hypercharge at (∅ → {T, e₅}) by +6. -/
theorem order_operators_break_hypercharge :
    lieBracket Y6_32 (conj32 Ui) ≠ 0 ∧
    lieBracket Y6_32 (conj32 Ut) ≠ 0 ∧
    lieBracket Y6_32 (conj32 Uc) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · intro h
    have h240 := congrFun (congrFun h 24) 0
    rw [Y6_intertwine] at h240
    revert h240
    decide

/-! ## Part 3: Splitting the T-Spine into SU(2)_L (ΔY = 0) and Spin(10)/SU(5) (ΔY = ±1) -/

def parity4 (x : Fin 16) : ℕ :=
  (x.val % 2 + (x.val / 2) % 2 + (x.val / 4) % 2 + (x.val / 8) % 2) % 2

/-- ΔY = 0 weak-isospin part of EPlus 3 / EMinus 3 (mode 3 ↔ mode 4 inside V₂). -/
def T_plus_weak : Matrix (Fin 16) (Fin 16) ℤ :=
  fun i j => if parity4 j = 1 then EPlus 3 i j else 0

def T_minus_weak : Matrix (Fin 16) (Fin 16) ℤ :=
  fun i j => if parity4 j = 0 then EMinus 3 i j else 0

def EPlus3_dY6 : Matrix (Fin 16) (Fin 16) ℤ :=
  fun i j => if parity4 j = 0 then EPlus 3 i j else 0

def T3_weak : Matrix (Fin 16) (Fin 16) ℤ := lieBracket T_plus_weak T_minus_weak

/-- Scaled electric charge 6Q = 3·T₃ + 6Y on L ≃ S⁺₁₀. -/
def Q_em_6 : Matrix (Fin 16) (Fin 16) ℤ := (3 : ℤ) • T3_weak + Y6_16

theorem tspine_splits_into_su2L_and_gut :
    EPlus 3 = T_plus_weak + EPlus3_dY6 ∧
    lieBracket Y6_16 T_plus_weak = 0 ∧
    lieBracket Y6_16 T_minus_weak = 0 ∧
    lieBracket Y6_32 (conj32 T_plus_weak) = 0 ∧
    lieBracket Y6_32 (conj32 T_minus_weak) = 0 := by
  have h0 : EPlus 3 = T_plus_weak + EPlus3_dY6 := by
    apply Matrix.ext; intro i j; revert i j; decide
  have h1 : lieBracket Y6_16 T_plus_weak = 0 := by
    apply Matrix.ext; intro i j; revert i j; decide
  have h2 : lieBracket Y6_16 T_minus_weak = 0 := by
    apply Matrix.ext; intro i j; revert i j; decide
  refine ⟨h0, h1, h2, ?_, ?_⟩
  · rw [Y6_intertwine, h1]; apply Matrix.ext; intro i j; simp [conj32_entry]
  · rw [Y6_intertwine, h2]; apply Matrix.ext; intro i j; simp [conj32_entry]

/-- The ΔY = 0 component of the T-spine closes the exact su(2)_L weak-isospin algebra. -/
theorem weak_su2_chevalley :
    lieBracket T_plus_weak T_minus_weak = T3_weak ∧
    lieBracket T3_weak T_plus_weak = (2 : ℤ) • T_plus_weak ∧
    lieBracket T3_weak T_minus_weak = (-2 : ℤ) • T_minus_weak := by
  refine ⟨rfl, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-- Exact electric charge eigenvalues 6Q = 3·T₃ + 6Y across all 16 Weyl states of S⁺₁₀:
    +4 (u), -2 (d), 0 (ν), -6 (e), -4 (uᶜ), +2 (dᶜ), +6 (eᶜ), 0 (νᶜ). -/
theorem electric_charge_spectrum_16 :
    Q_em_6 9 9 = 4 ∧ Q_em_6 10 10 = 4 ∧ Q_em_6 12 12 = 4 ∧
    Q_em_6 1 1 = -2 ∧ Q_em_6 2 2 = -2 ∧ Q_em_6 4 4 = -2 ∧
    Q_em_6 15 15 = 0 ∧ Q_em_6 7 7 = -6 ∧
    Q_em_6 3 3 = -4 ∧ Q_em_6 5 5 = -4 ∧ Q_em_6 6 6 = -4 ∧
    Q_em_6 11 11 = 2 ∧ Q_em_6 13 13 = 2 ∧ Q_em_6 14 14 = 2 ∧
    Q_em_6 8 8 = 6 ∧ Q_em_6 0 0 = 0 := by
  decide

/-- All V₃-coordinate flips (bits 0, 1, 2 = f, t, F) strictly shift hypercharge (leptoquark sector). -/
theorem v3_flips_never_preserve_hypercharge :
    ∀ a : Fin 3, ∀ i j : Fin 16, EPlus a.val i j ≠ 0 →
      y6State (lToFockEven i) ≠ y6State (lToFockEven j) := by
  decide

/-! ## Part 4: §90 Representation Mismatch: (2, 8) vs S⁺₁₀|_{G_SM} -/

theorem representation_mismatch_2x8_vs_spin10 :
    lieBracket Y6_16 (kron16 1 Ea1) ≠ 0 ∧
    lieBracket Y6_16 (kron16 1 Ea2) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h40 := congrFun (congrFun h 4) 0
    revert h40; decide
  · intro h
    have h20 := congrFun (congrFun h 2) 0
    revert h20; decide

end Imscribing.Millennium.Spin10Intertwiner