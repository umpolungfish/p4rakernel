import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic
set_option maxHeartbeats 800000


namespace Imscribing.TrilatticeYM



open Matrix
open scoped ComplexOrder

def pauli0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
def pauli1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def pauli2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def pauli3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem pauli0_eq_one : pauli0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli0]

theorem pauli_hermitian :
    pauli0.IsHermitian ∧ pauli1.IsHermitian ∧ pauli2.IsHermitian ∧ pauli3.IsHermitian := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauli0, pauli1, pauli2, pauli3])

theorem pauli_sq_one :
    pauli1 * pauli1 = 1 ∧ pauli2 * pauli2 = 1 ∧ pauli3 * pauli3 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> (ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauli1, pauli2, pauli3, Matrix.mul_apply, Fin.sum_univ_two])

theorem pauli_completeness (X : Matrix (Fin 2) (Fin 2) ℂ) :
    X + pauli1 * X * pauli1 + pauli2 * X * pauli2 + pauli3 * X * pauli3 =
      (2 * X.trace) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pauli1, pauli2, pauli3, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace,
      Matrix.diag_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, Fin.reduceFinMk] <;>
    norm_num <;> ring_nf <;> simp [Complex.I_sq] <;> ring

noncomputable def krausD : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => (Real.sqrt (5 / 14) : ℂ) • pauli0
  | 1 => (Real.sqrt (3 / 14) : ℂ) • pauli1
  | 2 => (Real.sqrt (3 / 14) : ℂ) • pauli2
  | 3 => (Real.sqrt (3 / 14) : ℂ) • pauli3

noncomputable def phiD (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ μ : Fin 4, krausD μ * X * (krausD μ)ᴴ

private lemma sqrt_rat_sq_complex (r : ℝ) (hr : 0 ≤ r) :
    (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
  norm_cast
  exact Real.mul_self_sqrt hr

theorem phiD_bistochastic :
    (∑ μ : Fin 4, (krausD μ)ᴴ * krausD μ = 1) ∧
    (∑ μ : Fin 4, krausD μ * (krausD μ)ᴴ = 1) := by
  have h0 : (krausD 0)ᴴ = krausD 0 := by
    simp [krausD, Matrix.conjTranspose_smul, pauli_hermitian.1.eq, Complex.star_def]
  have h1 : (krausD 1)ᴴ = krausD 1 := by
    simp [krausD, Matrix.conjTranspose_smul, pauli_hermitian.2.1.eq, Complex.star_def]
  have h2 : (krausD 2)ᴴ = krausD 2 := by
    simp [krausD, Matrix.conjTranspose_smul, pauli_hermitian.2.2.1.eq, Complex.star_def]
  have h3 : (krausD 3)ᴴ = krausD 3 := by
    simp [krausD, Matrix.conjTranspose_smul, pauli_hermitian.2.2.2.eq, Complex.star_def]
  have hsum : ∑ μ : Fin 4, krausD μ * krausD μ = 1 := by
    rw [Fin.sum_univ_four]
    simp only [krausD, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      pauli0_eq_one, pauli_sq_one.1, pauli_sq_one.2.1, pauli_sq_one.2.2, mul_one]
    rw [sqrt_rat_sq_complex (5 / 14) (by norm_num),
      sqrt_rat_sq_complex (3 / 14) (by norm_num)]
    rw [← add_smul, ← add_smul, ← add_smul]
    norm_num
  refine ⟨?_, ?_⟩
  · rw [Fin.sum_univ_four, h0, h1, h2, h3]; rw [Fin.sum_univ_four] at hsum; exact hsum
  · rw [Fin.sum_univ_four, h0, h1, h2, h3]; rw [Fin.sum_univ_four] at hsum; exact hsum

theorem phiD_depolarizing (X : Matrix (Fin 2) (Fin 2) ℂ) :
    phiD X = ((1 : ℂ) / 7) • X + ((3 : ℂ) / 7) • (X.trace • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  unfold phiD
  rw [Fin.sum_univ_four]
  have h0 : (krausD 0)ᴴ = krausD 0 := by
    simp [krausD, Matrix.conjTranspose_smul, pauli_hermitian.1.eq, Complex.star_def]
  have h1 : (krausD 1)ᴴ = krausD 1 := by
    simp [krausD, Matrix.conjTranspose_smul, pauli_hermitian.2.1.eq, Complex.star_def]
  have h2 : (krausD 2)ᴴ = krausD 2 := by
    simp [krausD, Matrix.conjTranspose_smul, pauli_hermitian.2.2.1.eq, Complex.star_def]
  have h3 : (krausD 3)ᴴ = krausD 3 := by
    simp [krausD, Matrix.conjTranspose_smul, pauli_hermitian.2.2.2.eq, Complex.star_def]
  rw [h0, h1, h2, h3]
  simp only [krausD, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pauli0_eq_one, one_mul, mul_one]
  rw [sqrt_rat_sq_complex (5 / 14) (by norm_num),
    sqrt_rat_sq_complex (3 / 14) (by norm_num)]
  have hcomp := pauli_completeness X
  have hsum :
      pauli1 * X * pauli1 + pauli2 * X * pauli2 + pauli3 * X * pauli3 =
        (2 * X.trace) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - X := by
    rw [← hcomp]; abel
  push_cast
  have hgrp :
      ((5 : ℂ) / 14) • X + ((3 : ℂ) / 14) • (pauli1 * X * pauli1) +
        ((3 : ℂ) / 14) • (pauli2 * X * pauli2) + ((3 : ℂ) / 14) • (pauli3 * X * pauli3) =
      ((5 : ℂ) / 14) • X + ((3 : ℂ) / 14) • (pauli1 * X * pauli1 + pauli2 * X * pauli2 + pauli3 * X * pauli3) := by
    simp only [smul_add, add_assoc]
  rw [hgrp, hsum]
  ext i j
  simp [Matrix.one_apply]
  split_ifs <;> ring

theorem phiD_eigenvalues :
    phiD pauli0 = pauli0 ∧
    phiD pauli1 = ((1 : ℂ) / 7) • pauli1 ∧
    phiD pauli2 = ((1 : ℂ) / 7) • pauli2 ∧
    phiD pauli3 = ((1 : ℂ) / 7) • pauli3 := by
  have ht0 : pauli0.trace = 2 := by simp [pauli0, Matrix.trace]; norm_num
  have ht1 : pauli1.trace = 0 := by simp [pauli1, Matrix.trace]
  have ht2 : pauli2.trace = 0 := by simp [pauli2, Matrix.trace]
  have ht3 : pauli3.trace = 0 := by simp [pauli3, Matrix.trace]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [phiD_depolarizing, ht0, pauli0_eq_one]; ext i j; simp; ring
  · rw [phiD_depolarizing, ht1]; simp
  · rw [phiD_depolarizing, ht2]; simp
  · rw [phiD_depolarizing, ht3]; simp

theorem phiD_unitary_covariant (U X : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1) :
    phiD (U * X * Uᴴ) = U * phiD X * Uᴴ := by
  have htr : (U * X * Uᴴ).trace = X.trace := by
    rw [Matrix.trace_mul_cycle, hU', Matrix.one_mul]
  rw [phiD_depolarizing, phiD_depolarizing, htr]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [Matrix.mul_one, hU]



theorem phiD_dirichlet_identity (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (Xᴴ * (X - phiD X)).trace =
      ((6 : ℂ) / 7) *
        ((X - (X.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ *
          (X - (X.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ))).trace := by
  set X0 := X - (X.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  have hdiff : X - phiD X = ((6 : ℂ) / 7) • X0 := by
    rw [phiD_depolarizing]
    ext i j
    simp only [X0, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> ring
  have hX : X = X0 + (X.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by simp [X0]
  have htr0 : X0.trace = 0 := by
    simp [X0, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
  rw [hdiff, Matrix.mul_smul, Matrix.trace_smul, hX]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_add, Matrix.trace_smul]
  rw [htr0, smul_zero, add_zero, smul_eq_mul]


noncomputable def omega3 : ℂ := (-1 + Complex.I * Real.sqrt 3) / 2

theorem omega3_props :
    omega3 * star omega3 = 1 ∧ 1 + 2 * omega3 = Complex.I * Real.sqrt 3 := by
  constructor
  · unfold omega3
    simp [Complex.star_def, Complex.conj_ofReal]
    ring_nf
    rw [Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  · unfold omega3; ring

noncomputable def psiSIC : Fin 4 → (Fin 2 → ℂ)
  | 0 => ![1, 0]
  | 1 => ![(1 : ℂ) / Real.sqrt 3, (Real.sqrt 2 : ℂ) / Real.sqrt 3]
  | 2 => ![(1 : ℂ) / Real.sqrt 3, (Real.sqrt 2 : ℂ) * omega3 / Real.sqrt 3]
  | 3 => ![(1 : ℂ) / Real.sqrt 3, (Real.sqrt 2 : ℂ) * star omega3 / Real.sqrt 3]

noncomputable def overlapSIC (i j : Fin 4) : ℂ := star (psiSIC i) ⬝ᵥ psiSIC j

theorem overlapSIC_diag (i : Fin 4) : overlapSIC i i = 1 := by
  have h2sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast; exact Real.sq_sqrt (by norm_num)
  have h3sq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    norm_cast; exact Real.sq_sqrt (by norm_num)
  have h3ne : (Real.sqrt 3 : ℂ) ≠ 0 := by norm_cast; positivity
  fin_cases i
  · simp [overlapSIC, psiSIC, dotProduct, Fin.sum_univ_two]
  · simp [overlapSIC, psiSIC, dotProduct, Fin.sum_univ_two, Complex.star_def, Complex.conj_ofReal]
    field_simp [h3ne]; rw [h2sq, h3sq]; norm_num
  · have hω' : star omega3 * omega3 = 1 := by rw [mul_comm]; exact omega3_props.1
    simp [overlapSIC, psiSIC, dotProduct, Fin.sum_univ_two, Complex.star_def, Complex.conj_ofReal]
    field_simp [h3ne]
    rw [h2sq, h3sq, show (starRingEnd ℂ) omega3 = star omega3 from rfl, mul_assoc, hω']
    norm_num
  · have hω := omega3_props.1
    simp [overlapSIC, psiSIC, dotProduct, Fin.sum_univ_two, Complex.star_def, Complex.conj_ofReal]
    field_simp [h3ne]
    rw [h2sq, h3sq, show (starRingEnd ℂ) omega3 = star omega3 from rfl, mul_assoc, hω]
    norm_num

theorem overlapSIC_normSq_offdiag :
    overlapSIC 0 1 * star (overlapSIC 0 1) = (1 : ℂ) / 3 ∧
    overlapSIC 1 2 * star (overlapSIC 1 2) = (1 : ℂ) / 3 := by
  have h2sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast; exact Real.sq_sqrt (by norm_num)
  have h3sq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    norm_cast; exact Real.sq_sqrt (by norm_num)
  have h3ne : (Real.sqrt 3 : ℂ) ≠ 0 := by norm_cast; positivity
  constructor
  · simp [overlapSIC, psiSIC, dotProduct, Fin.sum_univ_two, Complex.star_def, Complex.conj_ofReal]
    field_simp [h3ne]; rw [h3sq]
  · have h12 : overlapSIC 1 2 = Complex.I / Real.sqrt 3 := by
      simp [overlapSIC, psiSIC, dotProduct, Fin.sum_univ_two, Complex.star_def, Complex.conj_ofReal]
      field_simp [h3ne]
      rw [h2sq, omega3_props.2, mul_comm]
    rw [h12]
    simp [Complex.star_def, Complex.conj_ofReal]
    field_simp [h3ne]
    rw [Complex.I_sq, h3sq]
    norm_num

abbrev MatN (N : ℕ) := Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ

def hsInner {N : ℕ} (X Y : MatN N) : ℝ :=
  ∑ f : Fin N → Fin 2, ∑ g : Fin N → Fin 2,
    ((X f g).re * (Y f g).re + (X f g).im * (Y f g).im)

theorem hsInner_self_nonneg {N : ℕ} (X : MatN N) : 0 ≤ hsInner X X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

theorem hsInner_zero_right {N : ℕ} (X : MatN N) : hsInner X 0 = 0 := by
  simp [hsInner]

theorem hsInner_add_left {N : ℕ} (X Y Z : MatN N) :
    hsInner (X + Y) Z = hsInner X Z + hsInner Y Z := by
  have h : ∀ f g : Fin N → Fin 2,
      ((X + Y) f g).re * (Z f g).re + ((X + Y) f g).im * (Z f g).im =
        ((X f g).re * (Z f g).re + (X f g).im * (Z f g).im) +
        ((Y f g).re * (Z f g).re + (Y f g).im * (Z f g).im) := fun f g => by
    simp [Complex.add_re, Complex.add_im]; ring
  simp only [hsInner, h]
  simp_rw [Finset.sum_add_distrib]

theorem hsInner_add_right {N : ℕ} (X Y Z : MatN N) :
    hsInner X (Y + Z) = hsInner X Y + hsInner X Z := by
  have h : ∀ f g : Fin N → Fin 2,
      (X f g).re * ((Y + Z) f g).re + (X f g).im * ((Y + Z) f g).im =
        ((X f g).re * (Y f g).re + (X f g).im * (Y f g).im) +
        ((X f g).re * (Z f g).re + (X f g).im * (Z f g).im) := fun f g => by
    simp [Complex.add_re, Complex.add_im]; ring
  simp only [hsInner, h]
  simp_rw [Finset.sum_add_distrib]

theorem hsInner_sub_right {N : ℕ} (X Y Z : MatN N) :
    hsInner X (Y - Z) = hsInner X Y - hsInner X Z := by
  have h : ∀ f g : Fin N → Fin 2,
      (X f g).re * ((Y - Z) f g).re + (X f g).im * ((Y - Z) f g).im =
        ((X f g).re * (Y f g).re + (X f g).im * (Y f g).im) -
        ((X f g).re * (Z f g).re + (X f g).im * (Z f g).im) := fun f g => by
    simp [Complex.sub_re, Complex.sub_im]; ring
  simp only [hsInner, h]
  simp_rw [Finset.sum_sub_distrib]

theorem hsInner_smul_real_right {N : ℕ} (r : ℝ) (X Y : MatN N) :
    hsInner X ((r : ℂ) • Y) = r * hsInner X Y := by
  simp only [hsInner, Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => by ring

theorem hsInner_comm {N : ℕ} (X Y : MatN N) : hsInner X Y = hsInner Y X := by
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => by ring

theorem hsInner_eq_trace_re {N : ℕ} (X Y : MatN N) :
    ((Xᴴ * Y).trace).re = hsInner X Y := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, hsInner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => by ring

noncomputable def partialTraceProj (N : ℕ) (k : Fin N) (X : MatN N) : MatN N :=
  fun f g => if f k = g k then
    ((1 : ℂ) / 2) * ∑ b : Fin 2, X (Function.update f k b) (Function.update g k b) else 0

noncomputable def partialTraceProjLM (N : ℕ) (k : Fin N) : MatN N →ₗ[ℂ] MatN N where
  toFun := partialTraceProj N k
  map_add' X Y := by
    ext f g
    by_cases h : f k = g k <;>
      simp [partialTraceProj, h, Finset.sum_add_distrib, mul_add]
  map_smul' c X := by
    ext f g
    by_cases h : f k = g k <;>
      simp [partialTraceProj, h, Finset.mul_sum] <;> ring

noncomputable def phiSiteLM (N : ℕ) (k : Fin N) : MatN N →ₗ[ℂ] MatN N :=
  ((1 : ℂ) / 7) • LinearMap.id + ((6 : ℂ) / 7) • partialTraceProjLM N k

theorem partialTraceProj_idem (N : ℕ) (k : Fin N) (X : MatN N) :
    partialTraceProj N k (partialTraceProj N k X) = partialTraceProj N k X := by
  ext f g
  unfold partialTraceProj
  split_ifs with hfg
  · have hsum :
        ∑ b : Fin 2,
          (if Function.update f k b k = Function.update g k b k then
            ((1 : ℂ) / 2) * ∑ c : Fin 2,
              X (Function.update (Function.update f k b) k c)
                (Function.update (Function.update g k b) k c)
           else 0) =
        ∑ b : Fin 2, ((1 : ℂ) / 2) * ∑ c : Fin 2,
          X (Function.update f k c) (Function.update g k c) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [Function.update_self, Function.update_idem]
    rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [nsmul_eq_mul]
  · rfl

theorem partialTraceProj_comm (N : ℕ) (k l : Fin N) (hkl : k ≠ l) (X : MatN N) :
    partialTraceProj N k (partialTraceProj N l X) =
      partialTraceProj N l (partialTraceProj N k X) := by
  ext f g
  unfold partialTraceProj
  by_cases hfk : f k = g k <;> by_cases hfl : f l = g l
  · simp only [hfk, hfl, ↓reduceIte]
    have hl : ∀ b : Fin 2, Function.update f k b l = Function.update g k b l := by
      intro b; simp [Function.update_of_ne hkl.symm, hfl]
    have hk : ∀ c : Fin 2, Function.update f l c k = Function.update g l c k := by
      intro c; simp [Function.update_of_ne hkl, hfk]
    simp only [hl, hk, ↓reduceIte]
    simp only [← Finset.mul_sum]
    congr 1; congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [Function.update_comm hkl.symm, Function.update_comm hkl.symm]
  · simp only [hfk, hfl, ↓reduceIte]
    have hl : ∀ b : Fin 2, ¬ (Function.update f k b l = Function.update g k b l) := by
      intro b; simp [Function.update_of_ne hkl.symm, hfl]
    simp [hl]
  · simp only [hfk, hfl, ↓reduceIte]
    have hk : ∀ c : Fin 2, ¬ (Function.update f l c k = Function.update g l c k) := by
      intro c; simp [Function.update_of_ne hkl, hfk]
    simp [hk]
  · simp [hfk, hfl]

theorem partialTraceProj_conjTranspose (N : ℕ) (k : Fin N) (X : MatN N) :
    (partialTraceProj N k X)ᴴ = partialTraceProj N k (Xᴴ) := by
  ext f g
  simp only [Matrix.conjTranspose_apply, partialTraceProj]
  by_cases h : f k = g k
  · have hhalf : star (1 / 2 : ℂ) = 1 / 2 := by simp [Complex.star_def]
    rw [if_pos h, if_pos h.symm]
    simp only [StarMul.star_mul, star_sum, hhalf]
    ring
  · have h' : ¬(g k = f k) := fun h_eq => h h_eq.symm
    rw [if_neg h, if_neg h']
    simp only [star_zero]

theorem partialTraceProj_selfAdjoint (N : ℕ) (k : Fin N) (X Y : MatN N) :
    hsInner (partialTraceProj N k X) Y = hsInner X (partialTraceProj N k Y) := by
  rw [← hsInner_eq_trace_re, ← hsInner_eq_trace_re, partialTraceProj_conjTranspose]
  congr 1
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, partialTraceProj,
    Matrix.conjTranspose_apply]
  have h1 :
      (∑ f : Fin N → Fin 2, ∑ g : Fin N → Fin 2,
        (if f k = g k then
          (1 / 2 : ℂ) * ∑ b : Fin 2, star (X (Function.update g k b) (Function.update f k b))
         else 0) * Y g f) =
      ∑ t : (Fin N → Fin 2) × (Fin N → Fin 2) × Fin 2,
        if t.1 k = t.2.1 k then
          (1 / 2 : ℂ) * star (X (Function.update t.2.1 k t.2.2) (Function.update t.1 k t.2.2)) * Y t.2.1 t.1
        else 0 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hfg : f k = g k
    · simp only [hfg, ↓reduceIte, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    · simp only [hfg, ↓reduceIte, zero_mul, Finset.sum_const_zero]
  have h2 :
      (∑ f : Fin N → Fin 2, ∑ g : Fin N → Fin 2,
        star (X g f) *
          (if g k = f k then
            (1 / 2 : ℂ) * ∑ b : Fin 2, Y (Function.update g k b) (Function.update f k b)
           else 0)) =
      ∑ t : (Fin N → Fin 2) × (Fin N → Fin 2) × Fin 2,
        if t.1 k = t.2.1 k then
          (1 / 2 : ℂ) * star (X t.2.1 t.1) * Y (Function.update t.2.1 k t.2.2) (Function.update t.1 k t.2.2)
        else 0 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hfg : g k = f k
    · simp only [hfg, ↓reduceIte, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => by ring
    · have h_not : ¬(g k = f k) := hfg
      have h_not' : ¬(f k = g k) := fun h => h_not h.symm
      rw [if_neg h_not]
      simp only [mul_zero]
      refine (Finset.sum_eq_zero fun b _ => ?_).symm
      rw [if_neg h_not']
  rw [h1, h2]
  have h_restore (f : Fin N → Fin 2) (b : Fin 2) :
      Function.update (Function.update f k b) k (f k) = f := by
    ext x
    by_cases hx : x = k
    · subst hx; simp [Function.update_self]
    · simp [Function.update_of_ne hx]
  let e : ((Fin N → Fin 2) × (Fin N → Fin 2) × Fin 2) ≃
      ((Fin N → Fin 2) × (Fin N → Fin 2) × Fin 2) :=
    { toFun := fun ⟨f, g, b⟩ =>
        if f k = g k then (Function.update f k b, Function.update g k b, f k) else (f, g, b)
      invFun := fun ⟨f, g, b⟩ =>
        if f k = g k then (Function.update f k b, Function.update g k b, f k) else (f, g, b)
      left_inv := by
        rintro ⟨f, g, b⟩
        dsimp
        by_cases h : f k = g k
        · rw [if_pos h]
          have h_eq : Function.update f k b k = Function.update g k b k := by
            simp only [Function.update_self]
          rw [if_pos h_eq]
          dsimp
          rw [h_restore f b, h, h_restore g b, Function.update_self]
        · rw [if_neg h, if_neg h]
      right_inv := by
        rintro ⟨f, g, b⟩
        dsimp
        by_cases h : f k = g k
        · rw [if_pos h]
          have h_eq : Function.update f k b k = Function.update g k b k := by
            simp only [Function.update_self]
          rw [if_pos h_eq]
          dsimp
          rw [h_restore f b, h, h_restore g b, Function.update_self]
        · rw [if_neg h, if_neg h] }
  rw [Fintype.sum_equiv e]
  rintro ⟨f, g, b⟩
  dsimp [e]
  by_cases h : f k = g k
  · rw [if_pos h]
    simp [h_restore f b]
    try rw [Function.update_eq_self]
    rw [h]
    simp
    left
    congr 1
    ext x
    by_cases hx : x = k
    · subst hx; simp [h]
    · simp [Function.update_of_ne hx]
  · simp [h]


noncomputable def phiList (N : ℕ) : List (Fin N) → (MatN N →ₗ[ℂ] MatN N)
  | [] => LinearMap.id
  | k :: L => phiList N L ∘ₗ phiSiteLM N k

noncomputable def projList (N : ℕ) : List (Fin N) → (MatN N →ₗ[ℂ] MatN N)
  | [] => LinearMap.id
  | k :: L => projList N L ∘ₗ partialTraceProjLM N k

theorem phiSite_comm_partialTrace {N : ℕ} {k l : Fin N} (hkl : k ≠ l) (X : MatN N) :
    phiSiteLM N k (partialTraceProj N l X) = partialTraceProj N l (phiSiteLM N k X) := by
  ext f g
  simp only [phiSiteLM, partialTraceProjLM, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.coe_mk, AddHom.coe_mk, Matrix.add_apply, Matrix.smul_apply,
    partialTraceProj, smul_eq_mul]
  by_cases hfk : f k = g k <;> by_cases hfl : f l = g l
  · simp only [hfk, hfl, ↓reduceIte]
    have hl : ∀ b : Fin 2, Function.update f k b l = Function.update g k b l := by
      intro b; simp [Function.update_of_ne hkl.symm, hfl]
    have hk : ∀ c : Fin 2, Function.update f l c k = Function.update g l c k := by
      intro c; simp [Function.update_of_ne hkl, hfk]
    simp only [hl, hk, ↓reduceIte, Function.update_comm hkl, Fin.sum_univ_two]
    ring
  · simp only [hfk, hfl, ↓reduceIte]
    have hl : ∀ b : Fin 2, ¬ Function.update f k b l = Function.update g k b l := by
      intro b; simp [Function.update_of_ne hkl.symm, hfl]
    simp only [hl, ↓reduceIte, mul_zero, Finset.sum_const_zero, add_zero]
  · simp only [hfk, hfl, ↓reduceIte]
    have hk : ∀ c : Fin 2, ¬ Function.update f l c k = Function.update g l c k := by
      intro c; simp [Function.update_of_ne hkl, hfk]
    simp only [hk, ↓reduceIte, mul_zero, add_zero, Fin.sum_univ_two]
    ring
  · simp only [hfk, hfl, ↓reduceIte, mul_zero, add_zero]
theorem phiList_comm_partialTrace {N : ℕ} (k : Fin N) :
    ∀ (L : List (Fin N)), k ∉ L → ∀ X : MatN N,
      phiList N L (partialTraceProj N k X) = partialTraceProj N k (phiList N L X)
  | [], _, _ => rfl
  | l :: L, hk, X => by
      have hkl : k ≠ l := fun h => hk (by simp [h])
      have hkL : k ∉ L := fun h => hk (by simp [h])
      simp only [phiList, LinearMap.comp_apply]
      rw [phiSite_comm_partialTrace hkl.symm X]
      exact phiList_comm_partialTrace k L hkL (phiSiteLM N l X)

theorem projList_comm_partialTrace {N : ℕ} (k : Fin N) :
    ∀ (L : List (Fin N)), k ∉ L → ∀ X : MatN N,
      projList N L (partialTraceProj N k X) = partialTraceProj N k (projList N L X)
  | [], _, _ => rfl
  | l :: L, hk, X => by
      have hkl : k ≠ l := fun h => hk (by simp [h])
      have hkL : k ∉ L := fun h => hk (by simp [h])
      simp only [projList, LinearMap.comp_apply]
      change projList N L (partialTraceProj N l (partialTraceProj N k X)) =
        partialTraceProj N k (projList N L (partialTraceProj N l X))
      rw [partialTraceProj_comm N l k hkl.symm X]
      exact projList_comm_partialTrace k L hkL (partialTraceProj N l X)

theorem partialTraceProj_pythag {N : ℕ} (k : Fin N) (X : MatN N) :
    hsInner X X =
      hsInner (partialTraceProj N k X) (partialTraceProj N k X) +
        hsInner (X - partialTraceProj N k X) (X - partialTraceProj N k X) := by
  set X₁ := partialTraceProj N k X
  set X₂ := X - X₁
  have hX : X = X₁ + X₂ := by simp [X₂]
  have hPX₁ : partialTraceProj N k X₁ = X₁ := partialTraceProj_idem N k X
  have hPX₂ : partialTraceProj N k X₂ = 0 := by
    change partialTraceProjLM N k (X - X₁) = 0
    rw [LinearMap.map_sub]
    change partialTraceProj N k X - partialTraceProj N k X₁ = 0
    rw [hPX₁, sub_self]
  have horth12 : hsInner X₁ X₂ = 0 := by
    rw [← hPX₁, partialTraceProj_selfAdjoint, hPX₂, hsInner_zero_right]
  have horth21 : hsInner X₂ X₁ = 0 := by
    rw [hsInner_comm]; exact horth12
  nth_rw 1 2 [hX]
  rw [hsInner_add_left, hsInner_add_right, hsInner_add_right, horth12, horth21]
  ring

theorem phiList_bounds (N : ℕ) :
    ∀ (L : List (Fin N)), L.Nodup → ∀ X : MatN N,
      0 ≤ hsInner X (phiList N L X) ∧
      hsInner X (phiList N L X) ≤ hsInner X X ∧
      ((6 : ℝ) / 7) * hsInner (X - projList N L X) (X - projList N L X) ≤
        hsInner X (X - phiList N L X)
  | [], _, X => by
      simp only [phiList, projList, LinearMap.id_apply, sub_self, hsInner_zero_right, mul_zero]
      exact ⟨hsInner_self_nonneg X, le_rfl, le_rfl⟩
  | k :: L, hnd, X => by
      rw [List.nodup_cons] at hnd
      rcases hnd with ⟨hkL, hLnd⟩
      set X₁ := partialTraceProj N k X
      set X₂ := X - X₁
      have hX : X = X₁ + X₂ := by simp [X₂]
      have hPX₁ : partialTraceProj N k X₁ = X₁ := partialTraceProj_idem N k X
      have hPX₂ : partialTraceProj N k X₂ = 0 := by
        change partialTraceProjLM N k (X - X₁) = 0
        rw [LinearMap.map_sub]
        change partialTraceProj N k X - partialTraceProj N k X₁ = 0
        rw [hPX₁, sub_self]
      have hsite : phiSiteLM N k X = X₁ + ((1 : ℂ) / 7) • X₂ := by
        change ((1 : ℂ) / 7) • X + ((6 : ℂ) / 7) • X₁ = X₁ + ((1 : ℂ) / 7) • (X - X₁)
        ext f g
        simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        ring
      have hT : phiList N (k :: L) X =
          phiList N L X₁ + ((1 : ℂ) / 7) • phiList N L X₂ := by
        simp only [phiList, LinearMap.comp_apply, hsite, LinearMap.map_add, LinearMap.map_smul]
      have horth_1_T2 : hsInner X₁ (phiList N L X₂) = 0 := by
        rw [← hPX₁, partialTraceProj_selfAdjoint, ← phiList_comm_partialTrace k L hkL X₂,
          hPX₂, LinearMap.map_zero, hsInner_zero_right]
      have horth_2_T1 : hsInner X₂ (phiList N L X₁) = 0 := by
        have hfix : partialTraceProj N k (phiList N L X₁) = phiList N L X₁ := by
          rw [← phiList_comm_partialTrace k L hkL X₁, hPX₁]
        rw [← hfix, hsInner_comm, partialTraceProj_selfAdjoint, hPX₂, hsInner_zero_right]
      have hinner_T :
          hsInner X (phiList N (k :: L) X) =
            hsInner X₁ (phiList N L X₁) + (1 / 7 : ℝ) * hsInner X₂ (phiList N L X₂) := by
        calc
          hsInner X (phiList N (k :: L) X)
            = hsInner (X₁ + X₂) (phiList N L X₁ + ((1 : ℂ) / 7) • phiList N L X₂) := by
                nth_rw 1 [hX]; rw [hT]
          _ = hsInner X₁ (phiList N L X₁) + hsInner X₁ (((1 : ℂ) / 7) • phiList N L X₂) +
                (hsInner X₂ (phiList N L X₁) + hsInner X₂ (((1 : ℂ) / 7) • phiList N L X₂)) := by
                rw [hsInner_add_left, hsInner_add_right, hsInner_add_right]
          _ = hsInner X₁ (phiList N L X₁) + (1 / 7 : ℝ) * hsInner X₂ (phiList N L X₂) := by
                have hsmul1 : ((1 : ℂ) / 7) = (((1 / 7 : ℝ) : ℂ)) := by push_cast; rfl
                rw [hsmul1, hsInner_smul_real_right, hsInner_smul_real_right,
                  horth_1_T2, horth_2_T1]
                ring
      have ih1 := phiList_bounds N L hLnd X₁
      have ih2 := phiList_bounds N L hLnd X₂
      have hpy : hsInner X X = hsInner X₁ X₁ + hsInner X₂ X₂ := partialTraceProj_pythag k X
      have h0le : 0 ≤ hsInner X (phiList N (k :: L) X) := by
        rw [hinner_T]; linarith [ih1.1, ih2.1]
      have hleX : hsInner X (phiList N (k :: L) X) ≤ hsInner X X := by
        rw [hinner_T]
        linarith [ih1.2.1, ih2.2.1, ih2.1]
      have hsub1 : hsInner X (X - phiList N (k :: L) X) =
          hsInner X X - hsInner X (phiList N (k :: L) X) := hsInner_sub_right _ _ _
      have hsub2 : hsInner X₁ (X₁ - phiList N L X₁) =
          hsInner X₁ X₁ - hsInner X₁ (phiList N L X₁) := hsInner_sub_right _ _ _
      have hdiff_split :
          hsInner X (X - phiList N (k :: L) X) =
            hsInner X₁ (X₁ - phiList N L X₁) +
              (hsInner X₂ X₂ - (1 / 7 : ℝ) * hsInner X₂ (phiList N L X₂)) := by
        rw [hsub1, hinner_T, hpy, hsub2]
        ring
      have hQ_split :
          X - projList N (k :: L) X = (X₁ - projList N L X₁) + X₂ := by
        have hQL : projList N (k :: L) X = projList N L X₁ := by
          simp [projList, X₁, partialTraceProjLM]
        rw [hQL]
        nth_rw 1 [hX]
        abel
      have hPQ₁ : partialTraceProj N k (X₁ - projList N L X₁) = X₁ - projList N L X₁ := by
        change partialTraceProjLM N k (X₁ - projList N L X₁) = X₁ - projList N L X₁
        rw [LinearMap.map_sub]
        change partialTraceProj N k X₁ - partialTraceProj N k (projList N L X₁) = X₁ - projList N L X₁
        rw [← projList_comm_partialTrace k L hkL X₁, hPX₁]
      have horth_Q : hsInner (X₁ - projList N L X₁) X₂ = 0 := by
        rw [← hPQ₁, partialTraceProj_selfAdjoint, hPX₂, hsInner_zero_right]
      have horth_Q' : hsInner X₂ (X₁ - projList N L X₁) = 0 := by
        rw [hsInner_comm]; exact horth_Q
      have hnormQ :
          hsInner (X - projList N (k :: L) X) (X - projList N (k :: L) X) =
            hsInner (X₁ - projList N L X₁) (X₁ - projList N L X₁) + hsInner X₂ X₂ := by
        rw [hQ_split, hsInner_add_left, hsInner_add_right, hsInner_add_right, horth_Q, horth_Q']
        ring
      have hstep2 : (6 / 7 : ℝ) * hsInner X₂ X₂ ≤
          hsInner X₂ X₂ - (1 / 7 : ℝ) * hsInner X₂ (phiList N L X₂) := by
        linarith [ih2.2.1]
      refine ⟨h0le, hleX, ?_⟩
      rw [hdiff_split, hnormQ]
      linarith [ih1.2.2, hstep2]

noncomputable def phiTensor (N : ℕ) : MatN N →ₗ[ℂ] MatN N :=
  phiList N (List.finRange N)

noncomputable def tauProj (N : ℕ) : MatN N →ₗ[ℂ] MatN N :=
  projList N (List.finRange N)

theorem phiTensor_uniform_dirichlet_gap (N : ℕ) (X : MatN N) :
    ((6 : ℝ) / 7) * hsInner (X - tauProj N X) (X - tauProj N X) ≤
      hsInner X (X - phiTensor N X) :=
  (phiList_bounds N (List.finRange N) (List.nodup_finRange N) X).2.2

end Imscribing.TrilatticeYM