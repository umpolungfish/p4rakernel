import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
# Exact Feshbach / Schur-Complement Spectral & Gap Theorems (§55, §64, §148, §153)

Formalizes:
1. Exact completion-of-squares identity for block Hermitian operators `H = [[A, Bᴴ], [B, D]]`.
2. Exact Feshbach positivity equivalence `H - m I ≥ 0 ↔ F(m) ≥ 0` when `D - m I > 0`.
3. Complex Cauchy–Schwarz and the Three-Parameter Gap Theorem (`h₀ δ > v² ⇒ H ≥ m₋ I`).
-/

namespace Imscribing.TrilatticeYM



open Matrix
open scoped ComplexOrder MatrixOrder

section CompletionOfSquares

variable {n₀ n₁ : ℕ}

def blockOp (A : Matrix (Fin n₀) (Fin n₀) ℂ) (B : Matrix (Fin n₁) (Fin n₀) ℂ)
    (D : Matrix (Fin n₁) (Fin n₁) ℂ) :
    Matrix (Fin n₀ ⊕ Fin n₁) (Fin n₀ ⊕ Fin n₁) ℂ :=
  Matrix.fromBlocks A Bᴴ B D

theorem blockOp_isHermitian {A : Matrix (Fin n₀) (Fin n₀) ℂ}
    {B : Matrix (Fin n₁) (Fin n₀) ℂ} {D : Matrix (Fin n₁) (Fin n₁) ℂ}
    (hA : A.IsHermitian) (hD : D.IsHermitian) :
    (blockOp A B D).IsHermitian := by
  rw [blockOp, Matrix.isHermitian_fromBlocks_iff]
  exact ⟨hA, Matrix.conjTranspose_conjTranspose B, rfl, hD⟩

theorem feshbach_completion_of_squares
    (A : Matrix (Fin n₀) (Fin n₀) ℂ) (B K : Matrix (Fin n₁) (Fin n₀) ℂ)
    (D : Matrix (Fin n₁) (Fin n₁) ℂ)
    (hD : D.IsHermitian) (hDK : D * K = B)
    (x : Fin n₀ → ℂ) (y : Fin n₁ → ℂ) :
    star (Sum.elim x y) ⬝ᵥ (blockOp A B D *ᵥ Sum.elim x y) =
      star (y + K *ᵥ x) ⬝ᵥ (D *ᵥ (y + K *ᵥ x)) +
        star x ⬝ᵥ ((A - Bᴴ * K) *ᵥ x) := by
  have hKD : Kᴴ * D = Bᴴ := by
    calc Kᴴ * D = Kᴴ * Dᴴ := by rw [hD.eq]
      _ = (D * K)ᴴ := by rw [Matrix.conjTranspose_mul]
      _ = Bᴴ := by rw [hDK]
  have hKB : Kᴴ * B = Bᴴ * K := by
    calc Kᴴ * B = Kᴴ * (D * K) := by rw [hDK]
      _ = (Kᴴ * D) * K := by rw [Matrix.mul_assoc]
      _ = Bᴴ * K := by rw [hKD]
  have hL :
      star (Sum.elim x y) ⬝ᵥ (blockOp A B D *ᵥ Sum.elim x y) =
        star x ⬝ᵥ (A *ᵥ x) + star x ⬝ᵥ (Bᴴ *ᵥ y) +
        star y ⬝ᵥ (B *ᵥ x) + star y ⬝ᵥ (D *ᵥ y) := by
    simp [blockOp, Function.star_sumElim, Matrix.fromBlocks_mulVec, dotProduct_add,
      add_dotProduct]
    ring
  have hR1 :
      star (y + K *ᵥ x) ⬝ᵥ (D *ᵥ (y + K *ᵥ x)) =
        star y ⬝ᵥ (D *ᵥ y) + star y ⬝ᵥ (B *ᵥ x) +
        star x ⬝ᵥ (Bᴴ *ᵥ y) + star x ⬝ᵥ ((Bᴴ * K) *ᵥ x) := by
    have hs : star (K *ᵥ x) = star x ᵥ* Kᴴ := Matrix.star_mulVec K x
    simp only [Pi.add_apply, star_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
    have h1 : star y ⬝ᵥ (D *ᵥ (K *ᵥ x)) = star y ⬝ᵥ (B *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, hDK]
    have h2 : star (K *ᵥ x) ⬝ᵥ (D *ᵥ y) = star x ⬝ᵥ (Bᴴ *ᵥ y) := by
      rw [hs, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hKD, ← Matrix.dotProduct_mulVec]
    have h3 : star (K *ᵥ x) ⬝ᵥ (D *ᵥ (K *ᵥ x)) = star x ⬝ᵥ ((Bᴴ * K) *ᵥ x) := by
      rw [hs, Matrix.mulVec_mulVec, hDK, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hKB,
        ← Matrix.dotProduct_mulVec]
    rw [h1, h2, h3]
    ring
  have hR2 :
      star x ⬝ᵥ ((A - Bᴴ * K) *ᵥ x) = star x ⬝ᵥ (A *ᵥ x) - star x ⬝ᵥ ((Bᴴ * K) *ᵥ x) := by
    simp [Matrix.sub_mulVec, dotProduct_sub]
  rw [hL, hR1, hR2]
  ring

theorem feshbach_posSemidef_iff
    (A : Matrix (Fin n₀) (Fin n₀) ℂ) (B : Matrix (Fin n₁) (Fin n₀) ℂ)
    (D : Matrix (Fin n₁) (Fin n₁) ℂ)
    (hA : A.IsHermitian) (hD : D.PosDef) :
    (blockOp A B D).PosSemidef ↔ (A - Bᴴ * D⁻¹ * B).PosSemidef := by
  have hDu : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit
  have hDK : D * (D⁻¹ * B) = B := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv D hDu, Matrix.one_mul]
  have hF_herm : (A - Bᴴ * D⁻¹ * B).IsHermitian := by
    refine hA.sub ?_
    have hDinv : D⁻¹.IsHermitian := hD.isHermitian.inv
    calc (Bᴴ * D⁻¹ * B)ᴴ
        = Bᴴ * (D⁻¹)ᴴ * (Bᴴ)ᴴ := by simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Bᴴ * D⁻¹ * B := by rw [hDinv.eq, Matrix.conjTranspose_conjTranspose]
  constructor
  · intro hM
    rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hM ⊢
    refine ⟨hF_herm, fun x => ?_⟩
    have hsub := hM.2 (Sum.elim x (-((D⁻¹ * B) *ᵥ x)))
    have hcos := feshbach_completion_of_squares A B (D⁻¹ * B) D hD.isHermitian hDK
      x (-((D⁻¹ * B) *ᵥ x))
    simp only [neg_add_cancel, Matrix.mulVec_zero, dotProduct_zero, zero_add] at hcos
    rw [← Matrix.mul_assoc] at hcos
    rw [← hcos]
    exact hsub
  · intro hF
    rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hF ⊢
    refine ⟨blockOp_isHermitian hA hD.isHermitian, fun v => ?_⟩
    obtain ⟨x, y, rfl⟩ : ∃ x y, v = Sum.elim x y :=
      ⟨fun i => v (.inl i), fun j => v (.inr j), by ext i; cases i <;> rfl⟩
    have hcos := feshbach_completion_of_squares A B (D⁻¹ * B) D hD.isHermitian hDK x y
    rw [← Matrix.mul_assoc] at hcos
    rw [hcos]
    have h1 : 0 ≤ star (y + (D⁻¹ * B) *ᵥ x) ⬝ᵥ (D *ᵥ (y + (D⁻¹ * B) *ᵥ x)) :=
      (Matrix.posSemidef_iff_dotProduct_mulVec.mp hD.posSemidef).2 _
    have h2 : 0 ≤ star x ⬝ᵥ ((A - Bᴴ * D⁻¹ * B) *ᵥ x) := hF.2 x
    exact add_nonneg h1 h2

end CompletionOfSquares

section ThreeParameterGap

variable {n₀ n₁ : ℕ}

private lemma real_smul_one_isHermitian {α : Type*} [Fintype α] [DecidableEq α] (r : ℝ) :
    ((r : ℂ) • (1 : Matrix α α ℂ)).IsHermitian := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Complex.conj_ofReal]
  · simp [Matrix.one_apply, hij, Ne.symm hij]

private lemma complex_dot_self_re {n : ℕ} (w : Fin n → ℂ) :
    (star w ⬝ᵥ w).re = ∑ i : Fin n, ((w i).re ^ 2 + (w i).im ^ 2) := by
  simp [dotProduct, Complex.re_sum, Complex.mul_re, sq]

private lemma complex_dot_self_nonneg {n : ℕ} (w : Fin n → ℂ) :
    0 ≤ (star w ⬝ᵥ w).re := by
  rw [complex_dot_self_re]
  exact Finset.sum_nonneg fun i _ => add_nonneg (sq_nonneg _) (sq_nonneg _)

private lemma complex_dot_re_sq_le {n : ℕ} (y z : Fin n → ℂ) :
    ((star y ⬝ᵥ z).re) ^ 2 ≤ (star y ⬝ᵥ y).re * (star z ⬝ᵥ z).re := by
  let u : Fin n ⊕ Fin n → ℝ := Sum.elim (fun i => (y i).re) (fun i => (y i).im)
  let v : Fin n ⊕ Fin n → ℝ := Sum.elim (fun i => (z i).re) (fun i => (z i).im)
  have huv : ∑ x : Fin n ⊕ Fin n, u x * v x = (star y ⬝ᵥ z).re := by
    simp [u, v, Fintype.sum_sum_type, dotProduct, Complex.re_sum, Complex.mul_re,
      Finset.sum_add_distrib]
  have hu2 : ∑ x : Fin n ⊕ Fin n, u x ^ 2 = (star y ⬝ᵥ y).re := by
    rw [complex_dot_self_re]
    simp [u, Fintype.sum_sum_type, Finset.sum_add_distrib]
  have hv2 : ∑ x : Fin n ⊕ Fin n, v x ^ 2 = (star z ⬝ᵥ z).re := by
    rw [complex_dot_self_re]
    simp [v, Fintype.sum_sum_type, Finset.sum_add_distrib]
  rw [← huv, ← hu2, ← hv2]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v

theorem three_param_gap
    (H00 : Matrix (Fin n₀) (Fin n₀) ℂ) (V : Matrix (Fin n₁) (Fin n₀) ℂ)
    (H11 : Matrix (Fin n₁) (Fin n₁) ℂ)
    (h0 δ v : ℝ) (hh0 : 0 < h0) (hδ : 0 < δ) (hv : 0 ≤ v) (hcond : v ^ 2 < h0 * δ)
    (hH00 : (H00 - (h0 : ℂ) • (1 : Matrix (Fin n₀) (Fin n₀) ℂ)).PosSemidef)
    (hH11 : (H11 - (δ : ℂ) • (1 : Matrix (Fin n₁) (Fin n₁) ℂ)).PosSemidef)
    (hV : (((v ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin n₀) (Fin n₀) ℂ) - Vᴴ * V).PosSemidef) :
    let m := (h0 + δ - Real.sqrt ((h0 - δ) ^ 2 + 4 * v ^ 2)) / 2
    0 < m ∧ (blockOp H00 V H11 - (m : ℂ) • (1 : Matrix (Fin n₀ ⊕ Fin n₁) (Fin n₀ ⊕ Fin n₁) ℂ)).PosSemidef := by
  intro m
  set r := Real.sqrt ((h0 - δ) ^ 2 + 4 * v ^ 2)
  have hr_sq : r ^ 2 = (h0 - δ) ^ 2 + 4 * v ^ 2 := Real.sq_sqrt (by positivity)
  have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hm_pos : 0 < m := by
    have hsq : r ^ 2 < (h0 + δ) ^ 2 := by rw [hr_sq]; nlinarith
    have hlt : r < h0 + δ := by nlinarith
    dsimp [m]; linarith
  refine ⟨hm_pos, ?_⟩
  have hA_herm : H00.IsHermitian := by
    simpa using hH00.isHermitian.add (real_smul_one_isHermitian (α := Fin n₀) h0)
  have hD_herm : H11.IsHermitian := by
    simpa using hH11.isHermitian.add (real_smul_one_isHermitian (α := Fin n₁) δ)
  have hm_herm : ((m : ℂ) • (1 : Matrix (Fin n₀ ⊕ Fin n₁) (Fin n₀ ⊕ Fin n₁) ℂ)).IsHermitian :=
    real_smul_one_isHermitian (α := Fin n₀ ⊕ Fin n₁) m
  have hH_herm : (blockOp H00 V H11 - (m : ℂ) • 1).IsHermitian :=
    (blockOp_isHermitian hA_herm hD_herm).sub hm_herm
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hH_herm, fun w => ?_⟩
  obtain ⟨x, y, rfl⟩ : ∃ x y, w = Sum.elim x y :=
    ⟨fun i => w (.inl i), fun j => w (.inr j), by ext i; cases i <;> rfl⟩
  have him : (star (Sum.elim x y) ⬝ᵥ ((blockOp H00 V H11 - (m : ℂ) • 1) *ᵥ Sum.elim x y)).im = 0 := by
    set M := blockOp H00 V H11 - (m : ℂ) • (1 : Matrix (Fin n₀ ⊕ Fin n₁) (Fin n₀ ⊕ Fin n₁) ℂ)
    set z := Sum.elim x y
    have hconj : star (star z ⬝ᵥ (M *ᵥ z)) = star z ⬝ᵥ (M *ᵥ z) := by
      simp only [dotProduct, Matrix.mulVec, star_sum, StarMul.star_mul, star_star,
        Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      have hij : star (M i j) = M j i := congrFun (congrFun hH_herm.eq j) i
      rw [hij]
      simp only [Pi.star_apply, star_star]
      ring
    rw [Complex.star_def, Complex.conj_eq_iff_im] at hconj
    exact hconj
  rw [Complex.nonneg_iff]
  refine ⟨?_, him.symm⟩
  have h00_re : (h0 - m) * (star x ⬝ᵥ x).re ≤ (star x ⬝ᵥ ((H00 - (m : ℂ) • 1) *ᵥ x)).re := by
    have hq := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hH00).2 x
    have hqre : 0 ≤ (star x ⬝ᵥ ((H00 - (h0 : ℂ) • 1) *ᵥ x)).re := (Complex.nonneg_iff.mp hq).1
    have hid :
        (star x ⬝ᵥ ((H00 - (m : ℂ) • 1) *ᵥ x)).re =
          (star x ⬝ᵥ ((H00 - (h0 : ℂ) • 1) *ᵥ x)).re + (h0 - m) * (star x ⬝ᵥ x).re := by
      simp [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul, Complex.sub_re, Complex.mul_re]
      ring
    linarith
  have h11_re : (δ - m) * (star y ⬝ᵥ y).re ≤ (star y ⬝ᵥ ((H11 - (m : ℂ) • 1) *ᵥ y)).re := by
    have hq := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hH11).2 y
    have hqre : 0 ≤ (star y ⬝ᵥ ((H11 - (δ : ℂ) • 1) *ᵥ y)).re := (Complex.nonneg_iff.mp hq).1
    have hid :
        (star y ⬝ᵥ ((H11 - (m : ℂ) • 1) *ᵥ y)).re =
          (star y ⬝ᵥ ((H11 - (δ : ℂ) • 1) *ᵥ y)).re + (δ - m) * (star y ⬝ᵥ y).re := by
      simp [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul, Complex.sub_re, Complex.mul_re]
      ring
    linarith
  have hvx_le : (star (V *ᵥ x) ⬝ᵥ (V *ᵥ x)).re ≤ v ^ 2 * (star x ⬝ᵥ x).re := by
    have hq := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hV).2 x
    have hqre : 0 ≤ (star x ⬝ᵥ ((((v ^ 2 : ℝ) : ℂ) • 1 - Vᴴ * V) *ᵥ x)).re :=
      (Complex.nonneg_iff.mp hq).1
    have hvx : star (V *ᵥ x) ⬝ᵥ (V *ᵥ x) = star x ⬝ᵥ ((Vᴴ * V) *ᵥ x) := by
      rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
        ← Matrix.dotProduct_mulVec]
    have hid :
        (star x ⬝ᵥ ((((v ^ 2 : ℝ) : ℂ) • 1 - Vᴴ * V) *ᵥ x)).re =
          v ^ 2 * (star x ⬝ᵥ x).re - (star (V *ᵥ x) ⬝ᵥ (V *ᵥ x)).re := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul, ← hvx]
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    linarith
  have hcs : |(star y ⬝ᵥ (V *ᵥ x)).re| ≤ v * Real.sqrt ((star y ⬝ᵥ y).re * (star x ⬝ᵥ x).re) := by
    have h1 := complex_dot_re_sq_le y (V *ᵥ x)
    have hny : 0 ≤ (star y ⬝ᵥ y).re := complex_dot_self_nonneg y
    have h2 : ((star y ⬝ᵥ (V *ᵥ x)).re) ^ 2 ≤ v ^ 2 * ((star y ⬝ᵥ y).re * (star x ⬝ᵥ x).re) := by
      calc ((star y ⬝ᵥ (V *ᵥ x)).re) ^ 2
          ≤ (star y ⬝ᵥ y).re * (star (V *ᵥ x) ⬝ᵥ (V *ᵥ x)).re := h1
        _ ≤ (star y ⬝ᵥ y).re * (v ^ 2 * (star x ⬝ᵥ x).re) :=
            mul_le_mul_of_nonneg_left hvx_le hny
        _ = v ^ 2 * ((star y ⬝ᵥ y).re * (star x ⬝ᵥ x).re) := by ring
    have hnx : 0 ≤ (star x ⬝ᵥ x).re := complex_dot_self_nonneg x
    have hrhs : (v * Real.sqrt ((star y ⬝ᵥ y).re * (star x ⬝ᵥ x).re)) ^ 2 =
        v ^ 2 * ((star y ⬝ᵥ y).re * (star x ⬝ᵥ x).re) := by
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hny hnx)]
    rw [← hrhs] at h2
    exact abs_le.mpr (abs_le_of_sq_le_sq' h2 (mul_nonneg hv (Real.sqrt_nonneg _)))
  have habs : |h0 - δ| ≤ r := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hle_abs := abs_le.mp habs
  have hm_h0 : 0 ≤ h0 - m := by dsimp [m]; linarith [hle_abs.1]
  have hm_δ : 0 ≤ δ - m := by dsimp [m]; linarith [hle_abs.2]
  have hm_prod : (h0 - m) * (δ - m) = v ^ 2 := by
    dsimp [m]; nlinarith [hr_sq]
  have hamgm : 2 * v * Real.sqrt ((star y ⬝ᵥ y).re * (star x ⬝ᵥ x).re) ≤
      (h0 - m) * (star x ⬝ᵥ x).re + (δ - m) * (star y ⬝ᵥ y).re := by
    have hnx : 0 ≤ (star x ⬝ᵥ x).re := complex_dot_self_nonneg x
    have hny : 0 ≤ (star y ⬝ᵥ y).re := complex_dot_self_nonneg y
    have hsq : 0 ≤ (Real.sqrt ((h0 - m) * (star x ⬝ᵥ x).re) -
        Real.sqrt ((δ - m) * (star y ⬝ᵥ y).re)) ^ 2 := sq_nonneg _
    have hmul :
        Real.sqrt ((h0 - m) * (star x ⬝ᵥ x).re) * Real.sqrt ((δ - m) * (star y ⬝ᵥ y).re) =
          v * Real.sqrt ((star y ⬝ᵥ y).re * (star x ⬝ᵥ x).re) := by
      rw [← Real.sqrt_mul (mul_nonneg hm_h0 hnx)]
      have heq : (h0 - m) * (star x ⬝ᵥ x).re * ((δ - m) * (star y ⬝ᵥ y).re) =
          v ^ 2 * ((star y ⬝ᵥ y).re * (star x ⬝ᵥ x).re) := by
        rw [← hm_prod]; ring
      rw [heq, Real.sqrt_mul (sq_nonneg v), Real.sqrt_sq hv]
    nlinarith [Real.sq_sqrt (mul_nonneg hm_h0 hnx), Real.sq_sqrt (mul_nonneg hm_δ hny)]
  have hexpand :
      (star (Sum.elim x y) ⬝ᵥ ((blockOp H00 V H11 - (m : ℂ) • 1) *ᵥ Sum.elim x y)).re =
        (star x ⬝ᵥ ((H00 - (m : ℂ) • 1) *ᵥ x)).re +
        (star y ⬝ᵥ ((H11 - (m : ℂ) • 1) *ᵥ y)).re +
        2 * (star y ⬝ᵥ (V *ᵥ x)).re := by
    have hcross : (star x ⬝ᵥ (Vᴴ *ᵥ y)).re = (star y ⬝ᵥ (V *ᵥ x)).re := by
      have hs : star x ⬝ᵥ (Vᴴ *ᵥ y) = star (star y ⬝ᵥ (V *ᵥ x)) := by
        simp only [dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply,
          star_sum, StarMul.star_mul, star_star, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          simp only [Pi.star_apply, star_star]
          ring
      rw [hs]
      simp only [Complex.star_def, Complex.conj_re]
    have hL1 : Sum.elim x y ∘ Sum.inl = x := rfl
    have hL2 : Sum.elim x y ∘ Sum.inr = y := rfl
    have hMvec :
        ((blockOp H00 V H11 - (m : ℂ) • 1) *ᵥ Sum.elim x y) =
          Sum.elim ((H00 - (m : ℂ) • 1) *ᵥ x + Vᴴ *ᵥ y)
            (V *ᵥ x + (H11 - (m : ℂ) • 1) *ᵥ y) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, blockOp, Matrix.fromBlocks_mulVec,
        hL1, hL2]
      ext k
      cases k <;> simp [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] <;> ring
    rw [hMvec]
    simp only [dotProduct, Fintype.sum_sum_type, Function.star_sumElim, Sum.elim_inl, Sum.elim_inr,
      Pi.add_apply, mul_add, Complex.add_re, Finset.sum_add_distrib]
    change (star x ⬝ᵥ ((H00 - (m : ℂ) • 1) *ᵥ x)).re + (star x ⬝ᵥ (Vᴴ *ᵥ y)).re +
        ((star y ⬝ᵥ (V *ᵥ x)).re + (star y ⬝ᵥ ((H11 - (m : ℂ) • 1) *ᵥ y)).re) =
      (star x ⬝ᵥ ((H00 - (m : ℂ) • 1) *ᵥ x)).re + (star y ⬝ᵥ ((H11 - (m : ℂ) • 1) *ᵥ y)).re +
        2 * (star y ⬝ᵥ (V *ᵥ x)).re
    linarith [hcross]
  have hneg : -(v * Real.sqrt ((star y ⬝ᵥ y).re * (star x ⬝ᵥ x).re)) ≤ (star y ⬝ᵥ (V *ᵥ x)).re :=
    (abs_le.mp hcs).1
  linarith

end ThreeParameterGap

end Imscribing.TrilatticeYM
