import Mathlib.Analysis.Convex.Basic
import Imscribing.YangMills.ClayStatement
import Imscribing.YangMills.AsymptoticFreedomAndOSClosure

/-!
# Wick Rotation, Forward Light Cone V₊, and Forward Tube Geometry

1. `wickMap`: Euclidean-to-Minkowski embedding `(x₀, x₁, x₂, x₃) ↦ (i x₀, x₁, x₂, x₃)`.
2. `wick_ordered_mem_ForwardTube`: ordered positive Euclidean times land in `ForwardTube n`.
3. `forwardTube_isOpen` & `forwardTube_convex`: `ForwardTube n` is an open convex cone.
4. `lorentz_preserves_Vplus` & `lorentz_maps_forwardTube`: every `Λ : Lorentz4` preserves
   `ForwardTube n`.
-/

namespace Imscribing.YangMills.WickTube

open Imscribing.YangMills.ClaySpec
open Imscribing.YangMills.ContinuumInterfaces

/-- Wick rotation from Euclidean ℝ⁴ to complex Minkowski space ℂ⁴:
    x ↦ (i x₀, x₁, x₂, x₃). -/
noncomputable def wickMap (x : Spacetime4) : Fin 4 → ℂ :=
  fun μ => if μ = 0 then Complex.I * (x 0 : ℂ) else (x μ : ℂ)

/-- Open forward light cone V₊ ⊂ ℝ⁴: y₀ > 0 and y₁² + y₂² + y₃² < y₀². -/
def Vplus : Set (Fin 4 → ℝ) :=
  { y | 0 < y 0 ∧ y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 < y 0 ^ 2 }

theorem wick_ordered_mem_ForwardTube {n : ℕ} (x : Fin n → Spacetime4)
    (h0 : ∀ hk : 0 < n, 0 < (x ⟨0, hk⟩) 0)
    (hinc : ∀ k : Fin n, ∀ hk : 0 < (k : ℕ),
      (x ⟨(k : ℕ) - 1, by omega⟩) 0 < (x k) 0) :
    (fun k => wickMap (x k)) ∈ ForwardTube n := by
  intro k
  dsimp only
  have him_zero : ∀ j : Fin n, ∀ μ : Fin 4, μ ≠ 0 → (wickMap (x j) μ).im = 0 := by
    intro j μ hμ; simp [wickMap, hμ]
  have him_t : ∀ j : Fin n, (wickMap (x j) 0).im = (x j) 0 := by
    intro j; simp [wickMap]
  by_cases hk : (k : ℕ) = 0
  · have hpos_n : 0 < n := lt_of_le_of_lt (Nat.zero_le _) k.isLt
    have hk_eq : k = ⟨0, hpos_n⟩ := Fin.ext hk
    have h0' : 0 < (x k) 0 := by rw [hk_eq]; exact h0 hpos_n
    simp only [hk, ↓reduceDIte, him_t, him_zero _ 1 (by decide), him_zero _ 2 (by decide),
      him_zero _ 3 (by decide)]
    exact ⟨h0', by nlinarith⟩
  · have hk_pos : 0 < (k : ℕ) := Nat.pos_of_ne_zero hk
    have hdiff : 0 < (x k) 0 - (x ⟨(k : ℕ) - 1, by omega⟩) 0 := sub_pos.mpr (hinc k hk_pos)
    simp only [hk, ↓reduceDIte, him_t, him_zero _ 1 (by decide), him_zero _ 2 (by decide),
      him_zero _ 3 (by decide), sub_zero]
    exact ⟨hdiff, by nlinarith⟩

private lemma r3_cauchy_schwarz (a b : Fin 4 → ℝ) :
    (a 1 * b 1 + a 2 * b 2 + a 3 * b 3) ^ 2 ≤
      (a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2) * (b 1 ^ 2 + b 2 ^ 2 + b 3 ^ 2) := by
  have h : 0 ≤ (a 1 * b 2 - a 2 * b 1) ^ 2 + (a 1 * b 3 - a 3 * b 1) ^ 2 +
      (a 2 * b 3 - a 3 * b 2) ^ 2 := by positivity
  linarith [h]

theorem Vplus_smul {y : Fin 4 → ℝ} (hy : y ∈ Vplus) {a : ℝ} (ha : 0 < a) :
    a • y ∈ Vplus := by
  rcases hy with ⟨hy0, hysq⟩
  refine ⟨mul_pos ha hy0, ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  nlinarith [sq_pos_iff.mpr ha.ne']

theorem Vplus_add {y z : Fin 4 → ℝ} (hy : y ∈ Vplus) (hz : z ∈ Vplus) :
    y + z ∈ Vplus := by
  rcases hy with ⟨hy0, hysq⟩
  rcases hz with ⟨hz0, hzsq⟩
  refine ⟨add_pos hy0 hz0, ?_⟩
  have hcs := r3_cauchy_schwarz y z
  have h_prod_sq : (y 1 * z 1 + y 2 * z 2 + y 3 * z 3) ^ 2 < (y 0 * z 0) ^ 2 := by
    have hnn1 : 0 ≤ y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 := by positivity
    have hnn2 : 0 ≤ z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 := by positivity
    calc
      (y 1 * z 1 + y 2 * z 2 + y 3 * z 3) ^ 2
          ≤ (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) * (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2) := hcs
      _ < y 0 ^ 2 * z 0 ^ 2 := mul_lt_mul'' hysq hzsq hnn1 hnn2
      _ = (y 0 * z 0) ^ 2 := by ring
  have h_dot_lt : y 1 * z 1 + y 2 * z 2 + y 3 * z 3 < y 0 * z 0 := by
    nlinarith [mul_pos hy0 hz0]
  simp only [Pi.add_apply]
  nlinarith

/-- `ForwardTube n` is a convex cone in `(ℂ⁴)ⁿ`. -/
theorem forwardTube_convex (n : ℕ) : Convex ℝ (ForwardTube n) := by
  rw [convex_iff_forall_pos]
  intro z₁ hz₁ z₂ hz₂ a b ha hb _hab k
  have h1 := hz₁ k
  have h2 := hz₂ k
  let diff1 : Fin 4 → ℝ := fun μ =>
    if hk : (k : ℕ) = 0 then (z₁ k μ).im else (z₁ k μ).im - (z₁ ⟨k - 1, by omega⟩ μ).im
  let diff2 : Fin 4 → ℝ := fun μ =>
    if hk : (k : ℕ) = 0 then (z₂ k μ).im else (z₂ k μ).im - (z₂ ⟨k - 1, by omega⟩ μ).im
  have hdiff_eq : (fun μ : Fin 4 =>
      if hk : (k : ℕ) = 0 then ((a • z₁ + b • z₂) k μ).im
      else ((a • z₁ + b • z₂) k μ).im - ((a • z₁ + b • z₂) ⟨k - 1, by omega⟩ μ).im) =
      a • diff1 + b • diff2 := by
    ext μ
    by_cases hk : (k : ℕ) = 0
    · simp [diff1, diff2, hk, Pi.smul_apply, Pi.add_apply, Complex.add_im, Complex.real_smul]
    · simp [diff1, diff2, hk, Pi.smul_apply, Pi.add_apply, Complex.add_im, Complex.real_smul]
      ring
  change (fun μ : Fin 4 =>
      if hk : (k : ℕ) = 0 then ((a • z₁ + b • z₂) k μ).im
      else ((a • z₁ + b • z₂) k μ).im - ((a • z₁ + b • z₂) ⟨k - 1, by omega⟩ μ).im) ∈ Vplus
  rw [hdiff_eq]
  exact Vplus_add (Vplus_smul h1 ha) (Vplus_smul h2 hb)

/-- `ForwardTube n` is an open subset of `(ℂ⁴)ⁿ`. -/
theorem forwardTube_isOpen (n : ℕ) : IsOpen (ForwardTube n) := by
  have heq : ForwardTube n = ⋂ k : Fin n,
      { z : Fin n → Fin 4 → ℂ |
        let diff : Fin 4 → ℝ := fun μ =>
          if hk : (k : ℕ) = 0 then (z k μ).im else (z k μ).im - (z ⟨k - 1, by omega⟩ μ).im
        0 < diff 0 } ∩
      { z : Fin n → Fin 4 → ℂ |
        let diff : Fin 4 → ℝ := fun μ =>
          if hk : (k : ℕ) = 0 then (z k μ).im else (z k μ).im - (z ⟨k - 1, by omega⟩ μ).im
        0 < diff 0 ^ 2 - (diff 1 ^ 2 + diff 2 ^ 2 + diff 3 ^ 2) } := by
    ext z
    simp only [ForwardTube, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, sub_pos]
    rfl
  rw [heq]
  refine isOpen_iInter_of_finite fun k => ?_
  have h_cont_diff : ∀ μ : Fin 4, Continuous (fun z : Fin n → Fin 4 → ℂ =>
      if hk : (k : ℕ) = 0 then (z k μ).im else (z k μ).im - (z ⟨k - 1, by omega⟩ μ).im) := by
    intro μ
    by_cases hk : (k : ℕ) = 0
    · simp only [hk, ↓reduceDIte]
      exact Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply k))
    · simp only [hk, ↓reduceDIte]
      exact (Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply k))).sub
        (Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply ⟨k - 1, by omega⟩)))
  refine IsOpen.inter (isOpen_lt continuous_const (h_cont_diff 0)) ?_
  have h_quad : Continuous (fun z : Fin n → Fin 4 → ℂ =>
      (if hk : (k : ℕ) = 0 then (z k 0).im else (z k 0).im - (z ⟨k - 1, by omega⟩ 0).im) ^ 2 -
      ((if hk : (k : ℕ) = 0 then (z k 1).im else (z k 1).im - (z ⟨k - 1, by omega⟩ 1).im) ^ 2 +
       (if hk : (k : ℕ) = 0 then (z k 2).im else (z k 2).im - (z ⟨k - 1, by omega⟩ 2).im) ^ 2 +
       (if hk : (k : ℕ) = 0 then (z k 3).im else (z k 3).im - (z ⟨k - 1, by omega⟩ 3).im) ^ 2)) :=
    ((h_cont_diff 0).pow 2).sub
      ((((h_cont_diff 1).pow 2).add ((h_cont_diff 2).pow 2)).add ((h_cont_diff 3).pow 2))
  exact isOpen_lt continuous_const h_quad

/-- Every orthochronous proper Lorentz transformation preserves the forward light cone V₊. -/
theorem lorentz_preserves_Vplus (Λ : Lorentz4) {y : Fin 4 → ℝ} (hy : y ∈ Vplus) :
    Λ.mat.mulVec y ∈ Vplus := by
  let e₀ : Spacetime4 := (WithLp.equiv 2 (Fin 4 → ℝ)).symm ![1, 0, 0, 0]
  let yS : Spacetime4 := (WithLp.equiv 2 (Fin 4 → ℝ)).symm y
  have he0_self := Λ.preserves_metric e₀ e₀
  have hy_self := Λ.preserves_metric yS yS
  have he0_y := Λ.preserves_metric e₀ yS
  have h_a_eq : Λ.mat.mulVec e₀ = fun μ => Λ.mat μ 0 := by
    ext μ
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, e₀]
  have ha_sq : (Λ.mat 0 0) ^ 2 - (Λ.mat 1 0 ^ 2 + Λ.mat 2 0 ^ 2 + Λ.mat 3 0 ^ 2) = 1 := by
    have h1 : minkowskiInner e₀ e₀ = 1 := by simp [minkowskiInner, e₀]
    rw [h1] at he0_self
    simpa [minkowskiInner, h_a_eq] using he0_self
  have hw_sq : (Λ.mat.mulVec y 0) ^ 2 -
      (Λ.mat.mulVec y 1 ^ 2 + Λ.mat.mulVec y 2 ^ 2 + Λ.mat.mulVec y 3 ^ 2) =
      y 0 ^ 2 - (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) := by
    simpa [minkowskiInner, yS] using hy_self
  have haw_dot : Λ.mat 0 0 * Λ.mat.mulVec y 0 -
      (Λ.mat 1 0 * Λ.mat.mulVec y 1 + Λ.mat 2 0 * Λ.mat.mulVec y 2 +
       Λ.mat 3 0 * Λ.mat.mulVec y 3) = y 0 := by
    have h1 : minkowskiInner e₀ yS = y 0 := by simp [minkowskiInner, e₀, yS]
    rw [h1] at he0_y
    simpa [minkowskiInner, h_a_eq, yS] using he0_y
  rcases hy with ⟨hy0, hysq⟩
  have hw_pos_sq : Λ.mat.mulVec y 1 ^ 2 + Λ.mat.mulVec y 2 ^ 2 + Λ.mat.mulVec y 3 ^ 2 <
      (Λ.mat.mulVec y 0) ^ 2 := by linarith
  have ha0 := Λ.orthochronous
  have hcs := r3_cauchy_schwarz (fun μ => Λ.mat μ 0) (Λ.mat.mulVec y)
  have ha_sp : Λ.mat 1 0 ^ 2 + Λ.mat 2 0 ^ 2 + Λ.mat 3 0 ^ 2 < (Λ.mat 0 0) ^ 2 := by linarith
  have h_prod_sq : (Λ.mat 1 0 * Λ.mat.mulVec y 1 + Λ.mat 2 0 * Λ.mat.mulVec y 2 +
      Λ.mat 3 0 * Λ.mat.mulVec y 3) ^ 2 < (Λ.mat 0 0 * Λ.mat.mulVec y 0) ^ 2 := by
    have hnn1 : 0 ≤ Λ.mat 1 0 ^ 2 + Λ.mat 2 0 ^ 2 + Λ.mat 3 0 ^ 2 := by positivity
    have hnn2 : 0 ≤ Λ.mat.mulVec y 1 ^ 2 + Λ.mat.mulVec y 2 ^ 2 + Λ.mat.mulVec y 3 ^ 2 := by
      positivity
    calc
      (Λ.mat 1 0 * Λ.mat.mulVec y 1 + Λ.mat 2 0 * Λ.mat.mulVec y 2 +
          Λ.mat 3 0 * Λ.mat.mulVec y 3) ^ 2
          ≤ (Λ.mat 1 0 ^ 2 + Λ.mat 2 0 ^ 2 + Λ.mat 3 0 ^ 2) *
              (Λ.mat.mulVec y 1 ^ 2 + Λ.mat.mulVec y 2 ^ 2 + Λ.mat.mulVec y 3 ^ 2) := hcs
      _ < (Λ.mat 0 0) ^ 2 * (Λ.mat.mulVec y 0) ^ 2 := mul_lt_mul'' ha_sp hw_pos_sq hnn1 hnn2
      _ = (Λ.mat 0 0 * Λ.mat.mulVec y 0) ^ 2 := by ring
  have hw0_pos : 0 < Λ.mat.mulVec y 0 := by
    by_contra hle
    push_neg at hle
    nlinarith [sq_nonneg (Λ.mat 0 0 * Λ.mat.mulVec y 0 +
      (Λ.mat 1 0 * Λ.mat.mulVec y 1 + Λ.mat 2 0 * Λ.mat.mulVec y 2 +
       Λ.mat 3 0 * Λ.mat.mulVec y 3))]
  exact ⟨hw0_pos, hw_pos_sq⟩

/-- Every orthochronous proper Lorentz transformation maps `ForwardTube n` into itself. -/
theorem lorentz_maps_forwardTube {n : ℕ} (Λ : Lorentz4) {z : Fin n → Fin 4 → ℂ}
    (hz : z ∈ ForwardTube n) :
    (fun k => (Λ.mat.map Complex.ofReal).mulVec (z k)) ∈ ForwardTube n := by
  intro k
  have h_im : ∀ w : Fin 4 → ℂ,
      (fun μ : Fin 4 => ((Λ.mat.map Complex.ofReal).mulVec w μ).im) =
        Λ.mat.mulVec (fun μ => (w μ).im) := by
    intro w; ext μ
    simp [Matrix.mulVec, dotProduct, Complex.im_sum]
  have h_diff : (fun μ : Fin 4 =>
      if hk : (k : ℕ) = 0 then ((Λ.mat.map Complex.ofReal).mulVec (z k) μ).im
      else ((Λ.mat.map Complex.ofReal).mulVec (z k) μ).im -
        ((Λ.mat.map Complex.ofReal).mulVec (z ⟨k - 1, by omega⟩) μ).im) =
      Λ.mat.mulVec (fun μ =>
        if hk : (k : ℕ) = 0 then (z k μ).im else (z k μ).im - (z ⟨k - 1, by omega⟩ μ).im) := by
    by_cases hk : (k : ℕ) = 0
    · ext μ; simp [hk, h_im]
    · ext μ
      simp only [hk, ↓reduceDIte]
      rw [h_im, h_im, ← Matrix.mulVec_sub]
      rfl
  change (fun μ : Fin 4 =>
      if hk : (k : ℕ) = 0 then ((Λ.mat.map Complex.ofReal).mulVec (z k) μ).im
      else ((Λ.mat.map Complex.ofReal).mulVec (z k) μ).im -
        ((Λ.mat.map Complex.ofReal).mulVec (z ⟨k - 1, by omega⟩) μ).im) ∈ Vplus
  rw [h_diff]
  exact lorentz_preserves_Vplus Λ (hz k)

end Imscribing.YangMills.WickTube