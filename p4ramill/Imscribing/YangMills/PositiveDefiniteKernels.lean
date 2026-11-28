import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Imscribing.YangMills.WilsonActionBounds4D

/-!
# Bounded Positive-Definite Kernels & Exponential Double-Integral Positivity (`0 sorry`)
-/

namespace Imscribing.YangMills.PosDefKernels

open MeasureTheory
open scoped Topology
open Imscribing.YangMills.WilsonLattice4D
open Imscribing.YangMills.WilsonBounds4D

def IsBoundedPosDefKernel {α : Type*} [MeasurableSpace α] (K : α → α → ℂ) : Prop :=
  Measurable (fun p : α × α => K p.1 p.2) ∧
  (∀ p q, K q p = star (K p q)) ∧
  (∃ M : ℝ, 0 ≤ M ∧ ∀ p q, ‖K p q‖ ≤ M) ∧
  (∀ (n : ℕ) (c : Fin n → ℂ) (x : Fin n → α),
    0 ≤ (∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * K (x i) (x j)).re)

theorem isBoundedPosDefKernel_sum {α ι : Type*} [MeasurableSpace α]
    (s : Finset ι) (K : ι → α → α → ℂ)
    (hK : ∀ i ∈ s, IsBoundedPosDefKernel (K i)) :
    IsBoundedPosDefKernel (fun p q => ∑ i ∈ s, K i p q) := by
  refine ⟨Finset.measurable_sum s fun i hi => (hK i hi).1, fun p q => ?_, ?_, ?_⟩
  · simp only [star_sum]
    exact Finset.sum_congr rfl fun i hi => (hK i hi).2.1 p q
  · choose M hM_nn hM_bd using fun i (hi : i ∈ s) => (hK i hi).2.2.1
    refine ⟨∑ i ∈ s.attach, M i.1 i.2, Finset.sum_nonneg fun i _ => hM_nn i.1 i.2, fun p q => ?_⟩
    calc
      ‖∑ i ∈ s, K i p q‖ ≤ ∑ i ∈ s, ‖K i p q‖ := norm_sum_le _ _
      _ = ∑ i ∈ s.attach, ‖K i.1 p q‖ := (Finset.sum_attach s (fun i => ‖K i p q‖)).symm
      _ ≤ ∑ i ∈ s.attach, M i.1 i.2 := Finset.sum_le_sum fun i _ => hM_bd i.1 i.2 p q
  · intro n c x
    have h_swap :
        (∑ a : Fin n, ∑ b : Fin n, star (c a) * c b * ∑ i ∈ s, K i (x a) (x b)) =
          ∑ i ∈ s, ∑ a : Fin n, ∑ b : Fin n, star (c a) * c b * K i (x a) (x b) := by
      simp_rw [Finset.mul_sum]
      conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    rw [h_swap, Complex.re_sum]
    exact Finset.sum_nonneg fun i hi => (hK i hi).2.2.2 n c x

theorem isBoundedPosDefKernel_smul_nonneg {α : Type*} [MeasurableSpace α]
    {r : ℝ} (hr : 0 ≤ r) {K : α → α → ℂ} (hK : IsBoundedPosDefKernel K) :
    IsBoundedPosDefKernel (fun p q => (r : ℂ) * K p q) := by
  obtain ⟨hmeas, hherm, ⟨M, hM_nn, hM_bd⟩, hpsd⟩ := hK
  refine ⟨measurable_const.mul hmeas, fun p q => ?_, ⟨r * M, mul_nonneg hr hM_nn, fun p q => ?_⟩, ?_⟩
  · dsimp only
    rw [hherm p q]
    simp [Complex.conj_ofReal, mul_comm]
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left (hM_bd p q) hr
  · intro n c x
    have hsum :
        (∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * ((r : ℂ) * K (x i) (x j))) =
          (r : ℂ) * (∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * K (x i) (x j)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsum]
    have hre :
        ((r : ℂ) * (∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * K (x i) (x j))).re =
          r * (∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * K (x i) (x j)).re := by
      simp [Complex.mul_re]
    rw [hre]
    exact mul_nonneg hr (hpsd n c x)

private lemma realTrace_inv_eq_self {N : ℕ} (X : GaugeGroup N) :
    realTrace X⁻¹ = realTrace X := by
  have hL : (X⁻¹ : GaugeGroup N).val * (X : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    change ((X⁻¹ * X : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) = 1; simp
  have hR : (X : Matrix (Fin N) (Fin N) ℂ) * star (X : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp X.prop).1
  have hX : (X⁻¹ : GaugeGroup N).val = star (X : Matrix (Fin N) (Fin N) ℂ) := by
    calc (X⁻¹ : GaugeGroup N).val = (X⁻¹ : GaugeGroup N).val * 1 := (Matrix.mul_one _).symm
    _ = (X⁻¹ : GaugeGroup N).val * ((X : Matrix (Fin N) (Fin N) ℂ) * star (X : Matrix (Fin N) (Fin N) ℂ)) := by rw [hR]
    _ = ((X⁻¹ : GaugeGroup N).val * (X : Matrix (Fin N) (Fin N) ℂ)) * star (X : Matrix (Fin N) (Fin N) ℂ) := by rw [Matrix.mul_assoc]
    _ = star (X : Matrix (Fin N) (Fin N) ℂ) := by rw [hL, Matrix.one_mul]
  unfold realTrace; rw [hX]; simp [Matrix.trace, Matrix.star_apply, Complex.re_sum, Complex.star_def]

private lemma complex_re_rank1_psd {n : ℕ} (c z : Fin n → ℂ) :
    0 ≤ (∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * ((z i * star (z j)).re : ℂ)).re := by
  have hterm : ∀ i j : Fin n,
      (star (c i) * c j * ((z i * star (z j)).re : ℂ)).re =
        ((c i).re * (z i).re) * ((c j).re * (z j).re) +
        ((c i).re * (z i).im) * ((c j).re * (z j).im) +
        ((c i).im * (z i).re) * ((c j).im * (z j).re) +
        ((c i).im * (z i).im) * ((c j).im * (z j).im) := by
    intro i j
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  rw [Complex.re_sum]
  simp_rw [Complex.re_sum, hterm]
  have hsum_sq : ∀ f : Fin n → ℝ,
      (∑ i : Fin n, ∑ j : Fin n, f i * f j) = (∑ i : Fin n, f i) ^ 2 := by
    intro f
    rw [sq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  simp only [Finset.sum_add_distrib]
  rw [hsum_sq (fun i => (c i).re * (z i).re),
      hsum_sq (fun i => (c i).re * (z i).im),
      hsum_sq (fun i => (c i).im * (z i).re),
      hsum_sq (fun i => (c i).im * (z i).im)]
  positivity

theorem realTrace_unitary_kernel_isPosDef {α : Type*} [MeasurableSpace α] {N : ℕ}
    (A : α → GaugeGroup N)
    (hA_meas : ∀ a b : Fin N, Measurable (fun r => (A r : Matrix (Fin N) (Fin N) ℂ) a b)) :
    IsBoundedPosDefKernel (fun p q => (realTrace (A p * (A q)⁻¹) : ℂ)) := by
  have hinv : ∀ r : α, ((A r)⁻¹ : GaugeGroup N).val = star (A r : Matrix (Fin N) (Fin N) ℂ) := by
    intro r
    have hL : ((A r)⁻¹ : GaugeGroup N).val * (A r : Matrix (Fin N) (Fin N) ℂ) = 1 := by
      change (((A r)⁻¹ * A r : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) = 1; simp
    have hR : (A r : Matrix (Fin N) (Fin N) ℂ) * star (A r : Matrix (Fin N) (Fin N) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp (A r).prop).1
    calc
      ((A r)⁻¹ : GaugeGroup N).val
          = ((A r)⁻¹ : GaugeGroup N).val * 1 := (Matrix.mul_one _).symm
      _ = ((A r)⁻¹ : GaugeGroup N).val * ((A r : Matrix (Fin N) (Fin N) ℂ) * star (A r : Matrix (Fin N) (Fin N) ℂ)) := by rw [hR]
      _ = (((A r)⁻¹ : GaugeGroup N).val * (A r : Matrix (Fin N) (Fin N) ℂ)) * star (A r : Matrix (Fin N) (Fin N) ℂ) := by rw [Matrix.mul_assoc]
      _ = star (A r : Matrix (Fin N) (Fin N) ℂ) := by rw [hL, Matrix.one_mul]
  have h_re : ∀ p q : α,
      realTrace (A p * (A q)⁻¹) =
        ∑ a : Fin N, ∑ b : Fin N,
          ((A p : Matrix (Fin N) (Fin N) ℂ) a b * star ((A q : Matrix (Fin N) (Fin N) ℂ) a b)).re := by
    intro p q
    unfold realTrace
    rw [Matrix.trace]
    simp_rw [Matrix.diag_apply]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    change ((∑ b : Fin N, (A p : Matrix (Fin N) (Fin N) ℂ) a b * ((A q)⁻¹ : GaugeGroup N).val b a)).re = _
    rw [hinv q, Complex.re_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [Matrix.star_apply]
  refine ⟨?_, ?_, ⟨(N : ℝ), Nat.cast_nonneg N, fun p q => ?_⟩, ?_⟩
  · have h_eq : (fun p : α × α => (realTrace (A p.1 * (A p.2)⁻¹) : ℂ)) = fun p => Complex.ofReal (∑ a : Fin N, ∑ b : Fin N, ((A p.1 : Matrix _ _ ℂ) a b * star ((A p.2 : Matrix _ _ ℂ) a b)).re) := by ext p; rw [h_re p.1 p.2]
    rw [h_eq]
    refine Complex.continuous_ofReal.measurable.comp ?_
    refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
    refine Complex.continuous_re.measurable.comp ?_
    exact ((hA_meas a b).comp measurable_fst).mul
      (continuous_star.measurable.comp ((hA_meas a b).comp measurable_snd))
  · intro p q
    rw [Complex.star_def, Complex.conj_ofReal]
    apply congrArg Complex.ofReal
    have h1 : A q * (A p)⁻¹ = (A p * (A q)⁻¹)⁻¹ := by group
    rw [h1]
    exact realTrace_inv_eq_self _
  · rw [Complex.norm_real, Real.norm_eq_abs]
    exact realTrace_abs_le _
  · intro n c x
    simp_rw [h_re]
    push_cast
    have h_swap :
        (∑ i : Fin n, ∑ j : Fin n, star (c i) * c j *
          ∑ a : Fin N, ∑ b : Fin N,
            (((A (x i) : Matrix (Fin N) (Fin N) ℂ) a b *
              star ((A (x j) : Matrix (Fin N) (Fin N) ℂ) a b)).re : ℂ)) =
        ∑ a : Fin N, ∑ b : Fin N, ∑ i : Fin n, ∑ j : Fin n,
          star (c i) * c j *
            (((A (x i) : Matrix (Fin N) (Fin N) ℂ) a b *
              star ((A (x j) : Matrix (Fin N) (Fin N) ℂ) a b)).re : ℂ) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
      conv_lhs => arg 2; ext a; arg 2; ext i; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_comm
    rw [h_swap, Complex.re_sum]
    refine Finset.sum_nonneg fun a _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun b _ =>
      complex_re_rank1_psd c (fun i => (A (x i) : Matrix (Fin N) (Fin N) ℂ) a b)

private lemma real_psd_of_complex_psd {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ}
    (hsym : ∀ i j, M j i = M i j)
    (hpsd : ∀ c : Fin n → ℂ, 0 ≤ (∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * (M i j : ℂ)).re) :
    M.PosSemidef := by
  refine .of_dotProduct_mulVec_nonneg (by ext i j; simp [hsym i j]) fun x => ?_
  have h := hpsd (fun i => (x i : ℂ))
  have heq : (∑ i : Fin n, ∑ j : Fin n,
      star (x i : ℂ) * (x j : ℂ) * (M i j : ℂ)).re =
      ∑ i : Fin n, x i * ∑ j : Fin n, M i j * x j := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.conj_ofReal]; ring
  rw [heq] at h; simpa [dotProduct, Matrix.mulVec] using h

private lemma complex_psd_of_real_psd {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef)
    (c : Fin n → ℂ) :
    0 ≤ (∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * (M i j : ℂ)).re := by
  have hre : (∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * (M i j : ℂ)).re =
      (∑ i : Fin n, ∑ j : Fin n, (c i).re * M i j * (c j).re) +
      (∑ i : Fin n, ∑ j : Fin n, (c i).im * M i j * (c j).im) := by
    rw [Complex.re_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.star_def]; ring
  have h1 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, (c i).re * M i j * (c j).re := by
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using hM.dotProduct_mulVec_nonneg (fun i => (c i).re)
  have h2 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, (c i).im * M i j * (c j).im := by
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using hM.dotProduct_mulVec_nonneg (fun i => (c i).im)
  rw [hre]; exact add_nonneg h1 h2

open Matrix Finset in
private lemma real_hadamard_psd {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (of fun i j => A i j * B i j).PosSemidef := by
  refine .of_dotProduct_mulVec_nonneg (by ext i j; simp; rw [show A j i = A i j by simpa using congr_fun (congr_fun hA.1 i) j, show B j i = B i j by simpa using congr_fun (congr_fun hB.1 i) j]) fun x => ?_
  let U : Matrix (Fin n) (Fin n) ℝ := hB.1.eigenvectorUnitary.1
  let D : Matrix (Fin n) (Fin n) ℝ := diagonal hB.1.eigenvalues
  have hsp : B = U * D * star U := by simpa [U, D, Unitary.conjStarAlgAut_apply] using hB.1.spectral_theorem
  have hBe : ∀ i j, B i j = ∑ r, hB.1.eigenvalues r * (U i r * U j r) := fun i j => by
    conv_lhs => rw [hsp, mul_apply]
    congr 1; ext r
    have hr : (U * D) i r = U i r * hB.1.eigenvalues r := by
      rw [mul_apply]; exact (sum_eq_single r (fun k _ hk => by simp [D, hk]) (fun h => absurd (mem_univ r) h)).trans (by simp [D])
    rw [hr]; simp [star_apply]; ring
  let y r i := x i * U i r
  have hid : star x ⬝ᵥ ((of fun i j => A i j * B i j) *ᵥ x) = ∑ r, hB.1.eigenvalues r * (star (y r) ⬝ᵥ (A *ᵥ y r)) := by
    simp only [dotProduct, mulVec, of_apply, star_trivial, hBe, y]; simp_rw [mul_sum, sum_mul]; simp_rw [mul_sum]
    conv_lhs => arg 2; ext i; rw [sum_comm]
    rw [sum_comm]; congr 1; ext r; congr 1; ext i; congr 1; ext j; ring
  rw [hid]; exact sum_nonneg fun r _ => mul_nonneg (hB.eigenvalues_nonneg r) (hA.dotProduct_mulVec_nonneg (y r))

private lemma exp_real_kernel_finite_psd {α : Type*} [MeasurableSpace α]
    (K : α → α → ℝ) (hK : IsBoundedPosDefKernel (fun p q => (K p q : ℂ)))
    (n : ℕ) (c : Fin n → ℂ) (x : Fin n → α) :
    0 ≤ (∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * (Real.exp (K (x i) (x j)) : ℂ)).re := by
  let M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => K (x i) (x j)
  have hM_sym : ∀ i j, M j i = M i j := fun i j => by
    have h := hK.2.1 (x i) (x j)
    rw [Complex.star_def, Complex.conj_ofReal] at h
    exact Complex.ofReal_injective h
  have hM_psd : M.PosSemidef := real_psd_of_complex_psd hM_sym fun d => hK.2.2.2 n d x
  have hM_pow : ∀ k : ℕ, (Matrix.of fun i j => (M i j) ^ k).PosSemidef := by
    intro k
    induction k with
    | zero =>
        refine .of_dotProduct_mulVec_nonneg (by ext i j; simp) fun v => ?_
        have heq : dotProduct (star v) ((Matrix.of fun (_ _ : Fin n) => (1 : ℝ)).mulVec v) =
            (∑ i : Fin n, v i) ^ 2 := by
          simp [dotProduct, Matrix.mulVec, sq, Finset.sum_mul, Finset.mul_sum]; rw [Finset.sum_comm]
        simp only [pow_zero]; rw [heq]; exact sq_nonneg _
    | succ k ih =>
        simpa [pow_succ'] using real_hadamard_psd hM_psd ih
  have h_partial : ∀ N : ℕ,
      0 ≤ (∑ i : Fin n, ∑ j : Fin n, star (c i) * c j *
        Complex.ofReal (∑ k ∈ Finset.range N, (M i j) ^ k / (Nat.factorial k : ℝ))).re := by
    intro N
    have h_swap :
        (∑ i : Fin n, ∑ j : Fin n, star (c i) * c j *
          Complex.ofReal (∑ k ∈ Finset.range N, (M i j) ^ k / (Nat.factorial k : ℝ))) =
        ∑ k ∈ Finset.range N, ((Nat.factorial k : ℝ)⁻¹ : ℂ) *
          ∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * (((M i j) ^ k : ℝ) : ℂ) := by
      push_cast
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [div_eq_mul_inv]; ring
    rw [h_swap, Complex.re_sum]
    refine Finset.sum_nonneg fun k _ => ?_
    rw [← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (complex_psd_of_real_psd (hM_pow k) c)
  have h_tend : Filter.Tendsto (fun N : ℕ =>
      (∑ i : Fin n, ∑ j : Fin n, star (c i) * c j *
        Complex.ofReal (∑ k ∈ Finset.range N, (M i j) ^ k / (Nat.factorial k : ℝ))).re)
      Filter.atTop
      (𝓝 (∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * (Real.exp (M i j) : ℂ)).re) := by
    refine Complex.continuous_re.tendsto _ |>.comp ?_
    refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => ?_
    refine tendsto_const_nhds.mul ?_
    refine Complex.continuous_ofReal.tendsto _ |>.comp ?_
    have hsum : HasSum (fun k : ℕ => (M i j) ^ k / (Nat.factorial k : ℝ)) (Real.exp (M i j)) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp (M i j)
    exact hsum.tendsto_sum_nat
  exact ge_of_tendsto h_tend (Filter.Eventually.of_forall h_partial)

theorem exp_real_posDefKernel_double_integral_nonneg
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (K : α → α → ℝ) (hK : IsBoundedPosDefKernel (fun p q => (K p q : ℂ)))
    (B : ℝ) (hB : 0 ≤ B) (hK_bd : ∀ p q, |K p q| ≤ B)
    (g : α → ℂ) (hg_meas : Measurable g) (Bf : ℝ) (hBf : 0 ≤ Bf) (hg_bd : ∀ p, ‖g p‖ ≤ Bf) :
    0 ≤ (∫ p, ∫ q, star (g p) * g q * (Real.exp (K p q) : ℂ) ∂μ ∂μ).re := by
  by_cases hμ0 : μ Set.univ = 0
  · simp [Measure.measure_univ_eq_zero.mp hμ0]
  have hμ_pos : 0 < (μ Set.univ).toReal :=
    ENNReal.toReal_pos hμ0 (measure_ne_top μ Set.univ)
  let I : ℝ := (∫ p, ∫ q, star (g p) * g q * (Real.exp (K p q) : ℂ) ∂μ ∂μ).re
  let D : ℝ := (∫ p, star (g p) * g p * (Real.exp (K p p) : ℂ) ∂μ).re
  have hK_meas_real : Measurable (fun p : α × α => K p.1 p.2) :=
    Complex.continuous_re.measurable.comp hK.1
  have hExp_meas : Measurable (fun p : α × α => (Real.exp (K p.1 p.2) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (Real.continuous_exp.measurable.comp hK_meas_real)
  have hF_meas : Measurable (fun p : α × α => star (g p.1) * g p.2 * (Real.exp (K p.1 p.2) : ℂ)) :=
    ((continuous_star.measurable.comp (hg_meas.comp measurable_fst)).mul
      (hg_meas.comp measurable_snd)).mul hExp_meas
  have hF_bd : ∀ p q : α, ‖star (g p) * g q * (Real.exp (K p q) : ℂ)‖ ≤ Bf ^ 2 * Real.exp B := by
    intro p q
    rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have h1 : ‖g p‖ * ‖g q‖ ≤ Bf ^ 2 := by
      rw [sq]; exact mul_le_mul (hg_bd p) (hg_bd q) (norm_nonneg _) hBf
    exact mul_le_mul h1 (Real.exp_le_exp.mpr (le_trans (le_abs_self _) (hK_bd p q)))
      (Real.exp_pos _).le (sq_nonneg Bf)
  have hD_meas : Measurable (fun p : α => star (g p) * g p * (Real.exp (K p p) : ℂ)) :=
    hF_meas.comp (measurable_id.prodMk measurable_id)
  have hD_int : Integrable (fun p : α => star (g p) * g p * (Real.exp (K p p) : ℂ)) μ :=
    Integrable.of_bound hD_meas.aestronglyMeasurable (Bf ^ 2 * Real.exp B)
      (Filter.Eventually.of_forall fun p => hF_bd p p)
  have h_bound_n : ∀ m : ℕ, 0 ≤ ((m + 2 : ℝ) * (m + 1 : ℝ)) * (μ Set.univ).toReal ^ m * I +
      (m + 2 : ℝ) * (μ Set.univ).toReal ^ (m + 1) * D := by
    intro m
    let n := m + 2
    let μn : Measure (Fin n → α) := Measure.pi (fun _ => μ)
    haveI : IsFiniteMeasure μn := inferInstance
    have h_pair_meas : ∀ i j : Fin n,
        Measurable (fun ω : Fin n → α => star (g (ω i)) * g (ω j) * (Real.exp (K (ω i) (ω j)) : ℂ)) :=
      fun i j => by have hm : Measurable (fun ω : Fin n → α => (ω i, ω j)) := (measurable_pi_apply i).prodMk (measurable_pi_apply j); exact hF_meas.comp hm
    have h_pair_int : ∀ i j : Fin n,
        Integrable (fun ω : Fin n → α => star (g (ω i)) * g (ω j) * (Real.exp (K (ω i) (ω j)) : ℂ)) μn :=
      fun i j => Integrable.of_bound (h_pair_meas i j).aestronglyMeasurable (Bf ^ 2 * Real.exp B)
        (Filter.Eventually.of_forall fun ω => hF_bd (ω i) (ω j))
    have h_re_int : ∀ i j : Fin n,
        Integrable (fun ω : Fin n → α =>
          (star (g (ω i)) * g (ω j) * (Real.exp (K (ω i) (ω j)) : ℂ)).re) μn :=
      fun i j => (h_pair_int i j).re
    have h_int_nn : 0 ≤ ∫ ω : Fin n → α, (∑ i : Fin n, ∑ j : Fin n,
        star (g (ω i)) * g (ω j) * (Real.exp (K (ω i) (ω j)) : ℂ)).re ∂μn :=
      integral_nonneg fun ω => exp_real_kernel_finite_psd K hK n (fun i => g (ω i)) ω
    have h_sum_eq :
        (∫ ω : Fin n → α, (∑ i : Fin n, ∑ j : Fin n,
          star (g (ω i)) * g (ω j) * (Real.exp (K (ω i) (ω j)) : ℂ)).re ∂μn) =
        ∑ i : Fin n, ∑ j : Fin n,
          (∫ ω : Fin n → α, star (g (ω i)) * g (ω j) * (Real.exp (K (ω i) (ω j)) : ℂ) ∂μn).re := by
      simp_rw [Complex.re_sum]
      rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => h_re_int i j]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finset_sum _ fun j _ => h_re_int i j]
      exact Finset.sum_congr rfl fun j _ => by simpa using integral_re (h_pair_int i j)
    have h_diag : ∀ i : Fin n,
        (∫ ω : Fin n → α, star (g (ω i)) * g (ω i) * (Real.exp (K (ω i) (ω i)) : ℂ) ∂μn).re =
          (μ Set.univ).toReal ^ (m + 1) * D := by
      intro i
      have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin n => μ) i
      have h_int_prod : Integrable (fun p : α × (Fin (m + 1) → α) =>
          star (g p.1) * g p.1 * (Real.exp (K p.1 p.1) : ℂ))
          (μ.prod (Measure.pi fun _ => μ)) :=
        Integrable.of_bound ((hD_meas.comp measurable_fst).aestronglyMeasurable)
          (Bf ^ 2 * Real.exp B) (Filter.Eventually.of_forall fun p => hF_bd p.1 p.1)
      have heq : (∫ ω : Fin n → α, star (g (ω i)) * g (ω i) * (Real.exp (K (ω i) (ω i)) : ℂ) ∂μn) =
          ∫ p : α × (Fin (m + 1) → α),
            star (g p.1) * g p.1 * (Real.exp (K p.1 p.1) : ℂ) ∂(μ.prod (Measure.pi fun _ => μ)) := by
        rw [← hmp.integral_comp']; rfl
      rw [heq, integral_prod _ h_int_prod]
      have h_inner : ∀ p : α, (∫ _ : Fin (m + 1) → α,
          star (g p) * g p * (Real.exp (K p p) : ℂ) ∂(Measure.pi fun _ => μ)) =
          Complex.ofReal ((μ Set.univ).toReal ^ (m + 1)) * (star (g p) * g p * (Real.exp (K p p) : ℂ)) := by
        intro p
        simp [integral_const, Measure.real_def, Measure.pi_univ, Finset.prod_const, Finset.card_univ, ENNReal.toReal_pow]
      simp_rw [h_inner, integral_const_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]; rfl
    have h_off : ∀ i j : Fin n, i ≠ j →
        (∫ ω : Fin n → α, star (g (ω i)) * g (ω j) * (Real.exp (K (ω i) (ω j)) : ℂ) ∂μn).re =
          (μ Set.univ).toReal ^ m * I := by
      intro i j hij
      obtain ⟨j', hj'⟩ : ∃ j' : Fin (m + 1), i.succAbove j' = j :=
        Fin.exists_succAbove_eq hij.symm
      have hmp1 := measurePreserving_piFinSuccAbove (fun _ : Fin n => μ) i
      have hmp2 := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) j'
      have h_int1 : Integrable (fun p : α × (Fin (m + 1) → α) =>
          star (g p.1) * g (p.2 j') * (Real.exp (K p.1 (p.2 j')) : ℂ))
          (μ.prod (Measure.pi fun _ => μ)) :=
        Integrable.of_bound
          ((hF_meas.comp (measurable_fst.prodMk ((measurable_pi_apply j').comp measurable_snd))).aestronglyMeasurable)
          (Bf ^ 2 * Real.exp B) (Filter.Eventually.of_forall fun p => hF_bd p.1 (p.2 j'))
      have heq1 : (∫ ω : Fin n → α, star (g (ω i)) * g (ω j) * (Real.exp (K (ω i) (ω j)) : ℂ) ∂μn) =
          ∫ p : α × (Fin (m + 1) → α),
            star (g p.1) * g (p.2 j') * (Real.exp (K p.1 (p.2 j')) : ℂ)
              ∂(μ.prod (Measure.pi fun _ => μ)) := by
        rw [← hmp1.integral_comp']
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        rw [← hj']; rfl
      rw [heq1, integral_prod _ h_int1]
      have h_inner1 : ∀ a : α, (∫ q : Fin (m + 1) → α,
          star (g a) * g (q j') * (Real.exp (K a (q j')) : ℂ) ∂(Measure.pi fun _ => μ)) =
          Complex.ofReal ((μ Set.univ).toReal ^ m) * ∫ b : α, star (g a) * g b * (Real.exp (K a b) : ℂ) ∂μ := by
        intro a
        have h_int2 : Integrable (fun r : α × (Fin m → α) =>
            star (g a) * g r.1 * (Real.exp (K a r.1) : ℂ))
            (μ.prod (Measure.pi fun _ => μ)) :=
          Integrable.of_bound
            ((hF_meas.comp (measurable_const.prodMk measurable_fst)).aestronglyMeasurable)
            (Bf ^ 2 * Real.exp B) (Filter.Eventually.of_forall fun r => hF_bd a r.1)
        have heq2 : (∫ q : Fin (m + 1) → α,
            star (g a) * g (q j') * (Real.exp (K a (q j')) : ℂ) ∂(Measure.pi fun _ => μ)) =
            ∫ r : α × (Fin m → α), star (g a) * g r.1 * (Real.exp (K a r.1) : ℂ)
              ∂(μ.prod (Measure.pi fun _ => μ)) := by
          rw [← hmp2.integral_comp']; rfl
        rw [heq2, integral_prod _ h_int2]
        have h_const : ∀ b : α, (∫ _ : Fin m → α,
            star (g a) * g b * (Real.exp (K a b) : ℂ) ∂(Measure.pi fun _ => μ)) =
            Complex.ofReal ((μ Set.univ).toReal ^ m) * (star (g a) * g b * (Real.exp (K a b) : ℂ)) := by
          intro b
          simp [integral_const, Measure.real_def, Measure.pi_univ, Finset.prod_const, Finset.card_univ, ENNReal.toReal_pow]
        simp_rw [h_const, integral_const_mul]
      simp_rw [h_inner1, integral_const_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]; rfl
    rw [h_sum_eq] at h_int_nn
    have h_split :
        (∑ i : Fin n, ∑ j : Fin n,
          (∫ ω : Fin n → α, star (g (ω i)) * g (ω j) * (Real.exp (K (ω i) (ω j)) : ℂ) ∂μn).re) =
        ∑ i : Fin n, ((∫ ω : Fin n → α, star (g (ω i)) * g (ω i) * (Real.exp (K (ω i) (ω i)) : ℂ) ∂μn).re +
          ∑ j ∈ Finset.univ.erase i,
            (∫ ω : Fin n → α, star (g (ω i)) * g (ω j) * (Real.exp (K (ω i) (ω j)) : ℂ) ∂μn).re) :=
      Finset.sum_congr rfl fun i _ =>
        (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)).symm
    rw [h_split] at h_int_nn
    have h_eval : ∀ i : Fin n,
        ((∫ ω : Fin n → α, star (g (ω i)) * g (ω i) * (Real.exp (K (ω i) (ω i)) : ℂ) ∂μn).re +
          ∑ j ∈ Finset.univ.erase i,
            (∫ ω : Fin n → α, star (g (ω i)) * g (ω j) * (Real.exp (K (ω i) (ω j)) : ℂ) ∂μn).re) =
        (μ Set.univ).toReal ^ (m + 1) * D + (m + 1 : ℝ) * ((μ Set.univ).toReal ^ m * I) := by
      intro i
      rw [h_diag i]
      have h_off_sum : (∑ j ∈ Finset.univ.erase i,
          (∫ ω : Fin n → α, star (g (ω i)) * g (ω j) * (Real.exp (K (ω i) (ω j)) : ℂ) ∂μn).re) =
          (m + 1 : ℝ) * ((μ Set.univ).toReal ^ m * I) := by
        have h_const : ∀ j ∈ Finset.univ.erase i,
            (∫ ω : Fin n → α, star (g (ω i)) * g (ω j) * (Real.exp (K (ω i) (ω j)) : ℂ) ∂μn).re =
            (μ Set.univ).toReal ^ m * I := fun j hj => h_off i j (Finset.ne_of_mem_erase hj).symm
        rw [Finset.sum_congr rfl h_const, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin]
        simp [n]
      rw [h_off_sum]
    simp_rw [h_eval, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h_int_nn
    have h_alg : ((n : ℕ) : ℝ) • ((μ Set.univ).toReal ^ (m + 1) * D + (m + 1 : ℝ) * ((μ Set.univ).toReal ^ m * I)) =
        ((m + 2 : ℝ) * (m + 1 : ℝ)) * (μ Set.univ).toReal ^ m * I +
        (m + 2 : ℝ) * (μ Set.univ).toReal ^ (m + 1) * D := by
      simp [n, smul_eq_mul]; ring
    simp only [nsmul_eq_mul] at h_int_nn
    simp only [smul_eq_mul] at h_alg
    linarith [h_int_nn, h_alg]
  by_contra hI_neg
  push_neg at hI_neg
  have hI_lt : I < 0 := hI_neg
  obtain ⟨m, hm⟩ := exists_nat_gt ((μ Set.univ).toReal * |D| / (-I))
  have h_div := h_bound_n m
  have h_step : (μ Set.univ).toReal * D < -((m + 1 : ℝ) * I) := by
    have h1 : (μ Set.univ).toReal * |D| < (m : ℝ) * (-I) :=
      (div_lt_iff₀ (by linarith : 0 < -I)).mp hm
    have h2 : (μ Set.univ).toReal * D ≤ (μ Set.univ).toReal * |D| :=
      mul_le_mul_of_nonneg_left (le_abs_self D) hμ_pos.le
    linarith
  have h_bad : ((m + 2 : ℝ) * (m + 1 : ℝ)) * (μ Set.univ).toReal ^ m * I +
      (m + 2 : ℝ) * (μ Set.univ).toReal ^ (m + 1) * D < 0 := by
    have hfac : ((m + 2 : ℝ) * (m + 1 : ℝ)) * (μ Set.univ).toReal ^ m * I +
        (m + 2 : ℝ) * (μ Set.univ).toReal ^ (m + 1) * D =
        ((m + 2 : ℝ) * (μ Set.univ).toReal ^ m) * ((m + 1 : ℝ) * I + (μ Set.univ).toReal * D) := by
      rw [pow_succ]; ring
    rw [hfac]
    exact mul_neg_of_pos_of_neg (by positivity) (by linarith)
  linarith

end Imscribing.YangMills.PosDefKernels
