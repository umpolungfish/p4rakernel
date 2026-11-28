import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Imscribing.YangMills.BorchersContinuumReconstruction
import Imscribing.YangMills.OSHilbertCompletion
import Imscribing.YangMills.ConcreteSchwartzShiftAndReflect
import Imscribing.YangMills.ConcreteTensorProductSchwartz
import Imscribing.YangMills.ConcreteMinimalClayReduction

/-!
# OS Canonical Semigroup Continuity & Completion Lift (`0 sorry`)

1. `timeShiftSchwartz_seminorm_sub_le` & `timeShiftSchwartz_seminorm_lipschitz`:
   Mean-value Lipschitz estimates for Euclidean time-shifts in every Schwartz seminorm `(k, m)`.
2. `timeShiftSchwartz_continuous`:
   Continuity of `t ↦ timeShiftSchwartz t f` in the `EuclideanSchwartz n` topology.
3. `osSemigroup_extend_to_completion`, `concreteBalaban_osSemigroup_exists`,
   `osSemigroup_zero_eq_id`, `osSemigroup_strong_right_continuous_at_zero`:
   Unconditional construction of the contractive, self-adjoint, vacuum-preserving,
   strongly right-continuous Euclidean semigroup `T` on `UniformSpace.Completion H₀`
   directly from `B : ConcreteBalabanTarget N hN`.
-/

noncomputable section

namespace Imscribing.YangMills.OSCanonicalSemigroupContinuity

set_option maxSynthPendingDepth 1
set_option maxHeartbeats 800000

open scoped InnerProductSpace Topology
open Imscribing.YangMills.ContinuumInterfaces
open Imscribing.YangMills.ConcreteSchwartzShiftAndReflect
open Imscribing.YangMills.ConcreteTensorSchwartz
open Imscribing.YangMills.OSBorchers
open Imscribing.YangMills.BorchersReconstruction
open Imscribing.YangMills.BorchersSchwinger
open Imscribing.YangMills.OSCompletion
open Imscribing.YangMills.ConcreteMinimalReduction

/-- Euclidean time-translation vector `(t, 0, 0, 0)` on `Fin n → Spacetime4`. -/
def timeShiftVec (n : ℕ) (t : ℝ) : Fin n → ContinuumInterfaces.Spacetime4 :=
  fun _ => t • stdBasis4 0

/-- Euclidean time-shift operator on `EuclideanSchwartz n`. -/
def timeShiftSchwartz {n : ℕ} (t : ℝ) (f : EuclideanSchwartz n) : EuclideanSchwartz n :=
  shiftPos (timeShiftVec n t) f

private lemma timeShiftVec_unit_norm_le (n : ℕ) :
    ‖(fun _ : Fin n => stdBasis4 0)‖ ≤ (1 : ℝ) := by
  by_cases hn : n = 0
  · subst hn
    have h0 : (fun _ : Fin 0 => stdBasis4 0) = 0 := by ext k; exact k.elim0
    rw [h0, norm_zero]
    exact zero_le_one
  · rw [Pi.norm_def, show (1 : ℝ) = ((1 : NNReal) : ℝ) from rfl]
    refine NNReal.coe_le_coe.mpr (Finset.sup_le fun k _ => ?_)
    have hb : ‖stdBasis4 0‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp
    exact_mod_cast hb.le

private lemma iteratedFDeriv_shift_eq {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : E) (m : ℕ) (x : E) :
    iteratedFDeriv ℝ m (fun y => g (y - v)) x = iteratedFDeriv ℝ m g (x - v) := by
  induction m generalizing x with
  | zero => ext; simp
  | succ m ih =>
    ext L
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left]
    have h_fun : iteratedFDeriv ℝ m (fun z => g (z - v)) =
        fun y => iteratedFDeriv ℝ m g (y - v) := funext ih
    have h_diff : Differentiable ℝ (iteratedFDeriv ℝ m g) :=
      (hg.iteratedFDeriv_right (m := 1) (i := m)
        (by exact_mod_cast (le_top : (1 + m : ℕ∞) ≤ ⊤))).differentiable one_ne_zero
    have h_has : HasFDerivAt (fun y => iteratedFDeriv ℝ m g (y - v))
        ((fderiv ℝ (iteratedFDeriv ℝ m g) (x - v)).comp (ContinuousLinearMap.id ℝ E)) x :=
      (h_diff (x - v)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const v)
    rw [h_fun]
    simp only [Function.comp_apply]
    rw [h_has.fderiv]
    simp

private lemma iteratedFDeriv_sub_eq {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g₁ g₂ : E → F) (hg₁ : ContDiff ℝ (⊤ : ℕ∞) g₁) (hg₂ : ContDiff ℝ (⊤ : ℕ∞) g₂)
    (m : ℕ) (x : E) :
    iteratedFDeriv ℝ m (fun y => g₁ y - g₂ y) x =
      iteratedFDeriv ℝ m g₁ x - iteratedFDeriv ℝ m g₂ x := by
  induction m generalizing x with
  | zero => ext; simp
  | succ m ih =>
    ext L
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left,
      iteratedFDeriv_succ_eq_comp_left]
    have h_fun : iteratedFDeriv ℝ m (fun z => g₁ z - g₂ z) =
        fun y => iteratedFDeriv ℝ m g₁ y - iteratedFDeriv ℝ m g₂ y := funext ih
    have hd₁ : Differentiable ℝ (iteratedFDeriv ℝ m g₁) :=
      (hg₁.iteratedFDeriv_right (m := 1) (i := m)
        (by exact_mod_cast (le_top : (1 + m : ℕ∞) ≤ ⊤))).differentiable one_ne_zero
    have hd₂ : Differentiable ℝ (iteratedFDeriv ℝ m g₂) :=
      (hg₂.iteratedFDeriv_right (m := 1) (i := m)
        (by exact_mod_cast (le_top : (1 + m : ℕ∞) ≤ ⊤))).differentiable one_ne_zero
    have h_has : HasFDerivAt (fun y => iteratedFDeriv ℝ m g₁ y - iteratedFDeriv ℝ m g₂ y)
        (fderiv ℝ (iteratedFDeriv ℝ m g₁) x - fderiv ℝ (iteratedFDeriv ℝ m g₂) x) x :=
      (hd₁ x).hasFDerivAt.sub (hd₂ x).hasFDerivAt
    rw [h_fun]
    simp only [Function.comp_apply]
    rw [h_has.fderiv]
    simp

private lemma norm_fderiv_iteratedFDeriv_apply_le {n m : ℕ}
    (f : EuclideanSchwartz n) (y : Fin n → ContinuumInterfaces.Spacetime4)
    (w : Fin n → ContinuumInterfaces.Spacetime4) :
    ‖fderiv ℝ (iteratedFDeriv ℝ m (⇑f)) y w‖ ≤
      ‖iteratedFDeriv ℝ (m + 1) (⇑f) y‖ * ‖w‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  have h_eq : fderiv ℝ (iteratedFDeriv ℝ m (⇑f)) y w v =
      iteratedFDeriv ℝ (m + 1) (⇑f) y (Fin.cons w v) := by
    rw [iteratedFDeriv_succ_eq_comp_left]
    simp
  rw [h_eq]
  have h1 := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ (m + 1) (⇑f) y) (Fin.cons w v)
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] at h1
  calc ‖iteratedFDeriv ℝ (m + 1) (⇑f) y (Fin.cons w v)‖
      ≤ ‖iteratedFDeriv ℝ (m + 1) (⇑f) y‖ * (‖w‖ * ∏ i : Fin m, ‖v i‖) := h1
    _ = (‖iteratedFDeriv ℝ (m + 1) (⇑f) y‖ * ‖w‖) * ∏ i : Fin m, ‖v i‖ := by ring

/-- Quantitative Mean-Value seminorm difference bound for Euclidean time-shifts on
    `EuclideanSchwartz n`. -/
theorem timeShiftSchwartz_seminorm_sub_le {n : ℕ} (f : EuclideanSchwartz n) (t s : ℝ)
    (k m : ℕ) :
    SchwartzMap.seminorm ℂ k m (timeShiftSchwartz t f - timeShiftSchwartz s f) ≤
      |t - s| * ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * (max |t| |s|) ^ (k - j) * SchwartzMap.seminorm ℂ j (m + 1) f := by
  let R : ℝ := max |t| |s|
  let C_lip : ℝ := ∑ j ∈ Finset.range (k + 1),
    (k.choose j : ℝ) * R ^ (k - j) * SchwartzMap.seminorm ℂ j (m + 1) f
  have hR_nn : 0 ≤ R := le_trans (abs_nonneg t) (le_max_left _ _)
  have hC_nn : 0 ≤ C_lip := Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hR_nn _)) (apply_nonneg _ _)
  refine SchwartzMap.seminorm_le_bound ℂ k m _ (mul_nonneg (abs_nonneg _) hC_nn) fun x => ?_
  have h_sub_deriv :
      iteratedFDeriv ℝ m (⇑(timeShiftSchwartz t f - timeShiftSchwartz s f)) x =
        iteratedFDeriv ℝ m (⇑f) (x - timeShiftVec n t) -
          iteratedFDeriv ℝ m (⇑f) (x - timeShiftVec n s) := by
    change iteratedFDeriv ℝ m (fun y => (timeShiftSchwartz t f) y - (timeShiftSchwartz s f) y) x = _
    rw [iteratedFDeriv_sub_eq (⇑(timeShiftSchwartz t f)) (⇑(timeShiftSchwartz s f)) (timeShiftSchwartz t f).smooth' (timeShiftSchwartz s f).smooth']
    change iteratedFDeriv ℝ m (fun y => f (y - timeShiftVec n t)) x -
        iteratedFDeriv ℝ m (fun y => f (y - timeShiftVec n s)) x = _
    rw [iteratedFDeriv_shift_eq (⇑f) f.smooth' (timeShiftVec n t) m x,
      iteratedFDeriv_shift_eq (⇑f) f.smooth' (timeShiftVec n s) m x]
  rw [h_sub_deriv]
  let v₀ : Fin n → ContinuumInterfaces.Spacetime4 := fun _ => stdBasis4 0
  let γ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin n → ContinuumInterfaces.Spacetime4) ℂ :=
    fun τ => iteratedFDeriv ℝ m (⇑f) (x - τ • v₀)
  let g : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin n → ContinuumInterfaces.Spacetime4) ℂ :=
    fun τ => (‖x‖ ^ k) • γ τ
  have h_diff_f : Differentiable ℝ (iteratedFDeriv ℝ m (⇑f)) :=
    (f.smooth'.iteratedFDeriv_right (m := 1) (i := m)
      (by exact_mod_cast (le_top : (1 + m : ℕ∞) ≤ ⊤))).differentiable one_ne_zero
  let g' : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin n → ContinuumInterfaces.Spacetime4) ℂ :=
    fun τ => (‖x‖ ^ k) • (fderiv ℝ (iteratedFDeriv ℝ m (⇑f)) (x - τ • v₀) (-v₀))
  have hg_deriv : ∀ τ : ℝ, HasDerivAt g (g' τ) τ := fun τ => by
    have h_path : HasDerivAt (fun u : ℝ => x - u • v₀) (-v₀) τ := by
      simpa using (hasDerivAt_const τ x).sub ((hasDerivAt_id τ).smul_const v₀)
    have hγ : HasDerivAt γ (fderiv ℝ (iteratedFDeriv ℝ m (⇑f)) (x - τ • v₀) (-v₀)) τ :=
      (h_diff_f (x - τ • v₀)).hasFDerivAt.comp_hasDerivAt τ h_path
    exact hγ.const_smul (‖x‖ ^ k)
  let I : Set ℝ := Set.Icc (min s t) (max s t)
  have hI_conv : Convex ℝ I := convex_Icc (min s t) (max s t)
  have hsI : s ∈ I := ⟨min_le_left s t, le_max_left s t⟩
  have htI : t ∈ I := ⟨min_le_right s t, le_max_right s t⟩
  have hg_bound : ∀ τ ∈ I, ‖g' τ‖ ≤ C_lip := fun τ hτ => by
    have hτ_abs : |τ| ≤ R := by
      have hmin : -R ≤ τ := by
        have : -R ≤ min s t := by
          refine le_min ?_ ?_
          · exact neg_le.mpr (le_trans (neg_le_abs s) (le_max_right _ _))
          · exact neg_le.mpr (le_trans (neg_le_abs t) (le_max_left _ _))
        linarith [hτ.1]
      have hmax : τ ≤ R := by
        have : max s t ≤ R := max_le (le_trans (le_abs_self s) (le_max_right _ _))
          (le_trans (le_abs_self t) (le_max_left _ _))
        linarith [hτ.2]
      exact abs_le.mpr ⟨hmin, hmax⟩
    have hv₀_le : ‖v₀‖ ≤ 1 := timeShiftVec_unit_norm_le n
    have h_der : ‖fderiv ℝ (iteratedFDeriv ℝ m (⇑f)) (x - τ • v₀) (-v₀)‖ ≤
        ‖iteratedFDeriv ℝ (m + 1) (⇑f) (x - τ • v₀)‖ := by
      calc ‖fderiv ℝ (iteratedFDeriv ℝ m (⇑f)) (x - τ • v₀) (-v₀)‖
          ≤ ‖iteratedFDeriv ℝ (m + 1) (⇑f) (x - τ • v₀)‖ * ‖-v₀‖ :=
            norm_fderiv_iteratedFDeriv_apply_le f (x - τ • v₀) (-v₀)
        _ ≤ ‖iteratedFDeriv ℝ (m + 1) (⇑f) (x - τ • v₀)‖ * 1 := by
            rw [norm_neg]; exact mul_le_mul_of_nonneg_left hv₀_le (norm_nonneg _)
        _ = ‖iteratedFDeriv ℝ (m + 1) (⇑f) (x - τ • v₀)‖ := mul_one _
    have h_tri : ‖x‖ ≤ ‖x - τ • v₀‖ + R := by
      calc ‖x‖ = ‖(x - τ • v₀) + τ • v₀‖ := by abel_nf
        _ ≤ ‖x - τ • v₀‖ + ‖τ • v₀‖ := norm_add_le _ _
        _ = ‖x - τ • v₀‖ + |τ| * ‖v₀‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ ‖x - τ • v₀‖ + R * 1 :=
            add_le_add le_rfl (mul_le_mul hτ_abs hv₀_le (norm_nonneg _) hR_nn)
        _ = ‖x - τ • v₀‖ + R := by ring
    have hxk : ‖x‖ ^ k ≤ ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * ‖x - τ • v₀‖ ^ j * R ^ (k - j) := by
      calc ‖x‖ ^ k ≤ (‖x - τ • v₀‖ + R) ^ k := pow_le_pow_left₀ (norm_nonneg _) h_tri k
        _ = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * ‖x - τ • v₀‖ ^ j * R ^ (k - j) := by
          rw [add_pow]; refine Finset.sum_congr rfl fun j _ => ?_; ring
    calc ‖g' τ‖
        = ‖x‖ ^ k * ‖fderiv ℝ (iteratedFDeriv ℝ m (⇑f)) (x - τ • v₀) (-v₀)‖ := by
          dsimp [g']; rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) k)]
      _ ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) (⇑f) (x - τ • v₀)‖ :=
          mul_le_mul_of_nonneg_left h_der (pow_nonneg (norm_nonneg x) k)
      _ ≤ (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * ‖x - τ • v₀‖ ^ j * R ^ (k - j)) *
            ‖iteratedFDeriv ℝ (m + 1) (⇑f) (x - τ • v₀)‖ :=
          mul_le_mul_of_nonneg_right hxk (norm_nonneg _)
      _ = ∑ j ∈ Finset.range (k + 1),
            (k.choose j : ℝ) * R ^ (k - j) *
              (‖x - τ • v₀‖ ^ j * ‖iteratedFDeriv ℝ (m + 1) (⇑f) (x - τ • v₀)‖) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_; ring
      _ ≤ C_lip := by
          refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hR_nn _))
          exact SchwartzMap.le_seminorm ℂ j (m + 1) f (x - τ • v₀)
  have h_mvt := hI_conv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun τ _ => (hg_deriv τ).hasDerivWithinAt) hg_bound hsI htI
  have hg_eq : ‖g t - g s‖ =
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (⇑f) (x - timeShiftVec n t) -
        iteratedFDeriv ℝ m (⇑f) (x - timeShiftVec n s)‖ := by
    change ‖(‖x‖ ^ k) • iteratedFDeriv ℝ m (⇑f) (x - timeShiftVec n t) -
        (‖x‖ ^ k) • iteratedFDeriv ℝ m (⇑f) (x - timeShiftVec n s)‖ = _
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) k)]
  rw [← hg_eq]
  calc ‖g t - g s‖ ≤ C_lip * ‖t - s‖ := h_mvt
    _ = |t - s| * C_lip := by rw [Real.norm_eq_abs, mul_comm]

/-- Quantitative Lipschitz estimate for Schwartz seminorms under Euclidean time-shift. -/
theorem timeShiftSchwartz_seminorm_lipschitz {n : ℕ} (f : EuclideanSchwartz n) (t s : ℝ)
    (k m : ℕ) :
    |SchwartzMap.seminorm ℂ k m (timeShiftSchwartz t f) -
        SchwartzMap.seminorm ℂ k m (timeShiftSchwartz s f)| ≤
      |t - s| * ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * (max |t| |s|) ^ (k - j) * SchwartzMap.seminorm ℂ j (m + 1) f := by
  have h1 : SchwartzMap.seminorm ℂ k m (timeShiftSchwartz t f) -
      SchwartzMap.seminorm ℂ k m (timeShiftSchwartz s f) ≤
      SchwartzMap.seminorm ℂ k m (timeShiftSchwartz t f - timeShiftSchwartz s f) := by
    have htri := map_add_le_add (SchwartzMap.seminorm ℂ k m)
      (timeShiftSchwartz t f - timeShiftSchwartz s f) (timeShiftSchwartz s f)
    rw [sub_add_cancel] at htri
    linarith
  have h2 : SchwartzMap.seminorm ℂ k m (timeShiftSchwartz s f) -
      SchwartzMap.seminorm ℂ k m (timeShiftSchwartz t f) ≤
      SchwartzMap.seminorm ℂ k m (timeShiftSchwartz t f - timeShiftSchwartz s f) := by
    have htri := map_add_le_add (SchwartzMap.seminorm ℂ k m)
      (timeShiftSchwartz s f - timeShiftSchwartz t f) (timeShiftSchwartz t f)
    rw [sub_add_cancel, ← neg_sub (timeShiftSchwartz t f) (timeShiftSchwartz s f), map_neg_eq_map] at htri
    linarith
  exact le_trans (abs_sub_le_iff.mpr ⟨h1, h2⟩) (timeShiftSchwartz_seminorm_sub_le f t s k m)

/-- Continuity of `t ↦ timeShiftSchwartz t f` in the Schwartz topology on `EuclideanSchwartz n`. -/
theorem timeShiftSchwartz_continuous {n : ℕ} (f : EuclideanSchwartz n) :
    Continuous (fun t : ℝ => timeShiftSchwartz t f) := by
  rw [continuous_iff_continuousAt]
  intro s
  rw [ContinuousAt, (schwartz_withSeminorms ℂ (Fin n → ContinuumInterfaces.Spacetime4) ℂ).tendsto_nhds _ _]
  intro i ε hε
  rcases i with ⟨k, m⟩
  let R₀ : ℝ := |s| + 1
  let M : ℝ := (∑ j ∈ Finset.range (k + 1),
    (k.choose j : ℝ) * R₀ ^ (k - j) * SchwartzMap.seminorm ℂ j (m + 1) f) + 1
  have hM_pos : 0 < M := by
    have hsum_nn : 0 ≤ ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * R₀ ^ (k - j) * SchwartzMap.seminorm ℂ j (m + 1) f :=
      Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (by positivity) _)) (apply_nonneg _ _)
    linarith
  let δ : ℝ := min 1 (ε / M)
  have hδ_pos : 0 < δ := lt_min zero_lt_one (div_pos hε hM_pos)
  refine Metric.eventually_nhds_iff.mpr ⟨δ, hδ_pos, fun {t} ht => ?_⟩
  rw [Real.dist_eq] at ht
  have hts_lt_1 : |t - s| < 1 := lt_of_lt_of_le ht (min_le_left _ _)
  have hts_lt_eps : |t - s| < ε / M := lt_of_lt_of_le ht (min_le_right _ _)
  have hmax_le : max |t| |s| ≤ R₀ := by
    refine max_le ?_ (by dsimp [R₀]; linarith)
    calc |t| = |(t - s) + s| := by ring_nf
      _ ≤ |t - s| + |s| := abs_add_le _ _
      _ ≤ 1 + |s| := add_le_add hts_lt_1.le le_rfl
      _ = R₀ := by dsimp [R₀]; ring
  have h_sum_le :
      (∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * (max |t| |s|) ^ (k - j) * SchwartzMap.seminorm ℂ j (m + 1) f) ≤ M := by
    have hle : (∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * (max |t| |s|) ^ (k - j) * SchwartzMap.seminorm ℂ j (m + 1) f) ≤
        ∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℝ) * R₀ ^ (k - j) * SchwartzMap.seminorm ℂ j (m + 1) f := by
      refine Finset.sum_le_sum fun j _ => ?_
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (le_trans (abs_nonneg t) (le_max_left _ _)) hmax_le _)
        (Nat.cast_nonneg _)) (apply_nonneg _ _)
    linarith
  calc SchwartzMap.seminorm ℂ k m (timeShiftSchwartz t f - timeShiftSchwartz s f)
      ≤ |t - s| * ∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℝ) * (max |t| |s|) ^ (k - j) * SchwartzMap.seminorm ℂ j (m + 1) f :=
        timeShiftSchwartz_seminorm_sub_le f t s k m
    _ ≤ |t - s| * M := mul_le_mul_of_nonneg_left h_sum_le (abs_nonneg _)
    _ < (ε / M) * M := mul_lt_mul_of_pos_right hts_lt_eps hM_pos
    _ = ε := div_mul_cancel₀ ε hM_pos.ne'

/-- Any contractive right-continuous linear semigroup `T₀` on a pre-Hilbert space `H₀`
    extends uniquely to a strongly right-continuous contraction semigroup `T_ext` on
    `UniformSpace.Completion H₀`. -/
theorem osSemigroup_extend_to_completion {H₀ : Type*}
    [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
    (T₀ : ℝ → H₀ →ₗ[ℂ] H₀)
    (hT₀_zero : T₀ 0 = LinearMap.id)
    (hT₀_contr : ∀ t : ℝ, 0 ≤ t → ∀ v : H₀, ‖T₀ t v‖ ≤ ‖v‖)
    (hT₀_cont : ∀ v : H₀,
      Filter.Tendsto (fun t : ℝ => (T₀ t v : UniformSpace.Completion H₀))
        (𝓝[>] 0) (𝓝 (v : UniformSpace.Completion H₀))) :
    ∃ T_ext : ℝ → UniformSpace.Completion H₀ →L[ℂ] UniformSpace.Completion H₀,
      T_ext 0 = 1 ∧
      (∀ t : ℝ, 0 ≤ t → ∀ ψ : UniformSpace.Completion H₀, ‖T_ext t ψ‖ ≤ ‖ψ‖) ∧
      (∀ v : H₀, ∀ t : ℝ, 0 ≤ t →
        T_ext t (v : UniformSpace.Completion H₀) = (T₀ t v : UniformSpace.Completion H₀)) ∧
      (∀ ψ : UniformSpace.Completion H₀,
        Filter.Tendsto (fun t : ℝ => T_ext t ψ) (𝓝[>] 0) (𝓝 ψ)) := by
  let T_ext : ℝ → UniformSpace.Completion H₀ →L[ℂ] UniformSpace.Completion H₀ := fun t =>
    if ht : 0 ≤ t then liftContractionToCompletion (T₀ t) (hT₀_contr t ht)
    else ContinuousLinearMap.id ℂ _
  have h_coe : ∀ v : H₀, ∀ t : ℝ, 0 ≤ t →
      T_ext t (v : UniformSpace.Completion H₀) = (T₀ t v : UniformSpace.Completion H₀) := by
    intro v t ht
    dsimp [T_ext]
    rw [dif_pos ht]
    exact liftContractionToCompletion_coe (T₀ t) (hT₀_contr t ht) v
  have h_zero : T_ext 0 = 1 := by
    ext ψ
    induction ψ using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (T_ext 0).continuous continuous_id
    | ih v =>
      rw [h_coe v 0 le_rfl, hT₀_zero]
      rfl
  have h_contr : ∀ t : ℝ, 0 ≤ t → ∀ ψ : UniformSpace.Completion H₀, ‖T_ext t ψ‖ ≤ ‖ψ‖ := by
    intro t ht ψ
    induction ψ using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_le (continuous_norm.comp (T_ext t).continuous) continuous_norm
    | ih v =>
      rw [h_coe v t ht, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
      exact hT₀_contr t ht v
  have h_cont : ∀ ψ : UniformSpace.Completion H₀,
      Filter.Tendsto (fun t : ℝ => T_ext t ψ) (𝓝[>] 0) (𝓝 ψ) := by
    intro ψ
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hψ_mem : ψ ∈ closure (Set.range ((↑) : H₀ → UniformSpace.Completion H₀)) := by
      rw [UniformSpace.Completion.denseRange_coe.closure_eq]
      exact Set.mem_univ ψ
    obtain ⟨_, ⟨v, rfl⟩, hv⟩ := Metric.mem_closure_iff.mp hψ_mem (ε / 3) (by linarith)
    rw [dist_eq_norm] at hv
    have hv_lim := Metric.tendsto_nhds.mp (hT₀_cont v) (ε / 3) (by linarith)
    have h_pos : ∀ᶠ t : ℝ in 𝓝[>] 0, (0 : ℝ) ≤ t :=
      eventually_mem_nhdsWithin.mono fun _ ht => le_of_lt ht
    filter_upwards [hv_lim, h_pos] with t ht_lim ht_nn
    rw [dist_eq_norm] at ht_lim ⊢
    calc ‖T_ext t ψ - ψ‖
        = ‖T_ext t (ψ - (v : UniformSpace.Completion H₀)) +
            (T_ext t (v : UniformSpace.Completion H₀) - (v : UniformSpace.Completion H₀)) +
            ((v : UniformSpace.Completion H₀) - ψ)‖ := by
          rw [map_sub]; abel_nf
      _ ≤ ‖T_ext t (ψ - (v : UniformSpace.Completion H₀))‖ +
            ‖T_ext t (v : UniformSpace.Completion H₀) - (v : UniformSpace.Completion H₀)‖ +
            ‖(v : UniformSpace.Completion H₀) - ψ‖ :=
          le_trans (norm_add_le _ _) (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ‖ψ - (v : UniformSpace.Completion H₀)‖ +
            ‖(T₀ t v : UniformSpace.Completion H₀) - (v : UniformSpace.Completion H₀)‖ +
            ‖ψ - (v : UniformSpace.Completion H₀)‖ := by
          rw [h_coe v t ht_nn, norm_sub_rev (v : UniformSpace.Completion H₀) ψ]
          exact add_le_add (add_le_add (h_contr t ht_nn _) le_rfl) le_rfl
      _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add hv ht_lim) hv
      _ = ε := by ring
  exact ⟨T_ext, h_zero, h_contr, h_coe, h_cont⟩

private lemma concreteBorchersForm_shift_sub_norm_le
    (C : ContinuumSchwingerOS) (F : BorchersPos) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
      ‖concreteBorchersForm C (concreteBorchersShift t F - F)
          (concreteBorchersShift t F - F)‖ ≤ M * t ^ 2 := by
  obtain ⟨C_E0, α, k, hC_E0, hα, h_E0⟩ := C.linear_growth_E0
  choose C_t hC_t_nn hC_t_bd using fun m n : ℕ => concreteReflectTensorData.tensor_seminorm_le m n k
  let L : ℕ → ℝ := fun m =>
    ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * SchwartzMap.seminorm ℂ i 1 (F m).1
  have hL_nn : ∀ m, 0 ≤ L m := fun m =>
    Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)
  let M : ℝ := ∑ m ∈ F.support, ∑ n ∈ F.support,
    C_E0 ^ (m + n) * ((Nat.factorial (m + n) : ℝ) ^ α) * C_t m n *
      ((k + 1 : ℕ) : ℝ) ^ 2 * L m * L n
  have hM_nn : 0 ≤ M := by
    refine Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun n _ => ?_
    have h1 : 0 ≤ C_E0 ^ (m + n) := pow_nonneg hC_E0.le _
    have h2 : 0 ≤ (Nat.factorial (m + n) : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have := hC_t_nn m n
    have := hL_nn m
    have := hL_nn n
    positivity
  refine ⟨M, hM_nn, fun t ht => ?_⟩
  let ΔF : BorchersPos := concreteBorchersShift t F - F
  have h_supp : ΔF.support ⊆ F.support := by
    intro m hm
    rw [DFinsupp.mem_support_iff] at hm ⊢
    intro hFm0
    apply hm
    have h1 : (concreteBorchersShift t F) m = 0 := by
      change (borchersShift concreteReflectTensorData t F) m = 0
      unfold borchersShift
      simp only [DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_apply, hFm0, map_zero]
    change (concreteBorchersShift t F - F) m = 0
    rw [show (concreteBorchersShift t F - F) m = (concreteBorchersShift t F) m - F m from rfl,
      h1, hFm0, sub_zero]
  have h_refl_zero : ∀ m, concreteReflectTensorData.reflectConj m (0 : EuclideanSchwartz m) = 0 := by
    intro m
    have h0 : (0 : EuclideanSchwartz m) = (0 : ℂ) • (0 : EuclideanSchwartz m) := by simp
    rw [h0, concreteReflectTensorData.reflectConj_smul]; simp
  have h_ten_zero_left : ∀ m n (g : EuclideanSchwartz n),
      concreteReflectTensorData.tensor m n 0 g = 0 := by
    intro m n g
    have h0 : (0 : EuclideanSchwartz m) = (0 : ℂ) • (0 : EuclideanSchwartz m) := by simp
    rw [h0, concreteReflectTensorData.tensor_smul_left]; simp
  have h_ten_zero_right : ∀ m n (f : EuclideanSchwartz m),
      concreteReflectTensorData.tensor m n f 0 = 0 := by
    intro m n f
    have h0 : (0 : EuclideanSchwartz n) = (0 : ℂ) • (0 : EuclideanSchwartz n) := by simp
    rw [h0, concreteReflectTensorData.tensor_smul_right]; simp
  have h_form_eq : concreteBorchersForm C ΔF ΔF =
      ∑ m ∈ F.support, ∑ n ∈ F.support,
        C.S (m + n) (concreteReflectTensorData.tensor m n
          (concreteReflectTensorData.reflectConj m (ΔF m).1) (ΔF n).1) := by
    have h_def : concreteBorchersForm C ΔF ΔF =
        ∑ m ∈ ΔF.support, ∑ n ∈ ΔF.support,
          C.S (m + n) (concreteReflectTensorData.tensor m n
            (concreteReflectTensorData.reflectConj m (ΔF m).1) (ΔF n).1) := by
      change borchersForm C concreteReflectTensorData ΔF ΔF = _
      unfold borchersForm
      simp only [DFinsupp.sum]
      rfl
    rw [h_def, Finset.sum_subset h_supp]
    · refine Finset.sum_congr rfl fun m _ => ?_
      refine Finset.sum_subset h_supp fun n _ hn => ?_
      have hn0 : ΔF n = 0 := DFinsupp.notMem_support_iff.mp hn
      rw [hn0, show (0 : PosSchwartzSubmodule n).1 = 0 from rfl, h_ten_zero_right, map_zero]
    · intro m _ hm
      have hm0 : ΔF m = 0 := DFinsupp.notMem_support_iff.mp hm
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [hm0, show (0 : PosSchwartzSubmodule m).1 = 0 from rfl, h_refl_zero,
        h_ten_zero_left, map_zero]
  have h_delta_eq : ∀ m, (ΔF m).1 =
      timeShiftSchwartz t (F m).1 - timeShiftSchwartz 0 (F m).1 := by
    intro m
    have h1 : (concreteReflectTensorData.shiftPos t m (F m)).1 =
        timeShiftSchwartz t (F m).1 :=
      concreteReflectTensorData_shiftPos_coe ht.1.le m (F m)
    have h2 : (F m).1 = timeShiftSchwartz 0 (F m).1 := by
      have h0 := concreteReflectTensorData_shiftPos_coe le_rfl m (F m)
      rw [concreteReflectTensorData_shiftPos_zero m (F m)] at h0
      exact h0
    change (concreteReflectTensorData.shiftPos t m (F m) - F m).1 = _
    rw [Submodule.coe_sub, h1]
    exact congrArg (timeShiftSchwartz t (F m).1 - ·) h2
  have h_semi_delta : ∀ m, ∀ j ≤ k,
      SchwartzMap.seminorm ℂ j 0 (ΔF m).1 ≤ L m * t := by
    intro m j hj
    rw [h_delta_eq m]
    have hsub := timeShiftSchwartz_seminorm_sub_le (F m).1 t 0 j 0
    have ht_abs : |t - 0| = t := by rw [sub_zero, abs_of_pos ht.1]
    have hmax : max |t| |(0 : ℝ)| = t := by
      rw [abs_zero, abs_of_pos ht.1, max_eq_left ht.1.le]
    rw [ht_abs, hmax] at hsub
    have hsum_le :
        (∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * t ^ (j - i) * SchwartzMap.seminorm ℂ i 1 (F m).1) ≤ L m := by
      calc (∑ i ∈ Finset.range (j + 1),
            (j.choose i : ℝ) * t ^ (j - i) * SchwartzMap.seminorm ℂ i 1 (F m).1)
          ≤ ∑ i ∈ Finset.range (j + 1),
              (k.choose i : ℝ) * 1 * SchwartzMap.seminorm ℂ i 1 (F m).1 := by
            refine Finset.sum_le_sum fun i _ => ?_
            refine mul_le_mul_of_nonneg_right (mul_le_mul
              (Nat.cast_le.mpr (Nat.choose_le_choose i hj))
              (pow_le_one₀ ht.1.le ht.2.le)
              (pow_nonneg ht.1.le _) (Nat.cast_nonneg _)) (apply_nonneg _ _)
        _ = ∑ i ∈ Finset.range (j + 1),
              (k.choose i : ℝ) * SchwartzMap.seminorm ℂ i 1 (F m).1 := by
            refine Finset.sum_congr rfl fun i _ => by ring
        _ ≤ L m := by
            refine Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_mono (Nat.add_le_add_right hj 1)) ?_
            intro i _ _
            exact mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)
    calc SchwartzMap.seminorm ℂ j 0 (timeShiftSchwartz t (F m).1 - timeShiftSchwartz 0 (F m).1)
        ≤ t * ∑ i ∈ Finset.range (j + 1),
            (j.choose i : ℝ) * t ^ (j - i) * SchwartzMap.seminorm ℂ i 1 (F m).1 := hsub
      _ ≤ t * L m := mul_le_mul_of_nonneg_left hsum_le ht.1.le
      _ = L m * t := mul_comm _ _
  change ‖concreteBorchersForm C ΔF ΔF‖ ≤ M * t ^ 2
  rw [h_form_eq]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun m _ => ?_
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun n _ => ?_
  have h1 := h_E0 (m + n) (concreteReflectTensorData.tensor m n
    (concreteReflectTensorData.reflectConj m (ΔF m).1) (ΔF n).1)
  have h2 := hC_t_bd m n (concreteReflectTensorData.reflectConj m (ΔF m).1) (ΔF n).1
  have h_sum_refl :
      (∑ j ∈ Finset.range (k + 1),
        SchwartzMap.seminorm ℂ j 0 (concreteReflectTensorData.reflectConj m (ΔF m).1)) ≤
      ((k + 1 : ℕ) : ℝ) * L m * t := by
    calc (∑ j ∈ Finset.range (k + 1),
          SchwartzMap.seminorm ℂ j 0 (concreteReflectTensorData.reflectConj m (ΔF m).1))
        ≤ ∑ j ∈ Finset.range (k + 1), SchwartzMap.seminorm ℂ j 0 (ΔF m).1 :=
          Finset.sum_le_sum fun j _ => concreteReflectTensorData.reflectConj_seminorm_le m j _
      _ ≤ ∑ _j ∈ Finset.range (k + 1), L m * t :=
          Finset.sum_le_sum fun j hj =>
            h_semi_delta m j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      _ = ((k + 1 : ℕ) : ℝ) * L m * t := by simp [Finset.sum_const]; ring
  have h_sum_g :
      (∑ j ∈ Finset.range (k + 1), SchwartzMap.seminorm ℂ j 0 (ΔF n).1) ≤
      ((k + 1 : ℕ) : ℝ) * L n * t := by
    calc (∑ j ∈ Finset.range (k + 1), SchwartzMap.seminorm ℂ j 0 (ΔF n).1)
        ≤ ∑ _j ∈ Finset.range (k + 1), L n * t :=
          Finset.sum_le_sum fun j hj =>
            h_semi_delta n j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      _ = ((k + 1 : ℕ) : ℝ) * L n * t := by simp [Finset.sum_const]; ring
  have h_fac_nn : 0 ≤ C_E0 ^ (m + n) * ((Nat.factorial (m + n) : ℝ) ^ α) :=
    mul_nonneg (pow_nonneg hC_E0.le _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc ‖C.S (m + n) (concreteReflectTensorData.tensor m n
          (concreteReflectTensorData.reflectConj m (ΔF m).1) (ΔF n).1)‖
      ≤ C_E0 ^ (m + n) * ((Nat.factorial (m + n) : ℝ) ^ α) *
          SchwartzMap.seminorm ℂ k 0 (concreteReflectTensorData.tensor m n
            (concreteReflectTensorData.reflectConj m (ΔF m).1) (ΔF n).1) := h1
    _ ≤ C_E0 ^ (m + n) * ((Nat.factorial (m + n) : ℝ) ^ α) *
          (C_t m n *
            (∑ j ∈ Finset.range (k + 1),
              SchwartzMap.seminorm ℂ j 0 (concreteReflectTensorData.reflectConj m (ΔF m).1)) *
            (∑ j ∈ Finset.range (k + 1), SchwartzMap.seminorm ℂ j 0 (ΔF n).1)) :=
        mul_le_mul_of_nonneg_left h2 h_fac_nn
    _ ≤ C_E0 ^ (m + n) * ((Nat.factorial (m + n) : ℝ) ^ α) *
          (C_t m n * (((k + 1 : ℕ) : ℝ) * L m * t) * (((k + 1 : ℕ) : ℝ) * L n * t)) := by
        refine mul_le_mul_of_nonneg_left ?_ h_fac_nn
        refine mul_le_mul (mul_le_mul_of_nonneg_left h_sum_refl (hC_t_nn m n))
          h_sum_g (Finset.sum_nonneg fun _ _ => apply_nonneg _ _)
          (mul_nonneg (hC_t_nn m n) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hL_nn m)) ht.1.le))
    _ = (C_E0 ^ (m + n) * ((Nat.factorial (m + n) : ℝ) ^ α) * C_t m n *
          ((k + 1 : ℕ) : ℝ) ^ 2 * L m * L n) * t ^ 2 := by
        ring

/-- **Unconditional Euclidean Semigroup Existence & Strong Right Continuity:**
    Constructs the Euclidean contraction semigroup `T` directly from `B : ConcreteBalabanTarget N hN`
    and proves `T 0 = 1`, the semigroup law, self-adjointness, contractivity, strong right
    continuity at `0`, and vacuum invariance (`0 sorry`). -/
theorem concreteBalaban_osSemigroup_exists {N : ℕ} {hN : 2 ≤ N}
    (B : ConcreteBalabanTarget N hN) :
    let pre := buildBorchersPreData B.C concreteReflectTensorData
      B.h_herm B.h_rp B.h_symm B.h_cluster
    let core := quotInnerCore pre
    letI : NormedAddCommGroup (BorchersPos ⧸ nullSubmodule pre) := core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ (BorchersPos ⧸ nullSubmodule pre) := InnerProductSpace.ofCore core.toCore
    let H := UniformSpace.Completion (BorchersPos ⧸ nullSubmodule pre)
    let Ω : H := ((Submodule.Quotient.mk borchersVac : BorchersPos ⧸ nullSubmodule pre) : H)
    ∃ T : ℝ → H →L[ℂ] H,
      T 0 = 1 ∧
      (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s + t) = T s * T t) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ x y : H, ⟪x, T t y⟫_ℂ = ⟪T t x, y⟫_ℂ) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ x : H, ‖T t x‖ ≤ ‖x‖) ∧
      (∀ x : H, Filter.Tendsto (fun t : ℝ => T t x) (𝓝[>] 0) (𝓝 x)) ∧
      (∀ t : ℝ, 0 ≤ t → T t Ω = Ω) := by
  dsimp only
  let pre := buildBorchersPreData B.C concreteReflectTensorData
    B.h_herm B.h_rp B.h_symm B.h_cluster
  let core := quotInnerCore pre
  letI : NormedAddCommGroup (BorchersPos ⧸ nullSubmodule pre) := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ (BorchersPos ⧸ nullSubmodule pre) := InnerProductSpace.ofCore core.toCore
  let H := UniformSpace.Completion (BorchersPos ⧸ nullSubmodule pre)
  let Ω₀ : BorchersPos ⧸ nullSubmodule pre := Submodule.Quotient.mk borchersVac
  let T₀ := osBorchersPreSemigroup pre
  have hT₀_zero : T₀ 0 = LinearMap.id := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ F =>
      rw [osBorchersPreSemigroup_mk pre 0 le_rfl F]
      change (Submodule.Quotient.mk (concreteBorchersShift 0 F) : BorchersPos ⧸ nullSubmodule pre) =
        Submodule.Quotient.mk F
      rw [concreteBorchersShift_zero F]
  have hT₀_contr : ∀ t : ℝ, 0 ≤ t → ∀ v : BorchersPos ⧸ nullSubmodule pre,
      ‖T₀ t v‖ ≤ ‖v‖ := by
    have h := osBorchersPreSemigroup_contr pre
    dsimp only at h
    exact h
  have hT₀_symm : ∀ t : ℝ, 0 ≤ t → ∀ x y : BorchersPos ⧸ nullSubmodule pre,
      ⟪x, T₀ t y⟫_ℂ = ⟪T₀ t x, y⟫_ℂ := by
    have h := osBorchersPreSemigroup_symm pre
    dsimp only at h
    exact h
  have hT₀_cont : ∀ v : BorchersPos ⧸ nullSubmodule pre,
      Filter.Tendsto (fun t : ℝ => (T₀ t v : H)) (𝓝[>] 0) (𝓝 (v : H)) := by
    intro v
    induction v using Submodule.Quotient.induction_on with
    | _ F =>
      rw [tendsto_iff_norm_sub_tendsto_zero]
      obtain ⟨M, hM_nn, hM_bd⟩ := concreteBorchersForm_shift_sub_norm_le B.C F
      have h_le : ∀ᶠ t : ℝ in 𝓝[>] 0,
          ‖(T₀ t (Submodule.Quotient.mk F) : H) -
              ((Submodule.Quotient.mk F : BorchersPos ⧸ nullSubmodule pre) : H)‖ ≤
            Real.sqrt M * t := by
        filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
        have hsq : ‖(T₀ t (Submodule.Quotient.mk F) : H) -
              ((Submodule.Quotient.mk F : BorchersPos ⧸ nullSubmodule pre) : H)‖ ^ 2 ≤
            (Real.sqrt M * t) ^ 2 := by
          have hmk : T₀ t (Submodule.Quotient.mk F) = Submodule.Quotient.mk (pre.θ t F) :=
            osBorchersPreSemigroup_mk pre t ht.1.le F
          have hsub :
              (T₀ t (Submodule.Quotient.mk F) : H) -
                ((Submodule.Quotient.mk F : BorchersPos ⧸ nullSubmodule pre) : H) =
              ((Submodule.Quotient.mk (pre.θ t F - F) : BorchersPos ⧸ nullSubmodule pre) : H) := by
            rw [hmk, ← UniformSpace.Completion.coe_sub]
            congr 1
          rw [hsub, UniformSpace.Completion.norm_coe]
          have h_inner_sq :
              (⟪(Submodule.Quotient.mk (pre.θ t F - F) : BorchersPos ⧸ nullSubmodule pre),
                  Submodule.Quotient.mk (pre.θ t F - F)⟫_ℂ).re =
                ‖(Submodule.Quotient.mk (pre.θ t F - F) : BorchersPos ⧸ nullSubmodule pre)‖ ^ 2 := by
            rw [inner_self_eq_norm_sq_to_K]; norm_cast
          rw [← h_inner_sq]
          have h_re :
              (⟪(Submodule.Quotient.mk (pre.θ t F - F) : BorchersPos ⧸ nullSubmodule pre),
                  Submodule.Quotient.mk (pre.θ t F - F)⟫_ℂ).re ≤
                ‖concreteBorchersForm B.C (concreteBorchersShift t F - F)
                  (concreteBorchersShift t F - F)‖ :=
            Complex.re_le_norm _
          have h_mul_sq : (Real.sqrt M * t) ^ 2 = M * t ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hM_nn]
          rw [h_mul_sq]
          exact le_trans h_re (hM_bd t ht)
        have h_rhs_nn : 0 ≤ Real.sqrt M * t := mul_nonneg (Real.sqrt_nonneg _) ht.1.le
        nlinarith [norm_nonneg ((T₀ t (Submodule.Quotient.mk F) : H) -
          ((Submodule.Quotient.mk F : BorchersPos ⧸ nullSubmodule pre) : H))]
      have h_lim : Filter.Tendsto (fun t : ℝ => Real.sqrt M * t) (𝓝[>] 0) (𝓝 0) := by
        have h0 : Filter.Tendsto (fun t : ℝ => Real.sqrt M * t) (𝓝 0) (𝓝 (Real.sqrt M * 0)) :=
          (continuous_const.mul continuous_id).continuousAt.tendsto
        rw [mul_zero] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) h_le h_lim
  obtain ⟨T_ext, h_zero, h_contr, h_coe, h_cont⟩ :=
    osSemigroup_extend_to_completion T₀ hT₀_zero hT₀_contr hT₀_cont
  have h_add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T_ext (s + t) = T_ext s * T_ext t := by
    intro s t hs ht
    ext ψ
    induction ψ using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (T_ext (s + t)).continuous ((T_ext s * T_ext t).continuous)
    | ih v =>
      change T_ext (s + t) (v : H) = T_ext s (T_ext t (v : H))
      rw [h_coe v (s + t) (add_nonneg hs ht), h_coe v t ht, h_coe (T₀ t v) s hs,
        osBorchersPreSemigroup_add pre s t hs ht v]
  have h_symm : ∀ t : ℝ, 0 ≤ t → ∀ x y : H, ⟪x, T_ext t y⟫_ℂ = ⟪T_ext t x, y⟫_ℂ := by
    intro t ht x y
    induction x, y using UniformSpace.Completion.induction_on₂ with
    | hp =>
      exact isClosed_eq
        (continuous_fst.inner ((T_ext t).continuous.comp continuous_snd))
        (((T_ext t).continuous.comp continuous_fst).inner continuous_snd)
    | ih x y =>
      rw [h_coe x t ht, h_coe y t ht,
        UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe,
        hT₀_symm t ht x y]
  have h_vac : ∀ t : ℝ, 0 ≤ t → T_ext t (Ω₀ : H) = (Ω₀ : H) := by
    intro t ht
    rw [h_coe Ω₀ t ht]
    change ((osBorchersPreSemigroup pre t (Submodule.Quotient.mk pre.e₀) :
        BorchersPos ⧸ nullSubmodule pre) : H) =
      ((Submodule.Quotient.mk pre.e₀ : BorchersPos ⧸ nullSubmodule pre) : H)
    rw [osBorchersPreSemigroup_vac pre t ht]
  exact ⟨T_ext, h_zero, h_add, h_symm, h_contr, h_cont, h_vac⟩

/-- From `B : ConcreteBalabanTarget N hN`, the Euclidean semigroup satisfies `T 0 = 1`. -/
theorem osSemigroup_zero_eq_id {N : ℕ} {hN : 2 ≤ N}
    (B : ConcreteBalabanTarget N hN) :
    let pre := buildBorchersPreData B.C concreteReflectTensorData
      B.h_herm B.h_rp B.h_symm B.h_cluster
    let core := quotInnerCore pre
    letI : NormedAddCommGroup (BorchersPos ⧸ nullSubmodule pre) := core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ (BorchersPos ⧸ nullSubmodule pre) := InnerProductSpace.ofCore core.toCore
    let H := UniformSpace.Completion (BorchersPos ⧸ nullSubmodule pre)
    ∃ T : ℝ → H →L[ℂ] H, T 0 = 1 := by
  rcases concreteBalaban_osSemigroup_exists B with ⟨T, hT0, _⟩
  exact ⟨T, hT0⟩

/-- From `B : ConcreteBalabanTarget N hN`, the Euclidean semigroup is strongly right-continuous at `0`. -/
theorem osSemigroup_strong_right_continuous_at_zero {N : ℕ} {hN : 2 ≤ N}
    (B : ConcreteBalabanTarget N hN) :
    let pre := buildBorchersPreData B.C concreteReflectTensorData
      B.h_herm B.h_rp B.h_symm B.h_cluster
    let core := quotInnerCore pre
    letI : NormedAddCommGroup (BorchersPos ⧸ nullSubmodule pre) := core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ (BorchersPos ⧸ nullSubmodule pre) := InnerProductSpace.ofCore core.toCore
    let H := UniformSpace.Completion (BorchersPos ⧸ nullSubmodule pre)
    ∃ T : ℝ → H →L[ℂ] H,
      T 0 = 1 ∧
      ∀ ψ : H, Filter.Tendsto (fun t : ℝ => T t ψ) (𝓝[>] 0) (𝓝 ψ) := by
  rcases concreteBalaban_osSemigroup_exists B with ⟨T, hT0, _, _, _, hT_cont, _⟩
  exact ⟨T, hT0, hT_cont⟩

end Imscribing.YangMills.OSCanonicalSemigroupContinuity
