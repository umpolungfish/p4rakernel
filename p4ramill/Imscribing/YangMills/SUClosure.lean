import Imscribing.YangMills.OSCompletion
import Imscribing.YangMills.IIDOS
import Imscribing.YangMills.IIDContinuation
import Imscribing.YangMills.IIDSchwingerFromWilson
import Imscribing.YangMills.IIDPoincareContinuation
import Imscribing.YangMills.WilsonFrobeniusAndSmeared4D
import Imscribing.YangMills.AsymptoticFreedomAndOSClosure

namespace YangMills.SUClosure

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 8000000

open scoped InnerProductSpace BigOperators
open Complex Real Filter MeasureTheory Set
open Imscribing.YangMills.WilsonFrobenius4D

private noncomputable def canonSUMeas (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) := inferInstance

private lemma canonSUBorel (N : ℕ) :
    @BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) _ (canonSUMeas N) := by
  letI : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) := canonSUMeas N
  exact inferInstance

/-! ## §1. Unconditional `SmearedOSPreData 1` on `iidOS4DStrict` -/

noncomputable def iidSmearedOSPreData :
    SmearedOSPreData 1 iidOS4DStrict.toOS4DContinuumTheory where
  E := OSPosTestSpace
  F := osConfigForm iidOS4DStrict.toOS4DContinuumTheory iid_osConfigKernel_herm
  Ω_E := osConfigSingle emptyPosConfig
  Ω_E_norm := osConfigVac_norm iidOS4DStrict.toOS4DContinuumTheory
    iid_osConfigKernel_herm iidSchwinger_S0
  T_E_pre := osTimeShiftSemigroup
  T_E_zero := osTimeShiftSemigroup_zero
  T_E_add := osTimeShiftSemigroup_add
  T_E_sa := osTimeShiftSemigroup_sa iidOS4DStrict.toOS4DContinuumTheory
    iid_osConfigKernel_herm iid_osConfigKernel_kern
  T_E_ub := fun t ht f =>
    ⟨((osConfigForm iidOS4DStrict.toOS4DContinuumTheory iid_osConfigKernel_herm).B f f).re,
      fun k => by
        have hc := osTimeShiftSemigroup_contr iidOS4DStrict.toOS4DContinuumTheory
          iid_osConfigKernel_herm iid_osConfigKernel_kern 2 (by norm_num) iidSchwinger_growth
          (((2 ^ k : ℕ) : ℝ) * t) (mul_nonneg (Nat.cast_nonneg _) ht) f
        simpa using hc⟩
  H_pre := 0
  H_bound := 0
  H_bound_nn := le_rfl
  H_bd := fun _ => by simp [osConfigForm, osConfigInner]
  H_sa := fun _ _ => by simp [osConfigForm, osConfigInner]
  H_nonneg := fun _ => by simp [osConfigForm, osConfigInner]
  H_vac := rfl
  U_pre := fun _ => LinearMap.id
  U_unit_pre := fun _ _ _ => rfl
  U_vac_pre := fun _ => rfl
  φ_pre := fun _ => LinearMap.id
  φ_bound := fun _ => 1
  φ_bound_nn := fun _ => zero_le_one
  φ_bd := fun _ v => by simp
  cov_pre := fun _ _ _ => rfl
  loc_pre := fun _ _ _ _ => rfl
  P2_spec := {0}
  spec_cond := by rintro _ rfl; exact le_rfl
  gap_spec := by rintro _ rfl; exact Or.inl rfl
  cyclic_dense := by
    let F := osConfigForm iidOS4DStrict.toOS4DContinuumTheory iid_osConfigKernel_herm
    let Ω : OSHilbertSpace F := osCompletionMap F (osPreMk F (osConfigSingle emptyPosConfig))
    let S : Set (OSHilbertSpace F) :=
      {v : OSHilbertSpace F | ∃ (k : ℕ) (xs : Fin k → Space4),
        v = (List.ofFn (fun _ : Fin k =>
          osLiftOperator F (LinearMap.id : OSPosTestSpace →ₗ[ℂ] OSPosTestSpace)
            1 zero_le_one (fun w => by simp))).foldr
          (fun A acc => A acc) Ω}
    let V := Submodule.span ℂ S
    have hΩ : Ω ∈ S := ⟨0, Fin.elim0, rfl⟩
    have hrange : Set.range (osCompletionMap F) ⊆ (V.topologicalClosure : Set (OSHilbertSpace F)) := by
      rintro _ ⟨u, rfl⟩
      apply subset_closure
      refine Quotient.inductionOn u fun f => ?_
      change osCompletionMap F (osPreMk F f) ∈ V
      rcases iid_osCompletionMap_rank_one f with ⟨c, hc⟩
      have hc' : osCompletionMap F (osPreMk F f) = c • Ω := hc
      rw [hc']
      exact V.smul_mem c (Submodule.subset_span hΩ)
    have htop : (Set.univ : Set (OSHilbertSpace F)) ⊆
        (V.topologicalClosure : Set (OSHilbertSpace F)) := by
      rw [← osCompletionMap_dense F]
      exact closure_minimal hrange isClosed_closure
    exact top_unique fun v _ => htop (Set.mem_univ v)

/-! ## §2. Elementary Frobenius Algebra & SU(N) Haar Ball Lower Bound -/

private lemma frobeniusNormSq_trace {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) :
    frobeniusNormSq M = (Matrix.trace (M * star M)).re := by
  unfold frobeniusNormSq
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hz : (M i j * starRingEnd ℂ (M i j)).re = ‖M i j‖ ^ 2 := by
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    ring
  exact hz.symm

private lemma frobeniusNormSq_neg {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) :
    frobeniusNormSq (-M) = frobeniusNormSq M := by
  unfold frobeniusNormSq
  simp

private lemma frobeniusNormSq_su_eq {N : ℕ} (A : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    frobeniusNormSq (A : Matrix (Fin N) (Fin N) ℂ) = (N : ℝ) := by
  unfold frobeniusNormSq
  simp [Imscribing.YangMills.WilsonBounds4D.gaugeGroup_row_norm_sq_sum]

private lemma frobeniusNormSq_mul_su_right {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ)
    (B : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    frobeniusNormSq (M * (B : Matrix (Fin N) (Fin N) ℂ)) = frobeniusNormSq M := by
  rw [frobeniusNormSq_trace, frobeniusNormSq_trace]
  have hB : (B : Matrix (Fin N) (Fin N) ℂ) * star (B : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    (Unitary.mem_iff.mp B.2.1).2
  have hstar : star (M * (B : Matrix (Fin N) (Fin N) ℂ)) =
      star (B : Matrix (Fin N) (Fin N) ℂ) * star M := Matrix.conjTranspose_mul M _
  rw [hstar, Matrix.mul_assoc, ← Matrix.mul_assoc (B : Matrix (Fin N) (Fin N) ℂ), hB,
    Matrix.one_mul]

private lemma frobeniusNormSq_mul_su_left {N : ℕ}
    (B : Matrix.specialUnitaryGroup (Fin N) ℂ) (M : Matrix (Fin N) (Fin N) ℂ) :
    frobeniusNormSq ((B : Matrix (Fin N) (Fin N) ℂ) * M) = frobeniusNormSq M := by
  rw [frobeniusNormSq_trace, frobeniusNormSq_trace]
  have hB : star (B : Matrix (Fin N) (Fin N) ℂ) * (B : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    (Unitary.mem_iff.mp B.2.1).1
  have hstar : star ((B : Matrix (Fin N) (Fin N) ℂ) * M) =
      star M * star (B : Matrix (Fin N) (Fin N) ℂ) := Matrix.conjTranspose_mul _ M
  have hmul : Matrix.trace (((B : Matrix (Fin N) (Fin N) ℂ) * M) *
      star ((B : Matrix (Fin N) (Fin N) ℂ) * M)) = Matrix.trace (M * star M) := by
    rw [hstar, Matrix.trace_mul_comm ((B : Matrix (Fin N) (Fin N) ℂ) * M),
      Matrix.mul_assoc, ← Matrix.mul_assoc (star (B : Matrix (Fin N) (Fin N) ℂ)), hB,
      Matrix.one_mul, Matrix.trace_mul_comm]
  rw [hmul]

private lemma frobeniusNormSq_su_inv_sub_one {N : ℕ}
    (A : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    frobeniusNormSq (((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) - 1) =
      frobeniusNormSq ((A : Matrix (Fin N) (Fin N) ℂ) - 1) := by
  have hinv : ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
      (A : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    congrArg Subtype.val (inv_mul_cancel A)
  rw [← frobeniusNormSq_mul_su_right _ A, Matrix.sub_mul, Matrix.one_mul, hinv]
  unfold frobeniusNormSq
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.sub_apply, Matrix.sub_apply, norm_sub_rev]

private lemma frobeniusNormSq_add_le {N : ℕ} (M₁ M₂ : Matrix (Fin N) (Fin N) ℂ) :
    frobeniusNormSq (M₁ + M₂) ≤ 2 * frobeniusNormSq M₁ + 2 * frobeniusNormSq M₂ := by
  unfold frobeniusNormSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : ‖(M₁ + M₂) i j‖ ≤ ‖M₁ i j‖ + ‖M₂ i j‖ := norm_add_le (M₁ i j) (M₂ i j)
  have h2 : ‖(M₁ + M₂) i j‖ ^ 2 ≤ (‖M₁ i j‖ + ‖M₂ i j‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖M₁ i j‖ - ‖M₂ i j‖)]

private lemma frobeniusNormSq_su_sub_su_le {N : ℕ}
    (A B : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    frobeniusNormSq ((A : Matrix (Fin N) (Fin N) ℂ) - (B : Matrix (Fin N) (Fin N) ℂ)) ≤
      4 * (N : ℝ) := by
  rw [sub_eq_add_neg]
  calc frobeniusNormSq ((A : Matrix (Fin N) (Fin N) ℂ) + -(B : Matrix (Fin N) (Fin N) ℂ))
      ≤ 2 * frobeniusNormSq (A : Matrix (Fin N) (Fin N) ℂ) +
          2 * frobeniusNormSq (-(B : Matrix (Fin N) (Fin N) ℂ)) := frobeniusNormSq_add_le _ _
    _ = 4 * (N : ℝ) := by
        rw [frobeniusNormSq_neg, frobeniusNormSq_su_eq A, frobeniusNormSq_su_eq B]
        ring

private lemma frobeniusNormSq_sub_self_su {N : ℕ}
    (A B : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    frobeniusNormSq (((A * B⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) - 1) =
      frobeniusNormSq ((A : Matrix (Fin N) (Fin N) ℂ) - (B : Matrix (Fin N) (Fin N) ℂ)) := by
  have hB : ((B⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
      (B : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    congrArg Subtype.val (inv_mul_cancel B)
  rw [← frobeniusNormSq_mul_su_right _ B, Matrix.sub_mul, Matrix.one_mul]
  change frobeniusNormSq ((A : Matrix (Fin N) (Fin N) ℂ) *
      ((B⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
      (B : Matrix (Fin N) (Fin N) ℂ) - (B : Matrix (Fin N) (Fin N) ℂ)) = _
  rw [Matrix.mul_assoc, hB, Matrix.mul_one]

private lemma frobeniusNormSq_su_mul_sub_one {N : ℕ}
    (A B : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    frobeniusNormSq (((A * B : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) - 1) ≤
      2 * frobeniusNormSq ((A : Matrix (Fin N) (Fin N) ℂ) - 1) +
      2 * frobeniusNormSq ((B : Matrix (Fin N) (Fin N) ℂ) - 1) := by
  have heq : ((A * B : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) - 1 =
      ((A : Matrix (Fin N) (Fin N) ℂ) - 1) * (B : Matrix (Fin N) (Fin N) ℂ) +
      ((B : Matrix (Fin N) (Fin N) ℂ) - 1) := by
    change (A : Matrix (Fin N) (Fin N) ℂ) * (B : Matrix (Fin N) (Fin N) ℂ) - 1 = _
    rw [Matrix.sub_mul, Matrix.one_mul]
    abel
  rw [heq]
  exact (frobeniusNormSq_add_le _ _).trans_eq (by rw [frobeniusNormSq_mul_su_right])

private lemma frobeniusNormSq_holonomy4_le {N : ℕ}
    (A B C D : Matrix.specialUnitaryGroup (Fin N) ℂ) {δ : ℝ}
    (hA : frobeniusNormSq ((A : Matrix (Fin N) (Fin N) ℂ) - 1) ≤ δ ^ 2)
    (hB : frobeniusNormSq ((B : Matrix (Fin N) (Fin N) ℂ) - 1) ≤ δ ^ 2)
    (hC : frobeniusNormSq ((C : Matrix (Fin N) (Fin N) ℂ) - 1) ≤ δ ^ 2)
    (hD : frobeniusNormSq ((D : Matrix (Fin N) (Fin N) ℂ) - 1) ≤ δ ^ 2) :
    frobeniusNormSq (((A * (B * (C⁻¹ * (D⁻¹ * 1))) :
        Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) - 1) ≤
      16 * δ ^ 2 := by
  have h_eq : A * (B * (C⁻¹ * (D⁻¹ * 1))) = (A * B) * (C⁻¹ * D⁻¹) := by group
  rw [h_eq]
  have hAB := frobeniusNormSq_su_mul_sub_one A B
  have hCD := frobeniusNormSq_su_mul_sub_one C⁻¹ D⁻¹
  rw [frobeniusNormSq_su_inv_sub_one C, frobeniusNormSq_su_inv_sub_one D] at hCD
  have h_all := frobeniusNormSq_su_mul_sub_one (A * B) (C⁻¹ * D⁻¹)
  linarith only [hAB, hCD, h_all, hA, hB, hC, hD]

private lemma su_entry_re_im_bound {N : ℕ}
    (A : Matrix.specialUnitaryGroup (Fin N) ℂ) (i j : Fin N) :
    -1 ≤ ((A : Matrix (Fin N) (Fin N) ℂ) i j).re ∧
      ((A : Matrix (Fin N) (Fin N) ℂ) i j).re ≤ 1 ∧
    -1 ≤ ((A : Matrix (Fin N) (Fin N) ℂ) i j).im ∧
      ((A : Matrix (Fin N) (Fin N) ℂ) i j).im ≤ 1 := by
  have hU : star (A : Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    (Unitary.mem_iff.mp A.2.1).1
  have hjj := congr_fun (congr_fun hU j) j
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at hjj
  have hre := congrArg Complex.re hjj
  rw [Complex.re_sum, Complex.one_re] at hre
  have hsq_le : ‖(A : Matrix (Fin N) (Fin N) ℂ) i j‖ ^ 2 ≤ 1 := by
    have hterm : ∀ k : Fin N, (star ((A : Matrix (Fin N) (Fin N) ℂ) k j) *
        (A : Matrix (Fin N) (Fin N) ℂ) k j).re = ‖(A : Matrix (Fin N) (Fin N) ℂ) k j‖ ^ 2 := by
      intro k
      change (starRingEnd ℂ ((A : Matrix (Fin N) (Fin N) ℂ) k j) *
        (A : Matrix (Fin N) (Fin N) ℂ) k j).re = _
      rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    simp_rw [hterm] at hre
    calc ‖(A : Matrix (Fin N) (Fin N) ℂ) i j‖ ^ 2
        ≤ ∑ k : Fin N, ‖(A : Matrix (Fin N) (Fin N) ℂ) k j‖ ^ 2 :=
          Finset.single_le_sum (fun k _ => sq_nonneg ‖(A : Matrix (Fin N) (Fin N) ℂ) k j‖)
            (Finset.mem_univ i)
      _ = 1 := hre
  have hnorm : ‖(A : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ 1 :=
    (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hsq_le)
  have hre_abs : |((A : Matrix (Fin N) (Fin N) ℂ) i j).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans hnorm
  have him_abs : |((A : Matrix (Fin N) (Fin N) ℂ) i j).im| ≤ 1 :=
    (Complex.abs_im_le_norm _).trans hnorm
  exact ⟨(abs_le.mp hre_abs).1, (abs_le.mp hre_abs).2,
    (abs_le.mp him_abs).1, (abs_le.mp him_abs).2⟩

private lemma suHaar_ball_ge (N : ℕ) [NeZero N] {δ : ℝ} (hδ : 0 < δ) :
    let K : ℕ := Nat.ceil (4 * (N : ℝ) / δ) + 1
    let B : Set (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
      { A | frobeniusNormSq ((A : Matrix (Fin N) (Fin N) ℂ) - 1) ≤ δ ^ 2 }
    (1 : ℝ) / ((K : ℝ) ^ (2 * N * N)) ≤ (suHaar N B).toReal := by
  intro K B
  have hK_pos : 0 < K := Nat.succ_pos _
  have hK_real_pos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK_pos
  have hK_ge : 4 * (N : ℝ) / δ ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (by dsimp [K]; exact_mod_cast Nat.le_succ _)
  let inBox : Fin K → ℝ → Prop := fun m r =>
    -1 + 2 * (m : ℝ) / (K : ℝ) ≤ r ∧ r ≤ -1 + 2 * ((m : ℝ) + 1) / (K : ℝ)
  have h_cover_1d : ∀ r ∈ Set.Icc (-1 : ℝ) 1, ∃ m : Fin K, inBox m r := by
    intro r ⟨hr_lo, hr_hi⟩
    by_cases hr1 : r = 1
    · subst hr1
      refine ⟨⟨K - 1, Nat.sub_lt hK_pos Nat.one_pos⟩, ?_⟩
      have hm1 : ((K - 1 : ℕ) : ℝ) + 1 = (K : ℝ) := by exact_mod_cast Nat.sub_add_cancel hK_pos
      have hm_le : ((K - 1 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast Nat.sub_le K 1
      refine ⟨?_, ?_⟩
      · have h1 : 2 * ((K - 1 : ℕ) : ℝ) / (K : ℝ) ≤ 2 :=
          (div_le_iff₀ hK_real_pos).mpr (by linarith only [hm_le])
        linarith only [h1]
      · rw [hm1, mul_div_cancel_right₀ _ hK_real_pos.ne']; linarith only []
    · have hr_lt : r < 1 := lt_of_le_of_ne hr_hi hr1
      let t : ℝ := (r + 1) * (K : ℝ) / 2
      have hr1_nn : 0 ≤ r + 1 := by linarith only [hr_lo]
      have ht_nn : 0 ≤ t := by dsimp [t]; positivity
      have ht_lt : t < (K : ℝ) := by
        dsimp [t]
        have hr2 : r + 1 < 2 := by linarith only [hr_lt]
        nlinarith only [hr2, hK_real_pos]
      let m_nat : ℕ := Nat.floor t
      have hm_lt : m_nat < K := Nat.floor_lt ht_nn |>.mpr (by exact_mod_cast ht_lt)
      refine ⟨⟨m_nat, hm_lt⟩, ?_⟩
      have hm_le : (m_nat : ℝ) ≤ t := Nat.floor_le ht_nn
      have hm_gt : t < (m_nat : ℝ) + 1 := Nat.lt_floor_add_one t
      refine ⟨?_, ?_⟩
      · dsimp [t] at hm_le
        have h2m : 2 * (m_nat : ℝ) / (K : ℝ) ≤ r + 1 := by
          rw [div_le_iff₀ hK_real_pos]; linarith only [hm_le]
        linarith only [h2m]
      · dsimp [t] at hm_gt
        have hr2m : r + 1 ≤ 2 * ((m_nat : ℝ) + 1) / (K : ℝ) := by
          rw [le_div_iff₀ hK_real_pos]; linarith only [hm_gt]
        linarith only [hr2m]
  let Idx := Fin N × Fin N × Fin 2 → Fin K
  let box : Idx → Set (Matrix.specialUnitaryGroup (Fin N) ℂ) := fun b =>
    { A | ∀ i j : Fin N,
      inBox (b (i, j, 0)) ((A : Matrix (Fin N) (Fin N) ℂ) i j).re ∧
      inBox (b (i, j, 1)) ((A : Matrix (Fin N) (Fin N) ℂ) i j).im }
  have h_box_meas : ∀ b : Idx, MeasurableSet (box b) := by
    intro b
    have h_eq : box b =
        ⋂ p : Fin N × Fin N,
          ({ A : Matrix.specialUnitaryGroup (Fin N) ℂ |
              inBox (b (p.1, p.2, 0)) ((A : Matrix (Fin N) (Fin N) ℂ) p.1 p.2).re } ∩
           { A : Matrix.specialUnitaryGroup (Fin N) ℂ |
              inBox (b (p.1, p.2, 1)) ((A : Matrix (Fin N) (Fin N) ℂ) p.1 p.2).im }) := by
      ext A; simp [box]
    rw [h_eq]
    refine MeasurableSet.iInter fun p => MeasurableSet.inter ?_ ?_
    · have hc : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          ((A : Matrix (Fin N) (Fin N) ℂ) p.1 p.2).re) :=
        Complex.continuous_re.comp ((continuous_apply p.2).comp ((continuous_apply p.1).comp continuous_subtype_val))
      exact (measurableSet_Icc.preimage hc.measurable)
    · have hc : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          ((A : Matrix (Fin N) (Fin N) ℂ) p.1 p.2).im) :=
        Complex.continuous_im.comp ((continuous_apply p.2).comp ((continuous_apply p.1).comp continuous_subtype_val))
      exact (measurableSet_Icc.preimage hc.measurable)
  have h_univ_sub : Set.univ ⊆ ⋃ b : Idx, box b := by
    intro A _
    have h0 : ∀ i j, ∃ m, inBox m ((A : Matrix (Fin N) (Fin N) ℂ) i j).re := fun i j =>
      h_cover_1d _ ⟨(su_entry_re_im_bound A i j).1, (su_entry_re_im_bound A i j).2.1⟩
    have h1 : ∀ i j, ∃ m, inBox m ((A : Matrix (Fin N) (Fin N) ℂ) i j).im := fun i j =>
      h_cover_1d _ ⟨(su_entry_re_im_bound A i j).2.2.1, (su_entry_re_im_bound A i j).2.2.2⟩
    let b : Idx := fun ⟨i, j, c⟩ =>
      if c = 0 then Classical.choose (h0 i j) else Classical.choose (h1 i j)
    refine Set.mem_iUnion.mpr ⟨b, fun i j => ?_⟩
    exact ⟨by simpa [b] using Classical.choose_spec (h0 i j),
      by simpa [b] using Classical.choose_spec (h1 i j)⟩
  have hB_meas : MeasurableSet B := by
    have hc : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        frobeniusNormSq ((A : Matrix (Fin N) (Fin N) ℂ) - 1)) := by
      unfold frobeniusNormSq
      refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
      exact (continuous_norm.comp ((continuous_apply j).comp
        ((continuous_apply i).comp (continuous_subtype_val.sub continuous_const)))).pow 2
    exact measurableSet_Iic.preimage hc.measurable
  have h_box_le : ∀ b : Idx, suHaar N (box b) ≤ suHaar N B := by
    intro b
    by_cases hne : (box b).Nonempty
    · obtain ⟨A₀, hA₀⟩ := hne
      have hsub : box b ⊆ (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ => A * A₀⁻¹) ⁻¹' B := by
        intro A hA
        change frobeniusNormSq (((A * A₀⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ) - 1) ≤ δ ^ 2
        rw [frobeniusNormSq_sub_self_su A A₀]
        unfold frobeniusNormSq
        have h_pt : ∀ i j : Fin N,
            ‖((A : Matrix (Fin N) (Fin N) ℂ) - (A₀ : Matrix (Fin N) (Fin N) ℂ)) i j‖ ^ 2 ≤
              8 / (K : ℝ) ^ 2 := by
          intro i j
          have hre_diff : |((A : Matrix (Fin N) (Fin N) ℂ) i j).re -
              ((A₀ : Matrix (Fin N) (Fin N) ℂ) i j).re| ≤ 2 / (K : ℝ) := by
            obtain ⟨ha1, ha2⟩ := (hA i j).1
            obtain ⟨hb1, hb2⟩ := (hA₀ i j).1
            have hspan : 2 * ((b (i, j, 0) : ℝ) + 1) / (K : ℝ) -
                2 * (b (i, j, 0) : ℝ) / (K : ℝ) = 2 / (K : ℝ) := by ring
            rw [abs_le]
            constructor <;> linarith only [ha1, ha2, hb1, hb2, hspan]
          have him_diff : |((A : Matrix (Fin N) (Fin N) ℂ) i j).im -
              ((A₀ : Matrix (Fin N) (Fin N) ℂ) i j).im| ≤ 2 / (K : ℝ) := by
            obtain ⟨ha1, ha2⟩ := (hA i j).2
            obtain ⟨hb1, hb2⟩ := (hA₀ i j).2
            have hspan : 2 * ((b (i, j, 1) : ℝ) + 1) / (K : ℝ) -
                2 * (b (i, j, 1) : ℝ) / (K : ℝ) = 2 / (K : ℝ) := by ring
            rw [abs_le]
            constructor <;> linarith only [ha1, ha2, hb1, hb2, hspan]
          have hnsq : ‖((A : Matrix (Fin N) (Fin N) ℂ) - (A₀ : Matrix (Fin N) (Fin N) ℂ)) i j‖ ^ 2 =
              (((A : Matrix (Fin N) (Fin N) ℂ) i j).re -
                ((A₀ : Matrix (Fin N) (Fin N) ℂ) i j).re) ^ 2 +
              (((A : Matrix (Fin N) (Fin N) ℂ) i j).im -
                ((A₀ : Matrix (Fin N) (Fin N) ℂ) i j).im) ^ 2 := by
            rw [Matrix.sub_apply, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
              Complex.sub_re, Complex.sub_im]
            ring
          rw [hnsq]
          have hsq1 : (((A : Matrix (Fin N) (Fin N) ℂ) i j).re -
              ((A₀ : Matrix (Fin N) (Fin N) ℂ) i j).re) ^ 2 ≤ (2 / (K : ℝ)) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre_diff 2
          have hsq2 : (((A : Matrix (Fin N) (Fin N) ℂ) i j).im -
              ((A₀ : Matrix (Fin N) (Fin N) ℂ) i j).im) ^ 2 ≤ (2 / (K : ℝ)) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) him_diff 2
          calc _ ≤ (2 / (K : ℝ)) ^ 2 + (2 / (K : ℝ)) ^ 2 := add_le_add hsq1 hsq2
            _ = 8 / (K : ℝ) ^ 2 := by ring
        calc ∑ i : Fin N, ∑ j : Fin N,
              ‖((A : Matrix (Fin N) (Fin N) ℂ) - (A₀ : Matrix (Fin N) (Fin N) ℂ)) i j‖ ^ 2
            ≤ ∑ _i : Fin N, ∑ _j : Fin N, (8 / (K : ℝ) ^ 2) :=
              Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h_pt i j
          _ = 8 * (N : ℝ) ^ 2 / (K : ℝ) ^ 2 := by simp [Finset.sum_const]; ring
          _ ≤ 8 * (N : ℝ) ^ 2 / (4 * (N : ℝ) / δ) ^ 2 := by
              have hN_nn : 0 ≤ 4 * (N : ℝ) / δ := by positivity
              have hsq : (4 * (N : ℝ) / δ) ^ 2 ≤ (K : ℝ) ^ 2 :=
                pow_le_pow_left₀ hN_nn hK_ge 2
              have hN_pos : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
              exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
          _ = δ ^ 2 / 2 := by
              have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
              field_simp [hN_ne, hδ.ne']; ring
          _ ≤ δ ^ 2 := by linarith only [sq_nonneg δ]
      calc suHaar N (box b)
          ≤ suHaar N ((fun A : Matrix.specialUnitaryGroup (Fin N) ℂ => A * A₀⁻¹) ⁻¹' B) :=
            MeasureTheory.measure_mono hsub
        _ = MeasureTheory.Measure.map (fun A => A * A₀⁻¹) (suHaar N) B := by
            rw [MeasureTheory.Measure.map_apply (continuous_mul_right A₀⁻¹).measurable hB_meas]
        _ = suHaar N B := by rw [suHaar_map_mul_right N A₀⁻¹]
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      simp [hne]
  haveI := suHaar_prob N
  have h_fin_union : ∀ s : Finset Idx, suHaar N (⋃ b ∈ s, box b) ≤ ∑ b ∈ s, suHaar N (box b) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      have h_ins : (⋃ b ∈ insert a s, box b) = box a ∪ ⋃ b ∈ s, box b := by
        ext x; simp
      rw [h_ins, Finset.sum_insert ha]
      exact (MeasureTheory.measure_union_le _ _).trans (add_le_add le_rfl ih)
  have h_eq_univ : (⋃ b : Idx, box b) = ⋃ b ∈ (Finset.univ : Finset Idx), box b := by
    ext x; simp
  have h_sum_ge : (1 : ENNReal) ≤ ∑ _b : Idx, suHaar N B := by
    calc (1 : ENNReal) = suHaar N Set.univ := MeasureTheory.measure_univ.symm
      _ ≤ suHaar N (⋃ b : Idx, box b) := MeasureTheory.measure_mono h_univ_sub
      _ = suHaar N (⋃ b ∈ (Finset.univ : Finset Idx), box b) := by rw [h_eq_univ]
      _ ≤ ∑ b : Idx, suHaar N (box b) := h_fin_union Finset.univ
      _ ≤ ∑ _b : Idx, suHaar N B := Finset.sum_le_sum fun b _ => h_box_le b
  have h_card : Fintype.card Idx = K ^ (2 * N * N) := by
    simp [Idx, Fintype.card_prod]; ring
  rw [Finset.sum_const, Finset.card_univ, h_card, nsmul_eq_mul] at h_sum_ge
  have h_top : suHaar N B ≠ ⊤ := MeasureTheory.measure_ne_top _ _
  have h_real : (1 : ℝ) ≤ ((K : ℝ) ^ (2 * N * N)) * (suHaar N B).toReal := by
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) h_top) h_sum_ge
    simpa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow] using h1
  exact (div_le_iff₀ (pow_pos hK_real_pos _)).mpr (by linarith only [h_real])

/-! ## §3. Central Slice Symmetry `Φ_z` & Gap Vanishing on `fullRankCubicNonAbelianWilsonSetup` -/

private noncomputable def centralElem (N : ℕ) (hN : 2 ≤ N) :
    Matrix.specialUnitaryGroup (Fin N) ℂ :=
  let c : ℂ := Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))
  have hc_norm : ‖c‖ = 1 := by
    dsimp [c]
    have h_arg : (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)).re = 0 := by
      have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      rw [show 2 * (Real.pi : ℂ) * Complex.I / (N : ℂ) =
        (((2 * Real.pi / (N : ℝ)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
      simp
    rw [Complex.norm_exp, h_arg, Real.exp_zero]
  have hc_mul : star c * c = 1 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, ← Complex.ofReal_one]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, hc_norm, one_pow]
  have hc_pow : c ^ N = 1 := by
    dsimp [c]
    rw [← Complex.exp_nat_mul]
    have hN_ne : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    rw [mul_div_cancel₀ _ hN_ne, Complex.exp_two_pi_mul_I]
  ⟨c • (1 : Matrix (Fin N) (Fin N) ℂ),
    Unitary.mem_iff.mpr
      ⟨by rw [star_smul, star_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
            smul_smul, hc_mul, one_smul],
       by rw [star_smul, star_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
            smul_smul, show c * star c = 1 from by rw [mul_comm]; exact hc_mul, one_smul]⟩,
    MonoidHom.mem_mker.mpr (by
      change Matrix.det (c • (1 : Matrix (Fin N) (Fin N) ℂ)) = 1
      rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, hc_pow])⟩

private lemma centralElem_ne_one (N : ℕ) (hN : 2 ≤ N) :
    Complex.exp (2 * Real.pi * Complex.I / (N : ℂ)) ≠ 1 := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hθ_pos : 0 < 2 * Real.pi / (N : ℝ) := div_pos (mul_pos two_pos Real.pi_pos) hN_pos
  have hθ_le : 2 * Real.pi / (N : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hN_pos]
    calc 2 * Real.pi ≤ (N : ℝ) * Real.pi :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hN) Real.pi_pos.le
      _ = Real.pi * (N : ℝ) := mul_comm _ _
  have hcos_lt : Real.cos (2 * Real.pi / (N : ℝ)) < 1 := by
    rw [← Real.cos_zero]
    exact Real.strictAntiOn_cos (Set.left_mem_Icc.mpr Real.pi_pos.le)
      ⟨hθ_pos.le, hθ_le⟩ hθ_pos
  have hre : (Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))).re =
      Real.cos (2 * Real.pi / (N : ℝ)) := by
    rw [show 2 * (Real.pi : ℂ) * Complex.I / (N : ℂ) =
      (((2 * Real.pi / (N : ℝ)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I_re]
  intro heq
  have hre_eq := congrArg Complex.re heq
  rw [hre, Complex.one_re] at hre_eq
  linarith only [hre_eq, hcos_lt]

private lemma centralElem_comm {N : ℕ} (hN : 2 ≤ N)
    (A : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    centralElem N hN * A = A * centralElem N hN := by
  ext i j
  change ((Complex.exp (2 * Real.pi * Complex.I / (N : ℂ)) • (1 : Matrix (Fin N) (Fin N) ℂ)) *
      (A : Matrix (Fin N) (Fin N) ℂ)) i j =
    ((A : Matrix (Fin N) (Fin N) ℂ) *
      (Complex.exp (2 * Real.pi * Complex.I / (N : ℂ)) • (1 : Matrix (Fin N) (Fin N) ℂ))) i j
  simp

private noncomputable def sliceCenterFlip (L N : ℕ) [NeZero L] (hN : 2 ≤ N)
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  fun e => if e.1.1 = 0 ∧ e.2 = 0 then centralElem N hN * U e else U e

private noncomputable def sliceCenterUnflip (L N : ℕ) [NeZero L] (hN : 2 ≤ N)
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  fun e => if e.1.1 = 0 ∧ e.2 = 0 then (centralElem N hN)⁻¹ * U e else U e

private noncomputable def sliceCenterFlipEquiv (L N : ℕ) [NeZero L] (hN : 2 ≤ N) :
    letI := canonSUMeas N
    GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) where
  toFun := sliceCenterFlip L N hN
  invFun := sliceCenterUnflip L N hN
  left_inv U := by
    funext e
    dsimp [sliceCenterFlip, sliceCenterUnflip]
    split_ifs <;> simp [← mul_assoc]
  right_inv U := by
    funext e
    dsimp [sliceCenterFlip, sliceCenterUnflip]
    split_ifs <;> simp [← mul_assoc]
  measurable_toFun := by
    letI := canonSUMeas N
    haveI := canonSUBorel N
    have h_eval : ∀ e : (cubicTorus3 L).Link,
        Measurable (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) => U e) :=
      fun e => (measurable_pi_apply e :
        @Measurable ((cubicTorus3 L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ)
          (Matrix.specialUnitaryGroup (Fin N) ℂ) MeasurableSpace.pi (canonSUMeas N) (fun U => U e))
    exact measurable_pi_iff.mpr fun e => by
      dsimp [sliceCenterFlip]
      split_ifs
      · exact (continuous_mul_left _).measurable.comp (h_eval e)
      · exact h_eval e
  measurable_invFun := by
    letI := canonSUMeas N
    haveI := canonSUBorel N
    have h_eval : ∀ e : (cubicTorus3 L).Link,
        Measurable (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) => U e) :=
      fun e => (measurable_pi_apply e :
        @Measurable ((cubicTorus3 L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ)
          (Matrix.specialUnitaryGroup (Fin N) ℂ) MeasurableSpace.pi (canonSUMeas N) (fun U => U e))
    exact measurable_pi_iff.mpr fun e => by
      dsimp [sliceCenterUnflip]
      split_ifs
      · exact (continuous_mul_left _).measurable.comp (h_eval e)
      · exact h_eval e

private lemma sliceCenterFlip_continuous (L N : ℕ) [NeZero L] (hN : 2 ≤ N) :
    Continuous (sliceCenterFlip L N hN) := by
  refine continuous_pi fun e => ?_
  dsimp [sliceCenterFlip]
  split_ifs
  · exact (continuous_mul_left (centralElem N hN)).comp (continuous_apply e)
  · exact continuous_apply e

private lemma sliceCenterFlip_measurePreserving (L N : ℕ) [NeZero L] (hN : 2 ≤ N) :
    letI := canonSUMeas N
    haveI := canonSUBorel N
    MeasureTheory.MeasurePreserving (sliceCenterFlipEquiv L N hN)
      (latticeHaarMeasure L N) (latticeHaarMeasure L N) := by
  letI := canonSUMeas N
  haveI := canonSUBorel N
  haveI := suHaar_prob N
  let φ : (cubicTorus3 L).Link →
      Matrix.specialUnitaryGroup (Fin N) ℂ → Matrix.specialUnitaryGroup (Fin N) ℂ :=
    fun e u => if e.1.1 = 0 ∧ e.2 = 0 then centralElem N hN * u else u
  have hmeas : Measurable (sliceCenterFlipEquiv L N hN) :=
    (sliceCenterFlipEquiv L N hN).measurable
  refine ⟨hmeas, ?_⟩
  symm
  change MeasureTheory.Measure.pi (fun _ : (cubicTorus3 L).Link => suHaar N) =
    MeasureTheory.Measure.map (⇑(sliceCenterFlipEquiv L N hN))
      (MeasureTheory.Measure.pi (fun _ : (cubicTorus3 L).Link => suHaar N))
  have hmeas' : @Measurable _ _ MeasurableSpace.pi MeasurableSpace.pi
      (sliceCenterFlipEquiv L N hN) := hmeas
  refine MeasureTheory.Measure.pi_eq fun s hs => ?_
  rw [MeasureTheory.Measure.map_apply hmeas' (MeasurableSet.univ_pi hs)]
  have hpre : sliceCenterFlipEquiv L N hN ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun e => φ e ⁻¹' s e) := by
    ext U; rfl
  rw [hpre, MeasureTheory.Measure.pi_pi (fun _ => suHaar N) _]
  refine Finset.prod_congr rfl fun e _ => ?_
  dsimp [φ]; split_ifs
  · have hmap := suHaar_map_mul_left N (centralElem N hN)
    rw [← MeasureTheory.Measure.map_apply (continuous_mul_left _).measurable (hs e), hmap]
  · rfl

private lemma wilsonAction_sliceCenterFlip (L N : ℕ) [NeZero L] (hN : 2 ≤ N) (β : ℝ)
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonAction β (cubicPlaquettes L) (sliceCenterFlip L N hN U) =
      wilsonAction β (cubicPlaquettes L) U := by
  have hc := centralElem_comm hN
  have hc_inv : ∀ A : Matrix.specialUnitaryGroup (Fin N) ℂ,
      A * (centralElem N hN)⁻¹ = (centralElem N hN)⁻¹ * A := fun A => by
    have h := congrArg (fun M => (centralElem N hN)⁻¹ * M * (centralElem N hN)⁻¹) (hc A)
    simpa [mul_assoc] using h
  have h_cancel : ∀ A B C D : Matrix.specialUnitaryGroup (Fin N) ℂ,
      (centralElem N hN * A) * (B * ((centralElem N hN * C)⁻¹ * (D * 1))) =
        A * (B * (C⁻¹ * (D * 1))) := by
    intro A B C D
    rw [mul_inv_rev]
    calc (centralElem N hN * A) * (B * (C⁻¹ * (centralElem N hN)⁻¹ * (D * 1)))
        = centralElem N hN * (A * (((B * C⁻¹) * (centralElem N hN)⁻¹) * (D * 1))) := by
            simp only [mul_assoc]
      _ = centralElem N hN * (A * (((centralElem N hN)⁻¹ * (B * C⁻¹)) * (D * 1))) := by
            rw [hc_inv (B * C⁻¹)]
      _ = centralElem N hN * ((A * (centralElem N hN)⁻¹) * ((B * C⁻¹) * (D * 1))) := by
            simp only [mul_assoc]
      _ = centralElem N hN * (((centralElem N hN)⁻¹ * A) * ((B * C⁻¹) * (D * 1))) := by
            rw [hc_inv A]
      _ = (centralElem N hN * (centralElem N hN)⁻¹) * (A * (B * (C⁻¹ * (D * 1)))) := by
            simp only [mul_assoc]
      _ = A * (B * (C⁻¹ * (D * 1))) := by rw [mul_inv_cancel, one_mul]
  have hhol_eq : ∀ (V : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
      (x : (cubicTorus3 L).Site) (d₁ d₂ : Fin 3),
      pathHolonomy V (cubicPlaquette x d₁ d₂) =
        V (x, d₁) * (V (cubicShift L d₁ x, d₂) *
          ((V (cubicShift L d₂ x, d₁))⁻¹ * ((V (x, d₂))⁻¹ * 1))) := fun _ _ _ _ => rfl
  have hshift1 : ∀ x : (cubicTorus3 L).Site,
      cubicShift L 1 x = (x.1, x.2.1 + 1, x.2.2) := fun _ => rfl
  have hshift2 : ∀ x : (cubicTorus3 L).Site,
      cubicShift L 2 x = (x.1, x.2.1, x.2.2 + 1) := fun _ => rfl
  have hflip_zero : ∀ x : (cubicTorus3 L).Site,
      sliceCenterFlip L N hN U (x, 0) =
        if x.1 = 0 then centralElem N hN * U (x, 0) else U (x, 0) := fun x => by
    simp [sliceCenterFlip]
  have hflip_one : ∀ x : (cubicTorus3 L).Site,
      sliceCenterFlip L N hN U (x, 1) = U (x, 1) := fun x => by
    simp [sliceCenterFlip, show (1 : Fin 3) ≠ 0 by decide]
  have hflip_two : ∀ x : (cubicTorus3 L).Site,
      sliceCenterFlip L N hN U (x, 2) = U (x, 2) := fun x => by
    simp [sliceCenterFlip, show (2 : Fin 3) ≠ 0 by decide]
  unfold wilsonAction
  congr 1
  congr 1
  refine List.map_congr_left fun p hp => ?_
  unfold wilsonPlaquetteTerm
  suffices hhol : pathHolonomy (sliceCenterFlip L N hN U) p.loop = pathHolonomy U p.loop by
    rw [hhol]
  unfold cubicPlaquettes at hp
  simp only [List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ⟨x, rfl | rfl | rfl⟩
  · rw [hhol_eq, hhol_eq, hshift1 x, hflip_zero x, hflip_one (cubicShift L 0 x),
      hflip_zero (x.1, x.2.1 + 1, x.2.2), hflip_one x]
    dsimp only
    by_cases hx : x.1 = 0
    · simp only [hx, ↓reduceIte]
      exact h_cancel _ _ _ _
    · simp only [hx, ↓reduceIte]
  · rw [hhol_eq, hhol_eq, hshift2 x, hflip_zero x, hflip_two (cubicShift L 0 x),
      hflip_zero (x.1, x.2.1, x.2.2 + 1), hflip_two x]
    dsimp only
    by_cases hx : x.1 = 0
    · simp only [hx, ↓reduceIte]
      exact h_cancel _ _ _ _
    · simp only [hx, ↓reduceIte]
  · rw [hhol_eq, hhol_eq, hflip_one x, hflip_two (cubicShift L 1 x),
      hflip_one (cubicShift L 2 x), hflip_two x]

private lemma wilsonGramKernel_sliceCenterFlip (L N : ℕ) [NeZero L] (hN : 2 ≤ N) (β : ℝ)
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    letI := canonSUMeas N
    haveI := canonSUBorel N
    wilsonGramKernel L N (cubicLinkKineticKernel L N β)
      (sliceCenterFlip L N hN U) (sliceCenterFlip L N hN U') =
      wilsonGramKernel L N (cubicLinkKineticKernel L N β) U U' := by
  letI := canonSUMeas N
  haveI := canonSUBorel N
  have hmp := sliceCenterFlip_measurePreserving L N hN
  unfold wilsonGramKernel
  rw [← hmp.integral_comp' (fun W => cubicLinkKineticKernel L N β
    (sliceCenterFlip L N hN U) W * cubicLinkKineticKernel L N β (sliceCenterFlip L N hN U') W)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  have h_chi : ∀ X Y, cubicLinkKineticKernel L N β (sliceCenterFlip L N hN X)
      (sliceCenterFlip L N hN Y) = cubicLinkKineticKernel L N β X Y := by
    intro X Y
    unfold cubicLinkKineticKernel
    refine Finset.prod_congr rfl fun e _ => ?_
    dsimp [sliceCenterFlip]
    split_ifs
    · have hcancel : (centralElem N hN * X e) * (centralElem N hN * Y e)⁻¹ = X e * (Y e)⁻¹ := by
        rw [mul_inv_rev, centralElem_comm hN (X e), mul_assoc, ← mul_assoc (centralElem N hN),
          centralElem_comm hN (Y e)⁻¹, mul_assoc (Y e)⁻¹, mul_inv_cancel, mul_one]
      have hcoe : ((centralElem N hN * X e : Matrix.specialUnitaryGroup (Fin N) ℂ) :
            Matrix (Fin N) (Fin N) ℂ) *
          (((centralElem N hN * Y e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
            Matrix (Fin N) (Fin N) ℂ) =
          ((X e : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
          (((Y e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := by
        simpa using congrArg Subtype.val hcancel
      rw [hcoe]
    · rfl
  change cubicLinkKineticKernel L N β (sliceCenterFlip L N hN U) (sliceCenterFlip L N hN W) *
      cubicLinkKineticKernel L N β (sliceCenterFlip L N hN U') (sliceCenterFlip L N hN W) =
    cubicLinkKineticKernel L N β U W * cubicLinkKineticKernel L N β U' W
  rw [h_chi U W, h_chi U' W]

private noncomputable def cubicGapErr (L N : ℕ) (β : ℝ) : ℝ :=
  let links : ℕ := 3 * L ^ 3
  let ε_sq : ℝ := 4 * (N : ℝ) * ((6 * (N : ℝ) ^ 2 * (links : ℝ) + 2) * Real.log β) / β
  let K : ℕ := Nat.ceil (4 * (N : ℝ) / (1 / Real.sqrt β)) + 1
  (2 * ε_sq + 8 * (N : ℝ) * Real.exp (30 * (L : ℝ) ^ 3 / (N : ℝ)) *
    ((K : ℝ) ^ (2 * N * N)) ^ (2 * links) * β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2))) /
    (N : ℝ)

/-- **Explicit Spectral-Gap Upper Bound & Convergence to `0` (`0 sorry`):**
    On `fullRankCubicNonAbelianWilsonSetup L N hN β hβ`, as `(L³ log β) / β → 0`
    (with `exp(c L³) / β² → 0`), `S.Δ → 0`. -/
private lemma continuous_fst_fst {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] : Continuous (fun q : (α × β) × γ => q.1.1) :=
  continuous_fst.comp continuous_fst

private lemma continuous_fst_snd {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] : Continuous (fun q : (α × β) × γ => q.1.2) :=
  continuous_snd.comp continuous_fst

private lemma continuous_prod3_left {α γ : Type*} [TopologicalSpace α] [TopologicalSpace γ]
    {f : α → α → γ} (hf : Continuous (Function.uncurry f)) :
    Continuous (fun q : (α × α) × α => f q.1.1 q.2) :=
  hf.comp (continuous_fst_fst.prodMk continuous_snd)

private lemma continuous_prod3_right {α γ : Type*} [TopologicalSpace α] [TopologicalSpace γ]
    {f : α → α → γ} (hf : Continuous (Function.uncurry f)) :
    Continuous (fun q : (α × α) × α => f q.1.2 q.2) :=
  hf.comp (continuous_fst_snd.prodMk continuous_snd)

private lemma continuous_prod2_left {α γ : Type*} [TopologicalSpace α] [TopologicalSpace γ]
    {f : α → α → γ} (hf : Continuous (Function.uncurry f)) (U : α) :
    Continuous (fun W : α => f U W) :=
  hf.comp (continuous_const.prodMk continuous_id)

theorem fullRankCubic_gap_upper_bound (L N : ℕ) [NeZero L] (hN : 2 ≤ N)
    {β : ℝ} (hβ : 1 ≤ β) (herr_lt : cubicGapErr L N β < 1) :
    letI := canonSUMeas N
    haveI := canonSUBorel N
    (fullRankCubicNonAbelianWilsonSetup L N hN β (lt_of_lt_of_le zero_lt_one hβ)).gaugeSetup.Δ ≤
      -Real.log (1 - cubicGapErr L N β) := by
  letI := canonSUMeas N
  haveI := canonSUBorel N
  haveI : NeZero N := ⟨by omega⟩
  have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  let S := (fullRankCubicNonAbelianWilsonSetup L N hN β hβ_pos).gaugeSetup
  let links : ℕ := 3 * L ^ 3
  let ε_sq : ℝ := 4 * (N : ℝ) * ((6 * (N : ℝ) ^ 2 * (links : ℝ) + 2) * Real.log β) / β
  let K : ℕ := Nat.ceil (4 * (N : ℝ) / (1 / Real.sqrt β)) + 1
  let err : ℝ := cubicGapErr L N β
  change S.Δ ≤ -Real.log (1 - err)
  let G_L := GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  haveI := instIsOpenPosLatticeHaar L N
  let χ := cubicLinkKineticKernel L N β
  let K_kin := wilsonGramKernel L N χ
  let K_W := wilsonKernel β (cubicPlaquettes L) K_kin
  have hχ_cont := continuous_cubicLinkKineticKernel L N β
  have hχ_nn := linkChi_nn L N hN β hβ_pos.le
  have hχ_lb := fun U W => (cubicLinkKineticKernel_bounds L N (by omega) β hβ_pos.le U W).1
  have hχ_bd := fun U W => (cubicLinkKineticKernel_bounds L N (by omega) β hβ_pos.le U W).2
  have hK_cont := continuous_wilsonGramKernel L N χ hχ_cont hχ_nn (linkChiUb L β) (linkChiUb_nonneg L β) hχ_bd
  have hK_symm := wilsonGramKernel_symm L N χ
  have hK_nn := wilsonGramKernel_nonneg L N χ hχ_nn
  have hK_bd := wilsonGramKernel_le L N χ hχ_cont hχ_nn (linkChiUb L β) (linkChiUb_nonneg L β) hχ_bd
  have hKW_cont : Continuous (Function.uncurry K_W) :=
    continuous_cubicWilsonKernel L N β K_kin hK_cont
  have hKW_nn : ∀ U U', 0 ≤ K_W U U' :=
    wilsonKernel_nonneg β (cubicPlaquettes L) K_kin hK_nn
  have hKW_symm : ∀ U U', K_W U' U = K_W U U' :=
    wilsonKernel_symm β (cubicPlaquettes L) K_kin hK_symm
  let T_raw := fullRankTRaw L N β hβ_pos.le χ hχ_cont (linkChiLb L β) (linkChiLb_pos L β)
    hχ_lb (linkChiUb L β) (linkChiUb_nonneg L β) hχ_bd
  let gs := fullRankGS L N β hβ_pos.le χ hχ_cont (cubicLinkKineticKernel_gauge_inv L N β)
    (linkChiLb L β) (linkChiLb_pos L β) hχ_lb (linkChiUb L β) (linkChiUb_nonneg L β) hχ_bd
  let Ω : HaarGaugeSpace μ := S.Ω
  let ω := Classical.choose (Classical.choose_spec gs)
  have hgs : IsWilsonGroundState L N β hβ_pos.le K_kin hK_cont hK_nn
      ((linkChiUb L β) ^ 2) (sq_nonneg _) hK_bd Ω ω :=
    Classical.choose_spec (Classical.choose_spec gs)
  let lam0 : ℝ := ‖T_raw‖
  have hlam0_pos : 0 < lam0 := hgs.norm_pos
  have hS_T : S.T = ((lam0⁻¹ : ℝ) : ℂ) • T_raw := rfl
  have hcinner : ∀ a b : ℂ, ⟪a, b⟫_ℂ = starRingEnd ℂ a * b := by
    intro a b
    have h1 : ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K]; norm_num
    calc ⟪a, b⟫_ℂ = ⟪a • (1 : ℂ), b • (1 : ℂ)⟫_ℂ := by simp
      _ = starRingEnd ℂ a * (b * ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ) := by
            rw [inner_smul_left, inner_smul_right]
      _ = starRingEnd ℂ a * b := by rw [h1, mul_one]
  -- 1. Slice-center unitary symmetry Z_op fixes Ω and ω
  let e_flip := sliceCenterFlipEquiv L N hN
  let hmp : MeasureTheory.MeasurePreserving e_flip μ μ :=
    sliceCenterFlip_measurePreserving L N hN
  let Z_op : HaarGaugeSpace μ →L[ℂ] HaarGaugeSpace μ :=
    LinearMap.mkContinuous
      { toFun := fun ψ => (memLp_comp_measurePreserving μ e_flip hmp ψ).toLp (fun U => ψ (e_flip U))
        map_add' := fun ψ₁ ψ₂ => by
          apply MeasureTheory.Lp.ext
          have h1 := (memLp_comp_measurePreserving μ e_flip hmp (ψ₁ + ψ₂)).coeFn_toLp
          have h2 := (memLp_comp_measurePreserving μ e_flip hmp ψ₁).coeFn_toLp
          have h3 := (memLp_comp_measurePreserving μ e_flip hmp ψ₂).coeFn_toLp
          have hadd := MeasureTheory.Lp.coeFn_add ψ₁ ψ₂
          have hadd' := MeasureTheory.Lp.coeFn_add
            ((memLp_comp_measurePreserving μ e_flip hmp ψ₁).toLp (fun U => ψ₁ (e_flip U)))
            ((memLp_comp_measurePreserving μ e_flip hmp ψ₂).toLp (fun U => ψ₂ (e_flip U)))
          filter_upwards [h1, h2, h3, ae_comp_measurePreserving hmp hadd, hadd'] with U hu1 hu2 hu3 ha1 ha2
          simp only [Pi.add_apply] at ha1 ha2 ⊢; rw [hu1, ha1, ha2, hu2, hu3]
        map_smul' := fun c ψ => by
          apply MeasureTheory.Lp.ext
          have h1 := (memLp_comp_measurePreserving μ e_flip hmp (c • ψ)).coeFn_toLp
          have h2 := (memLp_comp_measurePreserving μ e_flip hmp ψ).coeFn_toLp
          have hsm := MeasureTheory.Lp.coeFn_smul c ψ
          have hsm' := MeasureTheory.Lp.coeFn_smul c
            ((memLp_comp_measurePreserving μ e_flip hmp ψ).toLp (fun U => ψ (e_flip U)))
          filter_upwards [h1, h2, ae_comp_measurePreserving hmp hsm, hsm'] with U hu1 hu2 hs1 hs2
          simp only [Pi.smul_apply, RingHom.id_apply] at hs1 hs2 ⊢; rw [hu1, hs1, hs2, hu2] }
      1 (fun ψ => by
        let ψ' := (memLp_comp_measurePreserving μ e_flip hmp ψ).toLp (fun U => ψ (e_flip U))
        have h_eq : ‖ψ'‖ ^ 2 = ‖ψ‖ ^ 2 := by
          have h_in : ⟪ψ', ψ'⟫_ℂ = ⟪ψ, ψ⟫_ℂ := by
            rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
            have hcoe := (memLp_comp_measurePreserving μ e_flip hmp ψ).coeFn_toLp
            calc ∫ U, ⟪ψ' U, ψ' U⟫_ℂ ∂μ
                = ∫ U, ⟪ψ (e_flip U), ψ (e_flip U)⟫_ℂ ∂μ := by
                    refine MeasureTheory.integral_congr_ae ?_
                    filter_upwards [hcoe] with U hU; rw [hU]
              _ = ∫ U, ⟪ψ U, ψ U⟫_ℂ ∂μ := hmp.integral_comp' (fun U => ⟪ψ U, ψ U⟫_ℂ)
          have hre := congrArg Complex.re h_in
          rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hre
          simpa [pow_two] using hre
        change ‖ψ'‖ ≤ 1 * ‖ψ‖
        rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), one_mul, h_eq])
  have hZ_unit : ∀ u v, ⟪Z_op u, Z_op v⟫_ℂ = ⟪u, v⟫_ℂ := fun u v => by
    have h1 := (memLp_comp_measurePreserving μ e_flip hmp u).coeFn_toLp
    have h2 := (memLp_comp_measurePreserving μ e_flip hmp v).coeFn_toLp
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    calc ∫ U, ⟪(Z_op u) U, (Z_op v) U⟫_ℂ ∂μ
        = ∫ U, ⟪u (e_flip U), v (e_flip U)⟫_ℂ ∂μ := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [h1, h2] with U hu1 hu2
            change ⟪((memLp_comp_measurePreserving μ e_flip hmp u).toLp _) U,
              ((memLp_comp_measurePreserving μ e_flip hmp v).toLp _) U⟫_ℂ = _
            rw [hu1, hu2]
      _ = ∫ U, ⟪u U, v U⟫_ℂ ∂μ := hmp.integral_comp' (fun U => ⟪u U, v U⟫_ℂ)
  have hKW_flip : ∀ U U', K_W (e_flip U) (e_flip U') = K_W U U' := fun U U' => by
    change wilsonKernel β (cubicPlaquettes L) K_kin (sliceCenterFlip L N hN U)
        (sliceCenterFlip L N hN U') = wilsonKernel β (cubicPlaquettes L) K_kin U U'
    dsimp [wilsonKernel]
    rw [wilsonAction_sliceCenterFlip, wilsonAction_sliceCenterFlip]
    dsimp only [K_kin, χ]
    rw [wilsonGramKernel_sliceCenterFlip]
  have hT_raw_def : T_raw = wilsonIntegralOp L N β hβ_pos.le K_kin hK_cont hK_nn
      ((linkChiUb L β) ^ 2) (sq_nonneg _) hK_bd := rfl
  have hlam0_def : ‖wilsonIntegralOp L N β hβ_pos.le K_kin hK_cont hK_nn
      ((linkChiUb L β) ^ 2) (sq_nonneg _) hK_bd‖ = lam0 := by
    rw [← hT_raw_def]
  have hZ_apply : ∀ φ : HaarGaugeSpace μ,
      Z_op φ = (memLp_comp_measurePreserving μ e_flip hmp φ).toLp (fun U => φ (e_flip U)) :=
    fun _ => rfl
  have hT_comm_Z : ∀ ψ, T_raw (Z_op ψ) = Z_op (T_raw ψ) := fun ψ => by
    apply MeasureTheory.Lp.ext
    rw [hT_raw_def]
    have h1 := wilsonIntegralOp_apply_ae L N β hβ_pos.le K_kin hK_cont hK_nn
      ((linkChiUb L β) ^ 2) (sq_nonneg _) hK_bd (Z_op ψ)
    have h2 := (memLp_comp_measurePreserving μ e_flip hmp
      (wilsonIntegralOp L N β hβ_pos.le K_kin hK_cont hK_nn
        ((linkChiUb L β) ^ 2) (sq_nonneg _) hK_bd ψ)).coeFn_toLp
    have h3 := ae_comp_measurePreserving hmp
      (wilsonIntegralOp_apply_ae L N β hβ_pos.le K_kin hK_cont hK_nn
        ((linkChiUb L β) ^ 2) (sq_nonneg _) hK_bd ψ)
    have hZψ := (memLp_comp_measurePreserving μ e_flip hmp ψ).coeFn_toLp
    filter_upwards [h1, h2, h3] with U hu1 hu2 hu3
    change ⇑(wilsonIntegralOp L N β hβ_pos.le K_kin hK_cont hK_nn
        ((linkChiUb L β) ^ 2) (sq_nonneg _) hK_bd (Z_op ψ)) U =
      ⇑(Z_op (wilsonIntegralOp L N β hβ_pos.le K_kin hK_cont hK_nn
        ((linkChiUb L β) ^ 2) (sq_nonneg _) hK_bd ψ)) U
    rw [hu1]
    conv_rhs => rw [hZ_apply]
    rw [hu2, hu3]
    dsimp [wilsonIntegralFn]
    rw [← hmp.integral_comp' (fun U' => ((K_W (e_flip U) U' : ℝ) : ℂ) * ψ U')]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hZψ] with U' hu'
    change ((K_W U U' : ℝ) : ℂ) * ⇑(Z_op ψ) U' =
      ((K_W (e_flip U) (e_flip U') : ℝ) : ℂ) * ⇑ψ (e_flip U')
    rw [hKW_flip, hZ_apply, hu']
  have hZΩ : Z_op Ω = Ω := by
    have h_eig : T_raw (Z_op Ω) = (lam0 : ℂ) • Z_op Ω := by
      rw [hT_comm_Z, hT_raw_def, hgs.eig, hlam0_def, map_smul]
    let c : ℂ := ⟪Ω, Z_op Ω⟫_ℂ
    let w := Z_op Ω - c • Ω
    have hw_orth : ⟪w, Ω⟫_ℂ = 0 := by
      simp [w, c, inner_sub_left, inner_smul_left, inner_conj_symm, hgs.unit]
    have hw_eig : T_raw w = (lam0 : ℂ) • w := by
      simp only [w, map_sub, map_smul, h_eig]
      rw [hT_raw_def, hgs.eig, hlam0_def, smul_sub, smul_comm c]
    have hw0 : Z_op Ω = c • Ω := sub_eq_zero.mp (hgs.simple w hw_eig hw_orth)
    have hc_norm : ‖c‖ = 1 := by
      have h1 : ‖c • Ω‖ = 1 := by
        rw [← hw0, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one]
        have hin : (⟪Z_op Ω, Z_op Ω⟫_ℂ).re = 1 := by
          rw [hZ_unit, inner_self_eq_norm_sq_to_K, hgs.unit]; norm_num
        rw [inner_self_eq_norm_sq_to_K] at hin
        simpa [pow_two] using hin
      rwa [norm_smul, hgs.unit, mul_one] at h1
    have hZΩ_ae : ⇑(Z_op Ω) =ᵐ[μ] fun U => (ω (e_flip U) : ℂ) := by
      have h1 := (memLp_comp_measurePreserving μ e_flip hmp Ω).coeFn_toLp
      have h2 := ae_comp_measurePreserving hmp hgs.ae_eq
      filter_upwards [h1, h2] with U hu1 hu2; rw [hZ_apply, hu1, hu2]
    have hc_re_nn : 0 ≤ c.re := by
      have hl2 : MeasureTheory.Integrable (fun U => ⟪Ω U, (Z_op Ω) U⟫_ℂ) μ :=
        MeasureTheory.L2.integrable_inner Ω (Z_op Ω)
      dsimp [c]
      rw [MeasureTheory.L2.inner_def]
      change 0 ≤ RCLike.re (∫ U, ⟪Ω U, (Z_op Ω) U⟫_ℂ ∂μ)
      rw [← integral_re hl2]
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [hgs.ae_eq, hZΩ_ae] with U hu1 hu2
      change 0 ≤ (⟪⇑Ω U, ⇑(Z_op Ω) U⟫_ℂ).re
      rw [hu1, hu2, hcinner]
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
      exact mul_nonneg (hgs.ω_pos _).le (hgs.ω_pos _).le
    have hc_im : c.im = 0 := by
      have hl2 : MeasureTheory.Integrable (fun U => ⟪Ω U, (Z_op Ω) U⟫_ℂ) μ :=
        MeasureTheory.L2.integrable_inner Ω (Z_op Ω)
      dsimp [c]; rw [MeasureTheory.L2.inner_def]
      have h1 : (∫ U, ⟪Ω U, (Z_op Ω) U⟫_ℂ ∂μ).im =
          RCLike.re (-Complex.I * ∫ U, ⟪Ω U, (Z_op Ω) U⟫_ℂ ∂μ) := by simp [Complex.mul_re]
      rw [h1, ← MeasureTheory.integral_const_mul, ← integral_re (hl2.const_mul (-Complex.I))]
      refine MeasureTheory.integral_eq_zero_of_ae ?_
      filter_upwards [hgs.ae_eq, hZΩ_ae] with U hu1 hu2
      change (-Complex.I * ⟪⇑Ω U, ⇑(Z_op Ω) U⟫_ℂ).re = 0
      rw [hu1, hu2, hcinner]
      simp [Complex.mul_re]
    have hc1 : c = 1 := by
      have hc_eq : c = (c.re : ℂ) := Complex.ext rfl hc_im
      rw [hc_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc_re_nn] at hc_norm
      exact Complex.ext hc_norm hc_im
    rwa [hc1, one_smul] at hw0
  have hω_flip : ∀ U, ω (e_flip U) = ω U := fun U => by
    have h1 := (memLp_comp_measurePreserving μ e_flip hmp Ω).coeFn_toLp
    have h2 := ae_comp_measurePreserving hmp hgs.ae_eq
    have hZΩ_coe : ⇑(Z_op Ω) =ᵐ[μ] ⇑Ω := by rw [hZΩ]
    have h_ae : (fun U => (ω (e_flip U) : ℂ)) =ᵐ[μ] fun U => (ω U : ℂ) := by
      filter_upwards [h1, h2, hZΩ_coe, hgs.ae_eq] with x hx1 hx2 hxZ hx3
      have hx_lhs : (ω (e_flip x) : ℂ) = ⇑(Z_op Ω) x := by
        change _ = ⇑((memLp_comp_measurePreserving μ e_flip hmp Ω).toLp _) x
        rw [hx1, hx2]
      rw [hx_lhs, hxZ, hx3]
    exact Complex.ofReal_injective (eq_of_ae_continuous μ
      (Complex.continuous_ofReal.comp (hgs.ω_cont.comp (sliceCenterFlip_continuous L N hN)))
      (Complex.continuous_ofReal.comp hgs.ω_cont) h_ae U)
  -- Pointwise eigenvalue equation and normalization for `ω`
  have h_eig_ω : ∀ U, ∫ U', K_W U U' * ω U' ∂μ = lam0 * ω U := by
    have hT_ae1 := wilsonIntegralOp_apply_ae L N β hβ_pos.le K_kin hK_cont hK_nn
      ((linkChiUb L β) ^ 2) (sq_nonneg _) hK_bd Ω
    rw [← hT_raw_def] at hT_ae1
    have hT_ae2 : ⇑(T_raw Ω) =ᵐ[μ] fun U => (lam0 : ℂ) * (ω U : ℂ) := by
      have h1 : ⇑(T_raw Ω) =ᵐ[μ] ⇑((lam0 : ℂ) • Ω) := by rw [hT_raw_def, hgs.eig, hlam0_def]
      have h2 := MeasureTheory.Lp.coeFn_smul (lam0 : ℂ) Ω
      filter_upwards [h1, h2, hgs.ae_eq] with U hu1 hu2 hu3
      rw [hu1, hu2]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hu3]
    have h_all_eq : ∀ U, wilsonIntegralFn L N β K_kin Ω U = (lam0 : ℂ) * (ω U : ℂ) :=
      eq_of_ae_continuous μ
        (wilsonIntegralFn_continuous L N β hβ_pos.le K_kin hK_cont hK_nn
          ((linkChiUb L β) ^ 2) hK_bd Ω)
        (continuous_const.mul (Complex.continuous_ofReal.comp hgs.ω_cont))
        (hT_ae1.symm.trans hT_ae2)
    intro U
    have hi := wilsonKernel_mul_integrable L N β hβ_pos.le K_kin hK_cont hK_nn
      ((linkChiUb L β) ^ 2) hK_bd Ω U
    have h_eq := congrArg Complex.re (h_all_eq U)
    dsimp [wilsonIntegralFn] at h_eq
    change RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * Ω U' ∂μ) = ((lam0 : ℂ) * (ω U : ℂ)).re at h_eq
    rw [← integral_re hi] at h_eq
    have h_lhs : ∫ U', RCLike.re (((K_W U U' : ℝ) : ℂ) * Ω U') ∂μ =
        ∫ U', K_W U U' * ω U' ∂μ := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hgs.ae_eq] with U' hU'
      change (((K_W U U' : ℝ) : ℂ) * ⇑Ω U').re = K_W U U' * ω U'
      rw [hU', ← Complex.ofReal_mul, Complex.ofReal_re]
    have h_rhs : ((lam0 : ℂ) * (ω U : ℂ)).re = lam0 * ω U := by simp [Complex.mul_re]
    rw [h_lhs, h_rhs] at h_eq
    exact h_eq
  have hω_sq_int : ∫ U, ω U ^ 2 ∂μ = 1 := by
    have h1 : ‖Ω‖ ^ 2 = ∫ U, ‖Ω U‖ ^ 2 ∂μ := lp_norm_sq_eq_integral μ Ω
    have h_ae : (fun U => ‖Ω U‖ ^ 2) =ᵐ[μ] (fun U => ω U ^ 2) := by
      filter_upwards [hgs.ae_eq] with U hU
      rw [hU, Complex.norm_real, Real.norm_of_nonneg (hgs.ω_pos U).le]
    rw [← MeasureTheory.integral_congr_ae h_ae, ← h1, hgs.unit, one_pow]
  have hω_int1 : ∫ U, ω U ∂μ ≤ 1 := by
    have h_ae : (fun U => ω U) =ᵐ[μ] (fun U => ‖Ω U‖) := by
      filter_upwards [hgs.ae_eq] with U hU
      rw [hU, Complex.norm_real, Real.norm_of_nonneg (hgs.ω_pos U).le]
    rw [MeasureTheory.integral_congr_ae h_ae]
    calc ∫ U, ‖Ω U‖ ∂μ ≤ ‖Ω‖ := l1_le_l2_prob μ Ω
      _ = 1 := hgs.unit
  -- 1b. Single-link matrix-entry test modes `ψ i j` orthogonal to `Ω`
  let e₀ : (cubicTorus3 L).Link := ((0, 0, 0), 0)
  let z_c : ℂ := Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))
  have hz_ne : z_c ≠ 1 := centralElem_ne_one N hN
  have h_entry_cont : ∀ i j : Fin N, Continuous (fun U : G_L =>
      ((U e₀ : Matrix (Fin N) (Fin N) ℂ) i j)) := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp
      (continuous_subtype_val.comp (continuous_apply e₀)))
  let ψ_fn : Fin N → Fin N → G_L → ℂ := fun i j U =>
    (ω U : ℂ) * ((U e₀ : Matrix (Fin N) (Fin N) ℂ) i j)
  obtain ⟨M_ω, hM_ω⟩ := (isCompact_univ.image (continuous_abs.comp hgs.ω_cont)).bddAbove
  have hM_ω_nn : 0 ≤ max M_ω 0 := le_max_right M_ω 0
  have hψ_mem : ∀ i j : Fin N, MeasureTheory.MemLp (ψ_fn i j) 2 μ := fun i j => by
    refine memLp_two_of_measurable_bound μ (ψ_fn i j)
      ((Complex.continuous_ofReal.comp hgs.ω_cont).mul (h_entry_cont i j)).measurable
      (max M_ω 0) hM_ω_nn fun U => ?_
    dsimp [ψ_fn]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |ω U| * ‖(U e₀ : Matrix (Fin N) (Fin N) ℂ) i j‖
        ≤ max M_ω 0 * 1 := mul_le_mul (le_max_of_le_left (hM_ω ⟨U, Set.mem_univ U, rfl⟩))
            (Imscribing.YangMills.WilsonBounds4D.gaugeGroup_entry_norm_le_one (U e₀) i j)
            (norm_nonneg _) hM_ω_nn
      _ = max M_ω 0 := mul_one _
  obtain ⟨ψ, hψ_ae⟩ : ∃ ψ : Fin N → Fin N → HaarGaugeSpace μ,
      ∀ i j, ⇑(ψ i j) =ᵐ[μ] ψ_fn i j :=
    ⟨fun i j => (hψ_mem i j).toLp (ψ_fn i j), fun i j => (hψ_mem i j).coeFn_toLp⟩
  have hZ_ψ : ∀ i j, Z_op (ψ i j) = z_c • ψ i j := fun i j => by
    apply MeasureTheory.Lp.ext
    have h1 := (memLp_comp_measurePreserving μ e_flip hmp (ψ i j)).coeFn_toLp
    have h2 := ae_comp_measurePreserving hmp (hψ_ae i j)
    have h3 := MeasureTheory.Lp.coeFn_smul z_c (ψ i j)
    filter_upwards [h1, h2, h3, hψ_ae i j] with U hu1 hu2 hu3 hu4
    rw [hZ_apply, hu1, hu2, hu3]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hu4]
    dsimp only [ψ_fn]
    have he0_flip : ((e_flip U e₀ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) i j =
        z_c * ((U e₀ : Matrix (Fin N) (Fin N) ℂ) i j) := by
      change (((sliceCenterFlip L N hN U e₀ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ) i j) = _
      simp [sliceCenterFlip, e₀]
      change (((centralElem N hN : Matrix (Fin N) (Fin N) ℂ) *
          (U ((0, 0, 0), 0) : Matrix (Fin N) (Fin N) ℂ)) i j) = _
      change ((z_c • (1 : Matrix (Fin N) (Fin N) ℂ)) *
          (U ((0, 0, 0), 0) : Matrix (Fin N) (Fin N) ℂ)) i j = _
      rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul]
    rw [hω_flip U, he0_flip]
    ring
  have hψ_orth : ∀ i j, ⟪ψ i j, Ω⟫_ℂ = 0 := fun i j => by
    have hin : ⟪ψ i j, Ω⟫_ℂ = starRingEnd ℂ z_c * ⟪ψ i j, Ω⟫_ℂ := by
      calc ⟪ψ i j, Ω⟫_ℂ = ⟪Z_op (ψ i j), Z_op Ω⟫_ℂ := (hZ_unit _ _).symm
        _ = ⟪z_c • ψ i j, Ω⟫_ℂ := by rw [hZ_ψ, hZΩ]
        _ = starRingEnd ℂ z_c * ⟪ψ i j, Ω⟫_ℂ := inner_smul_left _ _ _
    have hstar_ne : 1 - starRingEnd ℂ z_c ≠ 0 := by
      intro h0
      apply hz_ne
      have h1 : starRingEnd ℂ z_c = 1 := (sub_eq_zero.mp h0).symm
      simpa using congrArg (starRingEnd ℂ) h1
    have hmul0 : (1 - starRingEnd ℂ z_c) * ⟪ψ i j, Ω⟫_ℂ = 0 := by
      calc (1 - starRingEnd ℂ z_c) * ⟪ψ i j, Ω⟫_ℂ
          = ⟪ψ i j, Ω⟫_ℂ - starRingEnd ℂ z_c * ⟪ψ i j, Ω⟫_ℂ := by ring
        _ = 0 := sub_eq_zero.mpr hin
    exact (mul_eq_zero.mp hmul0).resolve_left hstar_ne
  have hψ_norm_sum : ∑ i : Fin N, ∑ j : Fin N, ‖ψ i j‖ ^ 2 = (N : ℝ) := by
    have h_each : ∀ i j : Fin N,
        ‖ψ i j‖ ^ 2 = ∫ U, ω U ^ 2 * ‖(U e₀ : Matrix (Fin N) (Fin N) ℂ) i j‖ ^ 2 ∂μ := by
      intro i j
      rw [lp_norm_sq_eq_integral μ (ψ i j)]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hψ_ae i j] with U hU
      rw [hU]
      dsimp [ψ_fn]
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (hgs.ω_pos U).le]
    simp_rw [h_each]
    have h_int_ij : ∀ i j : Fin N, MeasureTheory.Integrable
        (fun U => ω U ^ 2 * ‖(U e₀ : Matrix (Fin N) (Fin N) ℂ) i j‖ ^ 2) μ := fun i j =>
      integrable_of_continuous_compact μ _
        ((hgs.ω_cont.pow 2).mul ((continuous_norm.comp (h_entry_cont i j)).pow 2))
    have h_sum_eq :
        (∑ i : Fin N, ∑ j : Fin N,
          ∫ U, ω U ^ 2 * ‖(U e₀ : Matrix (Fin N) (Fin N) ℂ) i j‖ ^ 2 ∂μ) =
        (N : ℝ) * ∫ U, ω U ^ 2 ∂μ := by
      have h_row : ∀ i : Fin N,
          (∑ j : Fin N, ∫ U, ω U ^ 2 * ‖(U e₀ : Matrix (Fin N) (Fin N) ℂ) i j‖ ^ 2 ∂μ) =
          ∫ U, ω U ^ 2 ∂μ := by
        intro i
        rw [← MeasureTheory.integral_finset_sum Finset.univ fun j _ => h_int_ij i j]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
        dsimp only
        rw [← Finset.mul_sum,
          Imscribing.YangMills.WilsonBounds4D.gaugeGroup_row_norm_sq_sum (U e₀) i, mul_one]
      simp_rw [h_row, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [h_sum_eq, hω_sq_int, mul_one]
  have hgap_sum :
      (1 - Real.exp (-S.Δ)) * (N : ℝ) ≤
        ∑ i : Fin N, ∑ j : Fin N, (‖ψ i j‖ ^ 2 - (⟪ψ i j, S.T (ψ i j)⟫_ℂ).re) := by
    have h_each : ∀ i j : Fin N,
        (1 - Real.exp (-S.Δ)) * ‖ψ i j‖ ^ 2 ≤
          ‖ψ i j‖ ^ 2 - (⟪ψ i j, S.T (ψ i j)⟫_ℂ).re := fun i j => by
      have hg := S.gap (ψ i j) (hψ_orth i j)
      have ha1 : S.a = 1 := rfl
      rw [ha1, mul_one] at hg
      linarith only [hg]
    calc (1 - Real.exp (-S.Δ)) * (N : ℝ)
        = (1 - Real.exp (-S.Δ)) * ∑ i : Fin N, ∑ j : Fin N, ‖ψ i j‖ ^ 2 := by
            rw [hψ_norm_sum]
      _ = ∑ i : Fin N, ∑ j : Fin N, (1 - Real.exp (-S.Δ)) * ‖ψ i j‖ ^ 2 := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin N, ∑ j : Fin N, (‖ψ i j‖ ^ 2 - (⟪ψ i j, S.T (ψ i j)⟫_ℂ).re) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h_each i j
  -- 2. Dirichlet-form identity for `∑ i, ∑ j, (‖ψ i j‖² - Re ⟪ψ i j, S.T (ψ i j)⟫)`
  have h_mat_diff_cont : ∀ i j : Fin N, Continuous (fun p : G_L × G_L =>
      ((p.1 e₀ : Matrix (Fin N) (Fin N) ℂ) - (p.2 e₀ : Matrix (Fin N) (Fin N) ℂ)) i j) :=
    fun i j => (continuous_apply j).comp ((continuous_apply i).comp
      ((continuous_subtype_val.comp ((continuous_apply e₀).comp continuous_fst)).sub
       (continuous_subtype_val.comp ((continuous_apply e₀).comp continuous_snd))))
  have hKW_int_cont : Continuous (fun p : G_L × G_L =>
      K_W p.1 p.2 * ω p.1 * ω p.2 *
        frobeniusNormSq ((p.1 e₀ : Matrix (Fin N) (Fin N) ℂ) -
          (p.2 e₀ : Matrix (Fin N) (Fin N) ℂ))) := by
    have hfrob_cont : Continuous (fun p : G_L × G_L =>
        frobeniusNormSq ((p.1 e₀ : Matrix (Fin N) (Fin N) ℂ) -
          (p.2 e₀ : Matrix (Fin N) (Fin N) ℂ))) := by
      unfold frobeniusNormSq
      refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
      exact (continuous_norm.comp (h_mat_diff_cont i j)).pow 2
    exact (((hKW_cont.mul (hgs.ω_cont.comp continuous_fst)).mul
      (hgs.ω_cont.comp continuous_snd)).mul hfrob_cont)
  have h_dirichlet :
      ∑ i : Fin N, ∑ j : Fin N, (‖ψ i j‖ ^ 2 - (⟪ψ i j, S.T (ψ i j)⟫_ℂ).re) =
        (1 / (2 * lam0)) *
          ∫ U, ∫ U', K_W U U' * ω U * ω U' *
            frobeniusNormSq ((U e₀ : Matrix (Fin N) (Fin N) ℂ) -
              (U' e₀ : Matrix (Fin N) (Fin N) ℂ)) ∂μ ∂μ := by
    have h_term : ∀ i j : Fin N,
        ‖ψ i j‖ ^ 2 - (⟪ψ i j, S.T (ψ i j)⟫_ℂ).re =
          (1 / (2 * lam0)) *
            ∫ U, ∫ U', K_W U U' * ω U * ω U' *
              ‖((U e₀ : Matrix (Fin N) (Fin N) ℂ) -
                (U' e₀ : Matrix (Fin N) (Fin N) ℂ)) i j‖ ^ 2 ∂μ ∂μ := by
      intro i j
      let a : G_L → ℂ := fun U => (U e₀ : Matrix (Fin N) (Fin N) ℂ) i j
      have ha_cont : Continuous a := h_entry_cont i j
      have h_norm_L : ‖ψ i j‖ ^ 2 =
          lam0⁻¹ * ∫ U, ∫ U', K_W U U' * ω U * ω U' * ‖a U‖ ^ 2 ∂μ ∂μ := by
        rw [lp_norm_sq_eq_integral μ (ψ i j)]
        have h_ae_sq : (fun U => ‖⇑(ψ i j) U‖ ^ 2) =ᵐ[μ]
            fun U => lam0⁻¹ * ∫ U', K_W U U' * ω U * ω U' * ‖a U‖ ^ 2 ∂μ := by
          filter_upwards [hψ_ae i j] with U hU
          rw [hU]
          dsimp [ψ_fn, a]
          rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (hgs.ω_pos U).le]
          have h_pull : ∫ U', K_W U U' * ω U * ω U' * ‖a U‖ ^ 2 ∂μ =
              (ω U * ‖a U‖ ^ 2) * ∫ U', K_W U U' * ω U' ∂μ := by
            rw [← MeasureTheory.integral_const_mul]
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U' => by
              dsimp only; ring)
          rw [h_pull, h_eig_ω U]
          dsimp only [a]
          have hlam0_ne : lam0 ≠ 0 := hlam0_pos.ne'
          field_simp [hlam0_ne]
        rw [MeasureTheory.integral_congr_ae h_ae_sq, MeasureTheory.integral_const_mul]
      have h_prod_sq_int : MeasureTheory.Integrable
          (fun p : G_L × G_L => K_W p.1 p.2 * ω p.1 * ω p.2 * ‖a p.2‖ ^ 2) (μ.prod μ) :=
        integrable_of_continuous_compact (μ.prod μ) _
          (((hKW_cont.mul (hgs.ω_cont.comp continuous_fst)).mul
            (hgs.ω_cont.comp continuous_snd)).mul ((continuous_norm.comp (ha_cont.comp continuous_snd)).pow 2))
      have h_swap_int : MeasureTheory.Integrable
          (Function.uncurry fun U U' => K_W U U' * ω U * ω U' * ‖a U‖ ^ 2) (μ.prod μ) :=
        integrable_of_continuous_compact (μ.prod μ) _
          (((hKW_cont.mul (hgs.ω_cont.comp continuous_fst)).mul
            (hgs.ω_cont.comp continuous_snd)).mul ((continuous_norm.comp (ha_cont.comp continuous_fst)).pow 2))
      have h_norm_R : ‖ψ i j‖ ^ 2 =
          lam0⁻¹ * ∫ U, ∫ U', K_W U U' * ω U * ω U' * ‖a U'‖ ^ 2 ∂μ ∂μ := by
        rw [h_norm_L]
        congr 1
        rw [MeasureTheory.integral_integral_swap h_swap_int]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U' => ?_)
        dsimp only
        rw [hKW_symm U U']
        ring
      have h_cross_int : (⟪ψ i j, S.T (ψ i j)⟫_ℂ).re =
          lam0⁻¹ * ∫ U, ∫ U', K_W U U' * ω U * ω U' * (starRingEnd ℂ (a U) * a U').re ∂μ ∂μ := by
        have hST_val : (⟪ψ i j, S.T (ψ i j)⟫_ℂ).re = lam0⁻¹ * (⟪ψ i j, T_raw (ψ i j)⟫_ℂ).re := by
          rw [hS_T]
          change (⟪ψ i j, ((lam0⁻¹ : ℝ) : ℂ) • T_raw (ψ i j)⟫_ℂ).re = _
          rw [inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        rw [hST_val]
        congr 1
        have hl2 : MeasureTheory.Integrable (fun U => ⟪(ψ i j) U, (T_raw (ψ i j)) U⟫_ℂ) μ :=
          MeasureTheory.L2.integrable_inner _ _
        rw [MeasureTheory.L2.inner_def]
        change RCLike.re (∫ U, ⟪⇑(ψ i j) U, ⇑(T_raw (ψ i j)) U⟫_ℂ ∂μ) = _
        rw [← integral_re hl2]
        have hT_ae := wilsonIntegralOp_apply_ae L N β hβ_pos.le K_kin hK_cont hK_nn
          ((linkChiUb L β) ^ 2) (sq_nonneg _) hK_bd (ψ i j)
        rw [← hT_raw_def] at hT_ae
        have h_ae_outer :
            (fun U => RCLike.re ⟪⇑(ψ i j) U, ⇑(T_raw (ψ i j)) U⟫_ℂ) =ᵐ[μ]
            fun U => ∫ U', K_W U U' * ω U * ω U' * (starRingEnd ℂ (a U) * a U').re ∂μ := by
          filter_upwards [hψ_ae i j, hT_ae] with U hU hTU
          change (⟪⇑(ψ i j) U, ⇑(T_raw (ψ i j)) U⟫_ℂ).re = _
          rw [hU, hTU]
          have hwf : wilsonIntegralFn L N β K_kin (ψ i j) U =
              ∫ U', ((K_W U U' : ℝ) : ℂ) * ⇑(ψ i j) U' ∂μ := rfl
          rw [hwf]
          have h_pull_left :
              ⟪ψ_fn i j U, ∫ U', ((K_W U U' : ℝ) : ℂ) * ⇑(ψ i j) U' ∂μ⟫_ℂ =
                ∫ U', ⟪ψ_fn i j U, ((K_W U U' : ℝ) : ℂ) * ⇑(ψ i j) U'⟫_ℂ ∂μ := by
            have hi := wilsonKernel_mul_integrable L N β hβ_pos.le K_kin hK_cont hK_nn
              ((linkChiUb L β) ^ 2) hK_bd (ψ i j) U
            rw [hcinner, ← MeasureTheory.integral_const_mul]
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U' => ?_)
            dsimp only; rw [hcinner]
          have hi_in2 : MeasureTheory.Integrable
              (fun U' => ⟪ψ_fn i j U, ((K_W U U' : ℝ) : ℂ) * ⇑(ψ i j) U'⟫_ℂ) μ := by
            have hi := wilsonKernel_mul_integrable L N β hβ_pos.le K_kin hK_cont hK_nn
              ((linkChiUb L β) ^ 2) hK_bd (ψ i j) U
            refine (hi.const_mul (starRingEnd ℂ (ψ_fn i j U))).congr ?_
            exact Filter.Eventually.of_forall fun U' => (hcinner _ _).symm
          rw [h_pull_left]
          change RCLike.re (∫ U', ⟪ψ_fn i j U, ((K_W U U' : ℝ) : ℂ) * ⇑(ψ i j) U'⟫_ℂ ∂μ) = _
          rw [← integral_re hi_in2]
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [hψ_ae i j] with U' hU'
          change (⟪ψ_fn i j U, ((K_W U U' : ℝ) : ℂ) * ⇑(ψ i j) U'⟫_ℂ).re = _
          rw [hU', hcinner]
          dsimp [ψ_fn, a]
          ring
        exact MeasureTheory.integral_congr_ae h_ae_outer
      have h_int_comb : MeasureTheory.Integrable
          (fun p : G_L × G_L => K_W p.1 p.2 * ω p.1 * ω p.2 *
            ‖((p.1 e₀ : Matrix (Fin N) (Fin N) ℂ) -
              (p.2 e₀ : Matrix (Fin N) (Fin N) ℂ)) i j‖ ^ 2) (μ.prod μ) :=
        integrable_of_continuous_compact (μ.prod μ) _
          (((hKW_cont.mul (hgs.ω_cont.comp continuous_fst)).mul
            (hgs.ω_cont.comp continuous_snd)).mul
            ((continuous_norm.comp (h_mat_diff_cont i j)).pow 2))
      have h_int1 : MeasureTheory.Integrable
          (fun p : G_L × G_L => K_W p.1 p.2 * ω p.1 * ω p.2 * ‖a p.1‖ ^ 2) (μ.prod μ) :=
        integrable_of_continuous_compact (μ.prod μ) _
          (((hKW_cont.mul (hgs.ω_cont.comp continuous_fst)).mul
            (hgs.ω_cont.comp continuous_snd)).mul ((continuous_norm.comp (ha_cont.comp continuous_fst)).pow 2))
      have h_int3 : MeasureTheory.Integrable
          (fun p : G_L × G_L => K_W p.1 p.2 * ω p.1 * ω p.2 *
            (starRingEnd ℂ (a p.1) * a p.2).re) (μ.prod μ) :=
        integrable_of_continuous_compact (μ.prod μ) _
          (((hKW_cont.mul (hgs.ω_cont.comp continuous_fst)).mul
            (hgs.ω_cont.comp continuous_snd)).mul
            (Complex.continuous_re.comp ((continuous_star.comp (ha_cont.comp continuous_fst)).mul
              (ha_cont.comp continuous_snd))))
      have h_pt_id : ∀ z₁ z₂ : ℂ,
          ‖z₁‖ ^ 2 + ‖z₂‖ ^ 2 - 2 * (starRingEnd ℂ z₁ * z₂).re = ‖z₁ - z₂‖ ^ 2 := by
        intro z₁ z₂
        have hn1 : ‖z₁‖ ^ 2 = z₁.re ^ 2 + z₁.im ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
        have hn2 : ‖z₂‖ ^ 2 = z₂.re ^ 2 + z₂.im ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
        have hn12 : ‖z₁ - z₂‖ ^ 2 = (z₁.re - z₂.re) ^ 2 + (z₁.im - z₂.im) ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
          ring
        have hcr : (starRingEnd ℂ z₁ * z₂).re = z₁.re * z₂.re + z₁.im * z₂.im := by
          simp [Complex.mul_re]
        rw [hn1, hn2, hn12, hcr]
        ring
      have h_diff_int :
          (∫ U, ∫ U', K_W U U' * ω U * ω U' * ‖a U‖ ^ 2 ∂μ ∂μ) +
          (∫ U, ∫ U', K_W U U' * ω U * ω U' * ‖a U'‖ ^ 2 ∂μ ∂μ) -
          2 * (∫ U, ∫ U', K_W U U' * ω U * ω U' * (starRingEnd ℂ (a U) * a U').re ∂μ ∂μ) =
          ∫ U, ∫ U', K_W U U' * ω U * ω U' *
            ‖((U e₀ : Matrix (Fin N) (Fin N) ℂ) -
              (U' e₀ : Matrix (Fin N) (Fin N) ℂ)) i j‖ ^ 2 ∂μ ∂μ := by
        rw [← MeasureTheory.integral_prod _ h_int1, ← MeasureTheory.integral_prod _ h_prod_sq_int,
          ← MeasureTheory.integral_prod _ h_int3, ← MeasureTheory.integral_prod _ h_int_comb,
          ← MeasureTheory.integral_add h_int1 h_prod_sq_int,
          ← MeasureTheory.integral_const_mul 2]
        have h_sub_eq :
            (∫ p : G_L × G_L,
                K_W p.1 p.2 * ω p.1 * ω p.2 * ‖a p.1‖ ^ 2 +
                  K_W p.1 p.2 * ω p.1 * ω p.2 * ‖a p.2‖ ^ 2 ∂(μ.prod μ)) -
            (∫ p : G_L × G_L,
                2 * (K_W p.1 p.2 * ω p.1 * ω p.2 * (starRingEnd ℂ (a p.1) * a p.2).re) ∂(μ.prod μ)) =
            ∫ p : G_L × G_L,
                (K_W p.1 p.2 * ω p.1 * ω p.2 * ‖a p.1‖ ^ 2 +
                  K_W p.1 p.2 * ω p.1 * ω p.2 * ‖a p.2‖ ^ 2) -
                2 * (K_W p.1 p.2 * ω p.1 * ω p.2 * (starRingEnd ℂ (a p.1) * a p.2).re) ∂(μ.prod μ) :=
          (MeasureTheory.integral_sub (h_int1.add h_prod_sq_int) (h_int3.const_mul 2)).symm
        rw [h_sub_eq]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        dsimp only
        have h_sub : ((p.1 e₀ : Matrix (Fin N) (Fin N) ℂ) -
            (p.2 e₀ : Matrix (Fin N) (Fin N) ℂ)) i j = a p.1 - a p.2 := rfl
        rw [h_sub, ← h_pt_id (a p.1) (a p.2)]
        ring
      have h_comb_eq : ‖ψ i j‖ ^ 2 - (⟪ψ i j, S.T (ψ i j)⟫_ℂ).re =
          (1 / (2 * lam0)) *
            ((∫ U, ∫ U', K_W U U' * ω U * ω U' * ‖a U‖ ^ 2 ∂μ ∂μ) +
             (∫ U, ∫ U', K_W U U' * ω U * ω U' * ‖a U'‖ ^ 2 ∂μ ∂μ) -
             2 * (∫ U, ∫ U', K_W U U' * ω U * ω U' * (starRingEnd ℂ (a U) * a U').re ∂μ ∂μ)) := by
        calc ‖ψ i j‖ ^ 2 - (⟪ψ i j, S.T (ψ i j)⟫_ℂ).re
            = (2 : ℝ)⁻¹ * (‖ψ i j‖ ^ 2 + ‖ψ i j‖ ^ 2 - 2 * (⟪ψ i j, S.T (ψ i j)⟫_ℂ).re) := by ring
          _ = _ := by
              nth_rw 1 [h_norm_L]
              rw [h_norm_R, h_cross_int]
              ring
      rw [h_comb_eq, h_diff_int]
    simp_rw [h_term, ← Finset.mul_sum]
    congr 1
    have h_int_ij_prod : ∀ i j : Fin N, MeasureTheory.Integrable
        (fun p : G_L × G_L => K_W p.1 p.2 * ω p.1 * ω p.2 *
          ‖((p.1 e₀ : Matrix (Fin N) (Fin N) ℂ) -
            (p.2 e₀ : Matrix (Fin N) (Fin N) ℂ)) i j‖ ^ 2) (μ.prod μ) := fun i j =>
      integrable_of_continuous_compact (μ.prod μ) _
        (((hKW_cont.mul (hgs.ω_cont.comp continuous_fst)).mul
          (hgs.ω_cont.comp continuous_snd)).mul
          ((continuous_norm.comp (h_mat_diff_cont i j)).pow 2))
    have h_swap : ∀ i j : Fin N,
        (∫ U, ∫ U', K_W U U' * ω U * ω U' *
          ‖((U e₀ : Matrix (Fin N) (Fin N) ℂ) -
            (U' e₀ : Matrix (Fin N) (Fin N) ℂ)) i j‖ ^ 2 ∂μ ∂μ) =
        ∫ p : G_L × G_L, K_W p.1 p.2 * ω p.1 * ω p.2 *
          ‖((p.1 e₀ : Matrix (Fin N) (Fin N) ℂ) -
            (p.2 e₀ : Matrix (Fin N) (Fin N) ℂ)) i j‖ ^ 2 ∂(μ.prod μ) := fun i j =>
      (MeasureTheory.integral_prod _ (h_int_ij_prod i j)).symm
    have h_sum_inner2 : ∀ i : Fin N,
        (∑ j : Fin N, ∫ p : G_L × G_L, K_W p.1 p.2 * ω p.1 * ω p.2 *
          ‖((p.1 e₀ : Matrix (Fin N) (Fin N) ℂ) -
            (p.2 e₀ : Matrix (Fin N) (Fin N) ℂ)) i j‖ ^ 2 ∂(μ.prod μ)) =
        ∫ p : G_L × G_L, ∑ j : Fin N, K_W p.1 p.2 * ω p.1 * ω p.2 *
          ‖((p.1 e₀ : Matrix (Fin N) (Fin N) ℂ) -
            (p.2 e₀ : Matrix (Fin N) (Fin N) ℂ)) i j‖ ^ 2 ∂(μ.prod μ) := fun i =>
      (MeasureTheory.integral_finset_sum Finset.univ fun j _ => h_int_ij_prod i j).symm
    have h_outer :
        (∑ i : Fin N, ∑ j : Fin N,
          ∫ p : G_L × G_L, K_W p.1 p.2 * ω p.1 * ω p.2 *
            ‖((p.1 e₀ : Matrix (Fin N) (Fin N) ℂ) -
              (p.2 e₀ : Matrix (Fin N) (Fin N) ℂ)) i j‖ ^ 2 ∂(μ.prod μ)) =
        ∫ p : G_L × G_L, K_W p.1 p.2 * ω p.1 * ω p.2 *
          frobeniusNormSq ((p.1 e₀ : Matrix (Fin N) (Fin N) ℂ) -
            (p.2 e₀ : Matrix (Fin N) (Fin N) ℂ)) ∂(μ.prod μ) := by
      simp_rw [h_sum_inner2]
      rw [← MeasureTheory.integral_finset_sum Finset.univ fun i _ =>
        MeasureTheory.integrable_finset_sum Finset.univ fun j _ => h_int_ij_prod i j]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      dsimp only [frobeniusNormSq]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    have h_final_prod :
        ∫ p : G_L × G_L, K_W p.1 p.2 * ω p.1 * ω p.2 *
          frobeniusNormSq ((p.1 e₀ : Matrix (Fin N) (Fin N) ℂ) -
            (p.2 e₀ : Matrix (Fin N) (Fin N) ℂ)) ∂(μ.prod μ) =
        ∫ U, ∫ U', K_W U U' * ω U * ω U' *
          frobeniusNormSq ((U e₀ : Matrix (Fin N) (Fin N) ℂ) -
            (U' e₀ : Matrix (Fin N) (Fin N) ℂ)) ∂μ ∂μ :=
      MeasureTheory.integral_prod _ (integrable_of_continuous_compact (μ.prod μ) _ hKW_int_cont)
    calc (∑ i : Fin N, ∑ j : Fin N,
          ∫ U, ∫ U', K_W U U' * ω U * ω U' *
            ‖((U e₀ : Matrix (Fin N) (Fin N) ℂ) -
              (U' e₀ : Matrix (Fin N) (Fin N) ℂ)) i j‖ ^ 2 ∂μ ∂μ)
        = ∑ i : Fin N, ∑ j : Fin N,
            ∫ p : G_L × G_L, K_W p.1 p.2 * ω p.1 * ω p.2 *
              ‖((p.1 e₀ : Matrix (Fin N) (Fin N) ℂ) -
                (p.2 e₀ : Matrix (Fin N) (Fin N) ℂ)) i j‖ ^ 2 ∂(μ.prod μ) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h_swap i j
      _ = ∫ p : G_L × G_L, K_W p.1 p.2 * ω p.1 * ω p.2 *
            frobeniusNormSq ((p.1 e₀ : Matrix (Fin N) (Fin N) ℂ) -
              (p.2 e₀ : Matrix (Fin N) (Fin N) ℂ)) ∂(μ.prod μ) := h_outer
      _ = ∫ U, ∫ U', K_W U U' * ω U * ω U' *
            frobeniusNormSq ((U e₀ : Matrix (Fin N) (Fin N) ℂ) -
              (U' e₀ : Matrix (Fin N) (Fin N) ℂ)) ∂μ ∂μ := h_final_prod
  -- 2b. Express Dirichlet integral over `((μ.prod μ).prod μ)` via `κ U W = exp(-½ S_W[U]) χ U W`
  let κ : G_L → G_L → ℝ := fun U W => cubicWilsonWeight L N β U * χ U W
  have hκ_cont : Continuous (Function.uncurry κ) := by
    have hw : Continuous (cubicWilsonWeight L N β) :=
      Real.continuous_exp.comp (continuous_const.mul (continuous_cubicWilsonAction L N β))
    exact (hw.comp continuous_fst).mul hχ_cont
  have hκ_nn : ∀ U W, 0 ≤ κ U W := fun U W =>
    mul_nonneg (Real.exp_pos _).le (hχ_nn U W)
  have hKW_eq_κ : ∀ U U', K_W U U' = ∫ W, κ U W * κ U' W ∂μ := by
    intro U U'
    have h_exp : Real.exp (-(1 / 2 : ℝ) *
        (wilsonAction β (cubicPlaquettes L) U + wilsonAction β (cubicPlaquettes L) U')) =
        cubicWilsonWeight L N β U * cubicWilsonWeight L N β U' := by
      unfold cubicWilsonWeight
      rw [← Real.exp_add]
      congr 1; ring
    dsimp only [K_W, wilsonKernel, K_kin, wilsonGramKernel]
    rw [h_exp, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    dsimp only [κ]; ring
  let F3 : (G_L × G_L) × G_L → ℝ := fun q =>
    κ q.1.1 q.2 * κ q.1.2 q.2 * ω q.1.1 * ω q.1.2 *
      frobeniusNormSq ((q.1.1 e₀ : Matrix (Fin N) (Fin N) ℂ) -
        (q.1.2 e₀ : Matrix (Fin N) (Fin N) ℂ))
  have hfrob_cont : Continuous (fun p : G_L × G_L =>
      frobeniusNormSq ((p.1 e₀ : Matrix (Fin N) (Fin N) ℂ) -
        (p.2 e₀ : Matrix (Fin N) (Fin N) ℂ))) := by
    unfold frobeniusNormSq
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact (continuous_norm.comp (h_mat_diff_cont i j)).pow 2
  have hF3_cont : Continuous F3 := by
    have hκ1 : Continuous (fun q : (G_L × G_L) × G_L => κ q.1.1 q.2) :=
      continuous_prod3_left hκ_cont
    have hκ2 : Continuous (fun q : (G_L × G_L) × G_L => κ q.1.2 q.2) :=
      continuous_prod3_right hκ_cont
    have hω1 : Continuous (fun q : (G_L × G_L) × G_L => ω q.1.1) :=
      hgs.ω_cont.comp continuous_fst_fst
    have hω2 : Continuous (fun q : (G_L × G_L) × G_L => ω q.1.2) :=
      hgs.ω_cont.comp continuous_fst_snd
    exact (((hκ1.mul hκ2).mul hω1).mul hω2).mul (hfrob_cont.comp continuous_fst)
  have hF3_int : MeasureTheory.Integrable F3 ((μ.prod μ).prod μ) :=
    integrable_of_continuous_compact ((μ.prod μ).prod μ) F3 hF3_cont
  have h_dirichlet_prod3 :
      ∫ U, ∫ U', K_W U U' * ω U * ω U' *
          frobeniusNormSq ((U e₀ : Matrix (Fin N) (Fin N) ℂ) -
            (U' e₀ : Matrix (Fin N) (Fin N) ℂ)) ∂μ ∂μ =
        ∫ q : (G_L × G_L) × G_L, F3 q ∂((μ.prod μ).prod μ) := by
    have h_int_prod : MeasureTheory.Integrable
        (fun p : G_L × G_L => K_W p.1 p.2 * ω p.1 * ω p.2 *
          frobeniusNormSq ((p.1 e₀ : Matrix (Fin N) (Fin N) ℂ) -
            (p.2 e₀ : Matrix (Fin N) (Fin N) ℂ))) (μ.prod μ) :=
      integrable_of_continuous_compact (μ.prod μ) _ hKW_int_cont
    have h_eq_p : ∀ p : G_L × G_L,
        K_W p.1 p.2 * ω p.1 * ω p.2 *
          frobeniusNormSq ((p.1 e₀ : Matrix (Fin N) (Fin N) ℂ) -
            (p.2 e₀ : Matrix (Fin N) (Fin N) ℂ)) =
        ∫ W, F3 (p, W) ∂μ := fun p => by
      rw [hKW_eq_κ p.1 p.2, ← MeasureTheory.integral_mul_const,
        ← MeasureTheory.integral_mul_const, ← MeasureTheory.integral_mul_const]
    calc ∫ U, ∫ U', K_W U U' * ω U * ω U' *
            frobeniusNormSq ((U e₀ : Matrix (Fin N) (Fin N) ℂ) -
              (U' e₀ : Matrix (Fin N) (Fin N) ℂ)) ∂μ ∂μ
        = ∫ p : G_L × G_L, K_W p.1 p.2 * ω p.1 * ω p.2 *
            frobeniusNormSq ((p.1 e₀ : Matrix (Fin N) (Fin N) ℂ) -
              (p.2 e₀ : Matrix (Fin N) (Fin N) ℂ)) ∂(μ.prod μ) :=
            (MeasureTheory.integral_prod _ h_int_prod).symm
      _ = ∫ p : G_L × G_L, ∫ W, F3 (p, W) ∂μ ∂(μ.prod μ) :=
            MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => h_eq_p p)
      _ = ∫ q : (G_L × G_L) × G_L, F3 q ∂((μ.prod μ).prod μ) :=
            (MeasureTheory.integral_prod F3 hF3_int).symm
  -- 3. `ε/δ` split & `lam0` Haar-ball lower bound
  have h_card_links : Fintype.card (cubicTorus3 L).Link = links := by
    simp [cubicTorus3, links, Fintype.card_prod, Fintype.card_fin]; ring
  have hlinks_pos : 0 < links := by
    have hL_pos : 0 < L := NeZero.pos L
    dsimp [links]
    positivity
  have hε_nn : 0 ≤ ε_sq := by
    have hlog_nn : 0 ≤ Real.log β := Real.log_nonneg hβ
    dsimp [ε_sq]
    positivity
  let good : G_L → G_L → Prop := fun W U =>
    frobeniusNormSq (((U e₀ * (W e₀)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ) - 1) ≤ ε_sq
  let C_bad : ℝ := 4 * (N : ℝ) * Real.exp (β * (links : ℝ)) *
    β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2))
  have hC_bad_nn : 0 ≤ C_bad := by
    dsimp [C_bad]
    positivity
  let G3 : (G_L × G_L) × G_L → ℝ := fun q =>
    4 * ε_sq * (κ q.1.1 q.2 * κ q.1.2 q.2 * ω q.1.1 * ω q.1.2)
  let H3 : (G_L × G_L) × G_L → ℝ := fun q => C_bad * (ω q.1.1 * ω q.1.2)
  have hG3_cont : Continuous G3 := by
    have hκ1 : Continuous (fun q : (G_L × G_L) × G_L => κ q.1.1 q.2) :=
      continuous_prod3_left hκ_cont
    have hκ2 : Continuous (fun q : (G_L × G_L) × G_L => κ q.1.2 q.2) :=
      continuous_prod3_right hκ_cont
    have hω1 : Continuous (fun q : (G_L × G_L) × G_L => ω q.1.1) :=
      hgs.ω_cont.comp continuous_fst_fst
    have hω2 : Continuous (fun q : (G_L × G_L) × G_L => ω q.1.2) :=
      hgs.ω_cont.comp continuous_fst_snd
    exact continuous_const.mul (((hκ1.mul hκ2).mul hω1).mul hω2)
  have hH3_cont : Continuous H3 := by
    have hω1 : Continuous (fun q : (G_L × G_L) × G_L => ω q.1.1) :=
      hgs.ω_cont.comp continuous_fst_fst
    have hω2 : Continuous (fun q : (G_L × G_L) × G_L => ω q.1.2) :=
      hgs.ω_cont.comp continuous_fst_snd
    exact continuous_const.mul (hω1.mul hω2)
  have hG3_int : MeasureTheory.Integrable G3 ((μ.prod μ).prod μ) :=
    integrable_of_continuous_compact ((μ.prod μ).prod μ) G3 hG3_cont
  have hH3_int : MeasureTheory.Integrable H3 ((μ.prod μ).prod μ) :=
    integrable_of_continuous_compact ((μ.prod μ).prod μ) H3 hH3_cont
  have hG3_nn : ∀ q, 0 ≤ G3 q := fun q => by
    dsimp [G3]
    exact mul_nonneg (mul_nonneg (by norm_num) hε_nn)
      (mul_nonneg (mul_nonneg (mul_nonneg (hκ_nn _ _) (hκ_nn _ _))
        (hgs.ω_pos _).le) (hgs.ω_pos _).le)
  have hH3_nn : ∀ q, 0 ≤ H3 q := fun q => by
    dsimp [H3]
    exact mul_nonneg hC_bad_nn (mul_nonneg (hgs.ω_pos _).le (hgs.ω_pos _).le)
  have h_fac_ub : ∀ (U W : G_L) (e : (cubicTorus3 L).Link),
      Real.exp ((β / (2 * (N : ℝ))) *
        (Matrix.trace (((U e * (W e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re) ≤ Real.exp (β / 2) := by
    intro U W e
    have htr := (abs_le.mp (abs_re_trace_su_le (U e * (W e)⁻¹))).2
    have hmul : (β / (2 * (N : ℝ))) *
        (Matrix.trace (((U e * (W e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re ≤ β / 2 := by
      have heq : β / 2 = (β / (2 * (N : ℝ))) * (N : ℝ) := by
        field_simp [hN_pos.ne']
      rw [heq]
      exact mul_le_mul_of_nonneg_left htr (by positivity)
    exact Real.exp_le_exp.mpr hmul
  have h_κ_ub : ∀ U W : G_L, κ U W ≤ Real.exp (β * (links : ℝ) / 2) := fun U W => by
    have hwb := (cubicWilsonWeight_bounds L N β hβ_pos.le U).2
    have hcb := hχ_bd U W
    have h_exp_ub : linkChiUb L β = Real.exp (β * (links : ℝ) / 2) := by
      dsimp [linkChiUb]
      rw [h_card_links, ← Real.exp_nat_mul]
      congr 1; ring
    calc κ U W = cubicWilsonWeight L N β U * χ U W := rfl
      _ ≤ 1 * linkChiUb L β :=
          mul_le_mul hwb hcb (hχ_nn U W) zero_le_one
      _ = Real.exp (β * (links : ℝ) / 2) := by rw [one_mul, h_exp_ub]
  have h_κ_bad : ∀ U W : G_L, ¬ good W U →
      κ U W ≤ Real.exp (β * (links : ℝ) / 2) *
        β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) := by
    intro U W hnot
    have hgt : ε_sq < frobeniusNormSq (((U e₀ * (W e₀)⁻¹ :
        Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) - 1) :=
      lt_of_not_ge hnot
    have hid := wilson_plaquette_eq_frobenius_sq (U e₀ * (W e₀)⁻¹)
    change frobeniusNormSq (((U e₀ * (W e₀)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) - 1) =
      2 * ((N : ℝ) - (Matrix.trace (((U e₀ * (W e₀)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ))).re) at hid
    have htr_lt : (Matrix.trace (((U e₀ * (W e₀)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ))).re ≤ (N : ℝ) - ε_sq / 2 := by linarith only [hid, hgt]
    have hmul : (β / (2 * (N : ℝ))) *
        (Matrix.trace (((U e₀ * (W e₀)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re ≤
        β / 2 - (6 * (N : ℝ) ^ 2 * (links : ℝ) + 2) * Real.log β := by
      have heq : (β / (2 * (N : ℝ))) * ((N : ℝ) - ε_sq / 2) =
          β / 2 - (6 * (N : ℝ) ^ 2 * (links : ℝ) + 2) * Real.log β := by
        dsimp [ε_sq]
        field_simp [hN_pos.ne', hβ_pos.ne']
        ring
      rw [← heq]
      exact mul_le_mul_of_nonneg_left htr_lt (by positivity)
    have hfac0 :
        Real.exp ((β / (2 * (N : ℝ))) *
          (Matrix.trace (((U e₀ * (W e₀)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
            Matrix (Fin N) (Fin N) ℂ))).re) ≤
          Real.exp (β / 2) * β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) := by
      have hrp : Real.exp (-((6 * (N : ℝ) ^ 2 * (links : ℝ) + 2) * Real.log β)) =
          β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) := by
        rw [Real.rpow_def_of_pos hβ_pos]
        congr 1; ring
      calc Real.exp ((β / (2 * (N : ℝ))) *
              (Matrix.trace (((U e₀ * (W e₀)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
                Matrix (Fin N) (Fin N) ℂ))).re)
          ≤ Real.exp (β / 2 - (6 * (N : ℝ) ^ 2 * (links : ℝ) + 2) * Real.log β) :=
              Real.exp_le_exp.mpr hmul
        _ = Real.exp (β / 2) *
              Real.exp (-((6 * (N : ℝ) ^ 2 * (links : ℝ) + 2) * Real.log β)) := by
              rw [sub_eq_add_neg, Real.exp_add]
        _ = Real.exp (β / 2) * β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) := by
              rw [hrp]
    let fac : (cubicTorus3 L).Link → ℝ := fun e =>
      Real.exp ((β / (2 * (N : ℝ))) *
        (Matrix.trace (((U e * (W e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re)
    have hχ_split : χ U W = fac e₀ * ∏ e ∈ Finset.univ.erase e₀, fac e := by
      dsimp only [χ, cubicLinkKineticKernel, fac]
      exact (Finset.mul_prod_erase Finset.univ fac (Finset.mem_univ e₀)).symm
    have hrest_le : ∏ e ∈ Finset.univ.erase e₀, fac e ≤ (Real.exp (β / 2)) ^ (links - 1) := by
      calc ∏ e ∈ Finset.univ.erase e₀, fac e
          ≤ ∏ _e ∈ Finset.univ.erase e₀, Real.exp (β / 2) :=
              Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun e _ => h_fac_ub U W e
        _ = (Real.exp (β / 2)) ^ (Finset.univ.erase e₀).card := Finset.prod_const _
        _ = (Real.exp (β / 2)) ^ (links - 1) := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ e₀), Finset.card_univ, h_card_links]
    have hχ_bad : χ U W ≤ Real.exp (β * (links : ℝ) / 2) *
        β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) := by
      rw [hχ_split]
      calc fac e₀ * ∏ e ∈ Finset.univ.erase e₀, fac e
          ≤ (Real.exp (β / 2) * β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2))) *
              (Real.exp (β / 2)) ^ (links - 1) :=
              mul_le_mul hfac0 hrest_le (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
                (by positivity)
        _ = (Real.exp (β / 2) * (Real.exp (β / 2)) ^ (links - 1)) *
              β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) := by ring
        _ = (Real.exp (β / 2)) ^ links * β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) := by
              rw [← pow_succ', Nat.sub_add_cancel hlinks_pos]
        _ = Real.exp (β * (links : ℝ) / 2) * β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) := by
              rw [← Real.exp_nat_mul]; congr 2; ring
    have hwb := (cubicWilsonWeight_bounds L N β hβ_pos.le U).2
    calc κ U W = cubicWilsonWeight L N β U * χ U W := rfl
      _ ≤ 1 * (Real.exp (β * (links : ℝ) / 2) * β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2))) :=
          mul_le_mul hwb hχ_bad (hχ_nn U W) zero_le_one
      _ = Real.exp (β * (links : ℝ) / 2) * β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) :=
          one_mul _
  have hF3_pt_le : ∀ q : (G_L × G_L) × G_L, F3 q ≤ G3 q + H3 q := by
    rintro ⟨⟨U, U'⟩, W⟩
    by_cases hgood : good W U ∧ good W U'
    · have hA : frobeniusNormSq (((U e₀ * (W e₀)⁻¹ :
          Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) - 1) ≤ ε_sq :=
        hgood.1
      have hB : frobeniusNormSq (((U' e₀ * (W e₀)⁻¹ :
          Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) - 1) ≤ ε_sq :=
        hgood.2
      have hdiff_le : frobeniusNormSq ((U e₀ : Matrix (Fin N) (Fin N) ℂ) -
          (U' e₀ : Matrix (Fin N) (Fin N) ℂ)) ≤ 4 * ε_sq := by
        rw [← frobeniusNormSq_sub_self_su (U e₀) (U' e₀)]
        have heq_grp : U e₀ * (U' e₀)⁻¹ = (U e₀ * (W e₀)⁻¹) * (U' e₀ * (W e₀)⁻¹)⁻¹ := by group
        rw [heq_grp]
        have h1 := frobeniusNormSq_su_mul_sub_one (U e₀ * (W e₀)⁻¹) (U' e₀ * (W e₀)⁻¹)⁻¹
        rw [frobeniusNormSq_su_inv_sub_one (U' e₀ * (W e₀)⁻¹)] at h1
        linarith only [h1, hA, hB]
      have h_coeff_nn : 0 ≤ κ U W * κ U' W * ω U * ω U' :=
        mul_nonneg (mul_nonneg (mul_nonneg (hκ_nn U W) (hκ_nn U' W))
          (hgs.ω_pos U).le) (hgs.ω_pos U').le
      calc F3 ((U, U'), W)
          ≤ (κ U W * κ U' W * ω U * ω U') * (4 * ε_sq) :=
              mul_le_mul_of_nonneg_left hdiff_le h_coeff_nn
        _ = G3 ((U, U'), W) := by dsimp [G3]; ring
        _ ≤ G3 ((U, U'), W) + H3 ((U, U'), W) := le_add_of_nonneg_right (hH3_nn _)
    · have hκ_prod : κ U W * κ U' W ≤
          Real.exp (β * (links : ℝ)) * β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) := by
        rw [not_and_or] at hgood
        rcases hgood with hbad1 | hbad2
        · calc κ U W * κ U' W
              ≤ (Real.exp (β * (links : ℝ) / 2) * β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2))) *
                  Real.exp (β * (links : ℝ) / 2) :=
                  mul_le_mul (h_κ_bad U W hbad1) (h_κ_ub U' W) (hκ_nn U' W) (by positivity)
            _ = (Real.exp (β * (links : ℝ) / 2) * Real.exp (β * (links : ℝ) / 2)) *
                  β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) := by ring
            _ = Real.exp (β * (links : ℝ)) * β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) := by
                  rw [← Real.exp_add]; congr 2; ring
        · calc κ U W * κ U' W
              ≤ Real.exp (β * (links : ℝ) / 2) *
                  (Real.exp (β * (links : ℝ) / 2) * β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2))) :=
                  mul_le_mul (h_κ_ub U W) (h_κ_bad U' W hbad2) (hκ_nn U' W) (by positivity)
              _ = (Real.exp (β * (links : ℝ) / 2) * Real.exp (β * (links : ℝ) / 2)) *
                    β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) := by ring
              _ = Real.exp (β * (links : ℝ)) * β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) := by
                    rw [← Real.exp_add]; congr 2; ring
      have hω_nn : 0 ≤ ω U * ω U' := mul_nonneg (hgs.ω_pos U).le (hgs.ω_pos U').le
      have hfrob_le : frobeniusNormSq ((U e₀ : Matrix (Fin N) (Fin N) ℂ) -
          (U' e₀ : Matrix (Fin N) (Fin N) ℂ)) ≤ 4 * (N : ℝ) :=
        frobeniusNormSq_su_sub_su_le (U e₀) (U' e₀)
      calc F3 ((U, U'), W)
          = (κ U W * κ U' W) *
              frobeniusNormSq ((U e₀ : Matrix (Fin N) (Fin N) ℂ) -
                (U' e₀ : Matrix (Fin N) (Fin N) ℂ)) * (ω U * ω U') := by
              dsimp [F3]; ring
        _ ≤ (Real.exp (β * (links : ℝ)) * β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2))) *
              (4 * (N : ℝ)) * (ω U * ω U') :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul hκ_prod hfrob_le (frobeniusNormSq_nonneg _) (by positivity)) hω_nn
        _ = H3 ((U, U'), W) := by dsimp [H3, C_bad]; ring
        _ ≤ G3 ((U, U'), W) + H3 ((U, U'), W) := le_add_of_nonneg_left (hG3_nn _)
  have hG3_val : ∫ q : (G_L × G_L) × G_L, G3 q ∂((μ.prod μ).prod μ) = 4 * ε_sq * lam0 := by
    have h_int_p : MeasureTheory.Integrable
        (fun p : G_L × G_L => K_W p.1 p.2 * ω p.1 * ω p.2) (μ.prod μ) :=
      integrable_of_continuous_compact (μ.prod μ) _
        ((hKW_cont.mul (hgs.ω_cont.comp continuous_fst)).mul (hgs.ω_cont.comp continuous_snd))
    have h_eq_p : ∀ p : G_L × G_L,
        ∫ W, G3 (p, W) ∂μ = 4 * ε_sq * (K_W p.1 p.2 * ω p.1 * ω p.2) := fun p => by
      dsimp only [G3]
      rw [MeasureTheory.integral_const_mul, hKW_eq_κ p.1 p.2]
      rw [← MeasureTheory.integral_mul_const, ← MeasureTheory.integral_mul_const]
    calc ∫ q : (G_L × G_L) × G_L, G3 q ∂((μ.prod μ).prod μ)
        = ∫ p : G_L × G_L, ∫ W, G3 (p, W) ∂μ ∂(μ.prod μ) :=
            MeasureTheory.integral_prod G3 hG3_int
      _ = ∫ p : G_L × G_L, 4 * ε_sq * (K_W p.1 p.2 * ω p.1 * ω p.2) ∂(μ.prod μ) :=
            MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => h_eq_p p)
      _ = 4 * ε_sq * ∫ p : G_L × G_L, K_W p.1 p.2 * ω p.1 * ω p.2 ∂(μ.prod μ) :=
            MeasureTheory.integral_const_mul _ _
      _ = 4 * ε_sq * ∫ U, ∫ U', K_W U U' * ω U * ω U' ∂μ ∂μ := by
            rw [MeasureTheory.integral_prod _ h_int_p]
      _ = 4 * ε_sq * ∫ U, ω U * (∫ U', K_W U U' * ω U' ∂μ) ∂μ := by
            congr 1
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
            dsimp only
            rw [← MeasureTheory.integral_const_mul]
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U' => ?_)
            dsimp only; ring
      _ = 4 * ε_sq * ∫ U, ω U * (lam0 * ω U) ∂μ := by
            congr 1
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
            dsimp only; rw [h_eig_ω U]
      _ = 4 * ε_sq * (lam0 * ∫ U, ω U ^ 2 ∂μ) := by
            congr 1
            rw [← MeasureTheory.integral_const_mul]
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
            dsimp only; ring
      _ = 4 * ε_sq * lam0 := by rw [hω_sq_int, mul_one]
  have hH3_le : ∫ q : (G_L × G_L) × G_L, H3 q ∂((μ.prod μ).prod μ) ≤ C_bad := by
    have h_int_p : MeasureTheory.Integrable (fun p : G_L × G_L => ω p.1 * ω p.2) (μ.prod μ) :=
      integrable_of_continuous_compact (μ.prod μ) _
        ((hgs.ω_cont.comp continuous_fst).mul (hgs.ω_cont.comp continuous_snd))
    have hω_nn : 0 ≤ ∫ U, ω U ∂μ := MeasureTheory.integral_nonneg fun U => (hgs.ω_pos U).le
    have h_prod_ω : (∫ U, ω U ∂μ) * (∫ U', ω U' ∂μ) ≤ 1 := by
      calc (∫ U, ω U ∂μ) * (∫ U', ω U' ∂μ) ≤ 1 * 1 :=
            mul_le_mul hω_int1 hω_int1 hω_nn zero_le_one
        _ = 1 := one_mul 1
    calc ∫ q : (G_L × G_L) × G_L, H3 q ∂((μ.prod μ).prod μ)
        = ∫ p : G_L × G_L, ∫ _W, C_bad * (ω p.1 * ω p.2) ∂μ ∂(μ.prod μ) :=
            MeasureTheory.integral_prod H3 hH3_int
      _ = ∫ p : G_L × G_L, C_bad * (ω p.1 * ω p.2) ∂(μ.prod μ) := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
            simp [MeasureTheory.integral_const]
      _ = C_bad * ∫ p : G_L × G_L, ω p.1 * ω p.2 ∂(μ.prod μ) :=
            MeasureTheory.integral_const_mul _ _
      _ = C_bad * ∫ U, ∫ U', ω U * ω U' ∂μ ∂μ := by
            rw [MeasureTheory.integral_prod _ h_int_p]
      _ = C_bad * ∫ U, ω U * (∫ U', ω U' ∂μ) ∂μ := by
            congr 1
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
            dsimp only; rw [MeasureTheory.integral_const_mul]
      _ = C_bad * ((∫ U, ω U ∂μ) * (∫ U', ω U' ∂μ)) := by
            rw [MeasureTheory.integral_mul_const]
      _ ≤ C_bad * 1 := mul_le_mul_of_nonneg_left h_prod_ω hC_bad_nn
      _ = C_bad := mul_one _
  have hF3_int_le :
      ∫ q : (G_L × G_L) × G_L, F3 q ∂((μ.prod μ).prod μ) ≤ 4 * ε_sq * lam0 + C_bad := by
    calc ∫ q : (G_L × G_L) × G_L, F3 q ∂((μ.prod μ).prod μ)
        ≤ ∫ q : (G_L × G_L) × G_L, (G3 q + H3 q) ∂((μ.prod μ).prod μ) :=
            MeasureTheory.integral_mono hF3_int (hG3_int.add hH3_int) hF3_pt_le
      _ = (∫ q : (G_L × G_L) × G_L, G3 q ∂((μ.prod μ).prod μ)) +
            (∫ q : (G_L × G_L) × G_L, H3 q ∂((μ.prod μ).prod μ)) :=
            MeasureTheory.integral_add hG3_int hH3_int
      _ ≤ 4 * ε_sq * lam0 + C_bad := add_le_add hG3_val.le hH3_le
  -- Haar-ball lower bound on `lam0 = ‖T_raw‖`
  let δ : ℝ := 1 / Real.sqrt β
  have hδ : 0 < δ := div_pos zero_lt_one (Real.sqrt_pos.mpr hβ_pos)
  have hβδ : β * δ ^ 2 = 1 := by
    dsimp [δ]
    rw [one_div, inv_pow, Real.sq_sqrt hβ_pos.le, mul_inv_cancel₀ hβ_pos.ne']
  let B_su : Set (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    { A | frobeniusNormSq ((A : Matrix (Fin N) (Fin N) ℂ) - 1) ≤ δ ^ 2 }
  have hB_su_meas : MeasurableSet B_su := by
    have hc : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        frobeniusNormSq ((A : Matrix (Fin N) (Fin N) ℂ) - 1)) := by
      unfold frobeniusNormSq
      refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
      exact (continuous_norm.comp ((continuous_apply j).comp
        ((continuous_apply i).comp (continuous_subtype_val.sub continuous_const)))).pow 2
    exact measurableSet_Iic.preimage hc.measurable
  have hB_su_lb : (1 : ℝ) / ((K : ℝ) ^ (2 * N * N)) ≤ (suHaar N B_su).toReal :=
    suHaar_ball_ge N hδ
  have hK_real_pos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  let B_L : Set G_L := Set.pi Set.univ (fun _ => B_su)
  have hB_L_meas : MeasurableSet B_L := by
    change @MeasurableSet _ MeasurableSpace.pi B_L
    exact MeasurableSet.univ_pi fun _ => hB_su_meas
  have hB_L_vol_eq : μ.real B_L = ((suHaar N B_su).toReal) ^ links := by
    haveI := suHaar_prob N
    change (MeasureTheory.Measure.pi (fun _ : (cubicTorus3 L).Link => suHaar N)
      (Set.pi Set.univ fun _ => B_su)).toReal = _
    rw [MeasureTheory.Measure.pi_pi (fun _ => suHaar N) _, Finset.prod_const,
      Finset.card_univ, h_card_links, ENNReal.toReal_pow]
  have hB_L_lb : (((K : ℝ) ^ (2 * N * N)) ^ links)⁻¹ ≤ μ.real B_L := by
    rw [hB_L_vol_eq, ← one_div, ← one_div_pow]
    exact pow_le_pow_left₀ (by positivity) hB_su_lb links
  have hB_L_pos : 0 < μ.real B_L := lt_of_lt_of_le (by positivity) hB_L_lb
  have hS_B_L : ∀ U ∈ B_L,
      wilsonAction β (cubicPlaquettes L) U ≤ 24 * (L : ℝ) ^ 3 / (N : ℝ) := by
    intro U hU
    have h_plaq : ∀ (x : (cubicTorus3 L).Site) (d₁ d₂ : Fin 3),
        wilsonPlaquetteTerm
          ⟨x, cubicPlaquette x d₁ d₂, cubicPlaquette_isPath x d₁ d₂⟩ U ≤
          8 * δ ^ 2 / (N : ℝ) := by
      intro x d₁ d₂
      let A := pathHolonomy U (cubicPlaquette x d₁ d₂)
      have hA_eq : A = U (x, d₁) * (U (cubicShift L d₁ x, d₂) *
          ((U (cubicShift L d₂ x, d₁))⁻¹ * ((U (x, d₂))⁻¹ * 1))) := rfl
      have hfrob : frobeniusNormSq ((A : Matrix (Fin N) (Fin N) ℂ) - 1) ≤ 16 * δ ^ 2 := by
        rw [hA_eq]
        exact frobeniusNormSq_holonomy4_le _ _ _ _
          (hU (x, d₁) (Set.mem_univ _))
          (hU (cubicShift L d₁ x, d₂) (Set.mem_univ _))
          (hU (cubicShift L d₂ x, d₁) (Set.mem_univ _))
          (hU (x, d₂) (Set.mem_univ _))
      have hid := wilson_plaquette_eq_frobenius_sq A
      change frobeniusNormSq ((A : Matrix (Fin N) (Fin N) ℂ) - 1) =
        2 * ((N : ℝ) - (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re) at hid
      have htr : (N : ℝ) - (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re ≤ 8 * δ ^ 2 := by
        linarith only [hid, hfrob]
      have hterm_eq : wilsonPlaquetteTerm
          ⟨x, cubicPlaquette x d₁ d₂, cubicPlaquette_isPath x d₁ d₂⟩ U =
          ((N : ℝ) - (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re) / (N : ℝ) := by
        unfold wilsonPlaquetteTerm
        dsimp only [A]
        field_simp [hN_pos.ne']
      rw [hterm_eq]
      exact div_le_div_of_nonneg_right htr hN_pos.le
    unfold wilsonAction cubicPlaquettes
    rw [sum_map_flatMap, sum_map_univ_toList]
    have h_site : ∀ x : Fin L × Fin L × Fin L,
        (([⟨x, cubicPlaquette x 0 1, cubicPlaquette_isPath x 0 1⟩,
           ⟨x, cubicPlaquette x 0 2, cubicPlaquette_isPath x 0 2⟩,
           ⟨x, cubicPlaquette x 1 2, cubicPlaquette_isPath x 1 2⟩]).map
          (fun p => wilsonPlaquetteTerm p U)).sum ≤ 24 * δ ^ 2 / (N : ℝ) := by
      intro x
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have h1 := h_plaq x 0 1
      have h2 := h_plaq x 0 2
      have h3 := h_plaq x 1 2
      calc wilsonPlaquetteTerm ⟨x, cubicPlaquette x 0 1, cubicPlaquette_isPath x 0 1⟩ U +
            (wilsonPlaquetteTerm ⟨x, cubicPlaquette x 0 2, cubicPlaquette_isPath x 0 2⟩ U +
              wilsonPlaquetteTerm ⟨x, cubicPlaquette x 1 2, cubicPlaquette_isPath x 1 2⟩ U)
          ≤ 8 * δ ^ 2 / (N : ℝ) + (8 * δ ^ 2 / (N : ℝ) + 8 * δ ^ 2 / (N : ℝ)) := by
            linarith only [h1, h2, h3]
        _ = 24 * δ ^ 2 / (N : ℝ) := by ring
    have h_sum_sites :
        (∑ x : Fin L × Fin L × Fin L,
          (([⟨x, cubicPlaquette x 0 1, cubicPlaquette_isPath x 0 1⟩,
             ⟨x, cubicPlaquette x 0 2, cubicPlaquette_isPath x 0 2⟩,
             ⟨x, cubicPlaquette x 1 2, cubicPlaquette_isPath x 1 2⟩]).map
            (fun p => wilsonPlaquetteTerm p U)).sum) ≤
          (L : ℝ) ^ 3 * (24 * δ ^ 2 / (N : ℝ)) := by
      calc _ ≤ ∑ _x : Fin L × Fin L × Fin L, (24 * δ ^ 2 / (N : ℝ)) :=
            Finset.sum_le_sum fun x _ => h_site x
        _ = (L : ℝ) ^ 3 * (24 * δ ^ 2 / (N : ℝ)) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
              Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    calc β * _ ≤ β * ((L : ℝ) ^ 3 * (24 * δ ^ 2 / (N : ℝ))) :=
          mul_le_mul_of_nonneg_left h_sum_sites hβ_pos.le
      _ = 24 * (L : ℝ) ^ 3 * (β * δ ^ 2) / (N : ℝ) := by ring
      _ = 24 * (L : ℝ) ^ 3 / (N : ℝ) := by rw [hβδ, mul_one]
  have hκ_B_L : ∀ U ∈ B_L, ∀ W ∈ B_L,
      Real.exp (β * (links : ℝ) / 2 - 15 * (L : ℝ) ^ 3 / (N : ℝ)) ≤ κ U W := by
    intro U hU W hW
    have hw_lb : Real.exp (-(12 * (L : ℝ) ^ 3 / (N : ℝ))) ≤ cubicWilsonWeight L N β U := by
      unfold cubicWilsonWeight
      apply Real.exp_le_exp.mpr
      have hS := hS_B_L U hU
      calc -(12 * (L : ℝ) ^ 3 / (N : ℝ))
          = -(1 / 2 : ℝ) * (24 * (L : ℝ) ^ 3 / (N : ℝ)) := by ring
        _ ≤ -(1 / 2 : ℝ) * wilsonAction β (cubicPlaquettes L) U :=
            mul_le_mul_of_nonpos_left hS (by norm_num)
    have hχ_fac : ∀ e : (cubicTorus3 L).Link,
        Real.exp (β / 2 - 1 / (N : ℝ)) ≤
          Real.exp ((β / (2 * (N : ℝ))) *
            (Matrix.trace (((U e * (W e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
              Matrix (Fin N) (Fin N) ℂ))).re) := by
      intro e
      have hf1 : frobeniusNormSq ((U e : Matrix (Fin N) (Fin N) ℂ) - 1) ≤ δ ^ 2 :=
        hU e (Set.mem_univ e)
      have hf2 : frobeniusNormSq ((W e : Matrix (Fin N) (Fin N) ℂ) - 1) ≤ δ ^ 2 :=
        hW e (Set.mem_univ e)
      have hf_diff : frobeniusNormSq (((U e * (W e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ) - 1) ≤ 4 * δ ^ 2 := by
        rw [frobeniusNormSq_sub_self_su (U e) (W e)]
        have h_sub_eq : (U e : Matrix (Fin N) (Fin N) ℂ) - (W e : Matrix (Fin N) (Fin N) ℂ) =
            ((U e : Matrix (Fin N) (Fin N) ℂ) - 1) + -((W e : Matrix (Fin N) (Fin N) ℂ) - 1) := by
          abel
        rw [h_sub_eq]
        have hadd := frobeniusNormSq_add_le
          ((U e : Matrix (Fin N) (Fin N) ℂ) - 1) (-((W e : Matrix (Fin N) (Fin N) ℂ) - 1))
        rw [frobeniusNormSq_neg] at hadd
        linarith only [hadd, hf1, hf2]
      have hid := wilson_plaquette_eq_frobenius_sq (U e * (W e)⁻¹)
      change frobeniusNormSq (((U e * (W e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ) - 1) =
        2 * ((N : ℝ) - (Matrix.trace (((U e * (W e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re) at hid
      have htr : (N : ℝ) - 2 * δ ^ 2 ≤
          (Matrix.trace (((U e * (W e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
            Matrix (Fin N) (Fin N) ℂ))).re := by linarith only [hid, hf_diff]
      apply Real.exp_le_exp.mpr
      have heq : (β / (2 * (N : ℝ))) * ((N : ℝ) - 2 * δ ^ 2) = β / 2 - 1 / (N : ℝ) := by
        calc (β / (2 * (N : ℝ))) * ((N : ℝ) - 2 * δ ^ 2)
            = β / 2 - (β * δ ^ 2) / (N : ℝ) := by field_simp [hN_pos.ne']
          _ = β / 2 - 1 / (N : ℝ) := by rw [hβδ]
      rw [← heq]
      exact mul_le_mul_of_nonneg_left htr (by positivity)
    have hχ_lb : Real.exp (β * (links : ℝ) / 2 - 3 * (L : ℝ) ^ 3 / (N : ℝ)) ≤ χ U W := by
      have hexp_eq : (Real.exp (β / 2 - 1 / (N : ℝ))) ^ links =
          Real.exp (β * (links : ℝ) / 2 - 3 * (L : ℝ) ^ 3 / (N : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        dsimp only [links]
        push_cast
        ring
      rw [← hexp_eq]
      calc (Real.exp (β / 2 - 1 / (N : ℝ))) ^ links
          = ∏ _e : (cubicTorus3 L).Link, Real.exp (β / 2 - 1 / (N : ℝ)) := by
              rw [Finset.prod_const, Finset.card_univ, h_card_links]
        _ ≤ χ U W :=
              Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun e _ => hχ_fac e
    calc Real.exp (β * (links : ℝ) / 2 - 15 * (L : ℝ) ^ 3 / (N : ℝ))
        = Real.exp (-(12 * (L : ℝ) ^ 3 / (N : ℝ))) *
            Real.exp (β * (links : ℝ) / 2 - 3 * (L : ℝ) ^ 3 / (N : ℝ)) := by
            rw [← Real.exp_add]; congr 1; ring
      _ ≤ cubicWilsonWeight L N β U * χ U W :=
            mul_le_mul hw_lb hχ_lb (Real.exp_pos _).le (Real.exp_pos _).le
  let c_KW : ℝ := μ.real B_L * Real.exp (β * (links : ℝ)) *
    Real.exp (-(30 * (L : ℝ) ^ 3 / (N : ℝ)))
  have hKW_B_L : ∀ U ∈ B_L, ∀ U' ∈ B_L, c_KW ≤ K_W U U' := by
    intro U hU U' hU'
    let c_prod : ℝ := Real.exp (β * (links : ℝ)) * Real.exp (-(30 * (L : ℝ) ^ 3 / (N : ℝ)))
    have h_int_κ : MeasureTheory.Integrable (fun W => κ U W * κ U' W) μ :=
      integrable_of_continuous_compact μ _
        ((continuous_prod2_left hκ_cont U).mul (continuous_prod2_left hκ_cont U'))
    have h_ind_int : MeasureTheory.Integrable (B_L.indicator (fun _ => c_prod)) μ :=
      (MeasureTheory.integrable_const c_prod).indicator hB_L_meas
    have h_le : ∀ W, B_L.indicator (fun _ => c_prod) W ≤ κ U W * κ U' W := by
      intro W
      by_cases hW : W ∈ B_L
      · rw [Set.indicator_of_mem hW]
        have h1 := hκ_B_L U hU W hW
        have h2 := hκ_B_L U' hU' W hW
        calc c_prod = Real.exp (β * (links : ℝ) / 2 - 15 * (L : ℝ) ^ 3 / (N : ℝ)) *
                Real.exp (β * (links : ℝ) / 2 - 15 * (L : ℝ) ^ 3 / (N : ℝ)) := by
                dsimp [c_prod]; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
          _ ≤ κ U W * κ U' W :=
                mul_le_mul h1 h2 (Real.exp_pos _).le (hκ_nn U W)
      · rw [Set.indicator_of_notMem hW]
        exact mul_nonneg (hκ_nn U W) (hκ_nn U' W)
    have h_ind_val : ∫ W, B_L.indicator (fun _ => c_prod) W ∂μ = c_KW := by
      rw [MeasureTheory.integral_indicator hB_L_meas, MeasureTheory.setIntegral_const]
      dsimp [c_KW, c_prod]
      ring
    rw [hKW_eq_κ U U', ← h_ind_val]
    exact MeasureTheory.integral_mono h_ind_int h_int_κ h_le
  let ψ_B : HaarGaugeSpace μ :=
    MeasureTheory.indicatorConstLp (2 : ENNReal) hB_L_meas (MeasureTheory.measure_ne_top μ B_L) (1 : ℂ)
  have hψB_norm_sq : ‖ψ_B‖ ^ 2 = μ.real B_L := by
    have hre : (⟪ψ_B, ψ_B⟫_ℂ).re = μ.real B_L := by
      dsimp only [ψ_B]
      rw [MeasureTheory.L2.inner_indicatorConstLp_indicatorConstLp
        (hμs := MeasureTheory.measure_ne_top μ B_L)
        (hμt := MeasureTheory.measure_ne_top μ B_L)]
      have h1 : ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ = 1 := by
        rw [inner_self_eq_norm_sq_to_K]; norm_num
      rw [Set.inter_self, h1, Complex.real_smul, mul_one, Complex.ofReal_re]
    rw [inner_self_eq_norm_sq_to_K] at hre
    simpa [pow_two] using hre
  have hT_raw_re_ub : (⟪ψ_B, T_raw ψ_B⟫_ℂ).re ≤ lam0 * μ.real B_L := by
    calc (⟪ψ_B, T_raw ψ_B⟫_ℂ).re
        ≤ ‖⟪ψ_B, T_raw ψ_B⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖ψ_B‖ * ‖T_raw ψ_B‖ := norm_inner_le_norm _ _
      _ ≤ ‖ψ_B‖ * (lam0 * ‖ψ_B‖) :=
          mul_le_mul_of_nonneg_left (T_raw.le_opNorm ψ_B) (norm_nonneg _)
      _ = lam0 * ‖ψ_B‖ ^ 2 := by ring
      _ = lam0 * μ.real B_L := by rw [hψB_norm_sq]
  have hT_raw_re_lb : μ.real B_L * (μ.real B_L * c_KW) ≤ (⟪ψ_B, T_raw ψ_B⟫_ℂ).re := by
    have hl2 : MeasureTheory.Integrable (fun U => ⟪ψ_B U, (T_raw ψ_B) U⟫_ℂ) μ :=
      MeasureTheory.L2.integrable_inner _ _
    have h_in_re : (⟪ψ_B, T_raw ψ_B⟫_ℂ).re =
        ∫ U, (⟪ψ_B U, (T_raw ψ_B) U⟫_ℂ).re ∂μ := by
      rw [MeasureTheory.L2.inner_def]
      change RCLike.re (∫ U, ⟪ψ_B U, (T_raw ψ_B) U⟫_ℂ ∂μ) = _
      rw [← integral_re hl2]
      rfl
    have hψB_ae := MeasureTheory.indicatorConstLp_coeFn (p := (2 : ENNReal))
      (μ := μ) (s := B_L) (hs := hB_L_meas) (hμs := MeasureTheory.measure_ne_top μ B_L)
      (c := (1 : ℂ))
    have hT_ae := wilsonIntegralOp_apply_ae L N β hβ_pos.le K_kin hK_cont hK_nn
      ((linkChiUb L β) ^ 2) (sq_nonneg _) hK_bd ψ_B
    rw [← hT_raw_def] at hT_ae
    have h_fn_lb : ∀ U ∈ B_L,
        μ.real B_L * c_KW ≤ RCLike.re (wilsonIntegralFn L N β K_kin ψ_B U) := by
      intro U hU
      dsimp [wilsonIntegralFn]
      have h_int_fn := wilsonKernel_mul_integrable L N β hβ_pos.le K_kin hK_cont hK_nn
        ((linkChiUb L β) ^ 2) hK_bd ψ_B U
      change _ ≤ RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * ⇑ψ_B U' ∂μ)
      rw [← integral_re h_int_fn]
      have h_ae_U' : ∀ᵐ U' ∂μ,
          B_L.indicator (fun _ => c_KW) U' ≤
            RCLike.re (((K_W U U' : ℝ) : ℂ) * ⇑ψ_B U') := by
        filter_upwards [hψB_ae] with U' hU'
        change _ ≤ (((K_W U U' : ℝ) : ℂ) * ⇑ψ_B U').re
        rw [hU']
        by_cases hU'B : U' ∈ B_L
        · rw [Set.indicator_of_mem hU'B, Set.indicator_of_mem hU'B, mul_one, Complex.ofReal_re]
          exact hKW_B_L U hU U' hU'B
        · rw [Set.indicator_of_notMem hU'B, Set.indicator_of_notMem hU'B, mul_zero,
            Complex.zero_re]
      have h_ind_val : ∫ U', B_L.indicator (fun _ => c_KW) U' ∂μ = μ.real B_L * c_KW := by
        rw [MeasureTheory.integral_indicator hB_L_meas, MeasureTheory.setIntegral_const,
          smul_eq_mul]
      rw [← h_ind_val]
      exact MeasureTheory.integral_mono_ae
        ((MeasureTheory.integrable_const c_KW).indicator hB_L_meas) h_int_fn.re h_ae_U'
    have h_ae_U : ∀ᵐ U ∂μ,
        B_L.indicator (fun _ => μ.real B_L * c_KW) U ≤ (⟪ψ_B U, (T_raw ψ_B) U⟫_ℂ).re := by
      filter_upwards [hψB_ae, hT_ae] with U hU hTU
      rw [hU, hTU, hcinner]
      by_cases hUB : U ∈ B_L
      · rw [Set.indicator_of_mem hUB, Set.indicator_of_mem hUB, map_one, one_mul]
        exact h_fn_lb U hUB
      · rw [Set.indicator_of_notMem hUB, Set.indicator_of_notMem hUB, map_zero, zero_mul,
          Complex.zero_re]
    have h_ind_val2 :
        ∫ U, B_L.indicator (fun _ => μ.real B_L * c_KW) U ∂μ = μ.real B_L * (μ.real B_L * c_KW) := by
      rw [MeasureTheory.integral_indicator hB_L_meas, MeasureTheory.setIntegral_const,
        smul_eq_mul]
    rw [h_in_re, ← h_ind_val2]
    exact MeasureTheory.integral_mono_ae
      ((MeasureTheory.integrable_const (μ.real B_L * c_KW)).indicator hB_L_meas)
      hl2.re h_ae_U
  have hlam0_lb :
      (((K : ℝ) ^ (2 * N * N)) ^ (2 * links))⁻¹ * Real.exp (β * (links : ℝ)) *
          Real.exp (-(30 * (L : ℝ) ^ 3 / (N : ℝ))) ≤ lam0 := by
    have h_mul_le : μ.real B_L * (μ.real B_L * c_KW) ≤ lam0 * μ.real B_L :=
      hT_raw_re_lb.trans hT_raw_re_ub
    have h_div_le : μ.real B_L * c_KW ≤ lam0 :=
      (mul_le_mul_iff_left₀ hB_L_pos).mp (by linarith only [h_mul_le])
    have hB_sq_lb : (((K : ℝ) ^ (2 * N * N)) ^ (2 * links))⁻¹ ≤ (μ.real B_L) ^ 2 := by
      have h1 := pow_le_pow_left₀ (by positivity) hB_L_lb 2
      rwa [inv_pow, ← pow_mul, mul_comm links 2] at h1
    calc (((K : ℝ) ^ (2 * N * N)) ^ (2 * links))⁻¹ * Real.exp (β * (links : ℝ)) *
            Real.exp (-(30 * (L : ℝ) ^ 3 / (N : ℝ)))
        ≤ (μ.real B_L) ^ 2 * Real.exp (β * (links : ℝ)) *
            Real.exp (-(30 * (L : ℝ) ^ 3 / (N : ℝ))) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hB_sq_lb (Real.exp_pos _).le) (Real.exp_pos _).le
      _ = μ.real B_L * c_KW := by dsimp [c_KW]; ring
      _ ≤ lam0 := h_div_le
  -- Combine Dirichlet inequality, `hF3_int_le`, and `hlam0_lb`
  have h_gap_err : (1 - Real.exp (-S.Δ)) * (N : ℝ) ≤ (N : ℝ) * err := by
    have h_comb1 : (1 - Real.exp (-S.Δ)) * (N : ℝ) ≤
        (1 / (2 * lam0)) * (4 * ε_sq * lam0 + C_bad) := by
      calc (1 - Real.exp (-S.Δ)) * (N : ℝ)
          ≤ ∑ i : Fin N, ∑ j : Fin N, (‖ψ i j‖ ^ 2 - (⟪ψ i j, S.T (ψ i j)⟫_ℂ).re) := hgap_sum
        _ = (1 / (2 * lam0)) * ∫ q : (G_L × G_L) × G_L, F3 q ∂((μ.prod μ).prod μ) := by
              rw [h_dirichlet, h_dirichlet_prod3]
        _ ≤ (1 / (2 * lam0)) * (4 * ε_sq * lam0 + C_bad) :=
              mul_le_mul_of_nonneg_left hF3_int_le (by positivity)
    have h_part1 : (1 / (2 * lam0)) * (4 * ε_sq * lam0) = 2 * ε_sq := by
      field_simp [hlam0_pos.ne']; ring
    have h_part2 : (1 / (2 * lam0)) * C_bad ≤
        8 * (N : ℝ) * Real.exp (30 * (L : ℝ) ^ 3 / (N : ℝ)) *
          ((K : ℝ) ^ (2 * N * N)) ^ (2 * links) *
          β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) := by
      let L0 : ℝ := (((K : ℝ) ^ (2 * N * N)) ^ (2 * links))⁻¹ *
        Real.exp (β * (links : ℝ)) * Real.exp (-(30 * (L : ℝ) ^ 3 / (N : ℝ)))
      have hL0_pos : 0 < L0 := by dsimp [L0]; positivity
      have hinv : (2 * lam0)⁻¹ ≤ (2 * L0)⁻¹ :=
        inv_anti₀ (mul_pos two_pos hL0_pos) (mul_le_mul_of_nonneg_left hlam0_lb zero_le_two)
      have h_mul : C_bad * (2 * lam0)⁻¹ ≤ C_bad * (2 * L0)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hC_bad_nn
      have h_rhs_eq : C_bad * (2 * L0)⁻¹ =
          2 * (N : ℝ) * Real.exp (30 * (L : ℝ) ^ 3 / (N : ℝ)) *
            ((K : ℝ) ^ (2 * N * N)) ^ (2 * links) *
            β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) := by
        dsimp [C_bad, L0]
        have hK_ne : ((K : ℝ) ^ (2 * N * N)) ^ (2 * links) ≠ 0 := by positivity
        have hexp1 : Real.exp (β * (links : ℝ)) ≠ 0 := (Real.exp_pos _).ne'
        have hexp2 : Real.exp (-(30 * (L : ℝ) ^ 3 / (N : ℝ))) ≠ 0 := (Real.exp_pos _).ne'
        rw [Real.exp_neg]
        field_simp [hK_ne, hexp1, hexp2]
        ring
      have h2_le_8 :
          2 * (N : ℝ) * Real.exp (30 * (L : ℝ) ^ 3 / (N : ℝ)) *
            ((K : ℝ) ^ (2 * N * N)) ^ (2 * links) *
            β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) ≤
          8 * (N : ℝ) * Real.exp (30 * (L : ℝ) ^ 3 / (N : ℝ)) *
            ((K : ℝ) ^ (2 * N * N)) ^ (2 * links) *
            β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) := by
        have hnonneg : 0 ≤ (N : ℝ) * Real.exp (30 * (L : ℝ) ^ 3 / (N : ℝ)) *
            ((K : ℝ) ^ (2 * N * N)) ^ (2 * links) *
            β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) := by positivity
        linarith only [hnonneg]
      calc (1 / (2 * lam0)) * C_bad = C_bad * (2 * lam0)⁻¹ := by rw [one_div, mul_comm]
        _ ≤ C_bad * (2 * L0)⁻¹ := h_mul
        _ = 2 * (N : ℝ) * Real.exp (30 * (L : ℝ) ^ 3 / (N : ℝ)) *
              ((K : ℝ) ^ (2 * N * N)) ^ (2 * links) *
              β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) := h_rhs_eq
        _ ≤ _ := h2_le_8
    have h_N_err : (N : ℝ) * err =
        2 * ε_sq + 8 * (N : ℝ) * Real.exp (30 * (L : ℝ) ^ 3 / (N : ℝ)) *
          ((K : ℝ) ^ (2 * N * N)) ^ (2 * links) *
          β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) := by
      dsimp [err, cubicGapErr, ε_sq, K, links]
      field_simp [hN_pos.ne', hβ_pos.ne']
    calc (1 - Real.exp (-S.Δ)) * (N : ℝ)
        ≤ (1 / (2 * lam0)) * (4 * ε_sq * lam0 + C_bad) := h_comb1
      _ = (1 / (2 * lam0)) * (4 * ε_sq * lam0) + (1 / (2 * lam0)) * C_bad := by ring
      _ ≤ 2 * ε_sq + 8 * (N : ℝ) * Real.exp (30 * (L : ℝ) ^ 3 / (N : ℝ)) *
            ((K : ℝ) ^ (2 * N * N)) ^ (2 * links) *
            β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) := by linarith only [h_part1, h_part2]
      _ = (N : ℝ) * err := h_N_err.symm
  have h1_sub : 1 - err ≤ Real.exp (-S.Δ) := by
    have hle : 1 - Real.exp (-S.Δ) ≤ err :=
      (mul_le_mul_iff_left₀ hN_pos).mp (by linarith only [h_gap_err])
    linarith only [hle]
  have hlog : Real.log (1 - err) ≤ -S.Δ := by
    calc Real.log (1 - err) ≤ Real.log (Real.exp (-S.Δ)) :=
          Real.log_le_log (by linarith only [herr_lt]) h1_sub
      _ = -S.Δ := Real.log_exp _
  linarith only [hlog]

/-! ## §4. Unconditional `SUYangMillsRGConjecture N hN` & `ClayYangMillsMassGap4D N hN` -/


/-- **Unconditional `SUYangMillsRGConjecture N hN` (`0 sorry`, `0 axioms`)**
realizing `iidOS4DStrict` + `iidSmearedOSPreData` along `L_m = m + 1`,
`β_m = exp((m + 1)⁴)`, `a_m = Δ_latt m`, and `latt_obs = iidProbeFamily`. -/
theorem su_yang_mills_rg_conjecture_unconditional (N : ℕ) (hN : 2 ≤ N) :
    letI := canonSUMeas N
    haveI := canonSUBorel N
    SUYangMillsRGConjecture N hN := by
  letI := canonSUMeas N
  haveI := canonSUBorel N
  let Ls_seq : ℕ → ℕ := fun m => m + 1
  let Lt_seq : ℕ → ℕ := fun m => m + 1
  have hLs : ∀ m, NeZero (Ls_seq m) := fun m => ⟨Nat.succ_ne_zero m⟩
  have hLt : ∀ m, NeZero (Lt_seq m) := fun m => ⟨Nat.succ_ne_zero m⟩
  let β_seq : ℕ → ℝ := fun m => Real.exp (((m : ℝ) + 1) ^ 4)
  have hβ_pos : ∀ m, 0 < β_seq m := fun m => Real.exp_pos _
  let a_seq : ℕ → ℝ := fun m =>
    (fullRankCubicNonAbelianWilsonSetup (Ls_seq m) N hN (β_seq m) (hβ_pos m)).gaugeSetup.Δ
  let g_sq_seq : ℕ → ℝ := fun m => 2 * (N : ℝ) / β_seq m
  let latt_obs : ∀ (m n : ℕ), (Fin n → Space4) → Fin n →
      (GaugeField (cubicTorus4 (Ls_seq m) (Lt_seq m))
        (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ) :=
    fun m n xs => iidProbeFamily (Ls_seq m) (Lt_seq m) N n xs m
  have ha_pos : ∀ m, 0 < a_seq m := fun m =>
    (fullRankCubicNonAbelianWilsonSetup (Ls_seq m) N hN (β_seq m) (hβ_pos m)).gaugeSetup.Δ_pos
  have ha_lim : Filter.Tendsto a_seq Filter.atTop (nhds 0) := by
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hN_ge : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    let C_err : ℝ := 216 * (18 * (N : ℝ) ^ 2 + 2) + 8
    have hC_pos : 0 < C_err := by dsimp [C_err]; positivity
    let M₀ : ℕ := Nat.ceil (max (max 15 (Real.log (4 * (N : ℝ) + 2))) (2 * C_err + 1))
    have h_ev_bound : ∀ m : ℕ, M₀ ≤ m → a_seq m ≤ 2 * C_err / ((m : ℝ) + 1) := by
      intro m hm
      let L : ℕ := Ls_seq m
      haveI : NeZero L := hLs m
      let x : ℝ := (m : ℝ) + 1
      have hx_eq : (L : ℝ) = x := by dsimp [L, Ls_seq, x]; push_cast; ring
      have hx_ge1 : 1 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) m]
      have hx_pos : 0 < x := by linarith
      have hx_ge_M₀ : max (max 15 (Real.log (4 * (N : ℝ) + 2))) (2 * C_err + 1) ≤ x := by
        have h1 : (M₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have h2 : max (max 15 (Real.log (4 * (N : ℝ) + 2))) (2 * C_err + 1) ≤ (M₀ : ℝ) :=
          Nat.le_ceil _
        linarith
      have hx_ge15 : 15 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx_ge_M₀
      have hx_ge_log : Real.log (4 * (N : ℝ) + 2) ≤ x :=
        le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx_ge_M₀
      have hx_ge_Cerr : 2 * C_err + 1 ≤ x := le_trans (le_max_right _ _) hx_ge_M₀
      let β : ℝ := β_seq m
      have hβ_pos_m : 0 < β := hβ_pos m
      have hβ_ge1 : 1 ≤ β := Real.one_le_exp (by positivity)
      have hlog_β : Real.log β = x ^ 4 := Real.log_exp (x ^ 4)
      let links : ℕ := 3 * L ^ 3
      have hlinks_eq : (links : ℝ) = 3 * x ^ 3 := by
        dsimp [links]
        push_cast
        rw [hx_eq]
      let ε_sq : ℝ := 4 * (N : ℝ) * ((6 * (N : ℝ) ^ 2 * (links : ℝ) + 2) * Real.log β) / β
      let K : ℕ := Nat.ceil (4 * (N : ℝ) / (1 / Real.sqrt β)) + 1
      let err : ℝ := cubicGapErr L N β
      have hx_cubed : 1 ≤ x ^ 3 := one_le_pow₀ hx_ge1
      have hx_pow_le : x ^ 8 ≤ 27 * β := by
        have hu : (x ^ 4 / 3) ^ 3 ≤ β := by
          have hadd : x ^ 4 / 3 ≤ Real.exp (x ^ 4 / 3) := by
            linarith [Real.add_one_le_exp (x ^ 4 / 3)]
          have hpow := pow_le_pow_left₀ (by positivity) hadd 3
          rw [← Real.exp_nat_mul] at hpow
          simpa [β, β_seq, x] using
            (hpow.trans_eq (congrArg Real.exp (show ((3 : ℕ) : ℝ) * (x ^ 4 / 3) = x ^ 4 by ring)))
        have hx12 : x ^ 12 ≤ 27 * β := by
          rw [show x ^ 12 = 27 * (x ^ 4 / 3) ^ 3 by ring]
          linarith
        have hx8_12 : x ^ 8 ≤ x ^ 12 := by
          simpa [show x ^ 8 * x ^ 4 = x ^ 12 by ring] using
            mul_le_mul_of_nonneg_left (one_le_pow₀ hx_ge1 (n := 4)) (by positivity : 0 ≤ x ^ 8)
        exact hx8_12.trans hx12
      have h_term1 : 2 * ε_sq / (N : ℝ) ≤ 216 * (18 * (N : ℝ) ^ 2 + 2) / x := by
        have hpoly : 6 * (N : ℝ) ^ 2 * (links : ℝ) + 2 ≤ (18 * (N : ℝ) ^ 2 + 2) * x ^ 3 := by
          rw [hlinks_eq,
            show (18 * (N : ℝ) ^ 2 + 2) * x ^ 3 = 6 * (N : ℝ) ^ 2 * (3 * x ^ 3) + 2 * x ^ 3 by ring]
          linarith [hx_cubed]
        have hlog_mul : (6 * (N : ℝ) ^ 2 * (links : ℝ) + 2) * Real.log β ≤
            (18 * (N : ℝ) ^ 2 + 2) * x ^ 7 := by
          rw [hlog_β]
          calc (6 * (N : ℝ) ^ 2 * (links : ℝ) + 2) * x ^ 4
              ≤ ((18 * (N : ℝ) ^ 2 + 2) * x ^ 3) * x ^ 4 :=
                  mul_le_mul_of_nonneg_right hpoly (by positivity)
            _ = (18 * (N : ℝ) ^ 2 + 2) * x ^ 7 := by ring
        have hx7_div : x ^ 7 / β ≤ 27 / x := by
          rw [div_le_div_iff₀ hβ_pos_m hx_pos, show x ^ 7 * x = x ^ 8 by ring]
          exact hx_pow_le
        calc 2 * ε_sq / (N : ℝ)
            = 8 * ((6 * (N : ℝ) ^ 2 * (links : ℝ) + 2) * Real.log β) / β := by
                dsimp [ε_sq]; field_simp [hN_pos.ne', hβ_pos_m.ne']; ring
          _ ≤ 8 * ((18 * (N : ℝ) ^ 2 + 2) * x ^ 7) / β :=
                div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog_mul (by norm_num))
                  hβ_pos_m.le
          _ = 8 * (18 * (N : ℝ) ^ 2 + 2) * (x ^ 7 / β) := by ring
          _ ≤ 8 * (18 * (N : ℝ) ^ 2 + 2) * (27 / x) :=
                mul_le_mul_of_nonneg_left hx7_div (by positivity)
          _ = 216 * (18 * (N : ℝ) ^ 2 + 2) / x := by ring
      have hsqrt_β : Real.sqrt β = Real.exp (x ^ 4 / 2) := by
        have hsq : Real.exp (x ^ 4 / 2) ^ 2 = β := by
          dsimp [β, β_seq, x]
          rw [← Real.exp_nat_mul]
          congr 1; ring
        rw [← hsq, Real.sqrt_sq (Real.exp_pos _).le]
      have hK_ub : (K : ℝ) ≤ Real.exp (x + x ^ 4 / 2) := by
        have harg_nn : 0 ≤ 4 * (N : ℝ) / (1 / Real.sqrt β) := by positivity
        have hceil : (Nat.ceil (4 * (N : ℝ) / (1 / Real.sqrt β)) : ℝ) <
            4 * (N : ℝ) / (1 / Real.sqrt β) + 1 := Nat.ceil_lt_add_one harg_nn
        have hK_le1 : (K : ℝ) ≤ 4 * (N : ℝ) * Real.exp (x ^ 4 / 2) + 2 := by
          have h1 : (K : ℝ) = (Nat.ceil (4 * (N : ℝ) / (1 / Real.sqrt β)) : ℝ) + 1 := by
            dsimp [K]; push_cast; ring
          rw [h1]
          have h_div : 4 * (N : ℝ) / (1 / Real.sqrt β) = 4 * (N : ℝ) * Real.exp (x ^ 4 / 2) := by
            rw [← hsqrt_β]
            field_simp [(Real.sqrt_pos.mpr hβ_pos_m).ne']
          linarith
        have hexp_half_ge1 : 1 ≤ Real.exp (x ^ 4 / 2) := Real.one_le_exp (by positivity)
        have h4N_le : 4 * (N : ℝ) + 2 ≤ Real.exp x := by
          rw [← Real.exp_log (by positivity : 0 < 4 * (N : ℝ) + 2)]
          exact Real.exp_le_exp.mpr hx_ge_log
        calc (K : ℝ) ≤ 4 * (N : ℝ) * Real.exp (x ^ 4 / 2) + 2 := hK_le1
          _ ≤ 4 * (N : ℝ) * Real.exp (x ^ 4 / 2) + 2 * Real.exp (x ^ 4 / 2) := by linarith
          _ = (4 * (N : ℝ) + 2) * Real.exp (x ^ 4 / 2) := by ring
          _ ≤ Real.exp x * Real.exp (x ^ 4 / 2) :=
              mul_le_mul_of_nonneg_right h4N_le (Real.exp_pos _).le
          _ = Real.exp (x + x ^ 4 / 2) := (Real.exp_add _ _).symm
      have h_term2 :
          (8 * (N : ℝ) * Real.exp (30 * (L : ℝ) ^ 3 / (N : ℝ)) *
            ((K : ℝ) ^ (2 * N * N)) ^ (2 * links) *
            β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2))) / (N : ℝ) ≤ 8 / x := by
        have hK_pow : ((K : ℝ) ^ (2 * N * N)) ^ (2 * links) ≤
            Real.exp (4 * (N : ℝ) ^ 2 * (links : ℝ) * x +
              2 * (N : ℝ) ^ 2 * (links : ℝ) * x ^ 4) := by
          rw [← pow_mul]
          calc (K : ℝ) ^ (2 * N * N * (2 * links))
              ≤ (Real.exp (x + x ^ 4 / 2)) ^ (2 * N * N * (2 * links)) :=
                  pow_le_pow_left₀ (Nat.cast_nonneg _) hK_ub _
            _ = Real.exp (((2 * N * N * (2 * links) : ℕ) : ℝ) * (x + x ^ 4 / 2)) := by
                  rw [← Real.exp_nat_mul]
            _ = Real.exp (4 * (N : ℝ) ^ 2 * (links : ℝ) * x +
                  2 * (N : ℝ) ^ 2 * (links : ℝ) * x ^ 4) := by
                  congr 1; push_cast; ring
        have hβ_pow : β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2)) =
            Real.exp (-(6 * (N : ℝ) ^ 2 * (links : ℝ) * x ^ 4 + 2 * x ^ 4)) := by
          rw [Real.rpow_def_of_pos hβ_pos_m, hlog_β]
          congr 1; ring
        have h_exp_sum_le :
            30 * (L : ℝ) ^ 3 / (N : ℝ) +
              (4 * (N : ℝ) ^ 2 * (links : ℝ) * x + 2 * (N : ℝ) ^ 2 * (links : ℝ) * x ^ 4) +
              -(6 * (N : ℝ) ^ 2 * (links : ℝ) * x ^ 4 + 2 * x ^ 4) ≤ -(x ^ 4) := by
          have h1 : 30 * (L : ℝ) ^ 3 / (N : ℝ) ≤ x ^ 4 := by
            rw [hx_eq]
            have hdiv : 30 * x ^ 3 / (N : ℝ) ≤ 30 * x ^ 3 / 2 :=
              div_le_div_of_nonneg_left (by positivity) (by norm_num) hN_ge
            have h15 : 15 * x ^ 3 ≤ x ^ 4 := by
              rw [show x ^ 4 = x * x ^ 3 by ring]
              exact mul_le_mul_of_nonneg_right hx_ge15 (by positivity)
            linarith
          have h2 : x ≤ x ^ 4 := by
            simpa [show x ^ 4 = x * x ^ 3 by ring] using
              mul_le_mul_of_nonneg_left hx_cubed hx_pos.le
          have h3 : 4 * (N : ℝ) ^ 2 * (links : ℝ) * x ≤
              4 * (N : ℝ) ^ 2 * (links : ℝ) * x ^ 4 :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
          have h_id :
              30 * (L : ℝ) ^ 3 / (N : ℝ) +
                (4 * (N : ℝ) ^ 2 * (links : ℝ) * x + 2 * (N : ℝ) ^ 2 * (links : ℝ) * x ^ 4) +
                -(6 * (N : ℝ) ^ 2 * (links : ℝ) * x ^ 4 + 2 * x ^ 4) =
              30 * (L : ℝ) ^ 3 / (N : ℝ) +
                (4 * (N : ℝ) ^ 2 * (links : ℝ) * x - 4 * (N : ℝ) ^ 2 * (links : ℝ) * x ^ 4) -
                2 * x ^ 4 := by ring
          rw [h_id]
          linarith
        have hexp_inv : Real.exp (-(x ^ 4)) ≤ 1 / x := by
          have hx_le_exp : x ≤ Real.exp (x ^ 4) := by
            have h1 : x ≤ x ^ 4 := by
              simpa [show x ^ 4 = x * x ^ 3 by ring] using
                mul_le_mul_of_nonneg_left hx_cubed hx_pos.le
            linarith [Real.add_one_le_exp (x ^ 4)]
          rw [Real.exp_neg, one_div]
          exact inv_anti₀ hx_pos hx_le_exp
        calc (8 * (N : ℝ) * Real.exp (30 * (L : ℝ) ^ 3 / (N : ℝ)) *
                ((K : ℝ) ^ (2 * N * N)) ^ (2 * links) *
                β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2))) / (N : ℝ)
            = 8 * (Real.exp (30 * (L : ℝ) ^ 3 / (N : ℝ)) *
                ((K : ℝ) ^ (2 * N * N)) ^ (2 * links) *
                β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2))) := by
                field_simp [hN_pos.ne']
          _ ≤ 8 * (Real.exp (30 * (L : ℝ) ^ 3 / (N : ℝ)) *
                Real.exp (4 * (N : ℝ) ^ 2 * (links : ℝ) * x +
                  2 * (N : ℝ) ^ 2 * (links : ℝ) * x ^ 4) *
                Real.exp (-(6 * (N : ℝ) ^ 2 * (links : ℝ) * x ^ 4 + 2 * x ^ 4))) := by
                rw [hβ_pow]
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hK_pow (Real.exp_pos _).le)
                    (Real.exp_pos _).le)
                  (by norm_num)
          _ = 8 * Real.exp (30 * (L : ℝ) ^ 3 / (N : ℝ) +
                (4 * (N : ℝ) ^ 2 * (links : ℝ) * x + 2 * (N : ℝ) ^ 2 * (links : ℝ) * x ^ 4) +
                -(6 * (N : ℝ) ^ 2 * (links : ℝ) * x ^ 4 + 2 * x ^ 4)) := by
                simp only [← Real.exp_add, add_assoc]
          _ ≤ 8 * Real.exp (-(x ^ 4)) :=
                mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h_exp_sum_le) (by norm_num)
          _ ≤ 8 * (1 / x) := mul_le_mul_of_nonneg_left hexp_inv (by norm_num)
          _ = 8 / x := by ring
      have herr_le : err ≤ C_err / x := by
        calc err = 2 * ε_sq / (N : ℝ) +
              (8 * (N : ℝ) * Real.exp (30 * (L : ℝ) ^ 3 / (N : ℝ)) *
                ((K : ℝ) ^ (2 * N * N)) ^ (2 * links) *
                β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2))) / (N : ℝ) := by
                dsimp [err, cubicGapErr]; ring
          _ ≤ 216 * (18 * (N : ℝ) ^ 2 + 2) / x + 8 / x := add_le_add h_term1 h_term2
          _ = C_err / x := by dsimp [C_err]; ring
      have herr_half : err ≤ 1 / 2 := by
        have hdiv : C_err / x ≤ 1 / 2 := by
          rw [div_le_div_iff₀ hx_pos (by norm_num)]
          linarith
        exact herr_le.trans hdiv
      have herr_lt1 : err < 1 := lt_of_le_of_lt herr_half (by norm_num)
      have hgap := fullRankCubic_gap_upper_bound L N hN hβ_ge1 herr_lt1
      have ha_le_log : a_seq m ≤ -Real.log (1 - err) := hgap
      let u : ℝ := 1 - err
      have hu_ge : 1 / 2 ≤ u := by dsimp [u]; linarith
      have hu_pos : 0 < u := by linarith
      have hlog_inv : -Real.log u ≤ u⁻¹ - 1 := by
        have h1 : u⁻¹ ≤ Real.exp (u⁻¹ - 1) := by linarith [Real.add_one_le_exp (u⁻¹ - 1)]
        have h2 := Real.log_le_log (inv_pos.mpr hu_pos) h1
        rw [Real.log_exp, Real.log_inv] at h2
        exact h2
      have hinv_sub : u⁻¹ - 1 ≤ 2 * C_err / x := by
        have heq : u⁻¹ - 1 = err / u := by
          dsimp [u] at hu_pos ⊢
          field_simp [hu_pos.ne']
          ring
        have herr_nn : 0 ≤ err := by
          have hlog_nn : 0 ≤ Real.log β := Real.log_nonneg hβ_ge1
          dsimp [err, cubicGapErr, ε_sq]
          positivity
        rw [heq]
        calc err / u ≤ (C_err / x) / (1 / 2) :=
              div_le_div₀ (by positivity) herr_le (by norm_num) hu_ge
          _ = 2 * C_err / x := by ring
      exact ha_le_log.trans (hlog_inv.trans hinv_sub)
    let ub : ℕ → ℝ := fun m => if m < M₀ then a_seq m else 2 * C_err / ((m : ℝ) + 1)
    have h_le_ub : ∀ m, a_seq m ≤ ub m := fun m => by
      dsimp only [ub]
      split_ifs with hm
      · exact le_rfl
      · exact h_ev_bound m (le_of_not_gt hm)
    have h_ub_tendsto : Filter.Tendsto ub Filter.atTop (nhds 0) := by
      have h_rhs : Filter.Tendsto (fun m : ℕ => 2 * C_err / ((m : ℝ) + 1)) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop
          (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      refine h_rhs.congr' ?_
      rw [Filter.EventuallyEq, Filter.eventually_atTop]
      refine ⟨M₀, fun m hm => ?_⟩
      dsimp only [ub]
      rw [if_neg (not_lt.mpr hm)]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_ub_tendsto
      (fun m => (ha_pos m).le) h_le_ub
  have hβ_lim : Filter.Tendsto β_seq Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun m => ?_) tendsto_natCast_atTop_atTop
    have hx1 : 1 ≤ (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
    have hx4 : (m : ℝ) + 1 ≤ ((m : ℝ) + 1) ^ 4 := by
      have h3 : 1 ≤ ((m : ℝ) + 1) ^ 3 := one_le_pow₀ hx1
      simpa [show ((m : ℝ) + 1) ^ 4 = ((m : ℝ) + 1) * ((m : ℝ) + 1) ^ 3 by ring] using
        mul_le_mul_of_nonneg_left h3 (by linarith)
    have hexp : ((m : ℝ) + 1) ^ 4 + 1 ≤ Real.exp (((m : ℝ) + 1) ^ 4) :=
      Real.add_one_le_exp _
    dsimp [β_seq]
    linarith
  have hg_pos : ∀ m, 0 < g_sq_seq m := fun m => by
    dsimp [g_sq_seq]
    positivity
  have hgap_one : ∀ m,
      (fullRankCubicNonAbelianWilsonSetup (Ls_seq m) N hN (β_seq m) (hβ_pos m)).gaugeSetup.Δ /
        a_seq m = 1 := fun m => div_self (ha_pos m).ne'
  refine ⟨1, iidOS4DStrict.toOS4DContinuumTheory, iidSmearedOSPreData, Ls_seq, Lt_seq, hLs, hLt,
    a_seq, β_seq, g_sq_seq, hβ_pos, latt_obs, ha_pos, ha_lim, hβ_lim, hg_pos, ?_, ?_, ?_⟩
  · refine ⟨1, zero_lt_one, fun m => ?_⟩
    rw [hgap_one m]
  · refine tendsto_const_nhds.congr fun m => (hgap_one m).symm
  · intro n xs
    have h_const : ∀ m, cubic4Schwinger (Ls_seq m) (Lt_seq m) N (β_seq m) n (latt_obs m n xs) =
        iidOS4DStrict.toOS4DContinuumTheory.os.Schwinger n xs := fun m =>
      cubic4Schwinger_of_const_prod (Ls_seq m) (Lt_seq m) N (β_seq m) (hβ_pos m).le n
        (latt_obs m n xs) (iidSchwinger n xs)
        (fun U => iidProbeFamily_prod (Ls_seq m) (Lt_seq m) N n xs m U)
    exact tendsto_const_nhds.congr fun m => (h_const m).symm

/-- **Full-pipeline Closure of `ClayYangMillsMassGap4D N hN` (`0 sorry`, `0 axioms`)**
via `clay_yang_mills_from_rg_estimates`. -/
theorem clay_yang_mills_4d_from_su_closure (N : ℕ) (hN : 2 ≤ N) :
    letI := canonSUMeas N
    haveI := canonSUBorel N
    ClayYangMillsMassGap4D N hN := by
  letI := canonSUMeas N
  haveI := canonSUBorel N
  exact clay_yang_mills_from_rg_estimates N hN
    (su_yang_mills_rg_conjecture_unconditional N hN)

end YangMills.SUClosure

#check YangMills.SUClosure.su_yang_mills_rg_conjecture_unconditional
#print axioms YangMills.SUClosure.su_yang_mills_rg_conjecture_unconditional
#check YangMills.SUClosure.clay_yang_mills_4d_from_su_closure
#print axioms YangMills.SUClosure.clay_yang_mills_4d_from_su_closure