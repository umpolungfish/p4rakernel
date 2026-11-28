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

private noncomputable instance canonSUMeas (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) := inferInstance

private instance canonSUBorel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) := inferInstance

private instance canonGaugeBorel (L N : ℕ) [NeZero L] :
    BorelSpace (GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  Pi.borelSpace

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
  H_bd := fun _ => by
    simp [osConfigForm, osConfigInner_zero_left]
  H_sa := fun _ _ => by
    simp [osConfigForm, osConfigInner_zero_left, osConfigInner_zero_right]
  H_nonneg := fun _ => by
    simp [osConfigForm, osConfigInner_zero_right]
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
    have h_id_lift : ∀ x : Space4,
        osLiftOperator F (LinearMap.id : OSPosTestSpace →ₗ[ℂ] OSPosTestSpace)
          1 zero_le_one (fun v => by simp) = ContinuousLinearMap.id ℂ (OSHilbertSpace F) := by
      intro x
      ext1 z
      refine UniformSpace.Completion.induction_on z ?_ ?_
      · exact isClosed_eq
          (osLiftOperator F LinearMap.id 1 zero_le_one _).continuous
          (ContinuousLinearMap.id ℂ _).continuous
      · intro u
        refine Quotient.inductionOn u fun v => ?_
        change osLiftOperator F LinearMap.id 1 zero_le_one _
            (osCompletionMap F (osPreMk F v)) =
          osCompletionMap F (osPreMk F v)
        rw [osLiftOperator_coe]; rfl
    let S : Set (OSHilbertSpace F) :=
      {v : OSHilbertSpace F | ∃ (k : ℕ) (xs : Fin k → Space4),
        v = (List.ofFn (fun i : Fin k =>
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
  change ‖M i j‖ ^ 2 = (M i j * starRingEnd ℂ (M i j)).re
  rw [Complex.mul_conj, ← Complex.normSq_eq_norm_sq]
  simp

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
  rw [hstar]
  calc ((B : Matrix (Fin N) (Fin N) ℂ) * M * (star M * star (B : Matrix (Fin N) (Fin N) ℂ))).trace.re
      = ((B : Matrix (Fin N) (Fin N) ℂ) * (M * star M) * star (B : Matrix (Fin N) (Fin N) ℂ)).trace.re := by
          simp only [Matrix.mul_assoc]
    _ = (star (B : Matrix (Fin N) (Fin N) ℂ) * ((B : Matrix (Fin N) (Fin N) ℂ) * (M * star M))).trace.re := by
          rw [Matrix.trace_mul_comm]
    _ = ((star (B : Matrix (Fin N) (Fin N) ℂ) * (B : Matrix (Fin N) (Fin N) ℂ)) * (M * star M)).trace.re := by
          simp only [Matrix.mul_assoc]
    _ = (M * star M).trace.re := by
          rw [hB, Matrix.one_mul]

private lemma frobeniusNormSq_su_inv_sub_one {N : ℕ}
    (A : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    frobeniusNormSq (((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) - 1) =
      frobeniusNormSq ((A : Matrix (Fin N) (Fin N) ℂ) - 1) := by
  have hinv : ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
      (A : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    change ((A⁻¹ * A : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = 1
    simp
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
  have hsq : ‖(M₁ + M₂) i j‖ ^ 2 ≤ (‖M₁ i j‖ + ‖M₂ i j‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [hsq, sq_nonneg (‖M₁ i j‖ - ‖M₂ i j‖)]

private lemma frobeniusNormSq_sub_self_su {N : ℕ}
    (A B : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    frobeniusNormSq (((A * B⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) - 1) =
      frobeniusNormSq ((A : Matrix (Fin N) (Fin N) ℂ) - (B : Matrix (Fin N) (Fin N) ℂ)) := by
  have hB : ((B⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
      (B : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    change ((B⁻¹ * B : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = 1
    simp
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
    simp only [Submonoid.coe_mul, Matrix.sub_mul, Matrix.one_mul]
    abel
  rw [heq]
  exact (frobeniusNormSq_add_le _ _).trans_eq (by rw [frobeniusNormSq_mul_su_right])

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
          Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) =>
            sq_nonneg ‖(A : Matrix (Fin N) (Fin N) ℂ) k j‖) (Finset.mem_univ i)
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
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (Nat.le_succ _))
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
          (div_le_iff₀ hK_real_pos).mpr (by linarith)
        linarith
      · rw [hm1, mul_div_cancel_right₀ _ hK_real_pos.ne']; linarith
    · have hr_lt : r < 1 := lt_of_le_of_ne hr_hi hr1
      let t : ℝ := (r + 1) * (K : ℝ) / 2
      have ht_nn : 0 ≤ t := by dsimp [t]; nlinarith [hK_real_pos]
      have ht_lt : t < (K : ℝ) := by
        dsimp [t]
        have : r + 1 < 2 := by linarith
        nlinarith
      let m_nat : ℕ := Nat.floor t
      have hm_lt : m_nat < K := Nat.floor_lt ht_nn |>.mpr (by exact_mod_cast ht_lt)
      refine ⟨⟨m_nat, hm_lt⟩, ?_⟩
      have hm_le : (m_nat : ℝ) ≤ t := Nat.floor_le ht_nn
      have hm_gt : t < (m_nat : ℝ) + 1 := Nat.lt_floor_add_one t
      refine ⟨?_, ?_⟩
      · dsimp [t] at hm_le
        have : 2 * (m_nat : ℝ) / (K : ℝ) ≤ r + 1 := by
          rw [div_le_iff₀ hK_real_pos]; linarith
        linarith
      · dsimp [t] at hm_gt
        have : r + 1 ≤ 2 * ((m_nat : ℝ) + 1) / (K : ℝ) := by
          rw [le_div_iff₀ hK_real_pos]; linarith
        linarith
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
      exact (continuous_norm.comp ((continuous_apply j).comp ((continuous_apply i).comp
        ((continuous_subtype_val :
            Continuous fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
              (A : Matrix (Fin N) (Fin N) ℂ)).sub
          (continuous_const : Continuous fun _ : Matrix.specialUnitaryGroup (Fin N) ℂ =>
              (1 : Matrix (Fin N) (Fin N) ℂ)))))).pow 2
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
            rw [abs_le]
            constructor <;> linarith [show 2 * ((b (i, j, 0) : ℝ) + 1) / (K : ℝ) -
                2 * (b (i, j, 0) : ℝ) / (K : ℝ) = 2 / (K : ℝ) by ring]
          have him_diff : |((A : Matrix (Fin N) (Fin N) ℂ) i j).im -
              ((A₀ : Matrix (Fin N) (Fin N) ℂ) i j).im| ≤ 2 / (K : ℝ) := by
            obtain ⟨ha1, ha2⟩ := (hA i j).2
            obtain ⟨hb1, hb2⟩ := (hA₀ i j).2
            rw [abs_le]
            constructor <;> linarith [show 2 * ((b (i, j, 1) : ℝ) + 1) / (K : ℝ) -
                2 * (b (i, j, 1) : ℝ) / (K : ℝ) = 2 / (K : ℝ) by ring]
          have hnsq : ‖((A : Matrix (Fin N) (Fin N) ℂ) - (A₀ : Matrix (Fin N) (Fin N) ℂ)) i j‖ ^ 2 =
              (((A : Matrix (Fin N) (Fin N) ℂ) i j).re -
                ((A₀ : Matrix (Fin N) (Fin N) ℂ) i j).re) ^ 2 +
              (((A : Matrix (Fin N) (Fin N) ℂ) i j).im -
                ((A₀ : Matrix (Fin N) (Fin N) ℂ) i j).im) ^ 2 := by
            rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [sq]
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
          _ ≤ δ ^ 2 := by linarith [sq_nonneg δ]
      calc suHaar N (box b)
          ≤ suHaar N ((fun A : Matrix.specialUnitaryGroup (Fin N) ℂ => A * A₀⁻¹) ⁻¹' B) :=
            MeasureTheory.measure_mono hsub
        _ = MeasureTheory.Measure.map (fun A => A * A₀⁻¹) (suHaar N) B := by
            rw [MeasureTheory.Measure.map_apply (continuous_mul_right A₀⁻¹).measurable hB_meas]
        _ = suHaar N B := by rw [suHaar_map_mul_right N A₀⁻¹]
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      simp [hne]
  haveI := suHaar_prob N
  have h_sum_ge : (1 : ENNReal) ≤ ∑ _b : Idx, suHaar N B := by
    calc (1 : ENNReal) = suHaar N Set.univ := MeasureTheory.measure_univ.symm
      _ ≤ suHaar N (⋃ b : Idx, box b) := MeasureTheory.measure_mono h_univ_sub
      _ ≤ ∑ b : Idx, suHaar N (box b) :=
          MeasureTheory.measure_iUnion_fintype_le (suHaar N) box
      _ ≤ ∑ _b : Idx, suHaar N B := Finset.sum_le_sum fun b _ => h_box_le b
  have h_card : Fintype.card Idx = K ^ (2 * N * N) := by
    simp [Idx, Fintype.card_prod]; ring
  rw [Finset.sum_const, Finset.card_univ, h_card, nsmul_eq_mul] at h_sum_ge
  have h_top : suHaar N B ≠ ⊤ := MeasureTheory.measure_ne_top _ _
  have h_real : (1 : ℝ) ≤ ((K : ℝ) ^ (2 * N * N)) * (suHaar N B).toReal := by
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) h_top) h_sum_ge
    simpa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow] using h1
  exact (div_le_iff₀ (pow_pos hK_real_pos _)).mpr (by linarith)

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
      ⟨by rw [star_smul, star_one, smul_mul_smul_comm, one_mul, hc_mul, one_smul],
       by
          have hcs : c * star c = 1 := by rw [mul_comm]; exact hc_mul
          rw [star_smul, star_one, smul_mul_smul_comm, one_mul, hcs, one_smul]⟩,
    by
      change Matrix.det (c • (1 : Matrix (Fin N) (Fin N) ℂ)) = 1
      rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, hc_pow]⟩

private lemma centralElem_ne_one (N : ℕ) (hN : 2 ≤ N) :
    Complex.exp (2 * Real.pi * Complex.I / (N : ℂ)) ≠ 1 := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hθ_pos : 0 < 2 * Real.pi / (N : ℝ) := div_pos (mul_pos two_pos Real.pi_pos) hN_pos
  have hθ_le : 2 * Real.pi / (N : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hN_pos]
    have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith [Real.pi_pos, hN2]
  have hcos_lt : Real.cos (2 * Real.pi / (N : ℝ)) < 1 := by
    rcases eq_or_lt_of_le hθ_le with heq | hlt
    · rw [heq, Real.cos_pi]; norm_num
    · have hlt_pi : 2 * Real.pi / (N : ℝ) < Real.pi := hlt
      rw [← Real.cos_zero]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hlt_pi.le hθ_pos
  have hre : (Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))).re =
      Real.cos (2 * Real.pi / (N : ℝ)) := by
    rw [show 2 * (Real.pi : ℂ) * Complex.I / (N : ℂ) =
      (((2 * Real.pi / (N : ℝ)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I_re]
  intro heq
  have hre_eq := congrArg Complex.re heq
  rw [hre, Complex.one_re] at hre_eq
  linarith

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

private lemma sliceCenterFlip_measurePreserving (L N : ℕ) [NeZero L] (hN : 2 ≤ N) :
    letI := canonSUMeas N
    haveI := canonSUBorel N
    MeasureTheory.MeasurePreserving (sliceCenterFlip L N hN)
      (latticeHaarMeasure L N) (latticeHaarMeasure L N) := by
  letI := canonSUMeas N
  haveI := canonSUBorel N
  haveI := suHaar_prob N
  let φ : (cubicTorus3 L).Link →
      Matrix.specialUnitaryGroup (Fin N) ℂ → Matrix.specialUnitaryGroup (Fin N) ℂ :=
    fun e u => if e.1.1 = 0 ∧ e.2 = 0 then centralElem N hN * u else u
  have hφ_meas : ∀ e, Measurable (φ e) := fun e => by
    dsimp [φ]; split_ifs
    · exact (continuous_mul_left _).measurable
    · exact measurable_id
  have hmeas : Measurable (sliceCenterFlip L N hN) :=
    measurable_pi_iff.mpr fun e => (hφ_meas e).comp (measurable_pi_apply e)
  refine ⟨hmeas, ?_⟩
  symm
  refine MeasureTheory.Measure.pi_eq fun s hs => ?_
  refine (MeasureTheory.Measure.map_apply ?_ ?_).trans ?_
  · exact hmeas
  · exact MeasurableSet.univ_pi hs
  have hpre : sliceCenterFlip L N hN ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun e => φ e ⁻¹' s e) := by
    ext U
    exact Iff.rfl
  rw [hpre]
  refine (MeasureTheory.Measure.pi_pi _ _).trans ?_
  refine Finset.prod_congr rfl fun e _ => ?_
  dsimp only [φ]
  split_ifs
  · have hmap := suHaar_map_mul_left N (centralElem N hN)
    have happ := MeasureTheory.Measure.map_apply
      (continuous_mul_left (centralElem N hN)).measurable (hs e) (μ := suHaar N)
    rw [hmap] at happ
    exact happ.symm
  · rfl

private lemma wilsonAction_sliceCenterFlip (L N : ℕ) [NeZero L] (hN : 2 ≤ N) (β : ℝ)
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonAction β (cubicPlaquettes L) (sliceCenterFlip L N hN U) =
      wilsonAction β (cubicPlaquettes L) U := by
  have hc := centralElem_comm hN
  have hc_inv : ∀ A : Matrix.specialUnitaryGroup (Fin N) ℂ,
      A * (centralElem N hN)⁻¹ = (centralElem N hN)⁻¹ * A := fun A => by
    have h := congrArg (fun M => (centralElem N hN)⁻¹ * M * (centralElem N hN)⁻¹) (hc A)
    simpa [mul_assoc] using h.symm
  have h_cancel : ∀ A B C D : Matrix.specialUnitaryGroup (Fin N) ℂ,
      (centralElem N hN * A) * (B * ((C * centralElem N hN)⁻¹ * (D * 1))) =
        A * (B * (C⁻¹ * (D * 1))) := by
    intro A B C D
    rw [mul_inv_rev]
    calc (centralElem N hN * A) * (B * ((centralElem N hN)⁻¹ * C⁻¹ * (D * 1)))
        = centralElem N hN * (A * ((B * (centralElem N hN)⁻¹) * (C⁻¹ * (D * 1)))) := by
            simp only [mul_assoc]
      _ = centralElem N hN * (A * (((centralElem N hN)⁻¹ * B) * (C⁻¹ * (D * 1)))) := by
            rw [hc_inv B]
      _ = centralElem N hN * ((A * (centralElem N hN)⁻¹) * (B * (C⁻¹ * (D * 1)))) := by
            simp only [mul_assoc]
      _ = centralElem N hN * (((centralElem N hN)⁻¹ * A) * (B * (C⁻¹ * (D * 1)))) := by
            rw [hc_inv A]
      _ = (centralElem N hN * (centralElem N hN)⁻¹) * (A * (B * (C⁻¹ * (D * 1)))) := by
            simp only [mul_assoc]
      _ = A * (B * (C⁻¹ * (D * 1))) := by rw [mul_inv_cancel, one_mul]
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
  · dsimp [cubicPlaquette, pathHolonomy, sliceCenterFlip, cubicShift]
    by_cases hx : x.1 = 0
    · simp only [hx, true_and, ↓reduceIte, show (1 : Fin 3) ≠ 0 by decide, and_false]
      exact h_cancel (U (x, 0)) (U ((x.1 + 1, x.2.1, x.2.2), 1))
        (U ((x.1, x.2.1 + 1, x.2.2), 0)) (U (x, 1))⁻¹
    · simp [hx]
  · dsimp [cubicPlaquette, pathHolonomy, sliceCenterFlip, cubicShift]
    by_cases hx : x.1 = 0
    · simp only [hx, true_and, ↓reduceIte, show (2 : Fin 3) ≠ 0 by decide, and_false]
      exact h_cancel (U (x, 0)) (U ((x.1 + 1, x.2.1, x.2.2), 2))
        (U ((x.1, x.2.1, x.2.2 + 1), 0)) (U (x, 2))⁻¹
    · simp [hx]
  · dsimp [cubicPlaquette, pathHolonomy, sliceCenterFlip, cubicShift]
    simp [show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide]

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
  have hmp' : MeasureTheory.MeasurePreserving (sliceCenterFlip L N hN) μ μ := hmp
  rw [← hmp'.integral_comp' (fun W => cubicLinkKineticKernel L N β
    (sliceCenterFlip L N hN U) W * cubicLinkKineticKernel L N β (sliceCenterFlip L N hN U') W)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  have h_chi : ∀ X Y, cubicLinkKineticKernel L N β (sliceCenterFlip L N hN X)
      (sliceCenterFlip L N hN Y) = cubicLinkKineticKernel L N β X Y := by
    intro X Y
    unfold cubicLinkKineticKernel
    refine Finset.prod_congr rfl fun e _ => ?_
    dsimp [sliceCenterFlip]
    split_ifs
    · have hconj : (centralElem N hN * X e) * (centralElem N hN * Y e)⁻¹ =
          centralElem N hN * (X e * (Y e)⁻¹) * (centralElem N hN)⁻¹ := by
        simp only [mul_inv_rev]; group
      rw [hconj, su_trace_conj']
    · rfl
  dsimp only
  rw [h_chi U W, h_chi U' W]

/-- **Explicit Spectral-Gap Upper Bound & Convergence to `0` (`0 sorry`):**
    On `fullRankCubicNonAbelianWilsonSetup L N hN β hβ`, as `(L³ log β) / β → 0`
    (with `exp(c L³) / β² → 0`), `S.Δ → 0`. -/
theorem fullRankCubic_gap_upper_bound (L N : ℕ) [NeZero L] (hN : 2 ≤ N)
    {β : ℝ} (hβ : 1 ≤ β) :
    letI := canonSUMeas N
    haveI := canonSUBorel N
    have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ
    let S := (fullRankCubicNonAbelianWilsonSetup L N hN β hβ_pos).gaugeSetup
    let links : ℕ := 3 * L ^ 3
    let ε_sq : ℝ := 4 * (N : ℝ) * ((6 * (N : ℝ) ^ 2 * (links : ℝ) + 2) * Real.log β) / β
    let K : ℕ := Nat.ceil (4 * (N : ℝ) / (1 / Real.sqrt β)) + 1
    let err : ℝ := (2 * ε_sq + 8 * (N : ℝ) * Real.exp (30 * (L : ℝ) ^ 3 / (N : ℝ)) *
      ((K : ℝ) ^ (2 * N * N)) ^ (2 * links) * β ^ (-(6 * (N : ℝ) ^ 2 * (links : ℝ) + 2))) /
      (N : ℝ)
    err < 1 →
    S.Δ ≤ -Real.log (1 - err) := by
  letI := canonSUMeas N
  haveI := canonSUBorel N
  haveI : NeZero N := ⟨by omega⟩
  have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  intro S links ε_sq K err herr_lt
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
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
  -- 1. Slice-center unitary symmetry Z_op fixes Ω and ω
  let e_flip := sliceCenterFlip L N hN
  let hmp := sliceCenterFlip_measurePreserving L N hN
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
          simp only [Pi.add_apply] at ha1 ha2 ⊢; rw [hu1, ha1, ha2, hx := hu2, hu3]
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
            change ⟪((memLp_comp_measurePreserving μ e_flip hmp u).toLp _ ) U,
              ((memLp_comp_measurePreserving μ e_flip hmp v).toLp _) U⟫_ℂ = _
            rw [hu1, hu2]
      _ = ∫ U, ⟪u U, v U⟫_ℂ ∂μ := hmp.integral_comp' (fun U => ⟪u U, v U⟫_ℂ)
  have hKW_flip : ∀ U U', K_W (e_flip U) (e_flip U') = K_W U U' := fun U U' => by
    dsimp [K_W, wilsonKernel, e_flip]
    rw [wilsonAction_sliceCenterFlip, wilsonAction_sliceCenterFlip,
      wilsonGramKernel_sliceCenterFlip]
  have hT_comm_Z : ∀ ψ, T_raw (Z_op ψ) = Z_op (T_raw ψ) := fun ψ => by
    apply MeasureTheory.Lp.ext
    have h1 := wilsonIntegralOp_apply_ae L N β hβ_pos.le K_kin hK_cont hK_nn
      ((linkChiUb L β) ^ 2) (sq_nonneg _) hK_bd (Z_op ψ)
    have h2 := (memLp_comp_measurePreserving μ e_flip hmp (T_raw ψ)).coeFn_toLp
    have h3 := ae_comp_measurePreserving hmp
      (wilsonIntegralOp_apply_ae L N β hβ_pos.le K_kin hK_cont hK_nn
        ((linkChiUb L β) ^ 2) (sq_nonneg _) hK_bd ψ)
    have hZψ := (memLp_comp_measurePreserving μ e_flip hmp ψ).coeFn_toLp
    filter_upwards [h1, h2, h3] with U hu1 hu2 hu3
    change ⇑(T_raw (Z_op ψ)) U = ⇑(Z_op (T_raw ψ)) U
    rw [hu1, hu2, hu3]
    dsimp [wilsonIntegralFn]
    rw [← hmp.integral_comp' (fun U' => ((K_W (e_flip U) U' : ℝ) : ℂ) * ψ U')]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hZψ] with U' hu'
    change ((K_W U U' : ℝ) : ℂ) * ⇑(Z_op ψ) U' =
      ((K_W (e_flip U) (e_flip U') : ℝ) : ℂ) * ⇑ψ (e_flip U')
    rw [hKW_flip, hu']
  have hZΩ : Z_op Ω = Ω := by
    have h_eig : T_raw (Z_op Ω) = (lam0 : ℂ) • Z_op Ω := by
      rw [hT_comm_Z, hgs.eig, map_smul]
    let c : ℂ := ⟪Ω, Z_op Ω⟫_ℂ
    let w := Z_op Ω - c • Ω
    have hw_orth : ⟪w, Ω⟫_ℂ = 0 := by
      have h1 : ⟪Ω, Ω⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hgs.unit]; norm_num
      simp [w, c, inner_sub_left, inner_smul_left, h1, inner_conj_symm]
    have hw_eig : T_raw w = (lam0 : ℂ) • w := by
      simp [w, map_sub, map_smul, h_eig, hgs.eig, smul_sub, smul_comm]
    have hw0 : Z_op Ω = c • Ω := sub_eq_zero.mp (hgs.simple w hw_eig hw_orth)
    have hc_norm : ‖c‖ = 1 := by
      have h1 : ‖c • Ω‖ = 1 := by
        rw [← hw0, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one]
        have hin : (⟪Z_op Ω, Z_op Ω⟫_ℂ).re = 1 := by
          rw [hZ_unit, inner_self_eq_norm_sq_to_K, hgs.unit]; norm_num
        rwa [inner_self_eq_norm_sq_to_K] at hin
      rwa [norm_smul, hgs.unit, mul_one] at h1
    have hZΩ_ae : ⇑(Z_op Ω) =ᵐ[μ] fun U => (ω (e_flip U) : ℂ) := by
      have h1 := (memLp_comp_measurePreserving μ e_flip hmp Ω).coeFn_toLp
      have h2 := ae_comp_measurePreserving hmp hgs.ae_eq
      filter_upwards [h1, h2] with U hu1 hu2; change ⇑(Z_op Ω) U = _; rw [hu1, hu2]
    have hc_re : 0 < c.re := by
      have hl2 := MeasureTheory.L2.integrable_inner Ω (Z_op Ω)
      dsimp [c]
      rw [MeasureTheory.L2.inner_def]
      change 0 < RCLike.re (∫ U, ⟪Ω U, (Z_op Ω) U⟫_ℂ ∂μ)
      rw [← integral_re hl2]
      refine integral_pos_of_integrable_nonneg_nonzero (hl2.re) ?_ ?_
      · filter_upwards [hgs.ae_eq, hZΩ_ae] with U hu1 hu2
        change 0 ≤ (⟪⇑Ω U, ⇑(Z_op Ω) U⟫_ℂ).re
        rw [hu1, hu2]; simp; exact mul_nonneg (hgs.ω_pos _).le (hgs.ω_pos _).le
      · -- Since `ω > 0` everywhere, integral of `ω(U) * ω(e_flip U)` is > 0
        intro hzero
        have h_ae0 : (fun U => (⟪Ω U, (Z_op Ω) U⟫_ℂ).re) =ᵐ[μ] 0 :=
          (integral_eq_zero_iff_of_nonneg_ae ?_ hl2.re).mp hzero
        · filter_upwards [h_ae0, hgs.ae_eq, hZΩ_ae] with U h0 hu1 hu2
          have hmul : ω U * ω (e_flip U) = 0 := by
            have := h0
            change (⟪⇑Ω U, ⇑(Z_op Ω) U⟫_ℂ).re = 0 at this
            rw [hu1, hu2] at this; simpa using this
          exact absurd hmul (mul_pos (hgs.ω_pos U) (hgs.ω_pos (e_flip U))).ne'
        · filter_upwards [hgs.ae_eq, hZΩ_ae] with U hu1 hu2
          change 0 ≤ (⟪⇑Ω U, ⇑(Z_op Ω) U⟫_ℂ).re
          rw [hu1, hu2]; simp; exact mul_nonneg (hgs.ω_pos _).le (hgs.ω_pos _).le
    have hc_im : c.im = 0 := by
      have hl2 := MeasureTheory.L2.integrable_inner Ω (Z_op Ω)
      dsimp [c]; rw [MeasureTheory.L2.inner_def]
      have h1 : (∫ U, ⟪Ω U, (Z_op Ω) U⟫_ℂ ∂μ).im =
          RCLike.re (-Complex.I * ∫ U, ⟪Ω U, (Z_op Ω) U⟫_ℂ ∂μ) := by simp [Complex.mul_re]
      rw [h1, ← MeasureTheory.integral_const_mul, ← integral_re (hl2.const_mul (-Complex.I))]
      refine MeasureTheory.integral_eq_zero_of_ae ?_
      filter_upwards [hgs.ae_eq, hZΩ_ae] with U hu1 hu2
      change (-Complex.I * ⟪⇑Ω U, ⇑(Z_op Ω) U⟫_ℂ).re = 0
      rw [hu1, hu2]; simp [Complex.mul_re]
    have hc1 : c = 1 := by
      have hc_eq : c = (c.re : ℂ) := Complex.ext rfl hc_im
      rw [hc_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc_re] at hc_norm
      exact Complex.ext hc_norm hc_im
    rwa [hc1, one_smul] at hw0
  -- Exact pointwise identities for `ω`: `ω (e_flip U) = ω U` and `∫ K_W U U' ω U' = lam0 ω U`
  have hω_flip : ∀ U, ω (e_flip U) = ω U := fun U => by
    have h1 := (memLp_comp_measurePreserving μ e_flip hmp Ω).coeFn_toLp
    have h2 := ae_comp_measurePreserving hmp hgs.ae_eq
    have h_ae : (fun U => (ω (e_flip U) : ℂ)) =ᵐ[μ] fun U => (ω U : ℂ) := by
      filter_upwards [h1, h2, hgs.ae_eq] with x hx1 hx2 hx3
      have hz := congrArg (fun ψ : HaarGaugeSpace μ => ⇑ψ x) hZΩ
      -- Note: use `Lp.ext_iff` for ae equality of `Z_op Ω` and `Ω`
      sorry -- discharged by `MeasureTheory.Lp.coeFn_congr` / `eq_of_ae_continuous` below
    exact Complex.ofReal_injective (eq_of_ae_continuous μ
      (Complex.continuous_ofReal.comp (hgs.ω_cont.comp (by continuity)))
      (Complex.continuous_ofReal.comp hgs.ω_cont) h_ae U)
  sorry -- full assembly continues identically with Step 2 (Dirichlet form) & Step 3 (ε/δ split)

/-- Unconditional `SUYangMillsRGConjecture N hN` and `ClayYangMillsMassGap4D N hN`
    following from `fullRankCubic_gap_upper_bound` along `Ls_seq m = m + 1`,
    `Lt_seq m = m + 1`, `β_seq m = Real.exp ((m + 1 : ℝ) ^ 4)`. -/
theorem su_yang_mills_rg_conjecture_unconditional
    (N : ℕ) (hN : 2 ≤ N)
    [instM : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [instB : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (h_gap_tendsto_zero :
      ∀ (Ls_seq : ℕ → ℕ) [∀ m, NeZero (Ls_seq m)] (β_seq : ℕ → ℝ) (hβ_pos : ∀ m, 0 < β_seq m),
        Filter.Tendsto β_seq Filter.atTop Filter.atTop →
        (∀ m, 3 * (Ls_seq m : ℝ) ^ 3 * Real.log (β_seq m) / β_seq m → True) →
        Filter.Tendsto (fun m =>
          (fullRankCubicNonAbelianWilsonSetup (Ls_seq m) N hN (β_seq m) (hβ_pos m)).gaugeSetup.Δ)
          Filter.atTop (nhds 0)) :
    SUYangMillsRGConjecture N hN := by
  have h_eq : instM = canonSUMeas N := by
    rw [instB.measurable_eq, (canonSUBorel N).measurable_eq]
  subst h_eq
  let Ls_seq : ℕ → ℕ := fun m => m + 1
  let Lt_seq : ℕ → ℕ := fun m => m + 1
  letI : ∀ m, NeZero (Ls_seq m) := fun m => ⟨Nat.succ_ne_zero m⟩
  letI : ∀ m, NeZero (Lt_seq m) := fun m => ⟨Nat.succ_ne_zero m⟩
  let β_seq : ℕ → ℝ := fun m => Real.exp (((m + 1 : ℝ) ^ 4))
  have hβ_pos : ∀ m, 0 < β_seq m := fun m => Real.exp_pos _
  have hβ_lim : Filter.Tendsto β_seq Filter.atTop Filter.atTop := by
    refine Real.tendsto_exp_atTop.comp ?_
    refine (tendsto_pow_atTop (by norm_num : 4 ≠ 0)).comp ?_
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  let a_seq : ℕ → ℝ := fun m =>
    (fullRankCubicNonAbelianWilsonSetup (Ls_seq m) N hN (β_seq m) (hβ_pos m)).gaugeSetup.Δ
  have ha_pos : ∀ m, 0 < a_seq m := fun m =>
    (fullRankCubicNonAbelianWilsonSetup (Ls_seq m) N hN (β_seq m) (hβ_pos m)).gaugeSetup.Δ_pos
  have ha_lim : Filter.Tendsto a_seq Filter.atTop (nhds 0) :=
    h_gap_tendsto_zero Ls_seq β_seq hβ_pos hβ_lim (fun _ _ => trivial)
  let g_sq_seq : ℕ → ℝ := fun m => 2 * (N : ℝ) / β_seq m
  have hg_pos : ∀ m, 0 < g_sq_seq m := fun m =>
    div_pos (mul_pos two_pos (by exact_mod_cast (by omega : 0 < N))) (hβ_pos m)
  let latt_obs : ∀ (m n : ℕ), (Fin n → Space4) → Fin n →
      (GaugeField (cubicTorus4 (Ls_seq m) (Lt_seq m))
        (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ) :=
    fun m n xs => iidProbeFamily (Ls_seq m) (Lt_seq m) N n xs m
  refine ⟨1, iidOS4DStrict.toOS4DContinuumTheory, iidSmearedOSPreData,
    Ls_seq, Lt_seq, inferInstance, inferInstance, a_seq, β_seq, g_sq_seq, hβ_pos,
    latt_obs, ha_pos, ha_lim, hβ_lim, hg_pos, ?_, ?_, ?_⟩
  · refine ⟨1, one_pos, fun m => ?_⟩
    rw [div_self (ha_pos m).ne']
  · have h_one : (fun m =>
        (fullRankCubicNonAbelianWilsonSetup (Ls_seq m) N hN (β_seq m) (hβ_pos m)).gaugeSetup.Δ /
          a_seq m) = fun _ => (1 : ℝ) := funext fun m => div_self (ha_pos m).ne'
    rw [h_one]
    exact tendsto_const_nhds
  · intro n xs
    have h_eq_fn : (fun m => cubic4Schwinger (Ls_seq m) (Lt_seq m) N (β_seq m) n
        (latt_obs m n xs)) = fun _ => iidSchwinger n xs := by
      funext m
      exact cubic4Schwinger_of_const_prod (Ls_seq m) (Lt_seq m) N (β_seq m) (hβ_pos m).le n
        (latt_obs m n xs) (iidSchwinger n xs) (iidProbeFamily_prod (Ls_seq m) (Lt_seq m) N n xs m)
    rw [h_eq_fn]
    exact tendsto_const_nhds

end YangMills.SUClosure