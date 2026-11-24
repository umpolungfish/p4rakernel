import Mathlib
import Imscribing.YangMills.ContinuumClosure
import Imscribing.YangMills.IIDContinuation

open scoped InnerProductSpace
open Complex Real MeasureTheory Set

namespace YangMills

lemma iid_osConfigKernel_factor (x y : PosTimeConfig) :
    osConfigKernel iidOS4DStrict.toOS4DContinuumTheory x y =
      iidSchwinger x.n_pts x.pts * iidSchwinger y.n_pts y.pts := by
  dsimp [osConfigKernel, iidOS4DStrict, iidOS4D]
  rw [iidSchwinger_append]
  · rw [iidSchwinger_timeReflect]
  · intro i j
    exact timeReflect_neg (x.pts i) (x.pos_t i) (y.pts j) (y.pos_t j)

noncomputable def iidOSForm :=
  osConfigForm iidOS4DStrict.toOS4DContinuumTheory iid_osConfigKernel_herm

noncomputable def iidOSVac :=
  osCompletionMap iidOSForm
    (osPreMk iidOSForm (osConfigSingle emptyPosConfig))

lemma iid_osConfigVector_eq (x : PosTimeConfig) :
    osCompletionMap iidOSForm
      (osPreMk iidOSForm (osConfigSingle x)) =
        iidSchwinger x.n_pts x.pts • iidOSVac := by
  let ψ := osCompletionMap iidOSForm
    (osPreMk iidOSForm (osConfigSingle x))
  let Ω := iidOSVac
  let s := iidSchwinger x.n_pts x.pts
  have hsreal : starRingEnd ℂ s = s := iidSchwinger_conj _ _
  have hxx : ⟪ψ, ψ⟫_ℂ = s * s := by
    have h := osConfigKernel_eq_completion_inner
      iidOS4DStrict.toOS4DContinuumTheory iid_osConfigKernel_herm x x
    simpa [ψ, iidOSForm, s] using h.trans (iid_osConfigKernel_factor x x)
  have hxΩ : ⟪ψ, Ω⟫_ℂ = s := by
    have h := osConfigKernel_eq_completion_inner
      iidOS4DStrict.toOS4DContinuumTheory iid_osConfigKernel_herm x emptyPosConfig
    have h' : ⟪ψ, Ω⟫_ℂ =
        s * iidSchwinger emptyPosConfig.n_pts emptyPosConfig.pts := by
      simpa [ψ, Ω, iidOSVac, iidOSForm, s] using
        h.trans (iid_osConfigKernel_factor x emptyPosConfig)
    change ⟪ψ, Ω⟫_ℂ = s * iidSchwinger 0 Fin.elim0 at h'
    rw [iidSchwinger_S0] at h'
    simpa using h'
  have hΩx : ⟪Ω, ψ⟫_ℂ = s := by
    rw [← inner_conj_symm, hxΩ, hsreal]
  have hΩΩ : ⟪Ω, Ω⟫_ℂ = 1 := by
    have h := osConfigKernel_eq_completion_inner
      iidOS4DStrict.toOS4DContinuumTheory iid_osConfigKernel_herm
      emptyPosConfig emptyPosConfig
    have h' : ⟪Ω, Ω⟫_ℂ =
        iidSchwinger emptyPosConfig.n_pts emptyPosConfig.pts *
          iidSchwinger emptyPosConfig.n_pts emptyPosConfig.pts := by
      simpa [Ω, iidOSVac, iidOSForm] using
        h.trans (iid_osConfigKernel_factor emptyPosConfig emptyPosConfig)
    change ⟪Ω, Ω⟫_ℂ = iidSchwinger 0 Fin.elim0 * iidSchwinger 0 Fin.elim0 at h'
    rw [iidSchwinger_S0] at h'
    simpa using h'
  have hnorm : ‖ψ - s • Ω‖ ^ 2 = 0 := by
    rw [norm_sub_sq (𝕜 := ℂ)]
    have hcross : (⟪ψ, s • Ω⟫_ℂ).re = (s * s).re := by
      rw [inner_smul_right, hxΩ]
    have hψnorm : ‖ψ‖ ^ 2 = (s * s).re := by
      calc
        ‖ψ‖ ^ 2 = (⟪ψ, ψ⟫_ℂ).re := by
          simpa using (norm_sq_eq_re_inner (𝕜 := ℂ) ψ)
        _ = (s * s).re := congrArg Complex.re hxx
    have hΩnorm : ‖Ω‖ = 1 := by
      have hsq : ‖Ω‖ ^ 2 = 1 := by
        calc
          ‖Ω‖ ^ 2 = (⟪Ω, Ω⟫_ℂ).re := by
            simpa using (norm_sq_eq_re_inner (𝕜 := ℂ) Ω)
          _ = 1 := by rw [hΩΩ]; norm_num
      nlinarith [norm_nonneg Ω]
    have hnormΩ : ‖s • Ω‖ ^ 2 = ‖s‖ ^ 2 := by
      rw [norm_smul, hΩnorm]
      simp
    have hs_abs : ‖s‖ ^ 2 = (s * s).re := by
      calc
        ‖s‖ ^ 2 = Complex.normSq s := (Complex.normSq_eq_norm_sq s).symm
        _ = (s * s).re := by
          have h := congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := s))
          rw [hsreal] at h
          simpa using h
    have hcross' : RCLike.re ⟪ψ, s • Ω⟫_ℂ = (s * s).re := by
      simpa using hcross
    rw [hψnorm, hcross', hnormΩ, hs_abs]
    ring
  have hzero : ψ - s • Ω = 0 := by
    have hnorm0 : ‖ψ - s • Ω‖ = 0 := by
      nlinarith [hnorm, norm_nonneg (ψ - s • Ω)]
    exact norm_eq_zero.mp hnorm0
  dsimp [ψ, Ω, s, iidOSVac, iidOSForm] at hzero ⊢
  exact sub_eq_zero.mp hzero

lemma iid_osCompletionMap_rank_one (f : OSPosTestSpace) :
    ∃ c : ℂ, osCompletionMap iidOSForm (osPreMk iidOSForm f) = c • iidOSVac := by
  classical
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · refine ⟨0, ?_⟩
    have hz : osPreMk iidOSForm (0 : OSPosTestSpace) = 0 := rfl
    rw [hz, map_zero]
    simp
  · rintro f g ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c + d, ?_⟩
    have hadd : osPreMk iidOSForm (f + g) =
        osPreMk iidOSForm f + osPreMk iidOSForm g := by
      apply Quotient.sound
      change (f + g) - (f + g) ∈ osNullSpace iidOSForm
      simp
    rw [hadd, map_add, hc, hd, add_smul]
  · intro x c
    refine ⟨c * iidSchwinger x.n_pts x.pts, ?_⟩
    have hsingle :
        osCompletionMap iidOSForm (osPreMk iidOSForm (Finsupp.single x c)) =
          c • osCompletionMap iidOSForm
            (osPreMk iidOSForm (osConfigSingle x)) := by
      have hq : osPreMk iidOSForm (Finsupp.single x c) =
          c • osPreMk iidOSForm (osConfigSingle x) := by
        apply Quotient.sound
        change Finsupp.single x c - c • Finsupp.single x 1 ∈ osNullSpace iidOSForm
        simp
      rw [hq, map_smul]
    rw [hsingle, iid_osConfigVector_eq]
    simp [smul_smul, mul_assoc]

noncomputable def iidOSPoincareContinuation :
    OSPoincareContinuationHypothesis iidOS4DStrict where
  h_herm := iid_osConfigKernel_herm
  h_S0 := iidSchwinger_S0
  h_kern := iid_osConfigKernel_kern
  M_bd := 2
  hM_nn := by norm_num
  h_bd := iidSchwinger_growth
  U := fun _ => ContinuousLinearMap.id ℂ _
  U_one := rfl
  U_mul := by intro g h; simp
  U_unitary := by intro g x y; simp
  U_vac := by intro g; rfl
  U_trans_cont := by intro ψ; exact continuous_const
  φ := fun _ => ContinuousLinearMap.id ℂ _
  covariant := by intro g x; simp
  local_comm := by intro x y h; simp
  cyclic_dense := by
    let Ω := osCompletionMap iidOSForm
      (osPreMk iidOSForm (osConfigSingle emptyPosConfig))
    let S : Set (OSHilbertSpace iidOSForm) := {v |
      ∃ (k : ℕ) (xs : Fin k → Space4),
      v = (List.ofFn (fun _ : Fin k =>
        (ContinuousLinearMap.id ℂ (OSHilbertSpace iidOSForm)))).foldr
          (fun A acc => A acc) Ω}
    let V := Submodule.span ℂ S
    have hΩ : Ω ∈ S := by
      refine ⟨0, Fin.elim0, ?_⟩
      simp [S]
    have hsingle : ∀ x : PosTimeConfig,
        osCompletionMap iidOSForm (osPreMk iidOSForm (osConfigSingle x)) ∈ V := by
      intro x
      have hx : osCompletionMap iidOSForm
          (osPreMk iidOSForm (osConfigSingle x)) =
          iidSchwinger x.n_pts x.pts • Ω := iid_osConfigVector_eq x
      rw [hx]
      exact V.smul_mem _ (Submodule.subset_span hΩ)
    have hrange : Set.range (osCompletionMap iidOSForm) ⊆ V.topologicalClosure := by
      rintro _ ⟨u, rfl⟩
      apply subset_closure
      refine Quotient.inductionOn u ?_
      intro f
      change osCompletionMap iidOSForm (osPreMk iidOSForm f) ∈ V
      rcases iid_osCompletionMap_rank_one f with ⟨c, hc⟩
      have hc' : osCompletionMap iidOSForm (osPreMk iidOSForm f) = c • Ω := by
        simpa [Ω, iidOSVac] using hc
      rw [hc']
      exact V.smul_mem _ (Submodule.subset_span hΩ)
    have htop : (Set.univ : Set (OSHilbertSpace iidOSForm)) ⊆ V.topologicalClosure := by
      have hdense := osCompletionMap_dense iidOSForm
      rw [← hdense]
      exact closure_minimal hrange isClosed_closure
    change V.topologicalClosure = ⊤
    apply top_unique
    intro v hv
    exact htop (Set.mem_univ v)

end YangMills
