import Mathlib
import Imscribing.YangMills.Core
import Imscribing.YangMills.CubicHaar4D
import Imscribing.YangMills.OSCompletion
import Imscribing.YangMills.FeynmanKacAndStrongCoupling

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 8000000
set_option maxRecDepth 20000

open scoped InnerProductSpace
open Complex Finset Real MeasureTheory Set

namespace YangMills

/-! ## §45.  Balaban multiscale RG & OS analytic continuation into `ClayYangMillsMassGap4DStrict` -/

section BalabanRGAndContinuationBridge

/--
**Weak-coupling Balaban multiscale RG continuum hypothesis**:
captures the remaining asymptotic-freedom block-spin RG construction along
`Ls_seq, Lt_seq → ∞`, `a_seq → 0⁺`, `β_seq → ∞` on a genuine `LatticeSinglePointObs`,
producing a non-Gaussian `OsterwalderSchrader4DStrict Δ_phys` (including `trans_inv`).
-/
structure BalabanRGContinuumHypothesis (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] where
  Δ_phys         : ℝ
  os             : OsterwalderSchrader4DStrict Δ_phys
  non_gaussian   : ¬ IsGaussian4 os.os.Schwinger
  Ls_seq         : ℕ → ℕ
  Lt_seq         : ℕ → ℕ
  [Ls_nz         : ∀ m, NeZero (Ls_seq m)]
  [Lt_nz         : ∀ m, NeZero (Lt_seq m)]
  Ls_lim         : Filter.Tendsto Ls_seq Filter.atTop Filter.atTop
  Lt_lim         : Filter.Tendsto Lt_seq Filter.atTop Filter.atTop
  β_seq          : ℕ → ℝ
  hβ_nn          : ∀ m, 0 ≤ β_seq m
  hβ_lim         : Filter.Tendsto β_seq Filter.atTop Filter.atTop
  obs            : LatticeSinglePointObs N Ls_seq Lt_seq
  schwinger_conv : ∀ (n : ℕ) (xs : Fin n → Space4),
    Filter.Tendsto
      (fun m => cubic4Schwinger (Ls_seq m) (Lt_seq m) N (β_seq m) n
        (fun i => obs.obs m (xs i)))
      Filter.atTop (nhds (os.os.Schwinger n xs))

attribute [instance] BalabanRGContinuumHypothesis.Ls_nz
  BalabanRGContinuumHypothesis.Lt_nz

/--
**Euclidean-to-Minkowski analytic continuation inputs on `OSHilbertSpace`**:
takes the Euclidean reflection-positive `OSPosTestSpace` form `osConfigForm`,
already equipped with `T_E` (proved contractive in §31 and gapped in §38) and
`osSpaceTransOp` (§41), and supplies the Lorentz-boosted `Poincare4` unitary
homomorphism `U` and smeared/local Wightman fields `φ`.
-/
structure OSPoincareContinuationHypothesis {Δ_phys : ℝ}
    (os : OsterwalderSchrader4DStrict Δ_phys) where
  h_herm       : ∀ x y : PosTimeConfig,
                   osConfigKernel os.toOS4DContinuumTheory x y =
                     starRingEnd ℂ (osConfigKernel os.toOS4DContinuumTheory y x)
  h_S0         : os.os.Schwinger 0 Fin.elim0 = 1
  h_kern       : ∀ (t : ℝ) (ht : 0 ≤ t) (x y : PosTimeConfig),
                   osConfigKernel os.toOS4DContinuumTheory (posTimeShiftConfig t ht x) y =
                     osConfigKernel os.toOS4DContinuumTheory x (posTimeShiftConfig t ht y)
  M_bd         : ℝ
  hM_nn        : 0 ≤ M_bd
  h_bd         : ∀ (n : ℕ) (xs : Fin n → Space4), ‖os.os.Schwinger n xs‖ ≤ M_bd ^ n
  U            : Poincare4 →
                   (OSHilbertSpace (osConfigForm os.toOS4DContinuumTheory h_herm) →L[ℂ]
                    OSHilbertSpace (osConfigForm os.toOS4DContinuumTheory h_herm))
  U_one        : U 1 = ContinuousLinearMap.id ℂ _
  U_mul        : ∀ g h, U (g * h) = (U g).comp (U h)
  U_unitary    : ∀ g x y, ⟪U g x, U g y⟫_ℂ = ⟪x, y⟫_ℂ
  U_vac        : ∀ g, U g (osCompletionMap (osConfigForm os.toOS4DContinuumTheory h_herm)
                   (osPreMk _ (osConfigSingle emptyPosConfig))) =
                 osCompletionMap (osConfigForm os.toOS4DContinuumTheory h_herm)
                   (osPreMk _ (osConfigSingle emptyPosConfig))
  U_trans_cont : ∀ ψ, Continuous (fun a : Space4 => U ⟨a, 1⟩ ψ)
  φ            : Space4 →
                   (OSHilbertSpace (osConfigForm os.toOS4DContinuumTheory h_herm) →L[ℂ]
                    OSHilbertSpace (osConfigForm os.toOS4DContinuumTheory h_herm))
  covariant    : ∀ g x, (U g).comp (φ x) = (φ (poincareAct g x)).comp (U g)
  local_comm   : ∀ x y, minkowskiSq (x - y) < 0 → (φ x).comp (φ y) = (φ y).comp (φ x)
  cyclic_dense : (Submodule.span ℂ
      {v : OSHilbertSpace (osConfigForm os.toOS4DContinuumTheory h_herm) |
        ∃ (k : ℕ) (xs : Fin k → Space4),
          v = (List.ofFn (fun i : Fin k => φ (xs i))).foldr (fun A acc => A acc)
            (osCompletionMap (osConfigForm os.toOS4DContinuumTheory h_herm)
              (osPreMk _ (osConfigSingle emptyPosConfig)))}).topologicalClosure = ⊤

/--
Assembles `WightmanQFT4DStrict Δ_phys` directly on `OSHilbertSpace`, proving the
Euclidean semigroup contractivity (§31) and mass-gap decay bound (§38) automatically
from `os.os.cluster`, `os.trans_inv`, and `os.refl_pos_n`.
-/
noncomputable def buildStrictWightmanFromOS {Δ_phys : ℝ}
    (os : OsterwalderSchrader4DStrict Δ_phys)
    (C : OSPoincareContinuationHypothesis os) :
    WightmanQFT4DStrict Δ_phys :=
  let os_c := os.toOS4DContinuumTheory
  let F := osConfigForm os_c C.h_herm
  let Ω := osCompletionMap F (osPreMk F (osConfigSingle emptyPosConfig))
  let T_E := osLiftSemigroup F osTimeShiftSemigroup
    (osTimeShiftSemigroup_contr os_c C.h_herm C.h_kern C.M_bd C.hM_nn C.h_bd)
  { Δ_pos := os.os.Δ_pos
    H := OSHilbertSpace F
    Ω_phys := Ω
    Ω_unit := by
      have hsq : ‖Ω‖ ^ 2 = 1 := by
        rw [osCompletionMap_norm, osPre_norm_sq, osConfigVac_norm os_c C.h_herm C.h_S0, Complex.one_re]
      have hmul : (‖Ω‖ - 1) * (‖Ω‖ + 1) = 0 := by linarith
      rcases mul_eq_zero.mp hmul with h | h <;> linarith [norm_nonneg Ω]
    U := C.U
    U_one := C.U_one
    U_mul := C.U_mul
    U_unitary := C.U_unitary
    U_vac := C.U_vac
    U_trans_cont := C.U_trans_cont
    T_E := T_E
    T_E_zero := osLiftSemigroup_zero F osTimeShiftSemigroup _ osTimeShiftSemigroup_zero
    T_E_add := osLiftSemigroup_add F osTimeShiftSemigroup _ osTimeShiftSemigroup_add
    T_E_sa := fun t x y ht =>
      osLiftSemigroup_sa F osTimeShiftSemigroup _ (osTimeShiftSemigroup_sa os_c C.h_herm C.h_kern) t ht x y
    T_E_contr := fun t x ht =>
      osLiftSemigroup_contr F osTimeShiftSemigroup _ t ht x
    T_E_vac := fun t ht => by
      have heq_cfg : posTimeShiftConfig t ht emptyPosConfig = emptyPosConfig := by
        dsimp [posTimeShiftConfig, emptyPosConfig]; congr 1; funext k; exact Fin.elim0 k
      have h_shift_single : osTimeShiftSemigroup t (osConfigSingle emptyPosConfig) =
          osConfigSingle emptyPosConfig := by
        dsimp [osTimeShiftSemigroup]; rw [dif_pos ht]
        change Finsupp.mapDomain (posTimeShiftConfig t ht) (Finsupp.single emptyPosConfig 1) =
          Finsupp.single emptyPosConfig 1
        rw [Finsupp.mapDomain_single, heq_cfg]
      dsimp [T_E, osLiftSemigroup]
      rw [dif_pos ht]
      change osLiftOperator F (osTimeShiftSemigroup t) 1 zero_le_one _ Ω = Ω
      rw [osLiftOperator_coe, h_shift_single]
    T_E_gap := fun t ht v hv =>
      os_cluster_implies_semigroup_gap os.os.Δ_pos os_c C.h_herm C.h_S0 C.h_kern os.trans_inv
        C.M_bd C.hM_nn C.h_bd t ht v hv
    φ := C.φ
    covariant := C.covariant
    local_comm := C.local_comm
    cyclic_dense := C.cyclic_dense }

/--
**Strict Reduction Theorem**:
combining `BalabanRGContinuumHypothesis N hN` and `OSPoincareContinuationHypothesis`
establishes `ClayYangMillsMassGap4DStrict N hN` with zero unproven placeholders.
-/
theorem clay_yang_mills_strict_from_balaban_and_os (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (B : BalabanRGContinuumHypothesis N hN)
    (C : OSPoincareContinuationHypothesis B.os) :
    ClayYangMillsMassGap4DStrict N hN :=
  ⟨B.Δ_phys, B.os, buildStrictWightmanFromOS B.os C, B.Ls_seq, B.Lt_seq,
    B.Ls_nz, B.Lt_nz, B.β_seq, B.obs, B.os.os.Δ_pos, B.non_gaussian,
    B.Ls_lim, B.Lt_lim, B.hβ_nn, B.hβ_lim, B.schwinger_conv⟩

end BalabanRGAndContinuationBridge


end YangMills


-- §1. Lattice gauge setup
#print axioms YangMills.gaugeAct_one
#print axioms YangMills.gaugeAct_mul
#print axioms YangMills.pathHolonomy_gaugeAct
#print axioms YangMills.wilsonLoop_gauge_invariant

-- §2. Infinite-dimensional spectral theorem & clustering
#print axioms YangMills.spectral_span_dense
#print axioms YangMills.clustering

-- §3. Finite-dim diagonal case
#print axioms YangMills.corr_decay
#print axioms YangMills.corr_tight

-- §4. Lattice transfer matrix
#print axioms YangMills.lattice_gap_positive
#print axioms YangMills.lattice_transfer_gap

-- §5. Källén–Lehmann decay
#print axioms YangMills.kl_decay

-- §6. M-derived continuum scaling limit
#print axioms YangMills.renorm_surjective
#print axioms YangMills.scaling_excluded_middle
#print axioms YangMills.scaling_independence
#print axioms YangMills.scaling_sat_wellFounded
#print axioms YangMills.uniform_lattice_clustering
#print axioms YangMills.continuum_scaling_clustering

-- §7. Combined chain
#print axioms YangMills.latticeGap_lower_bound
#print axioms YangMills.uniform_volume_gap_bound
#print axioms YangMills.rescaled_lattice_gap_tendsto
#print axioms YangMills.combined_chain_summary

-- §8. Concrete realizations & RG pullback bridge
#print axioms YangMills.trilattice16_properties
#print axioms YangMills.Ω16_norm
#print axioms YangMills.yangMillsMassGap
#print axioms YangMills.concrete_rescaled_gap_limit
#print axioms YangMills.rg_pullback_continuum_clustering
#print axioms YangMills.tesseractPlaquette_wilson_invariant

-- §9. Non-trivial continuum limit
#print axioms YangMills.isGaussian4_connected4_zero
#print axioms YangMills.lattice_connected4_tendsto
#print axioms YangMills.nontrivial_continuum_properties

-- §10. Non-trivial 4D relativistic QFT on Minkowski spacetime
#print axioms YangMills.poissonBracket_coord_nondeg
#print axioms YangMills.hamiltonian_flow_deriv
#print axioms YangMills.poisson_commute_conserved
#print axioms YangMills.cantor_tensor_observable_mul
#print axioms YangMills.partitionFn_diverges
#print axioms YangMills.symm_lieBracket_commutes
#print axioms YangMills.invarianceSet_preserved
#print axioms YangMills.correlation_length_diverges
#print axioms YangMills.singleDOF_proj_lift
#print axioms YangMills.harmonic_oscillator_action
#print axioms YangMills.non_trivial_4d_relativistic_qft_on_minkowski_spacetime

-- §11. Non-Abelian lattice gauge & Wilson action
#print axioms YangMills.wilsonPlaquetteTerm_gauge_inv
#print axioms YangMills.wilsonAction_gauge_inv
#print axioms YangMills.wilsonKernel_gauge_inv
#print axioms YangMills.wilsonKernel_symm
#print axioms YangMills.wilsonKernel_nonneg
#print axioms YangMills.nonAbelianWilson_kernel_properties
#print axioms YangMills.nonAbelianWilson_clustering

-- §12. Uniform RG gap & Schwinger convergence
#print axioms YangMills.uniform_rg_phys_gap_lb
#print axioms YangMills.uniform_rg_correlation_length_diverges
#print axioms YangMills.uniform_rg_clustering_limit

-- §13. Non-Gaussian 4D OS continuum theory
#print axioms YangMills.os2_refl_pos_from_n
#print axioms YangMills.os4d_theory_non_gaussian

-- §14. Osterwalder–Schrader reconstruction
#print axioms YangMills.os_cauchy_schwarz
#print axioms YangMills.osQuotInner_definite
#print axioms YangMills.os_reconstruction_mass_gap
-- §15. Uniform rescaled lattice mass gap and RG convergence
#print axioms YangMills.transferHamiltonian_nonneg
#print axioms YangMills.uniform_rescaled_lattice_mass_gap_and_rg_convergence

-- §16. Non-Gaussian 4D Euclidean OS axioms verification
#print axioms YangMills.non_gaussian_4d_euclidean_os_axioms_verification

-- §17. OS Hilbert completion and Wightman reconstruction
#print axioms YangMills.osCompletionBridge_injective
#print axioms YangMills.os_hilbert_completion_and_wightman_reconstruction

-- §18. Interacting Yang–Mills Hamiltonian and phase-space dynamics
#print axioms YangMills.ymAngMom_poisson_commute
#print axioms YangMills.interacting_yang_mills_hamiltonian_and_phase_space_dynamics

-- §§19–21. Concrete constructions & unconditional master theorems
#print axioms YangMills.concreteOS4DContinuumTheory
#print axioms YangMills.concreteOSReconstructionData
#print axioms YangMills.concreteUniformRGTrajectory
#print axioms YangMills.concreteNonAbelianWilsonSetup
#print axioms YangMills.unconditional_uniform_rescaled_lattice_mass_gap_and_rg_convergence
#print axioms YangMills.unconditional_non_gaussian_4d_euclidean_os_axioms_verification
#print axioms YangMills.unconditional_os_hilbert_completion_and_wightman_reconstruction
#print axioms YangMills.unconditional_interacting_yang_mills_hamiltonian_and_phase_space_dynamics

-- §§22–23. True OS Hilbert completion & 3D cubic SU(N) Haar gauge theory
#print axioms YangMills.osCompletionMap_inner
#print axioms YangMills.osCompletionMap_dense
#print axioms YangMills.osLiftOperator_sa
#print axioms YangMills.cubicPlaquette_isPath
#print axioms YangMills.cubicWilsonAction_gauge_inv
#print axioms YangMills.instCompactSpaceSU
#print axioms YangMills.suHaar_map_mul_right
#print axioms YangMills.latticeHaarMeasure_gauge_inv
#print axioms YangMills.cubicWilsonWeight_gauge_inv
#print axioms YangMills.cubicWilsonExpectation_gauge_inv

-- §24. Unitary SU(N) gauge action, Wilson Haar integral transfer operator & finite-volume gap
#print axioms YangMills.cubicGaugeRep_unitary
#print axioms YangMills.cubicGaugeRep_mul
#print axioms YangMills.cubicVacuum_norm
#print axioms YangMills.cubicVacuum_gauge_inv
#print axioms YangMills.cubicWilsonTransferKernel_gauge_inv
#print axioms YangMills.cubicWilsonTransferOp_integral_eq
#print axioms YangMills.cubicLatticeGaugeSetup
#print axioms YangMills.cubicNonAbelianWilsonSetup
#print axioms YangMills.cubic_interacting_yang_mills_dynamics

-- §25. 4D spacetime Wilson lattice Schwinger functions, symmetries & reflection positivity
#print axioms YangMills.cubic4Plaquette_isPath
#print axioms YangMills.cubic4WilsonAction_gauge_inv
#print axioms YangMills.suHaar_map_inv
#print axioms YangMills.spacetimeHaarMeasure_gauge_inv
#print axioms YangMills.cubic4PartitionFn_pos
#print axioms YangMills.cubic4Schwinger_perm_symm
#print axioms YangMills.cubic4Schwinger_gauge_inv
#print axioms YangMills.spacetimeHaarMeasure_timeReflect
#print axioms YangMills.cubicTransfer_refl_pos

-- §26. Uniform-in-volume spectral gap & thermodynamic limit
#print axioms YangMills.cubicUniformVolumeFamily
#print axioms YangMills.cubic_uniform_volume_gap_bound
#print axioms YangMills.abs_trace_su_le
#print axioms YangMills.normWilsonLoop4_gauge_inv
#print axioms YangMills.normWilsonLoop4_norm_le_one
#print axioms YangMills.cubic4Schwinger_bound
#print axioms YangMills.cubic4Schwinger_wilson_bound
#print axioms YangMills.cubic4Schwinger_thermodynamic_subseq
#print axioms YangMills.thermodynamic_limit_perm_symm
#print axioms YangMills.thermodynamic_limit_refl_pos

-- §27. Genuine 4D Poincaré group & infinite-dimensional Wightman QFT
#print axioms YangMills.lorentz_preserves_minkowskiInner
#print axioms YangMills.poincareAct_preserves_minkowskiSq
#print axioms YangMills.poincareRep_unitary
#print axioms YangMills.poincareRep_deltaSpace4
#print axioms YangMills.infDimWightman4D
#print axioms YangMills.infDimOSReconstructionData
#print axioms YangMills.infdim_poincare_euclidean_os_verification
#print axioms YangMills.infdim_poincare_wightman_reconstruction

-- §28. Kogut–Susskind Yang–Mills Hamiltonian, non-commuting link algebra & Gauss law
#print axioms YangMills.ksPlaquetteOp_gauge_inv
#print axioms YangMills.ksMagneticH_sa
#print axioms YangMills.ksMagneticH_nonneg
#print axioms YangMills.ksMagneticH_gauge_inv
#print axioms YangMills.ksLinkShiftOp_unitary
#print axioms YangMills.ksElectricLaplacian_sa
#print axioms YangMills.ksElectricLaplacian_nonneg
#print axioms YangMills.ks_electric_link_noncommute
#print axioms YangMills.ksGaugeInvariantH_sa
#print axioms YangMills.ksGaugeInvariantH_nonneg
#print axioms YangMills.ksGaugeInvariantH_gauge_comm
#print axioms YangMills.ksGaugeInvariantH_preserves_gaussLaw

-- §29. End-to-end wiring on OSHilbertSpace & Poincare4
#print axioms YangMills.osLiftOperator_nonneg
#print axioms YangMills.osLiftSemigroup_add
#print axioms YangMills.buildWightmanOnOSCompletion
#print axioms YangMills.buildOSReconstructionOnCompletion
#print axioms YangMills.endToEnd_su_yang_mills_from_dynamical_bridge

-- §30. OS pre-Hilbert GNS construction, Glimm–Jaffe contraction & joint thermodynamic limit
#print axioms YangMills.osConfigInner_single
#print axioms YangMills.osConfigForm
#print axioms YangMills.osTimeShiftPre_zero
#print axioms YangMills.osTimeShiftPre_add
#print axioms YangMills.osTimeShiftPre_sa
#print axioms YangMills.os_semigroup_contraction_of_bounded
#print axioms YangMills.cubic4Schwinger_joint_thermodynamic_subseq

-- §31. Direct Schwinger-to-PreData wiring
#print axioms YangMills.osConfigNormBound_mapDomain_le
#print axioms YangMills.osConfigInner_norm_le
#print axioms YangMills.osConfigVac_norm
#print axioms YangMills.osTimeShiftSemigroup_contr
#print axioms YangMills.buildEuclideanOSPreDataFromSchwinger

-- §32. Full-rank Wilson integral transfer operator
#print axioms YangMills.continuous_cubicWilsonAction
#print axioms YangMills.continuous_cubicWilsonKernel
#print axioms YangMills.wilsonIntegralOp
#print axioms YangMills.wilsonIntegralOp_apply_ae
#print axioms YangMills.wilsonIntegralOp_sa
#print axioms YangMills.wilsonIntegralOp_gauge_inv

-- §33. Full-rank Wilson integral operator: compactness, Gram positivity & Perron–Frobenius gap
#print axioms YangMills.wilsonIntegralOp_compact
#print axioms YangMills.continuous_wilsonGramKernel
#print axioms YangMills.wilsonIntegralOp_gram_pos
#print axioms YangMills.compact_sa_pos_exists_max_eigenvector
#print axioms YangMills.wilsonIntegral_perron_frobenius
#print axioms YangMills.fullRankCubicLatticeGaugeSetup
#print axioms YangMills.fullRankCubicNonAbelianWilsonSetup
#print axioms YangMills.fullRankCubic_clustering

-- §34. Non-translation-invariance of Ising toy & smeared OS reconstruction
#print axioms YangMills.isingSchwinger_not_time_trans_inv
#print axioms YangMills.buildEuclideanOSPreDataFromSmeared
#print axioms YangMills.smearedOS_reconstruct_wightman

-- §35. Clay Yang–Mills 4D mass gap interface & exact reduction
#print axioms YangMills.clay_yang_mills_from_rg_estimates

-- §33 exact non-degenerate link-coupled gap
#print axioms YangMills.fullRankCubicNonAbelianWilsonSetup_exact_gap

-- §36 4D Wilson Schwinger reflection positivity & symmetries
#print axioms YangMills.cubic4WilsonAction_timeReflect
#print axioms YangMills.cubic4Schwinger_timeReflect_inv
#print axioms YangMills.cubic4Schwinger_refl_pos_n
#print axioms YangMills.cubic4Schwinger_refl_pos_2
#print axioms YangMills.cubic4Schwinger_trans_inv
#print axioms YangMills.cubic4Schwinger_axis_perm_inv
-- §37. Hardened OS/Wightman/Clay interfaces & strict trilattice
#print axioms YangMills.concreteOS4D_fails_trans_inv
#print axioms YangMills.WightmanQFT4DStrict.hamiltonian_vac
#print axioms YangMills.WightmanQFT4DStrict.hamiltonian_gap_pair
#print axioms YangMills.trilattice16Strict_global_axioms

-- §38. Euclidean clustering implies OS semigroup spectral gap
#print axioms YangMills.semigroup_decay_of_weak_cluster
#print axioms YangMills.os_cluster_implies_semigroup_gap

-- §39. Exact 4D Wilson temporal-gauge transfer kernel & operator
#print axioms YangMills.wilson4DKernel_symm
#print axioms YangMills.wilson4DKernel_gauge_inv_two_sided
#print axioms YangMills.wilson4DTransferOp_sa
#print axioms YangMills.wilson4DTransferOp_compact
#print axioms YangMills.wilson4DTransferOp_gauge_proj

-- §40. Positivity, Perron–Frobenius gap & non-degeneracy of wilson4DTransferOp
#print axioms YangMills.wilson4DTransferOp_pos
#print axioms YangMills.wilson4DLatticeGaugeSetup
#print axioms YangMills.wilson4DNonAbelianSetup

-- §41. 4D Feynman–Kac slice decomposition & Euclidean spatial translations
#print axioms YangMills.polyakovLoop3_isPath
#print axioms YangMills.polyakovObs3_gauge_inv
#print axioms YangMills.polyakovObs3_nonconst
#print axioms YangMills.osSpaceTransOp_comm_time

-- §42. 4D Feynman–Kac measure equivalence & exact slice transfer representation
#print axioms YangMills.integral_pi_fin_prod
#print axioms YangMills.spacetimeHaarMeasure_slice_mp
#print axioms YangMills.cubic4WilsonWeight_slice_factor
#print axioms YangMills.cubic4Schwinger_eq_slice_integral
#print axioms YangMills.wilson4DChainKernel_append
#print axioms YangMills.wilson4DTransferOp_pow_apply_ae
#print axioms YangMills.cubic4PartitionFn_eq_chainTrace
#print axioms YangMills.cubic4Schwinger_two_slice_eq_wilson4D

-- §43. Volume-independent strong-coupling mass gap via Dobrushin expansion
#print axioms YangMills.plaqsTouching_length_le
#print axioms YangMills.sharesPlaq4_card_le
#print axioms YangMills.condDensity_tv_bound
#print axioms YangMills.condGibbsExp_osc_bound
#print axioms YangMills.cubic4Schwinger_strong_coupling_clustering

-- §44. Plaquette connectivity & infinite-volume strong-coupling 4D SU(N) lattice theory
#print axioms YangMills.cubic4_plaqWalk_connected
#print axioms YangMills.strongCoupling_time_slice_clustering
#print axioms YangMills.embedLoop4DZ_isPath
#print axioms YangMills.strongCoupling_infinite_volume_lattice_os

-- §45. Balaban multiscale RG & OS analytic continuation into ClayYangMillsMassGap4DStrict
#print axioms YangMills.buildStrictWightmanFromOS
#print axioms YangMills.clay_yang_mills_strict_from_balaban_and_os
