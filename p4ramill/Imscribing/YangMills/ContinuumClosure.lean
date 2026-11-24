import Mathlib
import Imscribing.YangMills.Core
import Imscribing.YangMills.CubicHaar4D
import Imscribing.YangMills.OSCompletion
import Imscribing.YangMills.FeynmanKacAndStrongCoupling

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 8000000
set_option maxRecDepth 20000

open scoped InnerProductSpace Fin.IntCast
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
The Wightman object assembled from OS data uses the same completed configuration
vectors, whose inner products recover the reflected Schwinger kernel.
-/
theorem buildStrictWightmanFromOS_config_inner {Δ_phys : ℝ}
    (os : OsterwalderSchrader4DStrict Δ_phys)
    (C : OSPoincareContinuationHypothesis os)
    (x y : PosTimeConfig) :
    let W := buildStrictWightmanFromOS os C
    let F := osConfigForm os.toOS4DContinuumTheory C.h_herm
    letI : InnerProductSpace ℂ W.H := W.hInner
    ⟪(osCompletionMap F (osPreMk F (osConfigSingle x)) : W.H),
      (osCompletionMap F (osPreMk F (osConfigSingle y)) : W.H)⟫_ℂ =
        osConfigKernel os.toOS4DContinuumTheory x y := by
  let F := osConfigForm os.toOS4DContinuumTheory C.h_herm
  let W := buildStrictWightmanFromOS os C
  letI : InnerProductSpace ℂ W.H := W.hInner
  exact osConfigKernel_eq_completion_inner os.toOS4DContinuumTheory C.h_herm x y

/-- The assembled Wightman Hilbert space retains the OS time-shift kernel matrix coefficients. -/
theorem buildStrictWightmanFromOS_time_shift_kernel {Δ_phys : ℝ}
    (os : OsterwalderSchrader4DStrict Δ_phys)
    (C : OSPoincareContinuationHypothesis os)
    (t : ℝ) (ht : 0 ≤ t) (x y : PosTimeConfig) :
    let W := buildStrictWightmanFromOS os C
    let F := osConfigForm os.toOS4DContinuumTheory C.h_herm
    letI : InnerProductSpace ℂ W.H := W.hInner
    ⟪W.T_E t (osCompletionMap F (osPreMk F (osConfigSingle x))),
      osCompletionMap F (osPreMk F (osConfigSingle y))⟫_ℂ =
        osConfigKernel os.toOS4DContinuumTheory (posTimeShiftConfig t ht x) y := by
  let W := buildStrictWightmanFromOS os C
  let F := osConfigForm os.toOS4DContinuumTheory C.h_herm
  letI : InnerProductSpace ℂ W.H := W.hInner
  exact osTimeShiftConfig_eq_completion_inner os.toOS4DContinuumTheory C.h_herm
    C.h_kern C.M_bd C.hM_nn C.h_bd t ht x y

/-- Positive-time Schwinger values are vacuum coefficients of canonical states in the built space. -/
theorem buildStrictWightmanFromOS_schwinger_vacuum_coefficient {Δ_phys : ℝ}
    (os : OsterwalderSchrader4DStrict Δ_phys)
    (C : OSPoincareContinuationHypothesis os)
    (y : PosTimeConfig) :
    let W := buildStrictWightmanFromOS os C
    let F := osConfigForm os.toOS4DContinuumTheory C.h_herm
    letI : InnerProductSpace ℂ W.H := W.hInner
    ⟪W.Ω_phys,
      (osCompletionMap F (osPreMk F (osConfigSingle y)) : W.H)⟫_ℂ =
        os.os.Schwinger y.n_pts y.pts := by
  let W := buildStrictWightmanFromOS os C
  let F := osConfigForm os.toOS4DContinuumTheory C.h_herm
  letI : InnerProductSpace ℂ W.H := W.hInner
  change ⟪osCompletionMap F (osPreMk F (osConfigSingle emptyPosConfig)),
      osCompletionMap F (osPreMk F (osConfigSingle y))⟫_ℂ = _
  rw [osConfigKernel_eq_completion_inner]
  exact osConfigKernel_empty_left os.os.Δ_pos os.toOS4DContinuumTheory C.h_S0 y

/--
Positive-time Schwinger vacuum coefficients are limits of finite linear
combinations of vacuum coefficients of Wightman field words.
-/
theorem buildStrictWightmanFromOS_schwinger_field_word_approx {Δ_phys : ℝ}
    (os : OsterwalderSchrader4DStrict Δ_phys)
    (C : OSPoincareContinuationHypothesis os)
    (y : PosTimeConfig) :
    let W := buildStrictWightmanFromOS os C
    let F := osConfigForm os.toOS4DContinuumTheory C.h_herm
    letI : InnerProductSpace ℂ W.H := W.hInner
    ∀ ε > 0, ∃ v : W.H,
      v ∈ Submodule.span ℂ
        {w : W.H | ∃ (k : ℕ) (xs : Fin k → Space4),
          w = (List.ofFn (fun i : Fin k => W.φ (xs i))).foldr
            (fun A acc => A acc) W.Ω_phys} ∧
      ‖os.os.Schwinger y.n_pts y.pts - ⟪W.Ω_phys, v⟫_ℂ‖ < ε := by
  let W := buildStrictWightmanFromOS os C
  let F := osConfigForm os.toOS4DContinuumTheory C.h_herm
  letI : InnerProductSpace ℂ W.H := W.hInner
  let ψ : W.H := osCompletionMap F (osPreMk F (osConfigSingle y))
  let fieldWords : Set W.H := {w | ∃ (k : ℕ) (xs : Fin k → Space4),
    w = (List.ofFn (fun i : Fin k => W.φ (xs i))).foldr
      (fun A acc => A acc) W.Ω_phys}
  let fieldSpan : Submodule ℂ W.H := Submodule.span ℂ fieldWords
  have h_dense : fieldSpan.topologicalClosure = ⊤ := by
    simpa [fieldSpan, fieldWords] using W.cyclic_dense
  have h_mem : ψ ∈ (fieldSpan.topologicalClosure : Set W.H) := by
    rw [h_dense]
    exact Set.mem_univ ψ
  change ψ ∈ closure (fieldSpan : Set W.H) at h_mem
  intro W' F' ε hε
  have h_mem' : ψ ∈ closure (fieldSpan : Set W.H) := h_mem
  rw [Metric.mem_closure_iff] at h_mem'
  obtain ⟨v, hv_span, hv_dist⟩ := h_mem' (ε / 2) (by linarith)
  refine ⟨v, hv_span, ?_⟩
  have h_coeff : os.os.Schwinger y.n_pts y.pts = ⟪W.Ω_phys, ψ⟫_ℂ :=
    (buildStrictWightmanFromOS_schwinger_vacuum_coefficient os C y).symm
  calc
    ‖os.os.Schwinger y.n_pts y.pts - ⟪W.Ω_phys, v⟫_ℂ‖ =
        ‖⟪W.Ω_phys, ψ - v⟫_ℂ‖ := by rw [h_coeff, ← inner_sub_right]
    _ ≤ ‖W.Ω_phys‖ * ‖ψ - v‖ := norm_inner_le_norm _ _
    _ < ε := by
      rw [W.Ω_unit]
      have hnorm : ‖ψ - v‖ < ε / 2 := by simpa [dist_eq_norm] using hv_dist
      linarith

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

/-- The strengthened target records the actual OS continuation witness and
requires its Wightman theory to be the object built on the OS Hilbert completion. -/
def ClayYangMillsMassGap4DStrictOnOSCompletion (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] : Prop :=
  ∃ (Δ_phys : ℝ) (os : OsterwalderSchrader4DStrict Δ_phys)
    (C : OSPoincareContinuationHypothesis os)
    (Ls_seq Lt_seq : ℕ → ℕ) (hLs : ∀ m, NeZero (Ls_seq m))
    (hLt : ∀ m, NeZero (Lt_seq m)) (β_seq : ℕ → ℝ)
    (O : LatticeSinglePointObs N Ls_seq Lt_seq)
    (W : WightmanQFT4DStrict Δ_phys),
    0 < Δ_phys ∧
    ¬ IsGaussian4 os.os.Schwinger ∧
    Filter.Tendsto Ls_seq Filter.atTop Filter.atTop ∧
    Filter.Tendsto Lt_seq Filter.atTop Filter.atTop ∧
    (∀ m, 0 ≤ β_seq m) ∧
    Filter.Tendsto β_seq Filter.atTop Filter.atTop ∧
    (∀ (n : ℕ) (xs : Fin n → Space4),
      Filter.Tendsto
        (fun m => cubic4Schwinger (Ls_seq m) (Lt_seq m) N (β_seq m) n
          (fun i => O.obs m (xs i)))
        Filter.atTop (nhds (os.os.Schwinger n xs))) ∧
    W = buildStrictWightmanFromOS os C

/-- Balaban continuum data and its continuation witness inhabit the strengthened
target with the Wightman theory fixed to the OS completion construction. -/
theorem clay_yang_mills_strict_on_os_completion_from_balaban_and_os
    (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (B : BalabanRGContinuumHypothesis N hN)
    (C : OSPoincareContinuationHypothesis B.os) :
    ClayYangMillsMassGap4DStrictOnOSCompletion N hN :=
  ⟨B.Δ_phys, B.os, C, B.Ls_seq, B.Lt_seq, B.Ls_nz, B.Lt_nz, B.β_seq,
    B.obs, buildStrictWightmanFromOS B.os C, B.os.os.Δ_pos, B.non_gaussian,
    B.Ls_lim, B.Lt_lim, B.hβ_nn, B.hβ_lim, B.schwinger_conv, rfl⟩

/-- Forgetting the reconstruction identity recovers the existing strict target. -/
theorem clay_yang_mills_strict_on_os_completion_implies_strict
    (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (h : ClayYangMillsMassGap4DStrictOnOSCompletion N hN) :
    ClayYangMillsMassGap4DStrict N hN := by
  rcases h with ⟨Δ_phys, os, C, Ls_seq, Lt_seq, hLs, hLt, β_seq, O, W,
    hΔ, hnonG, hLs_lim, hLt_lim, hβ_nn, hβ_lim, hconv, hW⟩
  exact ⟨Δ_phys, os, W, Ls_seq, Lt_seq, hLs, hLt, β_seq, O,
    hΔ, hnonG, hLs_lim, hLt_lim, hβ_nn, hβ_lim, hconv⟩

end BalabanRGAndContinuationBridge

/-! ## Canonical thermodynamic limit data (proved from §44) -/

/-- Fixed strong-coupling parameter well within the Dobrushin contraction radius. -/
noncomputable def standardBeta0 : ℝ := 1 / 300

theorem standardBeta0_pos_val : 0 < standardBeta0 := by
  dsimp [standardBeta0]; norm_num

theorem standardBeta0_nonneg : 0 ≤ standardBeta0 := by
  dsimp [standardBeta0]; norm_num

theorem standardBeta0_dobrushin :
    18 * (1 - Real.exp (-12 * standardBeta0)) < 1 := by
  have h1 : 1 - 12 * standardBeta0 ≤ Real.exp (-12 * standardBeta0) := by
    have := Real.add_one_le_exp (-12 * standardBeta0)
    linarith
  have h2 : 1 - Real.exp (-12 * standardBeta0) ≤ 12 * standardBeta0 := by
    linarith
  have h3 : 18 * (1 - Real.exp (-12 * standardBeta0)) ≤ 18 * (12 * standardBeta0) := by
    nlinarith
  have h4 : 18 * (12 * standardBeta0) < 1 := by
    dsimp [standardBeta0]
    norm_num
  linarith

theorem standardBeta0_pos :
    0 < 18 * (1 - Real.exp (-12 * standardBeta0)) := by
  have h_exp : Real.exp (-12 * standardBeta0) < 1 := by
    rw [Real.exp_lt_one_iff]
    have : 0 < standardBeta0 := standardBeta0_pos_val
    linarith
  have h_sub : 0 < 1 - Real.exp (-12 * standardBeta0) := by linarith
  linarith

/-- Physical mass gap rate at `standardBeta0`. -/
noncomputable def standardDeltaPhys : ℝ :=
  strongCouplingClusterRate standardBeta0

theorem standardDeltaPhys_pos : 0 < standardDeltaPhys :=
  strongCouplingClusterRate_pos standardBeta0 standardBeta0_pos standardBeta0_dobrushin

/-- Extracted thermodynamic infinite-volume limit from `strongCoupling_infinite_volume_lattice_os`. -/
noncomputable def canonicalThermoData (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :=
  strongCoupling_infinite_volume_lattice_os N hN standardBeta0
    standardBeta0_nonneg standardBeta0_dobrushin standardBeta0_pos

noncomputable def canonicalS_inf (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    ∀ n : ℕ, (Fin n → Loop4DZ) → ℂ :=
  Classical.choose (canonicalThermoData N hN)

noncomputable def canonicalPhi (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    ℕ → ℕ :=
  Classical.choose (Classical.choose_spec (canonicalThermoData N hN))

theorem canonicalPhi_mono (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    StrictMono (canonicalPhi N hN) :=
  (Classical.choose_spec (Classical.choose_spec (canonicalThermoData N hN))).1

theorem canonicalS_inf_conv (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) (γs : Fin n → Loop4DZ) :
    Filter.Tendsto
      (fun m => cubic4Schwinger (2 * (canonicalPhi N hN m + 1)) (2 * (canonicalPhi N hN m + 1)) N standardBeta0 n
        (fun i => normWilsonLoop4 (embedLoop4DZ (2 * (canonicalPhi N hN m + 1)) (γs i))))
      Filter.atTop (nhds (canonicalS_inf N hN n γs)) :=
  (Classical.choose_spec (Classical.choose_spec (canonicalThermoData N hN))).2.1 n γs

/-- The zero-point lattice Schwinger function is identically 1 for all volumes and beta. -/
theorem cubic4Schwinger_zero (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (obs : Fin 0 → GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ) :
    cubic4Schwinger Ls Lt N β 0 obs = 1 := by
  dsimp [cubic4Schwinger]
  have hprod : (fun U => (∏ i : Fin 0, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)) =
      (fun U => ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)) := by
    funext U
    rw [Fin.prod_univ_zero, one_mul]
  rw [hprod, integral_complex_ofReal]
  have hpos := cubic4PartitionFn_pos Ls Lt N β hβ
  have hne : ((cubic4PartitionFn Ls Lt N β : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos
  exact inv_mul_cancel₀ hne

/-- Zero-point thermodynamic limit is 1. -/
theorem canonicalS_inf_zero (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    canonicalS_inf N hN 0 Fin.elim0 = 1 := by
  have hconv := canonicalS_inf_conv N hN 0 Fin.elim0
  have heq : (fun m => cubic4Schwinger (2 * (canonicalPhi N hN m + 1)) (2 * (canonicalPhi N hN m + 1)) N standardBeta0 0
      (fun i => normWilsonLoop4 (embedLoop4DZ (2 * (canonicalPhi N hN m + 1)) (Fin.elim0 i)))) =
      (fun _ => (1 : ℂ)) := by
    funext m
    exact cubic4Schwinger_zero _ _ N standardBeta0 standardBeta0_nonneg _
  rw [heq] at hconv
  exact tendsto_nhds_unique hconv tendsto_const_nhds

theorem canonicalS_inf_bd (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) (γs : Fin n → Loop4DZ) :
    ‖canonicalS_inf N hN n γs‖ ≤ 1 :=
  (Classical.choose_spec (Classical.choose_spec (canonicalThermoData N hN))).2.2.1 n γs

/-! ## §46W prerequisites -/

/-- Elementary square plaquette steps in the (1, 2) spatial plane. -/
def plaqSteps : List (Fin 4 × Bool) :=
  [(1, true), (2, true), (1, false), (2, false)]

theorem plaqSteps_closed : plaqSteps.foldl stepZ4 0 = 0 := by
  dsimp [plaqSteps, stepZ4]
  funext i; fin_cases i <;> rfl

/-- Canonical mapping from continuous spacetime `Space4` to discrete `Loop4DZ`. -/
noncomputable def canonicalLoop4DZ (x : Space4) : Loop4DZ where
  base := fun i => ⌊x i⌋
  steps := plaqSteps
  is_closed := plaqSteps_closed

/-! Helper lemmas for wiring canonicalOSStrict from strongCoupling_infinite_volume_lattice_os -/

-- Extract the axis-permutation invariance from canonicalThermoData
theorem canonicalS_inf_axis_perm (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) (σ : Equiv.Perm (Fin 4)) (xs : Fin n → Space4) :
    canonicalS_inf N hN n (fun i => permLoop4DZ σ (canonicalLoop4DZ (xs i))) =
    canonicalS_inf N hN n (fun i => canonicalLoop4DZ (xs i)) :=
  (Classical.choose_spec (Classical.choose_spec (canonicalThermoData N hN))).2.2.2.2.2.1 n σ
    (fun i => canonicalLoop4DZ (xs i))

-- Extract the ℤ⁴-translation invariance from canonicalThermoData
theorem canonicalS_inf_trans (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) (a : Fin 4 → ℤ) (xs : Fin n → Space4) :
    canonicalS_inf N hN n (fun i => transLoop4DZ a (canonicalLoop4DZ (xs i))) =
    canonicalS_inf N hN n (fun i => canonicalLoop4DZ (xs i)) :=
  (Classical.choose_spec (Classical.choose_spec (canonicalThermoData N hN))).2.2.2.2.1 n a
    (fun i => canonicalLoop4DZ (xs i))


/-! ## Two paths for the continuum Schwinger function -/

/-! ### Path A: direct floor embedding -/

/-- Path A continuum Schwinger: direct `canonicalLoop4DZ` embedding. -/
noncomputable def canonicalSContA (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) (xs : Fin n → Space4) : ℂ :=
  canonicalS_inf N hN n (fun i => canonicalLoop4DZ (xs i))

/-- Path A permutation symmetry — direct from the stored invariance. -/
theorem canonicalSContA_perm (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (xs : Fin n → Space4) :
    canonicalSContA N hN n (fun i => xs (σ i)) = canonicalSContA N hN n xs := by
  unfold canonicalSContA
  exact (Classical.choose_spec (Classical.choose_spec (canonicalThermoData N hN))).2.2.2.1 n σ (fun i => canonicalLoop4DZ (xs i))

/-- Path A: the loop of a translated point is a ℤ⁴ translate of the original
loop. -/
theorem canonicalLoop4DZ_trans (x a : Space4) :
    canonicalLoop4DZ (fun j => x j + a j) =
      transLoop4DZ (fun j => ⌊x j + a j⌋ - ⌊x j⌋) (canonicalLoop4DZ x) := by
  unfold canonicalLoop4DZ transLoop4DZ
  congr 1
  funext j
  simp

/-! ### Path B: difference embedding -/

/-- Path B embedding: loops based at differences `xsᵢ - xs₀`. -/
noncomputable def canonLoopDiff (n : ℕ) [NeZero n] (xs : Fin n → Space4) : Fin n → Loop4DZ :=
  fun i => canonicalLoop4DZ (fun j => xs i j - xs 0 j)

/-- Path B continuum Schwinger: difference embedding. -/
noncomputable def canonicalSContB (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) [NeZero n] (xs : Fin n → Space4) : ℂ :=
  canonicalS_inf N hN n (canonLoopDiff n xs)

/-- Path B real-space translation invariance — by construction. -/
theorem canonicalSContB_trans (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) [NeZero n] (a : Space4) (xs : Fin n → Space4) :
    canonicalSContB N hN n (fun i => fun j => xs i j + a j) =
      canonicalSContB N hN n xs := by
  unfold canonicalSContB canonLoopDiff
  congr 1
  funext i
  congr 1
  funext j
  ring

/-! ## Reflection positivity bridge -/

theorem cubic4Plaquette_supported (Ls M N : ℕ) [NeZero Ls] [NeZero M]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (x : (cubicTorus4 Ls (2*M)).Site) (ht : x.1.val < M) :
    SupportedOnPosTime Ls M N
      (fun U => normWilsonLoop4 (cubic4Plaquette x 1 2) U) := by
  intro U V hUV
  dsimp [normWilsonLoop4]
  have hpath : pathHolonomy U (cubic4Plaquette x 1 2) = pathHolonomy V (cubic4Plaquette x 1 2) := by
    unfold cubic4Plaquette
    simp only [pathHolonomy]
    have h1 : ¬ isNegTimeLink Ls M (x, (1 : Fin 4)) := by simp [isNegTimeLink]; omega
    have h2 : ¬ isNegTimeLink Ls M (cubicShift4 Ls (2*M) 1 x, (2 : Fin 4)) := by
      simp [isNegTimeLink, cubicShift4]; omega
    have h3 : ¬ isNegTimeLink Ls M (cubicShift4 Ls (2*M) 2 x, (1 : Fin 4)) := by
      simp [isNegTimeLink, cubicShift4]; omega
    have h4 : ¬ isNegTimeLink Ls M (x, (2 : Fin 4)) := by simp [isNegTimeLink]; omega
    simp [hUV _ h1, hUV _ h2, hUV _ h3, hUV _ h4]
  rw [hpath]

theorem cubic4Schwinger_wilson_refl_pos (Ls M N : ℕ) [NeZero Ls] [NeZero M]
    (β : ℝ) (hβ : 0 ≤ β) (hN : 1 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (x y : (cubicTorus4 Ls (2*M)).Site) (hx : x.1.val < M) (hy : y.1.val < M) :
    0 ≤ (∑ i : Fin 2, ∑ j : Fin 2,
      (1 : ℂ) * starRingEnd ℂ (1 : ℂ) *
        cubic4Schwinger Ls (2*M) N β 2
          ![fun U => starRingEnd ℂ (normWilsonLoop4 (N:=N) (cubic4Plaquette (if i = 0 then x else y) 1 2) (cubic4TimeReflect Ls (2*M) N U)),
            fun U => normWilsonLoop4 (N:=N) (cubic4Plaquette (if j = 0 then x else y) 1 2) U]).re := by
  let site : Fin 2 → (cubicTorus4 Ls (2*M)).Site := fun i => if i = 0 then x else y
  have hmeas : ∀ i : Fin 2, Measurable (fun U => (normWilsonLoop4 (N := N) (cubic4Plaquette (site i) (1 : Fin 4) (2 : Fin 4)) U : ℂ)) := by
    intro i
    have hph := measurable_pathHolonomy4 Ls (2*M) N (cubic4Plaquette (site i) (1:Fin 4) (2:Fin 4))
    have htr : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ))) := by
      simp only [Matrix.trace, Matrix.diag]
      exact continuous_finset_sum Finset.univ fun j _ =>
        (continuous_apply j).comp ((continuous_apply j).comp continuous_subtype_val)
    exact measurable_const.mul (htr.measurable.comp hph)
  have hbd : ∀ i U, ‖(normWilsonLoop4 (N := N) (cubic4Plaquette (site i) (1 : Fin 4) (2 : Fin 4)) U : ℂ)‖ ≤ 1 := by
    intro i U
    exact normWilsonLoop4_norm_le_one hN _ U
  have hsupp : ∀ i, SupportedOnPosTime Ls M N (fun U =>
      (normWilsonLoop4 (N := N) (cubic4Plaquette (site i) (1 : Fin 4) (2 : Fin 4)) U : ℂ)) := by
    intro i
    fin_cases i
    · simpa [site] using cubic4Plaquette_supported Ls M N x hx
    · simpa [site] using cubic4Plaquette_supported Ls M N y hy
  have h := cubic4Schwinger_refl_pos_2 Ls M N β hβ 2 (fun _ => 1)
    (fun i U => (normWilsonLoop4 (N := N) (cubic4Plaquette (site i) (1 : Fin 4) (2 : Fin 4)) U : ℂ))
    hmeas 1 zero_le_one hbd hsupp
  simpa [site] using h

/-- Floor of a negation is the negation of the floor, or one less. -/
theorem floor_neg_eq (r : ℝ) : ⌊-r⌋ = -⌊r⌋ ∨ ⌊-r⌋ = -⌊r⌋ - 1 := by
  set z : ℤ := ⌊r⌋ with hz
  have hzle : (z : ℝ) ≤ r := by rw [hz]; exact Int.floor_le r
  have hzlt : r < (z : ℝ) + 1 := by rw [hz]; exact Int.lt_floor_add_one r
  by_cases hfrac : r = (z : ℝ)
  · left
    rw [hfrac]
    simpa using (Int.floor_intCast (R := ℝ) (-z))
  · right
    have hgt : (z : ℝ) < r := lt_of_le_of_ne hzle (Ne.symm hfrac)
    apply Int.floor_eq_iff.mpr
    constructor
    · norm_num; linarith
    · norm_num; linarith

theorem thermodynamic_limit_refl_pos_eventually {m : ℕ} (c : Fin m → ℂ)
    (G_seq : ℕ → Fin m → Fin m → ℂ) (G_inf : Fin m → Fin m → ℂ)
    (hlim : ∀ i j, Filter.Tendsto (fun r => G_seq r i j) Filter.atTop (nhds (G_inf i j)))
    (hrp : ∀ᶠ r in Filter.atTop, 0 ≤ (∑ i : Fin m, ∑ j : Fin m, c i * starRingEnd ℂ (c j) * G_seq r i j).re) :
    0 ≤ (∑ i : Fin m, ∑ j : Fin m, c i * starRingEnd ℂ (c j) * G_inf i j).re := by
  have hsum_lim : Filter.Tendsto
      (fun r => (∑ i : Fin m, ∑ j : Fin m, c i * starRingEnd ℂ (c j) * G_seq r i j).re)
      Filter.atTop (nhds (∑ i, ∑ j, c i * starRingEnd ℂ (c j) * G_inf i j).re) := by
    refine Complex.continuous_re.continuousAt.tendsto.comp ?_
    refine tendsto_finset_sum Finset.univ fun i _ => ?_
    refine tendsto_finset_sum Finset.univ fun j _ => ?_
    exact tendsto_const_nhds.mul (hlim i j)
  exact ge_of_tendsto hsum_lim hrp

theorem cubic4Schwinger_wilson_refl_pos_gen (Ls M N : ℕ) [NeZero Ls] [NeZero M]
    (β : ℝ) (hβ : 0 ≤ β) (hN : 1 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (k : ℕ) (c : Fin k → ℂ) (site : Fin k → (cubicTorus4 Ls (2*M)).Site)
    (hpos : ∀ i, (site i).1.val < M) :
    0 ≤ (∑ i : Fin k, ∑ j : Fin k, c i * starRingEnd ℂ (c j) *
      cubic4Schwinger Ls (2*M) N β 2
        ![fun U => starRingEnd ℂ (normWilsonLoop4 (N:=N) (cubic4Plaquette (site i) 1 2) (cubic4TimeReflect Ls (2*M) N U)),
          fun U => normWilsonLoop4 (N:=N) (cubic4Plaquette (site j) 1 2) U]).re := by
  have hmeas : ∀ i : Fin k, Measurable (fun U => (normWilsonLoop4 (N := N) (cubic4Plaquette (site i) (1 : Fin 4) (2 : Fin 4)) U : ℂ)) := by
    intro i
    have hph := measurable_pathHolonomy4 Ls (2*M) N (cubic4Plaquette (site i) (1:Fin 4) (2:Fin 4))
    have htr : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ))) := by
      simp only [Matrix.trace, Matrix.diag]
      exact continuous_finset_sum Finset.univ fun j _ =>
        (continuous_apply j).comp ((continuous_apply j).comp continuous_subtype_val)
    exact measurable_const.mul (htr.measurable.comp hph)
  have hbd : ∀ i U, ‖(normWilsonLoop4 (N := N) (cubic4Plaquette (site i) (1 : Fin 4) (2 : Fin 4)) U : ℂ)‖ ≤ 1 := by
    intro i U
    exact normWilsonLoop4_norm_le_one hN _ U
  have hsupp : ∀ i, SupportedOnPosTime Ls M N (fun U =>
      (normWilsonLoop4 (N := N) (cubic4Plaquette (site i) (1 : Fin 4) (2 : Fin 4)) U : ℂ)) := by
    intro i
    exact cubic4Plaquette_supported Ls M N (site i) (hpos i)
  exact cubic4Schwinger_refl_pos_n Ls M N β hβ k (fun _ => 1) c
    (fun i _ U => normWilsonLoop4 (N:=N) (cubic4Plaquette (site i) (1:Fin 4) (2:Fin 4)) U)
    (fun i _ => hmeas i) 1 zero_le_one (fun i _ U => hbd i U) (fun i _ => hsupp i)

/-- Negation in Fin L agrees with the scoped integer cast of the negation. -/
theorem fin_neg_eq_intCast_neg (L : ℕ) [NeZero L] (z : ℤ) :
    (-(z : Fin L)) = ((-z : ℤ) : Fin L) := by
  apply Fin.ext
  rw [Fin.val_neg]
  rw [Fin.val_intCast]
  rw [Fin.val_intCast]
  by_cases hz0 : z % (L:ℤ) = 0
  · have hfin0 : (z : Fin L) = 0 := by
      apply Fin.ext
      rw [Fin.val_intCast]
      have hn : ((z % (L:ℤ)).toNat) = 0 := by simp [hz0]
      rw [hn]
      rfl
    rw [if_pos hfin0]
    have h' : (-z) % (L:ℤ) = 0 := by rw [Int.neg_emod]; simp [show (L:ℤ) ∣ z by exact Int.dvd_of_emod_eq_zero hz0]
    simp [h']
  · have hfin_ne : (z : Fin L) ≠ 0 := by
      intro hf
      apply hz0
      have hv := congrArg Fin.val hf
      rw [Fin.val_intCast] at hv
      have hLpos : 0 < (L:ℤ) := by exact_mod_cast (NeZero.pos L)
      have hznonneg : 0 ≤ z % (L:ℤ) := Int.emod_nonneg z (ne_of_gt hLpos)
      have hztonat : ((z % (L:ℤ)).toNat : ℤ) = z % (L:ℤ) := Int.toNat_of_nonneg hznonneg
      rw [show ((0 : Fin L).val) = 0 from rfl] at hv
      omega
    rw [if_neg hfin_ne]
    have hneg : (-z) % (L:ℤ) = (L:ℤ) - z % (L:ℤ) := by
      rw [Int.neg_emod]
      have hdiv : ¬ (L:ℤ) ∣ z := by intro hd; exact hz0 (Int.emod_eq_zero_of_dvd hd)
      simp [hdiv]
    rw [hneg]
    have hLpos : 0 < (L:ℤ) := by exact_mod_cast (NeZero.pos L)
    have hznonneg : 0 ≤ z % (L:ℤ) := Int.emod_nonneg z (ne_of_gt hLpos)
    have hztonat : ((z % (L:ℤ)).toNat : ℤ) = z % (L:ℤ) := Int.toNat_of_nonneg hznonneg
    have hto : (((L:ℤ) - z % (L:ℤ)).toNat) = L - (z % (L:ℤ)).toNat := by
      rw [← hztonat]
      have hzlt : z % (L:ℤ) < (L:ℤ) := Int.emod_lt_of_pos z hLpos
      omega
    rw [hto]

/-- Reflected-site loop (floor off by one) is a ℤ⁴ translate of the reflected-point loop. -/
theorem reflected_site_loop_translate (L : ℕ) [NeZero L] (x : Space4)
    (h : ⌊-x 0⌋ = -⌊x 0⌋ - 1) :
    embedLoop4DZ L (canonicalLoop4DZ (fun i => if i = 0 then (-(⌊x 0⌋ : ℤ) : ℝ) else x i)) =
      embedLoop4DZ L (transLoop4DZ (fun j => if j = 0 then (1 : ℤ) else 0) (canonicalLoop4DZ (euclidTimeReflect x))) := by
  congr 1
  unfold canonicalLoop4DZ transLoop4DZ euclidTimeReflect
  congr 1
  funext j
  fin_cases j <;> simp only [Fin.isValue] <;> simp (config := {decide := true})
  · rw [h]
    have hf : Int.floor (-(⌊x 0⌋ : ℝ)) = -(⌊x 0⌋) := by
      simpa using (Int.floor_intCast (R := ℝ) (-(⌊x 0⌋)))
    rw [hf]
    ring

/-! ## Time reflection compatibility -/

theorem normWilsonLoop4_spatial_timeReflect
    (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (cubicTorus4 Ls Lt).Site) :
    normWilsonLoop4 (N:=N) (cubic4Plaquette x 1 2) (cubic4TimeReflect Ls Lt N U) =
      normWilsonLoop4 (N:=N) (cubic4Plaquette ((-x.1, x.2.1, x.2.2.1, x.2.2.2)) 1 2) U := by
  have hsh : ∀ (d : Fin 4), d ≠ 0 → ∀ y : (cubicTorus4 Ls Lt).Site,
      cubicShift4 Ls Lt d (-y.1, y.2.1, y.2.2.1, y.2.2.2) =
        (-(cubicShift4 Ls Lt d y).1, (cubicShift4 Ls Lt d y).2.1,
         (cubicShift4 Ls Lt d y).2.2.1, (cubicShift4 Ls Lt d y).2.2.2) := by
    intro d hd ⟨t,a,b,c⟩
    fin_cases d <;> simp [cubicShift4] at hd ⊢
  unfold normWilsonLoop4 cubic4Plaquette
  simp only [pathHolonomy, cubic4TimeReflect, ↓reduceIte, show (1:Fin 4) ≠ 0 by decide,
    show (2:Fin 4) ≠ 0 by decide, hsh (1:Fin 4) (by decide), hsh (2:Fin 4) (by decide)]

theorem sinf_reflected_site_eq (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (x : Space4) :
    canonicalS_inf N hN 1 ![canonicalLoop4DZ (fun i => if i = 0 then (-(⌊x 0⌋ : ℤ) : ℝ) else x i)] =
      canonicalS_inf N hN 1 ![canonicalLoop4DZ (euclidTimeReflect x)] := by
  let y : Space4 := fun i => if i = 0 then (-(⌊x 0⌋ : ℤ) : ℝ) else x i
  let z : Space4 := euclidTimeReflect x
  have hf_int : Int.floor (-(⌊x 0⌋ : ℝ)) = -(⌊x 0⌋) := by
    simpa using (Int.floor_intCast (R := ℝ) (-(⌊x 0⌋)))
  change canonicalS_inf N hN 1 ![canonicalLoop4DZ y] = canonicalS_inf N hN 1 ![canonicalLoop4DZ z]
  have hbase_y : ∀ j, ⌊y j⌋ = (if j = 0 then -(⌊x 0⌋) else ⌊x j⌋) := by
    intro j; fin_cases j <;> simp [y, hf_int]
  have hbase_z : ∀ j, ⌊z j⌋ = (if j = 0 then ⌊-x 0⌋ else ⌊x j⌋) := by
    intro j; fin_cases j <;> simp [z, euclidTimeReflect]
  rcases floor_neg_eq (x 0) with h | h
  · have hloop : canonicalLoop4DZ y = canonicalLoop4DZ z := by
      unfold canonicalLoop4DZ
      congr 1
      funext j
      rw [hbase_y j, hbase_z j]
      by_cases hj : j = 0 <;> simp [hj, h]
    rw [hloop]
  · let a : Fin 4 → ℤ := fun j => if j = 0 then 1 else 0
    have hza : ∀ j, ⌊y j⌋ = ⌊z j⌋ + a j := by
      intro j
      rw [hbase_y j, hbase_z j]
      by_cases hj : j = 0
      · subst j; simp [a, h]
      · simp [a, hj]
    have hloop : canonicalLoop4DZ y = transLoop4DZ a (canonicalLoop4DZ z) := by
      unfold canonicalLoop4DZ transLoop4DZ
      congr 1
      funext j
      exact hza j
    rw [hloop]
    have ht := canonicalS_inf_trans N hN 1 a ![z]
    have hvec1 : ![transLoop4DZ a (canonicalLoop4DZ z)] = (fun _ : Fin 1 => transLoop4DZ a (canonicalLoop4DZ z)) := by
      ext i; fin_cases i; rfl
    have hvec2 : ![canonicalLoop4DZ z] = (fun _ : Fin 1 => canonicalLoop4DZ z) := by
      ext i; fin_cases i; rfl
    rw [hvec1, hvec2]
    have hvecz : ![z] = (fun _ : Fin 1 => z) := by ext i; fin_cases i; rfl
    rw [hvecz] at ht
    exact ht

theorem cubic4Schwinger_star (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) (obs : Fin n → GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ) :
    cubic4Schwinger Ls Lt N β n (fun i U => starRingEnd ℂ (obs i U)) =
      starRingEnd ℂ (cubic4Schwinger Ls Lt N β n obs) := by
  unfold cubic4Schwinger
  rw [map_mul]
  -- partition fn inverse is real
  rw [show starRingEnd ℂ (((cubic4PartitionFn Ls Lt N β)⁻¹ : ℂ)) = ((cubic4PartitionFn Ls Lt N β)⁻¹ : ℂ) by simp]
  -- integral of star(f * realweight) = star of integral
  rw [← integral_conj]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with U
  simp only [map_mul, map_prod, map_natCast]
  rw [show starRingEnd ℂ (((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)) = ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) by simp]

theorem embedFromZ4_append (L : ℕ) [NeZero L] (cur : Fin 4 → ℤ)
    (l₁ l₂ : List (Fin 4 × Bool)) :
    embedFromZ4 L cur (l₁ ++ l₂) =
      embedFromZ4 L cur l₁ ++ embedFromZ4 L (l₁.foldl stepZ4 cur) l₂ := by
  induction l₁ generalizing cur with
  | nil => rfl
  | cons p tl ih =>
    rcases p with ⟨d,b⟩
    cases b
    · rw [show embedFromZ4 L cur (((d,false)::tl)++l₂) =
          ((projSite4 L (stepZ4 cur (d,false)), d), false) :: embedFromZ4 L (stepZ4 cur (d,false)) (tl++l₂) from rfl]
      rw [show embedFromZ4 L cur ((d,false)::tl) =
          ((projSite4 L (stepZ4 cur (d,false)), d), false) :: embedFromZ4 L (stepZ4 cur (d,false)) tl from rfl]
      simp only [List.cons_append, List.foldl_cons]
      rw [ih]
    · rw [show embedFromZ4 L cur (((d,true)::tl)++l₂) =
          ((projSite4 L cur, d), true) :: embedFromZ4 L (stepZ4 cur (d,true)) (tl++l₂) from rfl]
      rw [show embedFromZ4 L cur ((d,true)::tl) =
          ((projSite4 L cur, d), true) :: embedFromZ4 L (stepZ4 cur (d,true)) tl from rfl]
      simp only [List.cons_append, List.foldl_cons]
      rw [ih]

-- pathHolonomy under append: hol(l₁++l₂) = hol l₁ * hol l₂
theorem ph_append (L : ℕ) [NeZero L] (N : ℕ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (U : GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (l₁ l₂ : List ((cubicTorus4 L L).Link × Bool)) :
    pathHolonomy U (l₁ ++ l₂) = pathHolonomy U l₁ * pathHolonomy U l₂ := by
  induction l₁ with
  | nil => simp [pathHolonomy]
  | cons hd tl ih => rcases hd with ⟨e,b⟩; cases b <;> simp [pathHolonomy, ih, mul_assoc]

-- unfold embedFromZ4 at a cons
theorem embed_cons (L : ℕ) [NeZero L] (cur : Fin 4 → ℤ) (d : Fin 4) (b : Bool)
    (tl : List (Fin 4 × Bool)) :
    embedFromZ4 L cur ((d,b)::tl) =
      (if b then ((projSite4 L cur, d), true) else ((projSite4 L (stepZ4 cur (d,false)), d), false)) ::
        embedFromZ4 L (stepZ4 cur (d,b)) tl := by
  cases b <;> rfl


noncomputable def contTimeRefl (x : Space4) : Space4 :=
  fun i => if i = 0 then -(⌊x 0⌋ : ℝ) + (x 0 - ⌊x 0⌋) else x i

theorem floor_contTimeRefl (x : Space4) : ⌊contTimeRefl x 0⌋ = -⌊x 0⌋ := by
  unfold contTimeRefl
  simp only [if_pos rfl]
  rw [Int.floor_eq_iff]
  constructor
  · have h : 0 ≤ x 0 - (⌊x 0⌋ : ℝ) := sub_nonneg.mpr (Int.floor_le (x 0))
    push_cast
    linarith
  · have h : x 0 - (⌊x 0⌋ : ℝ) < 1 := by linarith [Int.lt_floor_add_one (x 0)]
    push_cast
    linarith

-- The embedded loop at contTimeRefl x equals the reflectConj-translate of the loop at x:
-- base time floor negates exactly; spatial coords unchanged; steps (spatial plaquette 1,2) unchanged.
theorem canonicalLoop_contTimeRefl (x : Space4) :
    canonicalLoop4DZ (contTimeRefl x) =
      transLoop4DZ (fun j => if j = 0 then -2 * ⌊x 0⌋ else 0) (canonicalLoop4DZ x) := by
  unfold canonicalLoop4DZ transLoop4DZ
  congr 1
  funext j
  fin_cases j
  · change ⌊contTimeRefl x 0⌋ = ⌊x 0⌋ + (-2 * ⌊x 0⌋)
    rw [floor_contTimeRefl]
    ring
  · change ⌊x 1⌋ = ⌊x 1⌋ + 0; ring
  · change ⌊x 2⌋ = ⌊x 2⌋ + 0; ring
  · change ⌊x 3⌋ = ⌊x 3⌋ + 0; ring

def reflZ (x : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => if i = 0 then -x 0 else x i

theorem foldl_reflZ (steps : List (Fin 4 × Bool)) (x : Fin 4 → ℤ) :
    (steps.map fun p => if p.1 = 0 then (0, p.2) else (p.1, !p.2)).reverse.foldl stepZ4 (reflZ (steps.foldl stepZ4 x)) =
      reflZ x := by
  induction steps generalizing x with
  | nil => rfl
  | cons p tl ih =>
    simp only [List.map_cons, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih (stepZ4 x p)]
    rcases p with ⟨d,b⟩
    by_cases hd : d = 0
    · subst d
      funext i; fin_cases i <;> cases b <;> simp [reflZ, stepZ4] <;> ring_nf
    · funext i; fin_cases i <;> cases b <;> simp [reflZ, stepZ4, hd, Ne.symm hd] <;> split_ifs <;> omega


theorem foldl_mapflip_spatial (steps : List (Fin 4 × Bool)) (hsp : ∀ p ∈ steps, p.1 ≠ 0) (cur : Fin 4 → ℤ) :
    (steps.map fun p => (p.1, !p.2)).reverse.foldl stepZ4 (steps.foldl stepZ4 cur) = cur := by
  induction steps generalizing cur with
  | nil => rfl
  | cons p tl ih =>
    rcases p with ⟨d,b⟩
    have hd : d ≠ 0 := hsp (d,b) (by simp)
    simp only [List.map_cons, List.reverse_cons, List.foldl_cons]
    rw [List.foldl_append]
    rw [ih (by intro q hq; exact hsp q (by simp [hq])) (stepZ4 cur (d,b))]
    cases b
    · ext i; by_cases hi : i = d <;> simp [stepZ4, hi]
    · ext i; by_cases hi : i = d <;> simp [stepZ4, hi]

def flipStepT (p : Fin 4 × Bool) : Fin 4 × Bool :=
  if p.1 = 0 then (0, !p.2) else (p.1, p.2)
theorem stepZ4_reflZ (x : Fin 4 → ℤ) (p : Fin 4 × Bool) :
    stepZ4 (reflZ x) (flipStepT p) = reflZ (stepZ4 x p) := by
  rcases p with ⟨d,b⟩
  unfold reflZ flipStepT stepZ4
  by_cases hd : d = 0
  · subst d
    cases b <;> funext i <;> fin_cases i <;> simp <;> ring_nf
  · cases b <;> funext i <;> fin_cases i <;> simp [hd, Ne.symm hd] <;> ring_nf

def revFlip {L : ℕ} [NeZero L] : List ((cubicTorus4 L L).Link × Bool) → List ((cubicTorus4 L L).Link × Bool)
  | [] => []
  | (e,b)::tl => revFlip tl ++ [(e, !b)]

theorem hol_revFlip (L : ℕ) [NeZero L] (N : ℕ) (U : GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (γ : List ((cubicTorus4 L L).Link × Bool)) :
    pathHolonomy U (revFlip γ) = (pathHolonomy U γ)⁻¹ := by
  have happ : ∀ l₁ l₂, pathHolonomy U (l₁ ++ l₂) = pathHolonomy U l₁ * pathHolonomy U l₂ := by
    intro l₁ l₂; induction l₁ with
    | nil => simp [pathHolonomy]
    | cons hd tl ih => rcases hd with ⟨e,b⟩; cases b <;> simp [pathHolonomy, ih, mul_assoc]
  induction γ with
  | nil => simp [pathHolonomy, revFlip]
  | cons hd tl ih =>
    rcases hd with ⟨e,b⟩
    simp only [revFlip, happ, pathHolonomy]
    cases b <;> simp [pathHolonomy, ih, mul_inv_rev]

theorem star_normWilsonLoop4 (L : ℕ) [NeZero L] (N : ℕ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (U : GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (γ : List ((cubicTorus4 L L).Link × Bool)) :
    starRingEnd ℂ (normWilsonLoop4 γ U) = normWilsonLoop4 (revFlip γ) U := by
  unfold normWilsonLoop4
  change star (((N : ℝ)⁻¹ : ℂ) * (Matrix.trace ((pathHolonomy U γ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))) = _
  rw [star_mul]
  change star (Matrix.trace ((pathHolonomy U γ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) * star ((N:ℝ)⁻¹ : ℂ) = _
  have hstarN : star (((N:ℝ)⁻¹ : ℂ)) = ((N:ℝ)⁻¹ : ℂ) := by simp
  rw [hstarN]
  rw [hol_revFlip]
  let A : Matrix (Fin N) (Fin N) ℂ := (pathHolonomy U γ : Matrix.specialUnitaryGroup (Fin N) ℂ)
  have hct : star (Matrix.trace A) = Matrix.trace (A.conjTranspose) := (Matrix.trace_conjTranspose A).symm
  rw [hct]
  have hAinv : A.conjTranspose = ((pathHolonomy U γ)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) := by
    change star A = ((pathHolonomy U γ)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    exact (su_inv_val_eq_star (pathHolonomy U γ)).symm
  rw [hAinv]
  -- trace of inverse matrix
  change (Matrix.trace (((pathHolonomy U γ)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) * (↑N)⁻¹ = (↑N)⁻¹ * (Matrix.trace (((pathHolonomy U γ)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))
  ring


/-! ### Reflection positivity limit — assembly checklist

The pieces above suffice to pass 2-point reflection positivity to the
infinite-volume limit via `thermodynamic_limit_refl_pos_eventually`:

* `G_seq r i j := cubic4Schwinger (Lm r) (Lm r) N standardBeta0 2
    ![star(W_{site_i r} ∘ Θ_latt), W_{site_j r}]` with `Lm r = 2(φ r + 1)`.
* `G_inf i j := canonicalSContA N hN 2 ![Θ x_i, x_j]`.
* Convergence: `normWilsonLoop4_spatial_timeReflect` rewrites the reflected
  observable to the reflected site; `reflected_site_loop_translate` and
  `floor_neg_eq` show that loop is an integer translate of the reflected-point
  loop; `canonicalS_inf_trans` making their `S_inf` values equal; then
  `canonicalS_inf_conv` gives `hlim`.
* Finite positivity: `cubic4Schwinger_wilson_refl_pos_gen` applies whenever
  the site time coordinate `⌊x_i 0⌋ mod Lm r < φ r + 1`, which holds eventually
  since `φ r → ∞` (canonicalPhi_mono).
* `thermodynamic_limit_refl_pos_eventually c G_seq G_inf hlim hrp` concludes.

The final `canonicalSContA_refl2` theorem is the remaining assembly.
-/

/-! ## §46W. Canonical non-constancy witness for the embedded plaquette observable -/

/-- Successor of an integer cast in `Fin L` differs from the cast, for `L ≥ 2`. -/
theorem intCastFin_succ_ne (L : ℕ) [NeZero L] (hL : 2 ≤ L) (z : ℤ) :
    ((z + 1 : ℤ) : Fin L) ≠ (z : Fin L) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_intCast] at hv
  have hLne : (L : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
  have hLpos : 0 < (L : ℤ) := by exact_mod_cast (NeZero.pos L)
  have h1mod : (1 : ℤ) % (L : ℤ) = 1 := Int.emod_eq_of_lt (by omega) (by omega)
  have hred : (z + 1) % (L : ℤ) = (z % (L : ℤ) + 1) % (L : ℤ) := by
    rw [Int.add_emod, h1mod]
  rw [hred] at hv
  by_cases hlt : z % (L : ℤ) + 1 < (L : ℤ)
  · have htn1 : 0 ≤ z % (L : ℤ) := Int.emod_nonneg z hLne
    have htn2 : 0 ≤ z % (L : ℤ) + 1 := by linarith
    have h2 := Int.emod_eq_of_lt htn2 hlt
    rw [h2] at hv
    have h3n : z % (L : ℤ) + 1 = z % (L : ℤ) := by
      have hc : ((z % (L : ℤ) + 1).toNat : ℤ) = ((z % (L : ℤ)).toNat : ℤ) := by
        exact congrArg (fun k : ℕ => (k : ℤ)) hv
      rw [Int.toNat_of_nonneg htn2, Int.toNat_of_nonneg htn1] at hc
      exact hc
    omega
  · push_neg at hlt
    have hte : z % (L : ℤ) = (L : ℤ) - 1 := by
      have hb := Int.emod_lt_of_pos z hLpos
      have htn := Int.emod_nonneg z hLne
      omega
    have h2e : (z % (L : ℤ) + 1) % (L : ℤ) = 0 := by
      rw [hte]
      have : (L : ℤ) - 1 + 1 = (L : ℤ) := by ring
      rw [this, Int.emod_self]
    rw [h2e] at hv
    have hz0 : ((0 : ℤ).toNat : ℤ) = 0 := rfl
    have htn := Int.emod_nonneg z hLne
    have h3 : (z % (L : ℤ)).toNat = 0 := by
      exact_mod_cast hv.symm
    have h4 : z % (L : ℤ) ≤ 0 := Int.toNat_eq_zero.mp h3
    omega

/-- Predecessor of an integer cast in `Fin L` differs from the cast, for `L ≥ 2`. -/
theorem intCastFin_pred_ne (L : ℕ) [NeZero L] (hL : 2 ≤ L) (z : ℤ) :
    ((z - 1 : ℤ) : Fin L) ≠ (z : Fin L) := by
  intro h
  have h' : ((z : ℤ) : Fin L) = ((z - 1 + 1 : ℤ) : Fin L) := by
    congr 1
    ring
  exact intCastFin_succ_ne L hL (z - 1) (h'.symm.trans h.symm)

/-- A unit lattice step always moves the projected torus site, for `L ≥ 2`. -/
theorem projSite4_stepS_ne (L : ℕ) [NeZero L] (hL : 2 ≤ L)
    (x : Fin 4 → ℤ) (d : Fin 4) (b : Bool) :
    projSite4 L (stepZ4 x (d, b)) ≠ projSite4 L x := by
  cases b
  · intro h
    fin_cases d
    · exact intCastFin_pred_ne L hL (x 0) (by simpa [stepZ4, projSite4] using congrArg Prod.fst h)
    · exact intCastFin_pred_ne L hL (x 1)
        (by simpa [stepZ4, projSite4] using congrArg (fun s : (cubicTorus4 L L).Site => s.2.1) h)
    · exact intCastFin_pred_ne L hL (x 2)
        (by simpa [stepZ4, projSite4] using congrArg (fun s : (cubicTorus4 L L).Site => s.2.2.1) h)
    · exact intCastFin_pred_ne L hL (x 3)
        (by simpa [stepZ4, projSite4] using congrArg (fun s : (cubicTorus4 L L).Site => s.2.2.2) h)
  · intro h
    fin_cases d
    · exact intCastFin_succ_ne L hL (x 0) (by simpa [stepZ4, projSite4] using congrArg Prod.fst h)
    · exact intCastFin_succ_ne L hL (x 1)
        (by simpa [stepZ4, projSite4] using congrArg (fun s : (cubicTorus4 L L).Site => s.2.1) h)
    · exact intCastFin_succ_ne L hL (x 2)
        (by simpa [stepZ4, projSite4] using congrArg (fun s : (cubicTorus4 L L).Site => s.2.2.1) h)
    · exact intCastFin_succ_ne L hL (x 3)
        (by simpa [stepZ4, projSite4] using congrArg (fun s : (cubicTorus4 L L).Site => s.2.2.2) h)

/-- The canonical plaquette loop at `x`, unfolded into its 4 explicit links. -/
theorem embedLoop4DZ_canonicalPlaqW (L : ℕ) [NeZero L] (x : Space4) :
    embedLoop4DZ L (canonicalLoop4DZ x) =
      [ ((projSite4 L (fun i => ⌊x i⌋), (1 : Fin 4)), true),
        ((projSite4 L (stepZ4 (fun i => ⌊x i⌋) (1, true)), (2 : Fin 4)), true),
        ((projSite4 L (stepZ4 (stepZ4 (stepZ4 (fun i => ⌊x i⌋) (1, true)) (2, true))
          (1, false)), (1 : Fin 4)), false),
        ((projSite4 L (stepZ4 (stepZ4 (stepZ4 (stepZ4 (fun i => ⌊x i⌋) (1, true)) (2, true))
          (1, false)) (2, false)), (2 : Fin 4)), false) ] := by
  rfl

/-- Trivial witness field. -/
def witnessFieldOneW (N : ℕ) (L : ℕ) [NeZero L] :
    GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ) := fun _ => 1

/-- Single-flip witness field: exactly the base-site direction-1 link of the
canonical plaquette carries `suFlip2`; every other link is trivial. -/
noncomputable def witnessFieldFlipW (N : ℕ) (hN : 2 ≤ N) (L : ℕ) [NeZero L] (x : Space4) :
    GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ) := fun e =>
  if e = ((projSite4 L (fun i => ⌊x i⌋), (1 : Fin 4)) : (cubicTorus4 L L).Link) then
    suFlip2 N hN else 1

theorem witnessFieldOneW_hol (N : ℕ) (L : ℕ) [NeZero L] (x : Space4) :
    pathHolonomy (witnessFieldOneW N L)
      (embedLoop4DZ L (canonicalLoop4DZ x)) = 1 := by
  have h_fwd : ∀ γ : List ((cubicTorus4 L L).Link × Bool),
      pathHolonomy (witnessFieldOneW N L) γ = 1 := by
    intro γ
    induction γ with
    | nil => rfl
    | cons hd tl ih =>
      rcases hd with ⟨e, b⟩
      have hU : witnessFieldOneW N L e = 1 := rfl
      cases b
      · simp only [pathHolonomy, hU, one_mul, mul_one, inv_one, ih]
      · simp only [pathHolonomy, hU, one_mul, mul_one, inv_one, ih]
  exact h_fwd _

/-- The three tail links of the embedded canonical plaquette differ from the
base-site direction-1 link. -/
theorem tailLinksW_ne_flip (L : ℕ) [NeZero L] (hL : 2 ≤ L) (x : Space4) :
    ((projSite4 L (stepZ4 (fun i => ⌊x i⌋) (1, true)), (2 : Fin 4)) :
      (cubicTorus4 L L).Link) ≠
      ((projSite4 L (fun i => ⌊x i⌋), (1 : Fin 4)) : (cubicTorus4 L L).Link) ∧
    ((projSite4 L (stepZ4 (stepZ4 (stepZ4 (fun i => ⌊x i⌋) (1, true)) (2, true))
      (1, false)), (1 : Fin 4)) : (cubicTorus4 L L).Link) ≠
      ((projSite4 L (fun i => ⌊x i⌋), (1 : Fin 4)) : (cubicTorus4 L L).Link) ∧
    ((projSite4 L (stepZ4 (stepZ4 (stepZ4 (stepZ4 (fun i => ⌊x i⌋) (1, true)) (2, true))
      (1, false)) (2, false)), (2 : Fin 4)) : (cubicTorus4 L L).Link) ≠
      ((projSite4 L (fun i => ⌊x i⌋), (1 : Fin 4)) : (cubicTorus4 L L).Link) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact absurd (congrArg Prod.snd h) (by decide : ((2 : Fin 4) : Fin 4) ≠ (1 : Fin 4))
  · have hstep : (stepZ4 (stepZ4 (stepZ4 (fun i => ⌊x i⌋) (1, true)) (2, true))
        (1, false)) = stepZ4 (fun i => ⌊x i⌋) (2, true) := by
      dsimp [stepZ4]
      funext i; fin_cases i <;> simp [stepZ4] <;> split_ifs <;> rfl
    intro h
    rw [hstep] at h
    exact projSite4_stepS_ne L hL (fun i => ⌊x i⌋) (2 : Fin 4) true (congrArg Prod.fst h)
  · intro h
    exact absurd (congrArg Prod.snd h) (by decide : ((2 : Fin 4) : Fin 4) ≠ (1 : Fin 4))

theorem witnessFieldFlipW_hol (N : ℕ) (hN : 2 ≤ N) (L : ℕ) [NeZero L] (hL : 2 ≤ L) (x : Space4) :
    pathHolonomy (witnessFieldFlipW N hN L x)
      (embedLoop4DZ L (canonicalLoop4DZ x)) = suFlip2 N hN := by
  rw [embedLoop4DZ_canonicalPlaqW]
  have h1 : witnessFieldFlipW N hN L x
      ((projSite4 L (fun i => ⌊x i⌋), (1 : Fin 4)) : (cubicTorus4 L L).Link) = suFlip2 N hN :=
    if_pos rfl
  have h2 : witnessFieldFlipW N hN L x
      ((projSite4 L (stepZ4 (fun i => ⌊x i⌋) (1, true)), (2 : Fin 4)) :
        (cubicTorus4 L L).Link) = 1 :=
    if_neg (tailLinksW_ne_flip L hL x).1
  have h3 : witnessFieldFlipW N hN L x
      ((projSite4 L (stepZ4 (stepZ4 (stepZ4 (fun i => ⌊x i⌋) (1, true)) (2, true))
        (1, false)), (1 : Fin 4)) : (cubicTorus4 L L).Link) = 1 :=
    if_neg (tailLinksW_ne_flip L hL x).2.1
  have h4 : witnessFieldFlipW N hN L x
      ((projSite4 L (stepZ4 (stepZ4 (stepZ4 (stepZ4 (fun i => ⌊x i⌋) (1, true)) (2, true))
        (1, false)) (2, false)), (2 : Fin 4)) : (cubicTorus4 L L).Link) = 1 :=
    if_neg (tailLinksW_ne_flip L hL x).2.2
  simp only [pathHolonomy, h1, h2, h3, h4, one_mul, mul_one, inv_one]

theorem suFlip2_trace_cast (N : ℕ) (hN : 2 ≤ N) :
    (Matrix.trace ((suFlip2 N hN : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ)) = (((N : ℝ) - 4) : ℂ) := by
  refine Complex.ext (suFlip2_trace_re N hN) ?_
  simp only [suFlip2, Matrix.trace, Matrix.diag, Matrix.diagonal_apply_eq, Complex.im_sum,
    Complex.sub_im, Complex.ofReal_im]
  norm_num
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : (i : ℕ) < 2
  · simp [hi]
  · simp [hi]

theorem suOne_trace_cast (N : ℕ) :
    (Matrix.trace ((1 : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ)) = ((N : ℝ) : ℂ) := by
  refine Complex.ext (su_one_trace_re N) ?_
  simp

theorem canonicalWildcard_nonconstW (N : ℕ) (hN : 2 ≤ N) (L : ℕ) [NeZero L] (hL : 2 ≤ L)
    (x : Space4) :
    ∃ U₁ U₂ : GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ),
      normWilsonLoop4 (embedLoop4DZ L (canonicalLoop4DZ x)) U₁ ≠
        normWilsonLoop4 (embedLoop4DZ L (canonicalLoop4DZ x)) U₂ := by
  refine ⟨witnessFieldOneW N L, witnessFieldFlipW N hN L x, ?_⟩
  have hv1 : normWilsonLoop4 (embedLoop4DZ L (canonicalLoop4DZ x)) (witnessFieldOneW N L) = 1 := by
    dsimp only [normWilsonLoop4]
    rw [witnessFieldOneW_hol N L x]
    rw [suOne_trace_cast]
    have hnz : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    exact inv_mul_cancel₀ hnz
  have hv2 : normWilsonLoop4 (embedLoop4DZ L (canonicalLoop4DZ x)) (witnessFieldFlipW N hN L x)
      = ((N : ℝ)⁻¹ : ℂ) * (((N : ℝ) - 4) : ℂ) := by
    dsimp only [normWilsonLoop4]
    rw [witnessFieldFlipW_hol N hN L hL x, suFlip2_trace_cast]
  intro habs
  rw [hv1, hv2] at habs
  have hNc : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hstep : ((N : ℝ) : ℂ) * 1 =
      ((N : ℝ) : ℂ) * (((N : ℝ)⁻¹ : ℂ) * (((N : ℝ) - 4) : ℂ)) := by
    rw [habs]
  rw [mul_one, ← mul_assoc, mul_inv_cancel₀ hNc, one_mul] at hstep
  have hre := congrArg (fun z : ℂ => z.re) hstep
  have hre' : (N : ℝ) = (N : ℝ) - 4 := by simpa using hre
  linarith

/-! ## Plaquette embedding bridge -/

theorem cubic4Plaquette_floor (L : ℕ) [NeZero L] (x : Space4) :
    cubic4Plaquette (projSite4 L (fun i => ⌊x i⌋)) 1 2 =
      embedLoop4DZ L (canonicalLoop4DZ x) := by
  have hsite3 : projSite4 L (stepZ4 (stepZ4 (stepZ4 (fun i => ⌊x i⌋) (1, true)) (2, true)) (1, false)) =
      cubicShift4 L L 2 (projSite4 L (fun i => ⌊x i⌋)) := by
    have hstep : stepZ4 (stepZ4 (stepZ4 (fun i => ⌊x i⌋) (1, true)) (2, true)) (1, false) =
        stepZ4 (fun i => ⌊x i⌋) (2, true) := by
      funext i; fin_cases i <;> dsimp [stepZ4] <;> simp
    rw [hstep]
    exact projSite4_step_fwd L (fun i => ⌊x i⌋) 2
  have hstep4 : stepZ4 (stepZ4 (stepZ4 (stepZ4 (fun i => ⌊x i⌋) (1, true)) (2, true)) (1, false)) (2, false) =
      (fun i => ⌊x i⌋) := by
    funext i; fin_cases i <;> dsimp [stepZ4] <;> simp <;> split_ifs <;> ring
  have hsite2 : projSite4 L (stepZ4 (fun i => ⌊x i⌋) (1, true)) =
      cubicShift4 L L 1 (projSite4 L (fun i => ⌊x i⌋)) :=
    projSite4_step_fwd L (fun i => ⌊x i⌋) 1
  rw [embedLoop4DZ_canonicalPlaqW]
  unfold cubic4Plaquette
  rw [hsite2, hsite3, hstep4]

theorem schwinger_star_first (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) (i0 : Fin n) (obs : Fin n → GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ) :
    cubic4Schwinger Ls Lt N β n (fun i U => if i = i0 then starRingEnd ℂ (obs i U) else obs i U) =
      starRingEnd ℂ (cubic4Schwinger Ls Lt N β n (fun i U => if i = i0 then obs i U else starRingEnd ℂ (obs i U))) := by
  unfold cubic4Schwinger
  rw [map_mul]
  -- RHS: star(prefactor * integral) = star(prefactor) * star(integral); prefactor real
  rw [show starRingEnd ℂ (((cubic4PartitionFn Ls Lt N β)⁻¹ : ℂ)) = ((cubic4PartitionFn Ls Lt N β)⁻¹ : ℂ) by simp]
  rw [← integral_conj]
  congr 1
  apply integral_congr_ae
  filter_upwards with U
  simp only [map_mul, map_prod]
  have hprod : (∏ i, (if i = i0 then starRingEnd ℂ (obs i U) else obs i U)) =
      starRingEnd ℂ (∏ i, (if i = i0 then obs i U else starRingEnd ℂ (obs i U))) := by
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases h : i = i0 <;> simp [h]
  rw [hprod]
  have hp2 : (∏ x, (starRingEnd ℂ) (if x = i0 then obs x U else (starRingEnd ℂ) (obs x U))) =
      starRingEnd ℂ (∏ x, (if x = i0 then obs x U else (starRingEnd ℂ) (obs x U))) := by
    rw [map_prod]
  rw [hp2]
  congr 1
  simp

theorem wilson_refl_eq (L : ℕ) [NeZero L] (N : ℕ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (x : Space4) (U : GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    normWilsonLoop4 (cubic4Plaquette (projSite4 L (fun i => ⌊x i⌋)) 1 2) (cubic4TimeReflect L L N U) =
      normWilsonLoop4 (embedLoop4DZ L (canonicalLoop4DZ (contTimeRefl x))) U := by
  rw [normWilsonLoop4_spatial_timeReflect]
  -- LHS: W(plaquette at -site) U. Site = projSite4(floor(contTimeRefl x)) by exact floor neg
  rw [← cubic4Plaquette_floor]
  congr 2
  -- site equality
  unfold projSite4
  simp only
  congr 1
  rw [floor_contTimeRefl]
  rw [fin_neg_eq_intCast_neg]

/-- Trace of the inverse of an SU(N) matrix is the conjugate of its trace. -/
theorem su_trace_inv_eq_star (N : ℕ) (A : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Matrix.trace (((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) =
      starRingEnd ℂ (Matrix.trace ((A : Matrix (Fin N) (Fin N) ℂ))) := by
  change (↑A⁻¹ : Matrix (Fin N) (Fin N) ℂ).trace = star (↑A : Matrix (Fin N) (Fin N) ℂ).trace
  rw [← Matrix.trace_conjTranspose]
  congr 1

theorem sinf_revFlip (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] (γ : Loop4DZ) :
    Filter.Tendsto
      (fun m =>
        let L := 2*(canonicalPhi N hN m+1)
        cubic4Schwinger L L N standardBeta0 1
          ![fun U => normWilsonLoop4 (revFlip (embedLoop4DZ L γ)) U])
      Filter.atTop (nhds (starRingEnd ℂ (canonicalS_inf N hN 1 ![γ]))) := by
  -- finite: Wilson(revFlip embed γ) = star(Wilson(embed γ)) pointwise
  have hfin : ∀ m,
      (let L := 2*(canonicalPhi N hN m+1)
       cubic4Schwinger L L N standardBeta0 1 ![fun U => normWilsonLoop4 (revFlip (embedLoop4DZ L γ)) U]) =
      starRingEnd ℂ ((let L := 2*(canonicalPhi N hN m+1)
       cubic4Schwinger L L N standardBeta0 1 ![fun U => normWilsonLoop4 (embedLoop4DZ L γ) U])) := by
    intro m
    dsimp only
    let L := 2*(canonicalPhi N hN m+1)
    have hfun : (fun U : GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        normWilsonLoop4 (revFlip (embedLoop4DZ L γ)) U) =
        (fun U => starRingEnd ℂ (normWilsonLoop4 (embedLoop4DZ L γ) U)) := by
      funext U
      exact (star_normWilsonLoop4 L N U (embedLoop4DZ L γ)).symm
    rw [hfun]
    simpa using (cubic4Schwinger_star L L N standardBeta0 1
      (fun i => normWilsonLoop4 (embedLoop4DZ L γ) : Fin 1 → GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ))
  have h := canonicalS_inf_conv N hN 1 ![γ]
  have hs := (Complex.continuous_conj.continuousAt.tendsto).comp h
  convert hs using 1
  funext m
  simpa only [Function.comp_apply] using (hfin m)

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
#check YangMills.clay_yang_mills_strict_from_balaban_and_os
#print axioms YangMills.clay_yang_mills_strict_from_balaban_and_os
#check YangMills.clay_yang_mills_from_rg_estimates
#print axioms YangMills.clay_yang_mills_from_rg_estimates
#check YangMills.unconditional_uniform_rescaled_lattice_mass_gap_and_rg_convergence
#print axioms YangMills.unconditional_uniform_rescaled_lattice_mass_gap_and_rg_convergence
#check YangMills.concreteOS4DContinuumTheory
#print axioms YangMills.concreteOS4DContinuumTheory
#check YangMills.concreteUniformRGTrajectory
#print axioms YangMills.concreteUniformRGTrajectory
#check YangMills.WightmanQFT4DStrict
#print axioms YangMills.WightmanQFT4DStrict
#check YangMills.yangMillsMassGap
#print axioms YangMills.yangMillsMassGap
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
#print axioms YangMills.osConfigKernel_eq_completion_inner
#print axioms YangMills.osTimeShiftConfig_eq_completion_inner
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
#print axioms YangMills.buildStrictWightmanFromOS_config_inner
#print axioms YangMills.buildStrictWightmanFromOS_time_shift_kernel
#print axioms YangMills.buildStrictWightmanFromOS_schwinger_vacuum_coefficient
#print axioms YangMills.buildStrictWightmanFromOS_schwinger_field_word_approx
#print axioms YangMills.clay_yang_mills_strict_from_balaban_and_os
#print axioms YangMills.clay_yang_mills_strict_on_os_completion_from_balaban_and_os
#print axioms YangMills.clay_yang_mills_strict_on_os_completion_implies_strict
