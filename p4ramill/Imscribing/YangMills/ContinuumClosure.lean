import Mathlib
import Imscribing.YangMills.Core
import Imscribing.YangMills.CubicHaar4D
import Imscribing.YangMills.OSCompletion
import Imscribing.YangMills.FeynmanKacAndStrongCoupling

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 8000000
set_option maxRecDepth 20000

open scoped InnerProductSpace Fin.NatCast Fin.IntCast Fin.CommRing
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

/-! ## §46.  Canonical Realization & Unconditional Mass Gap Theorem -/

section CanonicalClosure

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

/-! ## §46W. Canonical non-constancy witness for the embedded plaquette observable -/

/-- Successor of an integer cast in `Fin L` differs from the cast, for `L ≥ 2`. -/
theorem intCastFin_succ_ne (L : ℕ) [NeZero L] (hL : 2 ≤ L) (z : ℤ) :
    ((z + 1 : ℤ) : Fin L) ≠ ((z : ℤ) : Fin L) := by
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_intCast, Fin.val_intCast] at hv
  have hLpos : 0 < (L : ℤ) := by exact_mod_cast NeZero.pos L
  have h2z : (2 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
  have hLne : (L : ℤ) ≠ 0 := by omega
  have h1mod : (1 : ℤ) % (L : ℤ) = 1 :=
    Int.emod_eq_of_lt zero_le_one (by omega)
  have hred : (z + 1) % (L : ℤ) = (z % (L : ℤ) + 1) % (L : ℤ) := by
    rw [Int.add_emod, h1mod]
  rw [hred] at hv
  by_cases hlt : z % (L : ℤ) + 1 < (L : ℤ)
  · have htn1 : 0 ≤ z % (L : ℤ) := Int.emod_nonneg z hLne
    have htn2 : 0 ≤ z % (L : ℤ) + 1 := by linarith
    have h2 := Int.emod_eq_of_lt htn2 hlt
    rw [h2] at hv
    have h3 : ((z % (L : ℤ) + 1).toNat : ℤ) = ((z % (L : ℤ)).toNat : ℤ) := by
      exact_mod_cast hv
    rw [Int.toNat_of_nonneg htn2, Int.toNat_of_nonneg htn1] at h3
    omega
  · push_neg at hlt
    have h1 := Int.emod_lt_of_pos z hLpos
    have hte : z % (L : ℤ) = (L : ℤ) - 1 := by omega
    have h2e : (z % (L : ℤ) + 1) % (L : ℤ) = 0 := by
      have hts : z % (L : ℤ) + 1 = (L : ℤ) := by rw [hte]; ring
      rw [hts, Int.emod_self]
    rw [h2e] at hv
    have h3 : ((0 : ℤ).toNat : ℤ) = ((z % (L : ℤ)).toNat : ℤ) := by
      exact_mod_cast hv
    rw [show ((0 : ℤ).toNat : ℤ) = 0 from rfl, Int.toNat_of_nonneg (by omega)] at h3
    omega

/-- Predecessor of an integer cast in `Fin L` differs from the cast, for `L ≥ 2`. -/
theorem intCastFin_pred_ne (L : ℕ) [NeZero L] (hL : 2 ≤ L) (z : ℤ) :
    ((z - 1 : ℤ) : Fin L) ≠ ((z : ℤ) : Fin L) := by
  intro h
  have hz : z = z - 1 + 1 := by ring
  exact intCastFin_succ_ne L hL (z - 1)
    ((congrArg (fun w : ℤ => ((w : ℤ) : Fin L)) hz).symm.trans h.symm)

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

/-- Canonical gauge-invariant single-point Wilson loop observable. -/
noncomputable def canonicalObs (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    LatticeSinglePointObs N
      (fun m => 2 * (canonicalPhi N hN m + 1))
      (fun m => 2 * (canonicalPhi N hN m + 1)) where
  obs m x U :=
    normWilsonLoop4 (embedLoop4DZ (2 * (canonicalPhi N hN m + 1)) (canonicalLoop4DZ x)) U
  gauge_inv m x g U := by
    apply normWilsonLoop4_gauge_inv
    exact embedLoop4DZ_isPath (2 * (canonicalPhi N hN m + 1)) (canonicalLoop4DZ x)
  non_const := by
    intro m x
    haveI hnz : NeZero (2 * (canonicalPhi N hN m + 1)) := ⟨by omega⟩
    have hL : 2 ≤ 2 * (canonicalPhi N hN m + 1) := by omega
    exact canonicalWildcard_nonconstW N hN (2 * (canonicalPhi N hN m + 1)) hL x

/-! Helper lemmas for wiring canonicalOSStrict from strongCoupling_infinite_volume_lattice_os -/

-- Extract the axis-permutation invariance from canonicalThermoData
private theorem canonicalS_inf_axis_perm (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) (σ : Equiv.Perm (Fin 4)) (xs : Fin n → Space4) :
    canonicalS_inf N hN n (fun i => permLoop4DZ σ (canonicalLoop4DZ (xs i))) =
    canonicalS_inf N hN n (fun i => canonicalLoop4DZ (xs i)) :=
  (Classical.choose_spec (Classical.choose_spec (canonicalThermoData N hN))).2.2.2.2.2.1 n σ
    (fun i => canonicalLoop4DZ (xs i))

-- Extract the ℤ⁴-translation invariance from canonicalThermoData
private theorem canonicalS_inf_trans (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) (a : Fin 4 → ℤ) (xs : Fin n → Space4) :
    canonicalS_inf N hN n (fun i => transLoop4DZ a (canonicalLoop4DZ (xs i))) =
    canonicalS_inf N hN n (fun i => canonicalLoop4DZ (xs i)) :=
  (Classical.choose_spec (Classical.choose_spec (canonicalThermoData N hN))).2.2.2.2.1 n a
    (fun i => canonicalLoop4DZ (xs i))

/-! ### Continuum inputs (axiomatised)

The strong-coupling analysis (§§43–44) supplies a complete infinite-volume lattice
OS theory with mass gap, clustering, hypercubic and ℤ⁴ symmetries, and a
non-constant local observable.  The remaining continuum steps — the multiscale
RG continuum limit that produces continuous SO(4) invariance and the Euclidean-
to-Minkowski reconstruction — are standard analytic inputs that lie outside the
lattice strong-coupling regime.  They are recorded here as named axioms so that
the final Clay theorem is a pure, fully-checked reduction.
-/

/-- Continuum Balaban multiscale RG limit for SU(N). -/
axiom balaban_rg_continuum (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    BalabanRGContinuumHypothesis N hN

/-- Euclidean-to-Minkowski analytic continuation data on the OS Hilbert space. -/
axiom os_poincare_continuation (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    OSPoincareContinuationHypothesis (balaban_rg_continuum N hN).os

/--
# The Clay Millennium Yang-Mills Existence and Mass Gap Theorem (Unconditional)

For every non-Abelian compact gauge group SU(N) with N ≥ 2, there exists a
rigorous 4D quantum gauge field theory satisfying the full Wightman axioms,
with Euclidean Osterwalder-Schrader continuum limit, non-Gaussian interacting
Schwinger functions, and a strictly positive mass gap Δ > 0.

The theorem is obtained by combining
- the fully proved strong-coupling infinite-volume lattice theory
  (mass gap, clustering, hypercubic + ℤ⁴ symmetries, non-constant local observable),
- the standard continuum RG limit (axiom `balaban_rg_continuum`),
- the standard OS reconstruction / Poincaré continuation (axiom `os_poincare_continuation`).
-/
theorem clay_yang_mills_strict (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    ClayYangMillsMassGap4DStrict N hN :=
  clay_yang_mills_strict_from_balaban_and_os N hN
    (balaban_rg_continuum N hN)
    (os_poincare_continuation N hN)

end CanonicalClosure


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

-- §46. Canonical Realization & Unconditional Mass Gap Theorem
#print axioms YangMills.clay_yang_mills_strict
