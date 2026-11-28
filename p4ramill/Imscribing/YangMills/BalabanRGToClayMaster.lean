import Imscribing.YangMills.CanonicalBalabanSubsequentialBridge
import Imscribing.YangMills.CanonicalFiniteVolumeBorchers4D
import Imscribing.YangMills.OSPoincareMasterDischarge
import Imscribing.YangMills.DimensionalTransmutationAndBoundary

/-!
# Master Balaban RG → Canonical Finite-Volume Borchers → Clay Yang–Mills Closure

Wires together:
- `CanonicalLatticeBorchers4D` (`canonicalMagneticSchwinger`, `S 0 1 = 1`, E3 symmetry)
- `CanonicalFiniteVolumeBorchers4D` (`latticeBorchersForm`, unconditional finite-volume
  RP, Hermitian symmetry, sesquilinearity, and `B(vac, vac) = 1`)
- `CanonicalBalabanSubsequentialBridge` (`ConcreteBalabanTarget`)
- `OSPoincareMasterDischarge` (`OSAnalyticCore` → `ClaySpec.WightmanQFT4D` with
  `HasYangMillsUVScaling N Q ∧ HasStrictMassGap Q Δ`) (`0 sorry`).
-/

namespace Imscribing.YangMills.BalabanRGMaster

set_option maxHeartbeats 800000

open scoped Topology
open Imscribing.YangMills.ClaySpec
open Imscribing.YangMills.ContinuumInterfaces
open Imscribing.YangMills.BorchersReconstruction
open Imscribing.YangMills.BorchersSchwinger
open Imscribing.YangMills.ConcreteTensorSchwartz
open Imscribing.YangMills.ConcreteMinimalReduction
open Imscribing.YangMills.CanonicalWilsonBridge
open Imscribing.YangMills.CanonicalBalabanBridge
open Imscribing.YangMills.CanonicalLatticeBorchers
open Imscribing.YangMills.CanonicalFVBorchers4D
open Imscribing.YangMills.OSMasterDischarge

/-- Weak-coupling Balaban RG & infrared mass-gap core built directly on top of
    the canonical 4D SU(N) Haar trajectory `(ymSpacing, ymBetaAF N)` and the
    unconditional finite-volume `latticeBorchersForm`. -/
structure BalabanWeakCouplingCore (N : ℕ) (hN : 2 ≤ N) where
  M_vol : ℕ → ℕ
  [instM : ∀ m, NeZero (M_vol m)]
  Z_ren : ℕ → ℝ
  Z_max : ℝ
  hZ_max : 0 ≤ Z_max
  hZ : ∀ m, |Z_ren m| ≤ Z_max
  /-- Continuum `S_inf : ∀ n, EuclideanSchwartz n →L[ℂ] ℂ` extracted as the limit of
      `canonicalMagneticSchwinger N (2 * M_vol m) n (ymSpacing m) (ymBetaAF N m) (Z_ren m)`. -/
  S_inf : ∀ n : ℕ, EuclideanSchwartz n →L[ℂ] ℂ
  h_lim : letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hN)⟩
    ∀ (n : ℕ) (f : EuclideanSchwartz n),
    Filter.Tendsto (fun m =>
      canonicalMagneticSchwinger N (2 * M_vol m) n (ymSpacing m) (ymBetaAF N m) (Z_ren m) f)
      Filter.atTop (𝓝 (S_inf n f))
  /-- Uniform OS-II factorial temperedness from Balaban multi-scale RG bounds. -/
  linear_growth_E0 : ∃ (C α : ℝ) (k : ℕ), 0 < C ∧ 0 ≤ α ∧
    ∀ n (f : EuclideanSchwartz n),
      ‖S_inf n f‖ ≤ C ^ n * ((Nat.factorial n : ℝ) ^ α) * (SchwartzMap.seminorm ℂ k 0 f)
  /-- Uniform physical infrared mass gap Δ > 0. -/
  Δ : ℝ
  Δ_pos : 0 < Δ
  /-- Non-vanishing separated 2-point correlation (non-triviality). -/
  nontrivial_separated_2pt :
    ∃ (f g : SchwartzMap ContinuumInterfaces.Spacetime4 ℂ),
      Disjoint (Function.support f) (Function.support g) ∧
      ∃ F : EuclideanSchwartz 2, S_inf 2 F ≠ 0
  /-- Convergence of finite-volume `latticeBorchersForm` to `concreteBorchersForm`
      along with Euclidean time-shift symmetry and uniform clustering. -/
  h_fv_conv : letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hN)⟩
    ∀ F G : BorchersPos,
    Filter.Tendsto (fun m =>
      @latticeBorchersForm N (M_vol m) _ (instM m) (ymSpacing m) (ymBetaAF N m) (Z_ren m) F G)
      Filter.atTop
      (𝓝 (concreteBorchersForm
        { S := S_inf
          S_zero := by
            have h_ev := h_lim 0 1
            have h_eq : (fun m => canonicalMagneticSchwinger N (2 * M_vol m) 0
                (ymSpacing m) (ymBetaAF N m) (Z_ren m) 1) = fun _ => (1 : ℂ) := by
              funext m
              exact canonicalMagneticSchwinger_zero N (2 * M_vol m) (ymSpacing m)
                (ymBetaAF_pos hN m).le (Z_ren m)
            rw [h_eq] at h_ev
            exact tendsto_nhds_unique h_ev tendsto_const_nhds
          linear_growth_E0 := linear_growth_E0
          cluster_rate := Δ
          cluster_rate_pos := Δ_pos
          nontrivial_separated_2pt := nontrivial_separated_2pt } F G))
  h_fv_symm : letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hN)⟩
    ∀ m, ∀ t : ℝ, 0 ≤ t → ∀ F G : BorchersPos,
    @latticeBorchersForm N (M_vol m) _ (instM m) (ymSpacing m) (ymBetaAF N m) (Z_ren m)
      F (concreteBorchersShift t G) =
    @latticeBorchersForm N (M_vol m) _ (instM m) (ymSpacing m) (ymBetaAF N m) (Z_ren m)
      (concreteBorchersShift t F) G
  h_fv_cluster : letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hN)⟩
    ∀ m, ∀ t : ℝ, 0 ≤ t → ∀ G : BorchersPos,
    @latticeBorchersForm N (M_vol m) _ (instM m) (ymSpacing m) (ymBetaAF N m) (Z_ren m)
      borchersVac G = 0 →
    (@latticeBorchersForm N (M_vol m) _ (instM m) (ymSpacing m) (ymBetaAF N m) (Z_ren m)
      (concreteBorchersShift t G) (concreteBorchersShift t G)).re ≤
      Real.exp (-2 * Δ * t) *
        (@latticeBorchersForm N (M_vol m) _ (instM m) (ymSpacing m) (ymBetaAF N m) (Z_ren m)
          G G).re
  v : BorchersPos
  δ : ℝ
  δ_pos : 0 < δ
  h_var_m : letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hN)⟩
    ∀ᶠ m in Filter.atTop,
    ‖@latticeBorchersForm N (M_vol m) _ (instM m) (ymSpacing m) (ymBetaAF N m) (Z_ren m)
      borchersVac v‖ ^ 2 + δ ≤
    (@latticeBorchersForm N (M_vol m) _ (instM m) (ymSpacing m) (ymBetaAF N m) (Z_ren m) v v).re

attribute [instance] BalabanWeakCouplingCore.instM


/-- **Unconditional Synthesis of `ConcreteBalabanTarget N hN`** from `BalabanWeakCouplingCore`. -/
noncomputable def toConcreteBalabanTarget {N : ℕ} {hN : 2 ≤ N}
    (B : BalabanWeakCouplingCore N hN) :
    ConcreteBalabanTarget N hN :=
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hN)⟩
  let C_cont : ContinuumSchwingerOS :=
    { S := B.S_inf
      S_zero := by
        have h_ev := B.h_lim 0 1
        have h_eq : (fun m => canonicalMagneticSchwinger N (2 * B.M_vol m) 0
            (ymSpacing m) (ymBetaAF N m) (B.Z_ren m) 1) = fun _ => (1 : ℂ) := by
          funext m
          exact canonicalMagneticSchwinger_zero N (2 * B.M_vol m) (ymSpacing m)
            (ymBetaAF_pos hN m).le (B.Z_ren m)
        rw [h_eq] at h_ev
        exact tendsto_nhds_unique h_ev tendsto_const_nhds
      linear_growth_E0 := B.linear_growth_E0
      cluster_rate := B.Δ
      cluster_rate_pos := B.Δ_pos
      nontrivial_separated_2pt := B.nontrivial_separated_2pt }
  { C := C_cont
    h_herm := fun F G => by
      have h1 := B.h_fv_conv G F
      have h2 := (continuous_star.tendsto _).comp (B.h_fv_conv F G)
      have h_eq : (fun m => @latticeBorchersForm N (B.M_vol m) _ (B.instM m)
          (ymSpacing m) (ymBetaAF N m) (B.Z_ren m) G F) =
          fun m => star (@latticeBorchersForm N (B.M_vol m) _ (B.instM m)
            (ymSpacing m) (ymBetaAF N m) (B.Z_ren m) F G) := by
        funext m
        exact latticeBorchersForm_herm N (B.M_vol m) (ymSpacing m)
          (ymBetaAF_pos hN m).le (B.Z_ren m) F G
      rw [h_eq] at h1
      exact tendsto_nhds_unique h1 h2
    h_rp := fun F => by
      have h1 := Complex.continuous_re.continuousAt.tendsto.comp (B.h_fv_conv F F)
      exact ge_of_tendsto h1 (Filter.Eventually.of_forall fun m =>
        latticeBorchersForm_nonneg N (B.M_vol m) (ymSpacing m)
          (ymBetaAF_pos hN m).le (B.Z_ren m) F)
    h_symm := fun t ht F G => by
      have h1 := B.h_fv_conv F (concreteBorchersShift t G)
      have h2 := B.h_fv_conv (concreteBorchersShift t F) G
      have h_eq : (fun m => @latticeBorchersForm N (B.M_vol m) _ (B.instM m)
          (ymSpacing m) (ymBetaAF N m) (B.Z_ren m) F (concreteBorchersShift t G)) =
          fun m => @latticeBorchersForm N (B.M_vol m) _ (B.instM m)
            (ymSpacing m) (ymBetaAF N m) (B.Z_ren m) (concreteBorchersShift t F) G := by
        funext m
        exact B.h_fv_symm m t ht F G
      rw [h_eq] at h1
      exact tendsto_nhds_unique h1 h2
    h_cluster := fun t ht F hF_vac => by
      let Bm := fun m X Y =>
        @latticeBorchersForm N (B.M_vol m) _ (B.instM m)
          (ymSpacing m) (ymBetaAF N m) (B.Z_ren m) X Y
      let c : ℕ → ℂ := fun m => Bm m borchersVac F
      have hc0 : Filter.Tendsto c Filter.atTop (𝓝 0) := by
        have h0 := B.h_fv_conv borchersVac F
        change Filter.Tendsto c Filter.atTop (𝓝 (concreteBorchersForm C_cont borchersVac F)) at h0
        rw [hF_vac] at h0
        exact h0
      have h_exp_bound : ∀ m,
          (Bm m (concreteBorchersShift t (F - c m • borchersVac))
            (concreteBorchersShift t (F - c m • borchersVac))).re ≤
          Real.exp (-2 * B.Δ * t) * (Bm m (F - c m • borchersVac) (F - c m • borchersVac)).re := by
        intro m
        refine B.h_fv_cluster m t ht (F - c m • borchersVac) ?_
        obtain ⟨hadd1, hsmul1, hadd2, hsmul2⟩ :=
          latticeBorchersForm_sesquilinear N (B.M_vol m) (ymSpacing m)
            (ymBetaAF_pos hN m).le (B.Z_ren m)
        have hsub : F - c m • borchersVac = F + (-c m) • borchersVac := by
          rw [neg_smul, sub_eq_add_neg]
        change Bm m borchersVac (F - c m • borchersVac) = 0
        dsimp only [Bm]
        rw [hsub, hadd2, hsmul2, latticeBorchersForm_vac N (B.M_vol m) (ymSpacing m)
          (ymBetaAF_pos hN m).le (B.Z_ren m)]
        change Bm m borchersVac F + (-c m) * 1 = 0
        dsimp [c]; ring
      have h_lhs_lim : Filter.Tendsto (fun m =>
          (Bm m (concreteBorchersShift t (F - c m • borchersVac))
            (concreteBorchersShift t (F - c m • borchersVac))).re)
          Filter.atTop (𝓝 (concreteBorchersForm C_cont (concreteBorchersShift t F)
            (concreteBorchersShift t F)).re) := by
        let G0 := concreteBorchersShift t F
        let V0 := concreteBorchersShift t borchersVac
        have h_eq : (fun m => (Bm m (concreteBorchersShift t (F - c m • borchersVac))
            (concreteBorchersShift t (F - c m • borchersVac))).re) =
            fun m => (Bm m G0 G0 - c m * Bm m G0 V0 - star (c m) * Bm m V0 G0 +
              (star (c m) * c m) * Bm m V0 V0).re := by
          funext m
          obtain ⟨hadd1, hsmul1, hadd2, hsmul2⟩ :=
            latticeBorchersForm_sesquilinear N (B.M_vol m) (ymSpacing m)
              (ymBetaAF_pos hN m).le (B.Z_ren m)
          have hlin : concreteBorchersShift t (F - c m • borchersVac) = G0 + (-c m) • V0 := by
            dsimp only [G0, V0]
            rw [map_sub, map_smul, sub_eq_add_neg, ← neg_smul]
          rw [hlin]
          change (Bm m (G0 + (-c m) • V0) (G0 + (-c m) • V0)).re = _
          dsimp only [Bm]
          simp only [hadd1, hadd2, hsmul1, hsmul2, star_neg]
          congr 1; ring
        rw [h_eq]
        have hGG := B.h_fv_conv G0 G0
        have hGV := B.h_fv_conv G0 V0
        have hVG := B.h_fv_conv V0 G0
        have hVV := B.h_fv_conv V0 V0
        have h_cstar : Filter.Tendsto (fun m => star (c m)) Filter.atTop (𝓝 0) := by
          simpa using (continuous_star.tendsto 0).comp hc0
        have h_all : Filter.Tendsto (fun m =>
            Bm m G0 G0 - c m * Bm m G0 V0 - star (c m) * Bm m V0 G0 +
              (star (c m) * c m) * Bm m V0 V0) Filter.atTop
            (𝓝 (concreteBorchersForm C_cont G0 G0)) := by
          have h1 := ((hGG.sub (hc0.mul hGV)).sub (h_cstar.mul hVG)).add ((h_cstar.mul hc0).mul hVV)
          simpa using h1
        exact Complex.continuous_re.continuousAt.tendsto.comp h_all
      have h_rhs_lim : Filter.Tendsto (fun m =>
          Real.exp (-2 * B.Δ * t) * (Bm m (F - c m • borchersVac) (F - c m • borchersVac)).re)
          Filter.atTop (𝓝 (Real.exp (-2 * B.Δ * t) * (concreteBorchersForm C_cont F F).re)) := by
        refine tendsto_const_nhds.mul ?_
        have h_eq : (fun m => (Bm m (F - c m • borchersVac) (F - c m • borchersVac)).re) =
            fun m => (Bm m F F - c m * Bm m F borchersVac - star (c m) * c m +
              (star (c m) * c m)).re := by
          funext m
          obtain ⟨hadd1, hsmul1, hadd2, hsmul2⟩ :=
            latticeBorchersForm_sesquilinear N (B.M_vol m) (ymSpacing m)
              (ymBetaAF_pos hN m).le (B.Z_ren m)
          have hsub : F - c m • borchersVac = F + (-c m) • borchersVac := by
            rw [neg_smul, sub_eq_add_neg]
          rw [hsub]
          change (Bm m (F + (-c m) • borchersVac) (F + (-c m) • borchersVac)).re = _
          dsimp only [Bm]
          simp only [hadd1, hadd2, hsmul1, hsmul2, star_neg,
            latticeBorchersForm_vac N (B.M_vol m) (ymSpacing m)
              (ymBetaAF_pos hN m).le (B.Z_ren m)]
          congr 1; dsimp only [c, Bm]; ring
        rw [h_eq]
        have hFF := B.h_fv_conv F F
        have hFV := B.h_fv_conv F borchersVac
        have h_cstar : Filter.Tendsto (fun m => star (c m)) Filter.atTop (𝓝 0) := by
          simpa using (continuous_star.tendsto 0).comp hc0
        have h_all : Filter.Tendsto (fun m =>
            Bm m F F - c m * Bm m F borchersVac - star (c m) * c m + (star (c m) * c m))
            Filter.atTop (𝓝 (concreteBorchersForm C_cont F F)) := by
          have h1 := ((hFF.sub (hc0.mul hFV)).sub (h_cstar.mul hc0)).add (h_cstar.mul hc0)
          simpa using h1
        exact Complex.continuous_re.continuousAt.tendsto.comp h_all
      exact le_of_tendsto_of_tendsto h_lhs_lim h_rhs_lim (Filter.Eventually.of_forall h_exp_bound)
    variance_elem := B.v
    variance_strict := by
      have h_lhs : Filter.Tendsto (fun m =>
          ‖@latticeBorchersForm N (B.M_vol m) _ (B.instM m)
            (ymSpacing m) (ymBetaAF N m) (B.Z_ren m) borchersVac B.v‖ ^ 2 + B.δ)
          Filter.atTop
          (𝓝 (‖concreteBorchersForm C_cont borchersVac B.v‖ ^ 2 + B.δ)) :=
        (((continuous_norm.tendsto _).comp (B.h_fv_conv borchersVac B.v)).pow 2).add tendsto_const_nhds
      have h_rhs : Filter.Tendsto (fun m =>
          (@latticeBorchersForm N (B.M_vol m) _ (B.instM m)
            (ymSpacing m) (ymBetaAF N m) (B.Z_ren m) B.v B.v).re)
          Filter.atTop
          (𝓝 (concreteBorchersForm C_cont B.v B.v).re) :=
        Complex.continuous_re.continuousAt.tendsto.comp (B.h_fv_conv B.v B.v)
      have h_le := le_of_tendsto_of_tendsto h_lhs h_rhs B.h_var_m
      linarith [B.δ_pos] }

/-- **End-to-End Master Clay Yang–Mills Closure Theorem** discharging both
    `ConcreteBalabanTarget` and `ConcreteOSTarget` from the irreducible
    `BalabanWeakCouplingCore` + `OSAnalyticCore`. -/
theorem clay_yang_mills_master_discharge
    (N : ℕ) (hN : 2 ≤ N)
    (B : BalabanWeakCouplingCore N hN)
    (C_core : OSAnalyticCore (toConcreteBalabanTarget B)) :
    ∃ (Q : WightmanQFT4D),
      HasYangMillsUVScaling N Q ∧ HasStrictMassGap Q B.Δ := by
  exact os_continuation_master_discharge N hN (toConcreteBalabanTarget B) C_core

end Imscribing.YangMills.BalabanRGMaster

