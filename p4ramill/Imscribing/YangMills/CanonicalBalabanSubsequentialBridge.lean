import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Imscribing.YangMills.AllDegreesSchwingerLimit
import Imscribing.YangMills.ConcreteMinimalClayReduction

/-!
# Canonical Lattice Subsequential Limit → `ConcreteBalabanTarget`

1. `continuous_of_schwartz_seminorm_bound`: upgrades any linear functional on
   `EuclideanSchwartz n` bounded by a finite sum of `SchwartzMap.seminorm`s
   to a genuine `EuclideanSchwartz n →L[ℂ] ℂ`.
2. `canonical_schwinger_clm_subseq`: extracts `CanonicalSchwingerLimitWitness`
   with continuous `S_inf n : EuclideanSchwartz n →L[ℂ] ℂ` and E3 symmetry.
3. `concrete_balaban_target_from_canonical_lattice`: constructs `ConcreteBalabanTarget N hN`
   from `CanonicalBalabanEstimates` via `borchers_axioms_of_lattice_limit` (`0 sorry`).
-/

namespace Imscribing.YangMills.CanonicalBalabanBridge

open scoped Topology
open MeasureTheory
open Imscribing.YangMills.ClaySpec
open Imscribing.YangMills.ContinuumInterfaces
open Imscribing.YangMills.WilsonLattice4D
open Imscribing.YangMills.CanonicalWilsonBridge
open Imscribing.YangMills.AllDegreesLimit
open Imscribing.YangMills.BorchersReconstruction
open Imscribing.YangMills.BorchersSchwinger
open Imscribing.YangMills.ContinuumPersistence
open Imscribing.YangMills.ConcreteTensorSchwartz
open Imscribing.YangMills.ConcreteMinimalReduction

/-- Any `ℂ`-linear functional on `EuclideanSchwartz n` bounded by a finite sum of
    `SchwartzMap.seminorm ℂ j 0` is continuous in the Schwartz topology. -/
theorem continuous_of_schwartz_seminorm_bound {n : ℕ}
    (L : EuclideanSchwartz n →ₗ[ℂ] ℂ)
    (M : ℕ) (c : ℕ → ℝ) (hc : ∀ j, 0 ≤ c j)
    (h_bd : ∀ f : EuclideanSchwartz n,
      ‖L f‖ ≤ ∑ j ∈ Finset.range (M + 1), c j * SchwartzMap.seminorm ℂ j 0 f) :
    Continuous L := by
  have h_semi_cont : ∀ j : ℕ, Continuous (fun f : EuclideanSchwartz n =>
      SchwartzMap.seminorm ℂ j 0 f) := fun j =>
    (schwartz_withSeminorms ℂ (Fin n → ContinuumInterfaces.Spacetime4) ℂ).continuous_seminorm (j, 0)
  have h_sum_cont : Continuous (fun f : EuclideanSchwartz n =>
      ∑ j ∈ Finset.range (M + 1), c j * SchwartzMap.seminorm ℂ j 0 f) :=
    continuous_finset_sum _ fun j _ => continuous_const.mul (h_semi_cont j)
  have h_at0 : ContinuousAt L 0 := by
    rw [ContinuousAt, map_zero, tendsto_iff_norm_sub_tendsto_zero]
    have h_sum_lim : Filter.Tendsto (fun f : EuclideanSchwartz n =>
        ∑ j ∈ Finset.range (M + 1), c j * SchwartzMap.seminorm ℂ j 0 f) (𝓝 0) (𝓝 0) := by
      have h0 := h_sum_cont.tendsto 0
      simpa using h0
    refine squeeze_zero (fun _ => norm_nonneg _) (fun f => ?_) h_sum_lim
    simpa using h_bd f
  exact continuous_of_continuousAt_zero L.toAddMonoidHom h_at0

/-- Continuous subsequential Schwinger limit extracted from the canonical 4D SU(N) Haar measure. -/
structure CanonicalSchwingerLimitWitness (N : ℕ) [NeZero N]
    (L : ℕ → ℕ) [∀ m, NeZero (L m)] (a β Z_ren : ℕ → ℝ) where
  φ : ℕ → ℕ
  hφ : StrictMono φ
  S_inf : ∀ n : ℕ, EuclideanSchwartz n →L[ℂ] ℂ
  h_lim : ∀ (n : ℕ) (f : EuclideanSchwartz n),
    Filter.Tendsto (fun m =>
      canonicalSmearedPlaqSchwinger N (L (φ m)) n (a (φ m)) (β (φ m)) (Z_ren (φ m)) f)
      Filter.atTop (𝓝 (S_inf n f))
  h_e3 : ∀ (n : ℕ) (π : Equiv.Perm (Fin n)) (f f_π : EuclideanSchwartz n),
    (∀ y : Fin n → ContinuumInterfaces.Spacetime4, f_π y = f (fun k => y (π k))) →
    S_inf n f_π = S_inf n f

/-- Extract `CanonicalSchwingerLimitWitness` unconditionally from `all_degrees_subsequential_schwinger_limit`. -/
noncomputable def canonical_schwinger_clm_subseq
    (N : ℕ) [NeZero N]
    (L : ℕ → ℕ) [∀ m, NeZero (L m)]
    (a β Z_ren : ℕ → ℝ) (Z_max : ℝ) (hZ_max : 0 ≤ Z_max)
    (ha : ∀ m, 0 < a m ∧ a m ≤ 1) (hβ : ∀ m, 0 ≤ β m)
    (hZ : ∀ m, |Z_ren m| ≤ Z_max)
    (D : ∀ n : ℕ, ℕ → EuclideanSchwartz n)
    (h_dense : ∀ n : ℕ, ∀ f : EuclideanSchwartz n, ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ,
        ((Z_max * 8192) ^ n * ∑ j ∈ Finset.range (8 * n + 1),
          ((8 * n).choose j : ℝ) * SchwartzMap.seminorm ℂ j 0 (f - D n k)) < ε) :
    Nonempty (CanonicalSchwingerLimitWitness N L a β Z_ren) := by
  have hex := all_degrees_subsequential_schwinger_limit N L a β Z_ren Z_max hZ_max
    ha hβ hZ D h_dense
  let φ := Classical.choose hex
  have h1 := Classical.choose_spec hex
  let S_lin := Classical.choose h1
  have h_spec := Classical.choose_spec h1
  let S_clm : ∀ n : ℕ, EuclideanSchwartz n →L[ℂ] ℂ := fun n =>
    { toLinearMap := S_lin n
      cont := by
        refine continuous_of_schwartz_seminorm_bound (S_lin n) (8 * n)
          (fun j => (Z_max * 8192) ^ n * ((8 * n).choose j : ℝ))
          (fun _ => by positivity) (fun f => ?_)
        have hbd := h_spec.2.2.1 n f
        simpa [Finset.mul_sum, mul_assoc] using hbd }
  exact ⟨{
    φ := φ
    hφ := h_spec.1
    S_inf := S_clm
    h_lim := h_spec.2.1
    h_e3 := h_spec.2.2.2 }⟩

/-- Residual weak-coupling Balaban RG & uniform mass-gap estimates on a
    `CanonicalSchwingerLimitWitness`. -/
structure CanonicalBalabanEstimates {N : ℕ} [NeZero N]
    {L : ℕ → ℕ} [∀ m, NeZero (L m)] {a β Z_ren : ℕ → ℝ}
    (W : CanonicalSchwingerLimitWitness N L a β Z_ren) where
  S_zero : W.S_inf 0 1 = 1
  linear_growth_E0 : ∃ (C α : ℝ) (k : ℕ), 0 < C ∧ 0 ≤ α ∧
    ∀ n (f : EuclideanSchwartz n),
      ‖W.S_inf n f‖ ≤ C ^ n * ((Nat.factorial n : ℝ) ^ α) * (SchwartzMap.seminorm ℂ k 0 f)
  Δ : ℝ
  Δ_pos : 0 < Δ
  nontrivial_separated_2pt :
    ∃ (f g : SchwartzMap ContinuumInterfaces.Spacetime4 ℂ),
      Disjoint (Function.support f) (Function.support g) ∧
      ∃ F : EuclideanSchwartz 2, W.S_inf 2 F ≠ 0
  B_m : ℕ → BorchersPos → BorchersPos → ℂ
  h_conv : ∀ F G : BorchersPos,
    Filter.Tendsto (fun m => B_m m F G) Filter.atTop
      (𝓝 (borchersForm
        { S := W.S_inf
          S_zero := S_zero
          linear_growth_E0 := linear_growth_E0
          cluster_rate := Δ
          cluster_rate_pos := Δ_pos
          nontrivial_separated_2pt := nontrivial_separated_2pt }
        concreteReflectTensorData F G))
  h_herm_m : ∀ m F G, B_m m G F = star (B_m m F G)
  h_rp_m : ∀ m F, 0 ≤ (B_m m F F).re
  h_symm_m : ∀ m, ∀ t : ℝ, 0 ≤ t → ∀ F G,
    B_m m F (concreteBorchersShift t G) = B_m m (concreteBorchersShift t F) G
  h_lin_m : ∀ m,
    (∀ F₁ F₂ G, B_m m (F₁ + F₂) G = B_m m F₁ G + B_m m F₂ G) ∧
    (∀ c F G, B_m m (c • F) G = star c * B_m m F G) ∧
    (∀ F G₁ G₂, B_m m F (G₁ + G₂) = B_m m F G₁ + B_m m F G₂) ∧
    (∀ c F G, B_m m F (c • G) = c * B_m m F G) ∧
    B_m m borchersVac borchersVac = 1
  h_cluster_m : ∀ m, ∀ t : ℝ, 0 ≤ t → ∀ G : BorchersPos,
    B_m m borchersVac G = 0 →
    (B_m m (concreteBorchersShift t G) (concreteBorchersShift t G)).re ≤
      Real.exp (-2 * Δ * t) * (B_m m G G).re
  v : BorchersPos
  δ : ℝ
  δ_pos : 0 < δ
  h_var_m : ∀ᶠ m in Filter.atTop, ‖B_m m borchersVac v‖ ^ 2 + δ ≤ (B_m m v v).re

/-- **Bridge from `CanonicalBalabanEstimates` to `ConcreteBalabanTarget N hN`.** -/
noncomputable def concrete_balaban_target_from_canonical_lattice
    (N : ℕ) (hN : 2 ≤ N)
    {L : ℕ → ℕ} [∀ m, NeZero (L m)] {a β Z_ren : ℕ → ℝ}
    (W : @CanonicalSchwingerLimitWitness N ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hN)⟩ L _ a β Z_ren)
    (E : @CanonicalBalabanEstimates N ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hN)⟩ L _ a β Z_ren W) :
    ConcreteBalabanTarget N hN :=
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hN)⟩
  let C_os : ContinuumSchwingerOS :=
    { S := W.S_inf
      S_zero := E.S_zero
      linear_growth_E0 := E.linear_growth_E0
      cluster_rate := E.Δ
      cluster_rate_pos := E.Δ_pos
      nontrivial_separated_2pt := E.nontrivial_separated_2pt }
  let h_ax := borchers_axioms_of_lattice_limit C_os concreteReflectTensorData E.B_m E.h_conv
    E.h_herm_m E.h_rp_m E.h_symm_m E.h_lin_m E.h_cluster_m
  let h_var := variance_strict_of_lattice_limit C_os concreteReflectTensorData E.B_m E.v
    (E.h_conv borchersVac E.v) (E.h_conv E.v E.v) E.δ_pos E.h_var_m
  { C := C_os
    h_herm := h_ax.1
    h_rp := h_ax.2.1
    h_symm := h_ax.2.2.1
    h_cluster := h_ax.2.2.2
    variance_elem := E.v
    variance_strict := h_var }

end Imscribing.YangMills.CanonicalBalabanBridge
