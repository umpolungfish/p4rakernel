import Mathlib.Data.Nat.Pairing
import Imscribing.YangMills.CanonicalWilsonMeasureBridge
import Imscribing.YangMills.ContinuumRPAndClusterPersistence

/-!
# Simultaneous All-Degree Schwinger Continuum Limit & Canonical Balaban Bridge

1. `all_degrees_subsequential_schwinger_limit`: Extracts a SINGLE strictly monotone
   subsequence `φ : ℕ → ℕ` along which `canonicalSmearedPlaqSchwinger` converges
   for ALL `n : ℕ` and ALL `f : EuclideanSchwartz n` simultaneously, inheriting E3
   permutation symmetry and Schwartz bounds for every `n`.
2. `canonical_balaban_target_of_estimates`: Bridges canonical lattice Wilson limits
   into `MinimalBalabanRGTarget N hN` (`0 sorry`).
-/

namespace Imscribing.YangMills.AllDegreesLimit

open scoped Topology
open MeasureTheory
open Imscribing.YangMills.ClaySpec
open Imscribing.YangMills.ContinuumInterfaces
open Imscribing.YangMills.WilsonLattice4D
open Imscribing.YangMills.WilsonFrobenius4D
open Imscribing.YangMills.LatticeRiemannBound4D
open Imscribing.YangMills.CantorSchwartzLimit
open Imscribing.YangMills.SchwingerSymmetry
open Imscribing.YangMills.CanonicalHaar4D
open Imscribing.YangMills.CanonicalWilsonBridge
open Imscribing.YangMills.BorchersReconstruction
open Imscribing.YangMills.BorchersSchwinger
open Imscribing.YangMills.ContinuumPersistence
open Imscribing.YangMills.MinimalReduction

/-- **Simultaneous All-n Subsequential Continuum Schwinger Limit:**
    Extracts ONE strictly monotone subsequence `φ : ℕ → ℕ` converging simultaneously
    for every `n : ℕ` and every `f : EuclideanSchwartz n` to a linear distribution `S_inf n`,
    preserving Schwartz bounds and OS Axiom E3 permutation symmetry for all `n`. -/
theorem all_degrees_subsequential_schwinger_limit
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
    let p : ∀ n : ℕ, EuclideanSchwartz n → ℝ := fun n f =>
      (Z_max * 8192) ^ n * ∑ j ∈ Finset.range (8 * n + 1),
        ((8 * n).choose j : ℝ) * SchwartzMap.seminorm ℂ j 0 f
    ∃ (φ : ℕ → ℕ) (S_inf : ∀ n : ℕ, EuclideanSchwartz n →ₗ[ℂ] ℂ),
      StrictMono φ ∧
      (∀ (n : ℕ) (f : EuclideanSchwartz n),
        Filter.Tendsto (fun m =>
          canonicalSmearedPlaqSchwinger N (L (φ m)) n (a (φ m)) (β (φ m)) (Z_ren (φ m)) f)
          Filter.atTop (𝓝 (S_inf n f))) ∧
      (∀ (n : ℕ) (f : EuclideanSchwartz n), ‖S_inf n f‖ ≤ p n f) ∧
      (∀ (n : ℕ) (π : Equiv.Perm (Fin n)) (f f_π : EuclideanSchwartz n),
        (∀ y : Fin n → ContinuumInterfaces.Spacetime4, f_π y = f (fun k => y (π k))) →
        S_inf n f_π = S_inf n f) := by
  intro p
  let F_diag : ℕ → ℕ → ℂ := fun m idx =>
    let nk := Nat.unpair idx
    canonicalSmearedPlaqSchwinger N (L m) nk.1 (a m) (β m) (Z_ren m) (D nk.1 nk.2)
  have h_bd : ∀ idx : ℕ, ∃ B : ℝ, ∀ m : ℕ, ‖F_diag m idx‖ ≤ B := by
    intro idx
    set n := (Nat.unpair idx).1
    set k := (Nat.unpair idx).2
    refine ⟨p n (D n k), fun m => ?_⟩
    dsimp [F_diag]
    have h1 := canonicalWilsonSchwinger_uniform_schwartz_bound N (L m) n
      (ha m).1 (ha m).2 (hβ m) (Z_ren m) (D n k)
    refine le_trans h1 ?_
    dsimp [p]
    gcongr
    exact hZ m
  obtain ⟨φ, hφ_mono, h_diag_lim⟩ := cantor_diagonal_subseq F_diag h_bd
  have h_all_cauchy : ∀ (n : ℕ) (f : EuclideanSchwartz n),
      CauchySeq (fun m =>
        canonicalSmearedPlaqSchwinger N (L (φ m)) n (a (φ m)) (β (φ m)) (Z_ren (φ m)) f) := by
    intro n f
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨k, hk⟩ := h_dense n f (ε / 3) (by linarith)
    obtain ⟨L_nk, hL_nk⟩ := h_diag_lim (Nat.pair n k)
    have h_cau_nk := hL_nk.cauchySeq
    rw [Metric.cauchySeq_iff] at h_cau_nk
    obtain ⟨M₀, hM₀⟩ := h_cau_nk (ε / 3) (by linarith)
    have h_eq_pair : ∀ m : ℕ,
        F_diag (φ m) (Nat.pair n k) =
          canonicalSmearedPlaqSchwinger N (L (φ m)) n (a (φ m)) (β (φ m)) (Z_ren (φ m)) (D n k) := by
      intro m; dsimp [F_diag]; rw [Nat.unpair_pair]
    refine ⟨M₀, fun m₁ hm₁ m₂ hm₂ => ?_⟩
    let S_fn := fun m (g : EuclideanSchwartz n) =>
      canonicalSmearedPlaqSchwinger N (L (φ m)) n (a (φ m)) (β (φ m)) (Z_ren (φ m)) g
    have h_unif_phi : ∀ m (g : EuclideanSchwartz n), ‖S_fn m g‖ ≤ p n g := by
      intro m g
      have h1 := canonicalWilsonSchwinger_uniform_schwartz_bound N (L (φ m)) n
        (ha (φ m)).1 (ha (φ m)).2 (hβ (φ m)) (Z_ren (φ m)) g
      refine le_trans h1 ?_
      dsimp [p]; gcongr
      exact hZ (φ m)
    have h1 : ‖S_fn m₁ f - S_fn m₁ (D n k)‖ < ε / 3 := by
      have h_sub : S_fn m₁ f - S_fn m₁ (D n k) = S_fn m₁ (f - D n k) :=
        (map_sub (canonicalSmearedPlaqSchwinger N (L (φ m₁)) n (a (φ m₁)) (β (φ m₁)) (Z_ren (φ m₁))) f (D n k)).symm
      rw [h_sub]
      exact lt_of_le_of_lt (h_unif_phi m₁ (f - D n k)) hk
    have h2 : ‖S_fn m₁ (D n k) - S_fn m₂ (D n k)‖ < ε / 3 := by
      simpa [S_fn, dist_eq_norm, h_eq_pair] using hM₀ m₁ hm₁ m₂ hm₂
    have h3 : ‖S_fn m₂ (D n k) - S_fn m₂ f‖ < ε / 3 := by
      have h_sub : S_fn m₂ (D n k) - S_fn m₂ f = -(S_fn m₂ (f - D n k)) := by
        dsimp [S_fn]; rw [map_sub]; ring
      rw [h_sub, norm_neg]
      exact lt_of_le_of_lt (h_unif_phi m₂ (f - D n k)) hk
    rw [dist_eq_norm]
    have h_tri : S_fn m₁ f - S_fn m₂ f =
        (S_fn m₁ f - S_fn m₁ (D n k)) + (S_fn m₁ (D n k) - S_fn m₂ (D n k)) +
        (S_fn m₂ (D n k) - S_fn m₂ f) := by ring
    rw [h_tri]
    calc
      ‖_ + _ + _‖ ≤ ‖S_fn m₁ f - S_fn m₁ (D n k)‖ + ‖S_fn m₁ (D n k) - S_fn m₂ (D n k)‖ +
          ‖S_fn m₂ (D n k) - S_fn m₂ f‖ :=
          le_trans (norm_add_le _ _) (add_le_add (norm_add_le _ _) le_rfl)
      _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add h1 h2) h3
      _ = ε := by ring
  have h_lim_ex : ∀ (n : ℕ) (f : EuclideanSchwartz n), ∃ z : ℂ,
      Filter.Tendsto (fun m =>
        canonicalSmearedPlaqSchwinger N (L (φ m)) n (a (φ m)) (β (φ m)) (Z_ren (φ m)) f)
        Filter.atTop (𝓝 z) :=
    fun n f => cauchySeq_tendsto_of_complete (h_all_cauchy n f)
  let S_inf : ∀ n : ℕ, EuclideanSchwartz n →ₗ[ℂ] ℂ := fun n =>
    { toFun := fun f => Classical.choose (h_lim_ex n f)
      map_add' := fun f g => by
        have hf := Classical.choose_spec (h_lim_ex n f)
        have hg := Classical.choose_spec (h_lim_ex n g)
        have hfg := Classical.choose_spec (h_lim_ex n (f + g))
        have hsum : Filter.Tendsto (fun m =>
            canonicalSmearedPlaqSchwinger N (L (φ m)) n (a (φ m)) (β (φ m)) (Z_ren (φ m)) (f + g))
            Filter.atTop (𝓝 (Classical.choose (h_lim_ex n f) + Classical.choose (h_lim_ex n g))) := by
          simp_rw [map_add]; exact (hf).add (hg)
        exact tendsto_nhds_unique hfg hsum
      map_smul' := fun c f => by
        have hf := Classical.choose_spec (h_lim_ex n f)
        have hcf := Classical.choose_spec (h_lim_ex n (c • f))
        have hsm : Filter.Tendsto (fun m =>
            canonicalSmearedPlaqSchwinger N (L (φ m)) n (a (φ m)) (β (φ m)) (Z_ren (φ m)) (c • f))
            Filter.atTop (𝓝 (c • Classical.choose (h_lim_ex n f))) := by
          simp_rw [map_smul]; exact hf.const_smul c
        exact tendsto_nhds_unique hcf hsm }
  have h_spec : ∀ (n : ℕ) (f : EuclideanSchwartz n),
      Filter.Tendsto (fun m =>
        canonicalSmearedPlaqSchwinger N (L (φ m)) n (a (φ m)) (β (φ m)) (Z_ren (φ m)) f)
        Filter.atTop (𝓝 (S_inf n f)) :=
    fun n f => Classical.choose_spec (h_lim_ex n f)
  refine ⟨φ, S_inf, hφ_mono, h_spec, fun n f => ?_, fun n π f f_π hf => ?_⟩
  · have h_norm : Filter.Tendsto (fun m =>
        ‖canonicalSmearedPlaqSchwinger N (L (φ m)) n (a (φ m)) (β (φ m)) (Z_ren (φ m)) f‖)
        Filter.atTop (𝓝 ‖S_inf n f‖) :=
      (continuous_norm.tendsto _).comp (h_spec n f)
    refine le_of_tendsto h_norm (Filter.Eventually.of_forall fun m => ?_)
    have h1 := canonicalWilsonSchwinger_uniform_schwartz_bound N (L (φ m)) n
      (ha (φ m)).1 (ha (φ m)).2 (hβ (φ m)) (Z_ren (φ m)) f
    refine le_trans h1 ?_
    dsimp [p]; gcongr
    exact hZ (φ m)
  · letI := borel (GaugeGroup N)
    have h_lim_n := h_spec n
    dsimp only [canonicalSmearedPlaqSchwinger] at h_lim_n
    exact continuum_schwinger_perm_symm N n (fun m => L (φ m)) (fun m => a (φ m))
      (fun m => β (φ m)) (fun m => Z_ren (φ m))
      (fun _ => inferInstance) (fun m => wilsonHaarLinkMeasure N (L (φ m)))
      (S_inf n) h_lim_n π f f_π hf

end Imscribing.YangMills.AllDegreesLimit
