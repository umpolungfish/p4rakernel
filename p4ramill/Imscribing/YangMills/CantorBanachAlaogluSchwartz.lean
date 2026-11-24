import Imscribing.YangMills.LatticeRiemannSchwartzBound4D

/-!
# Cantor Diagonal Extraction & Schwartz Equicontinuous Continuum Limit

Proves unconditionally (`0 sorry`):
1. `cantor_diagonal_subseq`: Any pointwise-bounded `F : ℕ → ℕ → ℂ` has a strictly
   monotone subsequence `φ` converging at every `k : ℕ`.
2. `equicontinuous_dense_limit`: Any family `S_m : TestFn →ₗ[ℂ] ℂ` uniformly
   dominated by a subadditive seminorm `p` converges along a subsequence on ALL
   of `TestFn` to a linear functional `S_∞` with `‖S_∞ f‖ ≤ p f`.
3. `wilson_lattice_subsequential_schwinger_limit`: Extracts a continuum Schwartz
   distribution `S_∞` from `smearedPlaqSchwinger` along any sequence with bounded
   `Z_ren m`, preserving the uniform Schwartz seminorm bound.
-/

namespace Imscribing.YangMills.CantorSchwartzLimit

open scoped Topology
open MeasureTheory
open Imscribing.YangMills.ClaySpec
open Imscribing.YangMills.ContinuumInterfaces
open Imscribing.YangMills.WilsonLattice4D
open Imscribing.YangMills.WilsonFrobenius4D
open Imscribing.YangMills.LatticeRiemannBound4D

private lemma extract_subseq_at
    (F : ℕ → ℕ → ℂ) (k : ℕ) (B : ℝ) (hB : ∀ m, ‖F m k‖ ≤ B)
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ) :
    ∃ (L : ℂ) (σ : ℕ → ℕ), StrictMono σ ∧
      Filter.Tendsto (fun m => F (ψ (σ m)) k) Filter.atTop (𝓝 L) := by
  have h_mem : ∀ m : ℕ, F (ψ m) k ∈ Metric.closedBall (0 : ℂ) B := fun m => by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hB (ψ m)
  obtain ⟨L, _, σ, hσ, h_tend⟩ := (isCompact_closedBall (0 : ℂ) B).tendsto_subseq h_mem
  exact ⟨L, σ, hσ, h_tend⟩

/-- **Cantor Diagonal Subsequence Theorem:**
    Every pointwise-bounded sequence `F : ℕ → ℕ → ℂ` admits a strictly monotone
    subsequence `φ : ℕ → ℕ` such that `F (φ m) k` converges for every `k : ℕ`. -/
theorem cantor_diagonal_subseq (F : ℕ → ℕ → ℂ)
    (h_bd : ∀ k : ℕ, ∃ B : ℝ, ∀ m : ℕ, ‖F m k‖ ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ k : ℕ, ∃ L : ℂ, Filter.Tendsto (fun m => F (φ m) k) Filter.atTop (𝓝 L) := by
  let S : Type := { ψ : ℕ → ℕ // StrictMono ψ }
  let next : ℕ → S → S := fun k s =>
    let ex := extract_subseq_at F k (Classical.choose (h_bd k))
      (Classical.choose_spec (h_bd k)) s.1 s.2
    ⟨s.1 ∘ Classical.choose (Classical.choose_spec ex),
      s.2.comp (Classical.choose_spec (Classical.choose_spec ex)).1⟩
  let step : ℕ → S
    | 0 => ⟨id, strictMono_id⟩
    | k + 1 => next k (step k)
  have h_step_sub : ∀ k : ℕ, ∃ (L : ℂ) (σ : ℕ → ℕ), StrictMono σ ∧
      (step (k + 1)).1 = (step k).1 ∘ σ ∧
      Filter.Tendsto (fun n => F ((step (k + 1)).1 n) k) Filter.atTop (𝓝 L) := by
    intro k
    let ex := extract_subseq_at F k (Classical.choose (h_bd k))
      (Classical.choose_spec (h_bd k)) (step k).1 (step k).2
    exact ⟨Classical.choose ex,
      Classical.choose (Classical.choose_spec ex),
      (Classical.choose_spec (Classical.choose_spec ex)).1,
      rfl,
      (Classical.choose_spec (Classical.choose_spec ex)).2⟩
  have h_step_le : ∀ a b : ℕ, a ≤ b →
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ (step b).1 = (step a).1 ∘ τ := by
    intro a b hab
    induction b with
    | zero =>
        have ha0 : a = 0 := Nat.le_zero.mp hab
        subst ha0
        exact ⟨id, strictMono_id, rfl⟩
    | succ b ih =>
        by_cases ha : a = b + 1
        · subst ha; exact ⟨id, strictMono_id, rfl⟩
        · have hab' : a ≤ b := by omega
          obtain ⟨τ, hτ, h_eq⟩ := ih hab'
          obtain ⟨_, σ, hσ, h_next, _⟩ := h_step_sub b
          refine ⟨τ ∘ σ, hτ.comp hσ, ?_⟩
          rw [h_next, h_eq, Function.comp_assoc]
  let φ : ℕ → ℕ := fun k => (step k).1 k
  have hφ_mono : StrictMono φ := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    obtain ⟨_, σ, hσ, h_eq, _⟩ := h_step_sub k
    have hk_le : k + 1 ≤ σ (k + 1) := hσ.id_le (k + 1)
    have hlt1 : (step k).1 k < (step k).1 (k + 1) := (step k).2 (Nat.lt_succ_self k)
    have hle2 : (step k).1 (k + 1) ≤ (step k).1 (σ (k + 1)) := (step k).2.monotone hk_le
    change (step k).1 k < (step (k + 1)).1 (k + 1)
    rw [h_eq]
    exact lt_of_lt_of_le hlt1 hle2
  refine ⟨φ, hφ_mono, fun k => ?_⟩
  obtain ⟨L, _, _, _, h_lim⟩ := h_step_sub k
  refine ⟨L, ?_⟩
  rw [Metric.tendsto_atTop] at h_lim ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := h_lim ε hε
  refine ⟨max N (k + 1), fun m hm => ?_⟩
  have hk1_le_m : k + 1 ≤ m := le_trans (le_max_right _ _) hm
  obtain ⟨τ, hτ, h_eq⟩ := h_step_le (k + 1) m hk1_le_m
  have h_ge : N ≤ τ m := le_trans (le_trans (le_max_left _ _) hm) (hτ.id_le m)
  have h_phi_m : φ m = (step (k + 1)).1 (τ m) := by
    dsimp [φ]; rw [h_eq]; rfl
  rw [h_phi_m]
  exact hN (τ m) h_ge

/-- **Equicontinuous Subsequential Limit Extension:**
    Any family of linear functionals `S_m : TestFn →ₗ[ℂ] ℂ` bounded uniformly by
    a subadditive seminorm `p` converges along a subsequence on ALL of `TestFn`
    (given a `p`-dense countable core `D : ℕ → TestFn`) to a linear
    functional `S_∞ : TestFn →ₗ[ℂ] ℂ` with `‖S_∞ f‖ ≤ p f`. -/
theorem equicontinuous_dense_limit
    {TestFn : Type*} [AddCommGroup TestFn] [Module ℂ TestFn]
    (p : TestFn → ℝ) (hp_nn : ∀ f, 0 ≤ p f)
    (hp_add : ∀ f g, p (f + g) ≤ p f + p g) (hp_neg : ∀ f, p (-f) = p f)
    (D : ℕ → TestFn) (h_dense : ∀ f : TestFn, ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, p (f - D k) < ε)
    (S_m : ℕ → TestFn →ₗ[ℂ] ℂ)
    (h_unif : ∀ m (f : TestFn), ‖S_m m f‖ ≤ p f) :
    ∃ (φ : ℕ → ℕ) (S_inf : TestFn →ₗ[ℂ] ℂ),
      StrictMono φ ∧
      (∀ f : TestFn, Filter.Tendsto (fun m => S_m (φ m) f) Filter.atTop (𝓝 (S_inf f))) ∧
      (∀ f : TestFn, ‖S_inf f‖ ≤ p f) := by
  obtain ⟨φ, hφ, h_dense_lim⟩ :=
    cantor_diagonal_subseq (fun m k => S_m m (D k)) (fun k => ⟨p (D k), fun m => h_unif m (D k)⟩)
  have h_cauchy : ∀ f : TestFn, CauchySeq (fun m => S_m (φ m) f) := by
    intro f
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨k, hk⟩ := h_dense f (ε / 3) (by linarith)
    obtain ⟨L, hL⟩ := h_dense_lim k
    have h_cau_k := hL.cauchySeq
    rw [Metric.cauchySeq_iff] at h_cau_k
    obtain ⟨N, hN⟩ := h_cau_k (ε / 3) (by linarith)
    refine ⟨N, fun m₁ hm₁ m₂ hm₂ => ?_⟩
    have h1 : ‖S_m (φ m₁) f - S_m (φ m₁) (D k)‖ < ε / 3 := by
      rw [← map_sub]
      exact lt_of_le_of_lt (h_unif (φ m₁) (f - D k)) hk
    have h2 : ‖S_m (φ m₁) (D k) - S_m (φ m₂) (D k)‖ < ε / 3 := by
      simpa [dist_eq_norm] using hN m₁ hm₁ m₂ hm₂
    have h3 : ‖S_m (φ m₂) (D k) - S_m (φ m₂) f‖ < ε / 3 := by
      rw [← map_sub, norm_sub_rev]
      exact lt_of_le_of_lt (h_unif (φ m₂) (f - D k)) hk
    rw [dist_eq_norm]
    have h_tri :
        S_m (φ m₁) f - S_m (φ m₂) f =
          (S_m (φ m₁) f - S_m (φ m₁) (D k)) +
          (S_m (φ m₁) (D k) - S_m (φ m₂) (D k)) +
          (S_m (φ m₂) (D k) - S_m (φ m₂) f) := by ring
    rw [h_tri]
    calc
      ‖_ + _ + _‖ ≤ ‖S_m (φ m₁) f - S_m (φ m₁) (D k)‖ +
          ‖S_m (φ m₁) (D k) - S_m (φ m₂) (D k)‖ +
          ‖S_m (φ m₂) (D k) - S_m (φ m₂) f‖ :=
          le_trans (norm_add_le _ _) (add_le_add_right (norm_add_le _ _) _)
      _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add h1 h2) h3
      _ = ε := by ring
  have h_ex : ∀ f : TestFn, ∃ z : ℂ,
      Filter.Tendsto (fun m => S_m (φ m) f) Filter.atTop (𝓝 z) :=
    fun f => cauchySeq_tendsto_of_complete (h_cauchy f)
  let S_fun : TestFn → ℂ := fun f => Classical.choose (h_ex f)
  have h_spec : ∀ f : TestFn,
      Filter.Tendsto (fun m => S_m (φ m) f) Filter.atTop (𝓝 (S_fun f)) :=
    fun f => Classical.choose_spec (h_ex f)
  let S_inf : TestFn →ₗ[ℂ] ℂ :=
    { toFun := S_fun
      map_add' := fun f g => by
        have hsum : Filter.Tendsto (fun m => S_m (φ m) (f + g)) Filter.atTop
            (𝓝 (S_fun f + S_fun g)) := by
          simp_rw [map_add]; exact (h_spec f).add (h_spec g)
        exact tendsto_nhds_unique (h_spec (f + g)) hsum
      map_smul' := fun c f => by
        have hsm : Filter.Tendsto (fun m => S_m (φ m) (c • f)) Filter.atTop
            (𝓝 (c • S_fun f)) := by
          simp_rw [map_smul]; exact (h_spec f).const_smul c
        exact tendsto_nhds_unique (h_spec (c • f)) hsm }
  have h_bd : ∀ f : TestFn, ‖S_inf f‖ ≤ p f := by
    intro f
    have h_norm : Filter.Tendsto (fun m => ‖S_m (φ m) f‖) Filter.atTop (𝓝 ‖S_inf f‖) :=
      (continuous_norm.tendsto _).comp (h_spec f)
    exact le_of_tendsto h_norm (Filter.Eventually.of_forall fun m => h_unif (φ m) f)
  exact ⟨φ, S_inf, hφ, h_spec, h_bd⟩

/-- **Subsequential Continuum Schwinger Distribution from 4D SU(N) Lattice Wilson Measures:**
    For any sequence of volumes `L m ≥ 1`, spacings `a m ∈ (0, 1]`, couplings `β m ≥ 0`,
    and bounded renormalization `|Z_ren m| ≤ Z_max`, `smearedPlaqSchwinger` admits a
    convergent subsequence to a linear Schwartz distribution `S_∞` with E0 continuity bound. -/
theorem wilson_lattice_subsequential_schwinger_limit
    (N n : ℕ) [NeZero N]
    (L : ℕ → ℕ) [∀ m, NeZero (L m)]
    (a β Z_ren : ℕ → ℝ) (Z_max : ℝ) (hZ_max : 0 ≤ Z_max)
    (ha : ∀ m, 0 < a m ∧ a m ≤ 1) (hβ : ∀ m, 0 ≤ β m)
    (hZ : ∀ m, |Z_ren m| ≤ Z_max)
    (h_meas_sp : ∀ m, MeasurableSpace (LinkConfig N (L m)))
    (μ : ∀ m, @Measure (LinkConfig N (L m)) (h_meas_sp m))
    (h_prob : ∀ m, @IsProbabilityMeasure (LinkConfig N (L m)) (h_meas_sp m) (μ m))
    (h_act_meas : ∀ m, @Measurable _ _ (h_meas_sp m) _ (fun U => wilsonAction N (L m) (β m) U))
    (h_prod_meas : ∀ m (xs : Fin n → Lat4 (L m)),
      @Measurable _ _ (h_meas_sp m) _ (fun U => (∏ k : Fin n, localPlaqDensity N (L m) U (xs k) : ℂ)))
    (D : ℕ → EuclideanSchwartz n)
    (h_dense : ∀ f : EuclideanSchwartz n, ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ,
        ((Z_max * 8192) ^ n * ∑ j ∈ Finset.range (8 * n + 1),
          ((8 * n).choose j : ℝ) * SchwartzMap.seminorm ℂ j 0 (f - D k)) < ε) :
    let p : EuclideanSchwartz n → ℝ := fun f =>
      (Z_max * 8192) ^ n * ∑ j ∈ Finset.range (8 * n + 1),
        ((8 * n).choose j : ℝ) * SchwartzMap.seminorm ℂ j 0 f
    ∃ (φ : ℕ → ℕ) (S_∞ : EuclideanSchwartz n →ₗ[ℂ] ℂ),
      StrictMono φ ∧
      (∀ f : EuclideanSchwartz n,
        Filter.Tendsto (fun m =>
          @smearedPlaqSchwinger N (L (φ m)) n _ (a (φ m)) (β (φ m)) (Z_ren (φ m))
            (h_meas_sp (φ m)) (μ (φ m)) f)
          Filter.atTop (𝓝 (S_∞ f))) ∧
      (∀ f : EuclideanSchwartz n, ‖S_∞ f‖ ≤ p f) := by
  intro p
  have hp_nn : ∀ f, 0 ≤ p f := fun f => by
    dsimp [p]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ =>
      mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))
  have hp_add : ∀ f g, p (f + g) ≤ p f + p g := fun f g => by
    dsimp [p]
    rw [← mul_add, ← Finset.sum_add_distrib]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by positivity)
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (map_add_le_add (SchwartzMap.seminorm ℂ j 0) f g)
      (Nat.cast_nonneg _)
  have hp_neg : ∀ f, p (-f) = p f := fun f => by
    dsimp [p]
    refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
    rw [map_neg_eq_map]
  let S_m : ℕ → EuclideanSchwartz n →ₗ[ℂ] ℂ := fun m =>
    @smearedPlaqSchwinger N (L m) n _ (a m) (β m) (Z_ren m) (h_meas_sp m) (μ m)
  have h_unif : ∀ m (f : EuclideanSchwartz n), ‖S_m m f‖ ≤ p f := by
    intro m f
    letI := h_meas_sp m
    letI := h_prob m
    have h1 := smearedPlaqSchwinger_uniform_schwartz_bound N (L m) n
      (ha m).1 (ha m).2 (hβ m) (Z_ren m) (μ m) (h_act_meas m) (h_prod_meas m) f
    refine le_trans h1 ?_
    dsimp [p]
    gcongr
    · exact hZ m
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)
  exact equicontinuous_dense_limit p hp_nn hp_add hp_neg D h_dense S_m h_unif

end Imscribing.YangMills.CantorSchwartzLimit