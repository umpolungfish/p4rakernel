import Imscribing.YangMills.PositiveDefiniteKernels

/-!
# 4D SU(N) Wilson Spatial Transfer Kernel: Symmetry, Bounds & Positivity

1. Defines 3D spatial link configurations `SpatConfig N L` and the exact 4D SU(N)
   Wilson transfer kernel `wilsonTransferKernel N L β μ_W U V` integrating over
   temporal gauge links `W : SpatLat L → GaugeGroup N`.
2. Proves **`wilsonTransferKernel_symm`** via `W ↦ W⁻¹` and `realTrace_inv`.
3. Proves **`wilsonTransferKernel_bounds`**: `0 < exp(-21 β |L³|) ≤ K_W(U, V) ≤ exp(3 β |L³|)`.
4. Proves **`wilsonTransferKernel_pos_semidef`**: positive semi-definiteness on all
   bounded measurable `f : SpatConfig N L → ℂ` via `W = W₂⁻¹ W₁` and
   `exp_real_posDefKernel_double_integral_nonneg`.
-/

namespace Imscribing.YangMills.LatticeTransfer4D

open MeasureTheory
open Imscribing.YangMills.WilsonLattice4D
open Imscribing.YangMills.WilsonBounds4D
open Imscribing.YangMills.LatticeRP4D
open Imscribing.YangMills.PosDefKernels

/-- 3D periodic spatial torus `(ℤ/Lℤ)³`. -/
abbrev SpatLat (L : ℕ) := Fin 3 → ZMod L

def spatStep (L : ℕ) (i : Fin 3) : SpatLat L :=
  fun j => if j = i then 1 else 0

/-- 3D spatial link configuration `U(x, i) ∈ SU(N)`. -/
abbrev SpatConfig (N L : ℕ) := SpatLat L → Fin 3 → GaugeGroup N

/-- 3D spatial plaquette holonomy. -/
def spatPlaq {N L : ℕ} (U : SpatConfig N L) (x : SpatLat L) (i j : Fin 3) : GaugeGroup N :=
  U x i * U (x + spatStep L i) j * (U (x + spatStep L j) i)⁻¹ * (U x j)⁻¹

/-- Half-weighted 3D spatial plaquette action `V_spat(U)`. -/
noncomputable def spatAction (N L : ℕ) [NeZero N] (β : ℝ) (U : SpatConfig N L) : ℝ :=
  (β / 2) * ∑ x : SpatLat L, ∑ i : Fin 3, ∑ j : Fin 3,
    (1 - realTrace (spatPlaq U x i j) / (N : ℝ))

/-- Temporal-plaquette link coupling between spatial slices `U` and `V` via `W`. -/
noncomputable def bondTraceSum {N L : ℕ} (U V : SpatConfig N L)
    (W : SpatLat L → GaugeGroup N) : ℝ :=
  ∑ x : SpatLat L, ∑ i : Fin 3,
    realTrace ((W x)⁻¹ * U x i * W (x + spatStep L i) * (V x i)⁻¹)

/-- Exact 4D SU(N) Wilson transfer kernel `K_W(U, V)` integrating out temporal links `W`. -/
noncomputable def wilsonTransferKernel (N L : ℕ) [NeZero N] (β : ℝ)
    [MeasurableSpace (SpatLat L → GaugeGroup N)] (μ_W : Measure (SpatLat L → GaugeGroup N))
    (U V : SpatConfig N L) : ℝ :=
  Real.exp (-spatAction N L β U) * Real.exp (-spatAction N L β V) *
    ∫ W : SpatLat L → GaugeGroup N, Real.exp ((β / (N : ℝ)) * bondTraceSum U V W) ∂μ_W

theorem spatAction_bounds {N L : ℕ} [NeZero N] {β : ℝ} (hβ : 0 ≤ β) (U : SpatConfig N L) :
    0 ≤ spatAction N L β U ∧
    spatAction N L β U ≤ 9 * β * ((Fintype.card (SpatLat L) : ℕ) : ℝ) := by
  unfold spatAction
  have h0 : 0 ≤ ∑ x : SpatLat L, ∑ i : Fin 3, ∑ j : Fin 3,
      (1 - realTrace (spatPlaq U x i j) / (N : ℝ)) :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => (plaquette_density_bounds _).1
  have hup : (∑ x : SpatLat L, ∑ i : Fin 3, ∑ j : Fin 3,
      (1 - realTrace (spatPlaq U x i j) / (N : ℝ))) ≤
      18 * ((Fintype.card (SpatLat L) : ℕ) : ℝ) := by
    calc
      (∑ x : SpatLat L, ∑ i : Fin 3, ∑ j : Fin 3,
          (1 - realTrace (spatPlaq U x i j) / (N : ℝ)))
          ≤ ∑ _x : SpatLat L, ∑ _i : Fin 3, ∑ _j : Fin 3, (2 : ℝ) :=
              Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ =>
                Finset.sum_le_sum fun j _ => (plaquette_density_bounds _).2
      _ = 18 * ((Fintype.card (SpatLat L) : ℕ) : ℝ) := by
            simp [Finset.sum_const, Finset.card_univ]; ring
  refine ⟨mul_nonneg (by positivity) h0, ?_⟩
  have h1 := mul_le_mul_of_nonneg_left hup (by positivity : 0 ≤ β / 2)
  linarith

theorem bondTraceSum_abs_le {N L : ℕ} [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (U V : SpatConfig N L) (W : SpatLat L → GaugeGroup N) :
    |(β / (N : ℝ)) * bondTraceSum U V W| ≤ 3 * β * ((Fintype.card (SpatLat L) : ℕ) : ℝ) := by
  have hN : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  rw [abs_mul, abs_of_nonneg (div_nonneg hβ hN.le)]
  unfold bondTraceSum
  have hsum : |∑ x : SpatLat L, ∑ i : Fin 3,
      realTrace ((W x)⁻¹ * U x i * W (x + spatStep L i) * (V x i)⁻¹)| ≤
      3 * (N : ℝ) * ((Fintype.card (SpatLat L) : ℕ) : ℝ) := by
    calc
      |∑ x : SpatLat L, ∑ i : Fin 3, _|
          ≤ ∑ x : SpatLat L, |∑ i : Fin 3, _| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x : SpatLat L, (3 * (N : ℝ)) := by
            refine Finset.sum_le_sum fun x _ => ?_
            calc
              |∑ i : Fin 3, _| ≤ ∑ i : Fin 3, |_| := Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ _i : Fin 3, (N : ℝ) := Finset.sum_le_sum fun i _ => realTrace_abs_le _
              _ = 3 * (N : ℝ) := by simp [Finset.sum_const]
      _ = 3 * (N : ℝ) * ((Fintype.card (SpatLat L) : ℕ) : ℝ) := by
            simp [Finset.sum_const, Finset.card_univ]; ring
  have h_le := mul_le_mul_of_nonneg_left hsum (div_nonneg hβ hN.le)
  have heq : (β / (N : ℝ)) * (3 * (N : ℝ) * ((Fintype.card (SpatLat L) : ℕ) : ℝ)) =
      3 * β * ((Fintype.card (SpatLat L) : ℕ) : ℝ) := by field_simp [hN.ne']
  rwa [heq] at h_le

private lemma bondTraceSum_inv (U V : SpatConfig N L) (W : SpatLat L → GaugeGroup N) :
    bondTraceSum V U (fun x => (W x)⁻¹) = bondTraceSum U V W := by
  unfold bondTraceSum
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  have h_conj : ((W x)⁻¹)⁻¹ * V x i * (W (x + spatStep L i))⁻¹ * (U x i)⁻¹ =
      (W x) * (((W x)⁻¹ * U x i * W (x + spatStep L i) * (V x i)⁻¹)⁻¹) * (W x)⁻¹ := by
    group
  rw [h_conj, realTrace_conj, realTrace_inv]

/-- **Exact Symmetry of the 4D SU(N) Wilson Transfer Kernel:** `K_W(U, V) = K_W(V, U)`
    when `μ_W` is invariant under point-wise group inversion `W ↦ W⁻¹`. -/
theorem wilsonTransferKernel_symm (N L : ℕ) [NeZero N] (β : ℝ)
    [MeasurableSpace (SpatLat L → GaugeGroup N)] (μ_W : Measure (SpatLat L → GaugeGroup N))
    (h_inv_mp : Measure.map (fun W : SpatLat L → GaugeGroup N => fun x => (W x)⁻¹) μ_W = μ_W)
    (h_inv_meas : Measurable (fun W : SpatLat L → GaugeGroup N => fun x => (W x)⁻¹))
    (h_bond_meas : ∀ U V, Measurable (fun W => Real.exp ((β / (N : ℝ)) * bondTraceSum U V W)))
    (U V : SpatConfig N L) :
    wilsonTransferKernel N L β μ_W U V = wilsonTransferKernel N L β μ_W V U := by
  unfold wilsonTransferKernel
  have h_int : ∫ W, Real.exp ((β / (N : ℝ)) * bondTraceSum U V W) ∂μ_W =
      ∫ W, Real.exp ((β / (N : ℝ)) * bondTraceSum V U W) ∂μ_W := by
    conv_rhs => rw [← h_inv_mp, integral_map h_inv_meas.aemeasurable (h_bond_meas V U).aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    rw [bondTraceSum_inv]
  rw [h_int]; ring

/-- **Strict Uniform Positive Lower and Upper Bounds on `K_W(U, V)`.** -/
theorem wilsonTransferKernel_bounds (N L : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    [MeasurableSpace (SpatLat L → GaugeGroup N)] (μ_W : Measure (SpatLat L → GaugeGroup N))
    [IsProbabilityMeasure μ_W]
    (h_bond_meas : ∀ U V, Measurable (fun W => Real.exp ((β / (N : ℝ)) * bondTraceSum U V W)))
    (U V : SpatConfig N L) :
    0 < Real.exp (-(21 * β * ((Fintype.card (SpatLat L) : ℕ) : ℝ))) ∧
    Real.exp (-(21 * β * ((Fintype.card (SpatLat L) : ℕ) : ℝ))) ≤
      wilsonTransferKernel N L β μ_W U V ∧
    wilsonTransferKernel N L β μ_W U V ≤
      Real.exp (3 * β * ((Fintype.card (SpatLat L) : ℕ) : ℝ)) := by
  set C := ((Fintype.card (SpatLat L) : ℕ) : ℝ)
  have hU := spatAction_bounds hβ U
  have hV := spatAction_bounds hβ V
  have h_int_bnd : Integrable (fun W => Real.exp ((β / (N : ℝ)) * bondTraceSum U V W)) μ_W :=
    Integrable.of_bound (h_bond_meas U V).aestronglyMeasurable (Real.exp (3 * β * C))
      (Filter.Eventually.of_forall fun W => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) (bondTraceSum_abs_le hβ U V W)))
  have h_int_lo : Real.exp (-(3 * β * C)) ≤
      ∫ W, Real.exp ((β / (N : ℝ)) * bondTraceSum U V W) ∂μ_W := by
    have h_c : Real.exp (-(3 * β * C)) = ∫ _W, Real.exp (-(3 * β * C)) ∂μ_W := by simp [integral_const]
    rw [h_c]
    refine integral_mono (integrable_const _) h_int_bnd fun W => ?_
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (bondTraceSum_abs_le hβ U V W)).1])
  have h_int_hi : (∫ W, Real.exp ((β / (N : ℝ)) * bondTraceSum U V W) ∂μ_W) ≤
      Real.exp (3 * β * C) := by
    have h_c : Real.exp (3 * β * C) = ∫ _W, Real.exp (3 * β * C) ∂μ_W := by simp [integral_const]
    rw [h_c]
    refine integral_mono h_int_bnd (integrable_const _) fun W => ?_
    exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) (bondTraceSum_abs_le hβ U V W))
  unfold wilsonTransferKernel
  refine ⟨Real.exp_pos _, ?_, ?_⟩
  · have h_spU : Real.exp (-(9 * β * C)) ≤ Real.exp (-spatAction N L β U) :=
      Real.exp_le_exp.mpr (neg_le_neg hU.2)
    have h_spV : Real.exp (-(9 * β * C)) ≤ Real.exp (-spatAction N L β V) :=
      Real.exp_le_exp.mpr (neg_le_neg hV.2)
    have h_eq : Real.exp (-(21 * β * C)) =
        Real.exp (-(9 * β * C)) * Real.exp (-(9 * β * C)) * Real.exp (-(3 * β * C)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [h_eq]
    exact mul_le_mul (mul_le_mul h_spU h_spV (Real.exp_pos _).le (Real.exp_pos _).le) h_int_lo
      (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  · have h_spU : Real.exp (-spatAction N L β U) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hU.1)
    have h_spV : Real.exp (-spatAction N L β V) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hV.1)
    have h_prod1 : Real.exp (-spatAction N L β U) * Real.exp (-spatAction N L β V) ≤ 1 := by
      simpa using mul_le_mul h_spU h_spV (Real.exp_pos _).le zero_le_one
    calc
      Real.exp (-spatAction N L β U) * Real.exp (-spatAction N L β V) *
          ∫ W, Real.exp ((β / (N : ℝ)) * bondTraceSum U V W) ∂μ_W
          ≤ 1 * Real.exp (3 * β * C) := by
              exact mul_le_mul h_prod1 h_int_hi (le_trans (Real.exp_pos _).le h_int_lo) zero_le_one
      _ = Real.exp (3 * β * C) := one_mul _

/-- **Positive Semi-Definiteness of the 4D SU(N) Transfer Kernel:**
    Splitting `W = W₂⁻¹ W₁` factors `bondTraceSum U V (W₂⁻¹ W₁)` as
    `∑ x i, realTrace (A_{x,i}(U, W₁) * (A_{x,i}(V, W₂))⁻¹)`, yielding
    `0 ≤ Re ∫∫ star(f U) f V K_W_split(U, W₁; V, W₂) dμ dμ` for every bounded measurable `f`. -/
theorem wilsonTransferKernel_pos_semidef
    {N L : ℕ} [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    [MeasurableSpace (GaugeGroup N)] [MeasurableMul₂ (GaugeGroup N)] [MeasurableInv (GaugeGroup N)]
    (hEntry : ∀ i j : Fin N, Measurable (fun A : GaugeGroup N => (A : Matrix (Fin N) (Fin N) ℂ) i j))
    (μ : Measure (SpatConfig N L × (SpatLat L → GaugeGroup N))) [IsFiniteMeasure μ]
    (f : SpatConfig N L → ℂ) (hf_meas : Measurable f) (Bf : ℝ) (hBf : 0 ≤ Bf)
    (hf_bound : ∀ U, ‖f U‖ ≤ Bf) :
    0 ≤ (∫ p, (∫ q, star (f p.1) * f q.1 *
      (Real.exp (-spatAction N L β p.1) * Real.exp (-spatAction N L β q.1) *
        Real.exp ((β / (N : ℝ)) * bondTraceSum p.1 q.1 (fun x => (q.2 x)⁻¹ * p.2 x)) : ℂ) ∂μ) ∂μ).re := by
  let bondA : SpatLat L → Fin 3 → (SpatConfig N L × (SpatLat L → GaugeGroup N)) → GaugeGroup N :=
    fun x i r => (r.2 x) * r.1 x i * (r.2 (x + spatStep L i))⁻¹
  let K_bond : (SpatConfig N L × (SpatLat L → GaugeGroup N)) →
      (SpatConfig N L × (SpatLat L → GaugeGroup N)) → ℝ := fun p q =>
    ∑ x : SpatLat L, ∑ i : Fin 3,
      (β / (N : ℝ)) * realTrace (bondA x i p * (bondA x i q)⁻¹)
  have hK_eq : ∀ p q,
      (β / (N : ℝ)) * bondTraceSum p.1 q.1 (fun x => (q.2 x)⁻¹ * p.2 x) = K_bond p q := by
    intro p q
    unfold bondTraceSum K_bond
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    dsimp [bondA]
    have h_cyc : ((q.2 x)⁻¹ * p.2 x)⁻¹ * p.1 x i * ((q.2 (x + spatStep L i))⁻¹ * p.2 (x + spatStep L i)) *
        (q.1 x i)⁻¹ =
        (p.2 x)⁻¹ * ((p.2 x * p.1 x i * (p.2 (x + spatStep L i))⁻¹) *
          (q.2 x * q.1 x i * (q.2 (x + spatStep L i))⁻¹)⁻¹) * p.2 x := by
      group
    rw [h_cyc, show (p.2 x)⁻¹ * _ * p.2 x = (p.2 x)⁻¹ * _ * ((p.2 x)⁻¹)⁻¹ from by simp, realTrace_conj]
  have hK_posdef : IsBoundedPosDefKernel (fun p q => (K_bond p q : ℂ)) := by
    have h_c : (fun p q => (K_bond p q : ℂ)) = fun p q =>
        ∑ x : SpatLat L, ∑ i : Fin 3, ((β / (N : ℝ) : ℝ) : ℂ) *
          (realTrace (bondA x i p * (bondA x i q)⁻¹) : ℂ) := by
      ext p q; dsimp [K_bond]; push_cast; rfl
    rw [h_c]
    refine isBoundedPosDefKernel_sum Finset.univ _ fun x _ =>
      isBoundedPosDefKernel_sum Finset.univ _ fun i _ => ?_
    refine isBoundedPosDefKernel_smul_nonneg (div_nonneg hβ (Nat.cast_nonneg N))
      (realTrace_unitary_kernel_isPosDef (bondA x i) ?_)
    intro a b
    dsimp [bondA]
    have mp1 : Measurable (fun r : SpatConfig N L × (SpatLat L → GaugeGroup N) => r.2 x) :=
      (measurable_pi_apply x).comp measurable_snd
    have mp2 : Measurable (fun r : SpatConfig N L × (SpatLat L → GaugeGroup N) => r.1 x i) :=
      ((measurable_pi_apply i).comp (measurable_pi_apply x)).comp measurable_fst
    have mp3 : Measurable (fun r : SpatConfig N L × (SpatLat L → GaugeGroup N) =>
        (r.2 (x + spatStep L i))⁻¹) :=
      ((measurable_pi_apply _).comp measurable_snd).inv
    exact (hEntry a b).comp ((mp1.mul mp2).mul mp3)
  let B_bond : ℝ := 3 * β * ((Fintype.card (SpatLat L) : ℕ) : ℝ)
  have hK_bound : ∀ p q, |K_bond p q| ≤ B_bond := fun p q => by
    rw [← hK_eq p q]; exact bondTraceSum_abs_le hβ p.1 q.1 _
  let g : (SpatConfig N L × (SpatLat L → GaugeGroup N)) → ℂ := fun p =>
    f p.1 * (Real.exp (-spatAction N L β p.1) : ℂ)
  have h_spat_meas : Measurable (fun U : SpatConfig N L => spatAction N L β U) := by
    unfold spatAction
    refine measurable_const.mul (Finset.measurable_sum _ fun x _ =>
      Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
    refine measurable_const.sub ((Complex.continuous_re.measurable.comp ?_).div_const _)
    unfold spatPlaq
    have ml1 : Measurable (fun U : SpatConfig N L => U x i) :=
      (measurable_pi_apply i).comp (measurable_pi_apply x)
    have ml2 : Measurable (fun U : SpatConfig N L => U (x + spatStep L i) j) :=
      (measurable_pi_apply j).comp (measurable_pi_apply _)
    have ml3 : Measurable (fun U : SpatConfig N L => (U (x + spatStep L j) i)⁻¹) :=
      ((measurable_pi_apply i).comp (measurable_pi_apply _)).inv
    have ml4 : Measurable (fun U : SpatConfig N L => (U x j)⁻¹) :=
      ((measurable_pi_apply j).comp (measurable_pi_apply x)).inv
    have mprod : Measurable (fun U : SpatConfig N L => spatPlaq U x i j) :=
      ((ml1.mul ml2).mul ml3).mul ml4
    change Measurable (fun U : SpatConfig N L =>
      Matrix.trace ((spatPlaq U x i j : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ))
    exact Finset.measurable_sum _ fun k _ => (hEntry k k).comp mprod
  have hg_meas : Measurable g :=
    (hf_meas.comp measurable_fst).mul
      (Complex.continuous_ofReal.measurable.comp
        (Real.continuous_exp.measurable.comp (h_spat_meas.comp measurable_fst).neg))
  have hg_bound : ∀ p, ‖g p‖ ≤ Bf := by
    intro p
    dsimp [g]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hexp1 : Real.exp (-spatAction N L β p.1) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (spatAction_bounds hβ p.1).1)
    simpa using mul_le_mul (hf_bound p.1) hexp1 (Real.exp_pos _).le hBf
  have h_pos := exp_real_posDefKernel_double_integral_nonneg μ K_bond hK_posdef
    B_bond (by positivity) hK_bound g hg_meas Bf hBf hg_bound
  have h_eq_int : ∀ p q,
      star (f p.1) * f q.1 *
        (Real.exp (-spatAction N L β p.1) * Real.exp (-spatAction N L β q.1) *
          Real.exp ((β / (N : ℝ)) * bondTraceSum p.1 q.1 (fun x => (q.2 x)⁻¹ * p.2 x)) : ℂ) =
      star (g p) * g q * (Real.exp (K_bond p q) : ℂ) := by
    intro p q
    rw [hK_eq p q]
    dsimp [g]
    rw [star_mul, Complex.conj_ofReal]
    push_cast
    ring
  simpa [h_eq_int] using h_pos

end Imscribing.YangMills.LatticeTransfer4D