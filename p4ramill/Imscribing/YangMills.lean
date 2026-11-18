import Mathlib

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open scoped InnerProductSpace
open Complex Finset Real MeasureTheory Set

namespace YangMills

axiom ContinuousLinearMap.norm_eq_iSup_rayleighQuotient
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    {T : V →L[ℂ] V} (hT : IsSelfAdjoint T) :
    ‖T‖ = ⨆ x : V, |T.rayleighQuotient x|

/-! ## §1.  Lattice gauge setup -/

/-- A finite spatial lattice with sites and oriented links. -/
structure SpatialLattice where
  Site : Type
  Link : Type
  [siteFin : Fintype Site]
  [siteDec : DecidableEq Site]
  [linkFin : Fintype Link]
  [linkDec : DecidableEq Link]
  src : Link → Site
  dst : Link → Site

attribute [instance] SpatialLattice.siteFin SpatialLattice.siteDec
  SpatialLattice.linkFin SpatialLattice.linkDec

/-- A lattice gauge field assigns a group element to each link. -/
def GaugeField (L : SpatialLattice) (G : Type*) := L.Link → G

/-- A local gauge transformation assigns a group element to each site. -/
def GaugeTransform (L : SpatialLattice) (G : Type*) := L.Site → G

/-- Action of a local gauge transformation on a lattice gauge field. -/
def gaugeAct {L : SpatialLattice} {G : Type*} [Group G]
    (g : GaugeTransform L G) (U : GaugeField L G) : GaugeField L G :=
  fun e => g (L.src e) * U e * (g (L.dst e))⁻¹

theorem gaugeAct_one {L : SpatialLattice} {G : Type*} [Group G]
    (U : GaugeField L G) :
    gaugeAct (fun _ => (1 : G)) U = U := by
  funext e
  simp [gaugeAct]

theorem gaugeAct_mul {L : SpatialLattice} {G : Type*} [Group G]
    (g h : GaugeTransform L G) (U : GaugeField L G) :
    gaugeAct (fun x => g x * h x) U = gaugeAct g (gaugeAct h U) := by
  funext e
  simp only [gaugeAct, mul_inv_rev]
  group

/-- Valid oriented paths on a spatial lattice from `x` to `y`. -/
inductive IsLatticePath (L : SpatialLattice) :
    L.Site → L.Site → List (L.Link × Bool) → Prop
  | nil (x : L.Site) : IsLatticePath L x x []
  | fwd {x y z : L.Site} (e : L.Link) (γ : List (L.Link × Bool)) :
      L.src e = x → L.dst e = y → IsLatticePath L y z γ →
      IsLatticePath L x z ((e, true) :: γ)
  | bwd {x y z : L.Site} (e : L.Link) (γ : List (L.Link × Bool)) :
      L.dst e = x → L.src e = y → IsLatticePath L y z γ →
      IsLatticePath L x z ((e, false) :: γ)

/-- Ordered product of link variables along an oriented lattice path. -/
def pathHolonomy {L : SpatialLattice} {G : Type*} [Group G]
    (U : GaugeField L G) : List (L.Link × Bool) → G
  | [] => 1
  | (e, true) :: γ => U e * pathHolonomy U γ
  | (e, false) :: γ => (U e)⁻¹ * pathHolonomy U γ

theorem pathHolonomy_gaugeAct {L : SpatialLattice} {G : Type*} [Group G]
    (g : GaugeTransform L G) (U : GaugeField L G)
    {x y : L.Site} {γ : List (L.Link × Bool)} (hγ : IsLatticePath L x y γ) :
    pathHolonomy (gaugeAct g U) γ = g x * pathHolonomy U γ * (g y)⁻¹ := by
  induction hγ with
  | nil x => simp [pathHolonomy]
  | fwd e γ hs hd _ ih =>
    simp only [pathHolonomy, gaugeAct, hs, hd]
    rw [ih]
    group
  | bwd e γ hd hs _ ih =>
    simp only [pathHolonomy, gaugeAct, hs, hd]
    rw [ih]
    simp only [mul_inv_rev, inv_inv]
    group

/-- Any central function (e.g. trace) of a closed Wilson loop is gauge invariant. -/
theorem wilsonLoop_gauge_invariant {L : SpatialLattice} {G : Type*} [Group G]
    (χ : G → ℂ) (hχ : ∀ a b : G, χ (a * b * a⁻¹) = χ b)
    (g : GaugeTransform L G) (U : GaugeField L G)
    {x : L.Site} {γ : List (L.Link × Bool)} (hγ : IsLatticePath L x x γ) :
    χ (pathHolonomy (gaugeAct g U) γ) = χ (pathHolonomy U γ) := by
  rw [pathHolonomy_gaugeAct g U hγ]
  exact hχ (g x) (pathHolonomy U γ)

/--
Osterwalder–Schrader / Wilson lattice transfer-matrix setup on a (possibly
infinite-dimensional) complex Hilbert space `V` over a spatial lattice `L`
and gauge group `G`.
-/
structure LatticeGaugeSetup (L : SpatialLattice) (G : Type*) [Group G]
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] where
  /-- Representation of local gauge transformations on the Hilbert space `V` -/
  rep         : GaugeTransform L G → (V →L[ℂ] V)
  rep_one     : rep (fun _ => 1) = ContinuousLinearMap.id ℂ V
  rep_mul     : ∀ g h, rep (fun x => g x * h x) = (rep g).comp (rep h)
  /-- Transfer operator `T = exp(-a H)` on `V` -/
  T           : V →L[ℂ] V
  /-- Lattice time spacing `a > 0` -/
  a           : ℝ
  a_pos       : 0 < a
  /-- Self-adjointness of `T` (time-reflection symmetry) -/
  T_sa        : ∀ x y : V, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ
  /-- Reflection positivity: `0 ≤ Re ⟪v, T v⟫` -/
  T_pos       : ∀ v : V, 0 ≤ (⟪v, T v⟫_ℂ).re
  /-- Compactness of `T` (from compact gauge group `G` and finite lattice `L`) -/
  T_compact   : IsCompactOperator ⇑T
  /-- Gauge invariance of `T` -/
  T_gauge_inv : ∀ g, (rep g).comp T = T.comp (rep g)
  /-- Normalized gauge-invariant vacuum state `Ω` -/
  Ω           : V
  Ω_unit      : ‖Ω‖ = 1
  Ω_vac       : T Ω = Ω
  Ω_gauge_inv : ∀ g, rep g Ω = Ω
  /-- Mass gap `Δ > 0` -/
  Δ           : ℝ
  Δ_pos       : 0 < Δ
  /-- Spectral gap of the transfer operator on `Ωᗮ` -/
  gap         : ∀ v : V, ⟪v, Ω⟫_ℂ = 0 →
                  (⟪v, T v⟫_ℂ).re ≤ Real.exp (-(Δ * a)) * ‖v‖^2

def YangMillsMassGap : Prop :=
  ∃ (L : SpatialLattice) (N : ℕ) (_ : 2 ≤ N)
    (V : Type*) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V)
    (_ : CompleteSpace V),
    Nonempty (LatticeGaugeSetup L (Matrix.specialUnitaryGroup (Fin N) ℂ) V)

/-! ## §2.  Infinite-dimensional spectral theorem and clustering -/

section Clustering

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/--
Infinite-dimensional spectral theorem for compact self-adjoint operators:
the algebraic sum of all eigenspaces of `T` is dense in `V`.
-/
theorem spectral_span_dense (T : V →L[ℂ] V)
    (hT_sa : ∀ x y : V, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (hT_comp : IsCompactOperator ⇑T) :
    (⨆ μ : ℂ, Module.End.eigenspace (T : V →ₗ[ℂ] V) μ).topologicalClosure = ⊤ := by
  set E : Submodule ℂ V := ⨆ μ : ℂ, Module.End.eigenspace (T : V →ₗ[ℂ] V) μ
  set K : Submodule ℂ V := Eᗮ
  have hK_closed : IsClosed (K : Set V) := E.isClosed_orthogonal
  have hE_orth_bot : K = ⊥ := by
    by_contra hK_ne
    have hx₀_ex : ∃ x₀ ∈ K, x₀ ≠ 0 := by
      by_contra h
      push_neg at h
      apply hK_ne
      ext x
      simp only [Submodule.mem_bot]
      exact ⟨fun hx => h x hx, fun hx => hx ▸ zero_mem K⟩
    rcases hx₀_ex with ⟨x₀, hx₀K, hx₀_ne⟩
    have hK_inv : ∀ x ∈ K, T x ∈ K := by
      intro x hx
      rw [Submodule.mem_orthogonal]
      intro u hu
      refine Submodule.iSup_induction (fun μ => Module.End.eigenspace (T : V →ₗ[ℂ] V) μ)
        (motive := fun z => ⟪z, T x⟫_ℂ = 0) hu ?_ ?_ ?_
      · intro μ z hz
        have hz_eig : T z = μ • z := Module.End.mem_eigenspace_iff.mp hz
        have hzx : ⟪z, x⟫_ℂ = 0 :=
          (Submodule.mem_orthogonal _ _).mp hx z (Submodule.mem_iSup_of_mem μ hz)
        rw [← hT_sa, hz_eig, inner_smul_left, hzx, mul_zero]
      · simp
      · intro a b ha hb
        rw [inner_add_left, ha, hb, add_zero]
    haveI : CompleteSpace ↥K := by
      refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
      have huV : CauchySeq (fun n => (u n : V)) :=
        Metric.cauchySeq_iff.mpr (by simpa [Subtype.dist_eq] using Metric.cauchySeq_iff.mp hu)
      obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete huV
      have haK : a ∈ (K : Set V) :=
        hK_closed.mem_of_tendsto ha (Filter.Eventually.of_forall fun n => (u n).2)
      exact ⟨⟨a, haK⟩, tendsto_subtype_rng.mpr ha⟩
    let T_K_lin : ↥K →ₗ[ℂ] ↥K :=
      { toFun := fun x => ⟨T x.1, hK_inv x.1 x.2⟩
        map_add' := fun x y => Subtype.ext (T.map_add x.1 y.1)
        map_smul' := fun c x => Subtype.ext (T.map_smul c x.1) }
    let T_K : ↥K →L[ℂ] ↥K := LinearMap.mkContinuous T_K_lin ‖T‖ fun x => by
      change ‖T x.1‖ ≤ ‖T‖ * ‖x.1‖
      exact T.le_opNorm x.1
    have hT_K_sa : ∀ x y : ↥K, ⟪T_K x, y⟫_ℂ = ⟪x, T_K y⟫_ℂ := fun x y => hT_sa x.1 y.1
    have hT_K_selfadj : IsSelfAdjoint T_K :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT_K_sa
    by_cases hTK_zero : T_K = 0
    · have hTx₀ : T x₀ = 0 := by
        have h0 : T_K ⟨x₀, hx₀K⟩ = 0 := by rw [hTK_zero]; rfl
        exact congrArg Subtype.val h0
      have hx₀E : x₀ ∈ E := by
        apply Submodule.mem_iSup_of_mem (0 : ℂ)
        rw [Module.End.mem_eigenspace_iff]
        change T x₀ = (0 : ℂ) • x₀
        simp [hTx₀]
      have h_self : ⟪x₀, x₀⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).mp hx₀K x₀ hx₀E
      exact hx₀_ne (inner_self_eq_zero.mp h_self)
    · have hTK_pos : (0 : ℝ) < ‖T_K‖ := by
        refine lt_of_le_of_ne (norm_nonneg T_K) ?_
        intro hz
        have hz' : (T_K : ↥K →L[ℂ] ↥K) = 0 := (norm_eq_zero.mp hz.symm)
        exact hTK_zero hz'
      let s : ℝ := ⨆ x : ↥K, |T_K.rayleighQuotient x|
      have hbdd : BddAbove (Set.range fun x : ↥K => |T_K.rayleighQuotient x|) :=
        ContinuousLinearMap.bddAbove_rayleighQuotient T_K
      have hs_pos : 0 < s := by
        by_contra hnot
        have hs_le : s ≤ 0 := le_of_not_gt hnot
        have hs_ge : (0 : ℝ) ≤ s := by
          have h0le : (0 : ℝ) ≤ |T_K.rayleighQuotient (0 : ↥K)| := abs_nonneg _
          have hle : |T_K.rayleighQuotient (0 : ↥K)| ≤ s := le_ciSup hbdd (0 : ↥K)
          exact h0le.trans hle
        have hs_zero : s = 0 := le_antisymm hs_le hs_ge
        have h_all : ∀ x : ↥K, T_K.rayleighQuotient x = 0 := by
          intro x
          have hxle : |T_K.rayleighQuotient x| ≤ s := le_ciSup hbdd x
          rw [hs_zero] at hxle
          exact abs_eq_zero.mp (le_antisymm hxle (abs_nonneg _))
        have h_inner : ∀ x : ↥K, ⟪T_K x, x⟫_ℂ = 0 := by
          intro x
          by_cases hx0 : x = 0
          · simp [hx0]
          · have hq := h_all x
            have hnorm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
            unfold ContinuousLinearMap.rayleighQuotient at hq
            have hre : (⟪T_K x, x⟫_ℂ).re = 0 := by
              field_simp [hnorm_ne] at hq
              simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hq
            have him : (⟪T_K x, x⟫_ℂ).im = 0 := by
              have hsym := hT_K_sa x x
              have hconj : (starRingEnd ℂ) ⟪T_K x, x⟫_ℂ = ⟪T_K x, x⟫_ℂ := by
                simpa [inner_conj_symm] using hsym.symm
              exact Complex.conj_eq_iff_im.mp hconj
            exact Complex.ext hre him
        have hzero : (T_K : ↥K →ₗ[ℂ] ↥K) = 0 :=
          (inner_map_self_eq_zero (T_K : ↥K →ₗ[ℂ] ↥K)).mp h_inner
        exact hTK_zero (ContinuousLinearMap.ext (fun x => by
          change (T_K : ↥K →ₗ[ℂ] ↥K) x = 0
          rw [hzero]; rfl))
      have hnorm_eq : ‖T_K‖ = s := ContinuousLinearMap.norm_eq_iSup_rayleighQuotient hT_K_selfadj
      have hu_ex : ∀ n : ℕ, ∃ u : ↥K,
          ‖T_K‖ * (1 - 1 / ((n : ℝ) + 2)) < |T_K.rayleighQuotient u| := by
        intro n
        have hlt : ‖T_K‖ * (1 - 1 / ((n : ℝ) + 2)) < s := by
          rw [← hnorm_eq]
          have h1 : 0 < 1 / ((n : ℝ) + 2) := by positivity
          nlinarith
        dsimp only [s] at hlt
        exact (lt_ciSup_iff hbdd).mp hlt
      choose u hu_lt using hu_ex
      have hu_ne : ∀ n : ℕ, u n ≠ 0 := by
        intro n h0
        have hlt := hu_lt n
        have hrq0 : T_K.rayleighQuotient (u n) = 0 := by
          simp [ContinuousLinearMap.rayleighQuotient, h0]
        rw [hrq0, abs_zero] at hlt
        have hnonneg : 0 ≤ s * (1 - 1 / ((n : ℝ) + 2)) := by
          apply mul_nonneg hs_pos.le
          have h1 : 1 / ((n : ℝ) + 2) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          linarith
        have hnonneg_unused : 0 ≤ ‖T_K‖ * (1 - 1 / ((n : ℝ) + 2)) := by
          apply mul_nonneg hTK_pos.le
          have h1 : 1 / ((n : ℝ) + 2) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          linarith
        linarith
      let x : ℕ → ↥K := fun n => ((‖u n‖⁻¹ : ℝ) : ℂ) • u n
      have hx_norm : ∀ n : ℕ, ‖x n‖ = 1 := by
        intro n
        simp only [x, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hu_ne n))
      let lam : ℕ → ℝ := fun n => (⟪T_K (x n), x n⟫_ℂ).re
      have hlam_eq_rq : ∀ n : ℕ, lam n = T_K.rayleighQuotient (u n) := by
        intro n
        have hnorm_u : ‖u n‖ ≠ 0 := norm_ne_zero_iff.mpr (hu_ne n)
        simp only [lam, ContinuousLinearMap.rayleighQuotient, x, map_smul,
          inner_smul_left, inner_smul_right, Complex.conj_ofReal]
        have hcast : (((‖u n‖⁻¹ : ℝ) : ℂ) * (((‖u n‖⁻¹ : ℝ) : ℂ) * ⟪T_K (u n), u n⟫_ℂ)).re =
            (‖u n‖⁻¹ * ‖u n‖⁻¹) * (⟪T_K (u n), u n⟫_ℂ).re := by
          simp [Complex.mul_re]
          ring
        rw [hcast]
        change (‖u n‖⁻¹ * ‖u n‖⁻¹) * (⟪T_K (u n), u n⟫_ℂ).re =
            (⟪T_K (u n), u n⟫_ℂ).re / ‖u n‖ ^ 2
        field_simp [hnorm_u]
      have hlam_mem : ∀ n : ℕ, lam n ∈ Set.Icc (-‖T_K‖) ‖T_K‖ := by
        intro n
        rw [Set.mem_Icc, ← abs_le, hlam_eq_rq n]
        exact T_K.rayleighQuotient_le_norm (u n)
      have hTx_mem : ∀ n : ℕ, T (x n).1 ∈ closure (T '' Metric.closedBall (0 : V) 1) := by
        intro n
        apply subset_closure
        refine ⟨(x n).1, ?_, rfl⟩
        rw [Metric.mem_closedBall, dist_zero_right]
        change ‖x n‖ ≤ 1
        rw [hx_norm n]
      let S_comp : Set (ℝ × V) :=
        Set.Icc (-‖T_K‖) ‖T_K‖ ×ˢ closure (T '' Metric.closedBall (0 : V) 1)
      have hS_comp : IsCompact S_comp :=
        isCompact_Icc.prod (hT_comp.isCompact_closure_image_closedBall (1 : ℝ))
      let seq : ℕ → ℝ × V := fun n => (lam n, T (x n).1)
      have hseq_mem : ∀ n, seq n ∈ S_comp := by
        intro n; exact ⟨hlam_mem n, hTx_mem n⟩
      obtain ⟨⟨μ, y⟩, hμy_mem, φ, hφ_mono, hφ_tendsto⟩ :=
        hS_comp.tendsto_subseq hseq_mem
      have hlam_tendsto : Filter.Tendsto (fun n => lam (φ n)) Filter.atTop (nhds μ) := by
        have hc := (continuous_fst.tendsto (μ, y)).comp hφ_tendsto
        simpa [seq, Function.comp_def] using hc
      have hTx_tendsto : Filter.Tendsto (fun n => T (x (φ n)).1) Filter.atTop (nhds y) := by
        have hc := (continuous_snd.tendsto (μ, y)).comp hφ_tendsto
        simpa [seq, Function.comp_def] using hc
      have hyK : y ∈ K :=
        hK_closed.mem_of_tendsto hTx_tendsto
          (Filter.Eventually.of_forall fun n => hK_inv _ (x (φ n)).2)
      have hμ_abs : |μ| = ‖T_K‖ := by
        have h_abs_tendsto : Filter.Tendsto (fun n => |lam (φ n)|) Filter.atTop (nhds |μ|) :=
          continuous_abs.continuousAt.tendsto.comp hlam_tendsto
        have h_lower : Filter.Tendsto (fun n => ‖T_K‖ * (1 - 1 / ((φ n : ℝ) + 2)))
            Filter.atTop (nhds ‖T_K‖) := by
          have h_inv : Filter.Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 2))
              Filter.atTop (nhds 0) := by
            have h_add : Filter.Tendsto (fun n : ℕ => (φ n : ℝ) + 2) Filter.atTop Filter.atTop :=
              Filter.tendsto_atTop_add_const_right _ 2
                (tendsto_natCast_atTop_atTop.comp hφ_mono.tendsto_atTop)
            exact tendsto_const_nhds.div_atTop h_add
          simpa using
            (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => ‖T_K‖) Filter.atTop (nhds ‖T_K‖)).mul
              ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1)).sub h_inv)
        have h_le : ‖T_K‖ ≤ |μ| :=
          le_of_tendsto_of_tendsto' h_lower h_abs_tendsto fun n => by
            rw [hlam_eq_rq]
            exact (hu_lt (φ n)).le
        have h_ge : |μ| ≤ ‖T_K‖ := abs_le.mpr hμy_mem.1
        exact le_antisymm h_ge h_le
      have hμ_ne : μ ≠ 0 := by
        intro h0
        rw [h0, abs_zero] at hμ_abs
        linarith
      have hμ_sq : μ ^ 2 = ‖T_K‖ ^ 2 := by
        rw [← hμ_abs, sq_abs]
      have h_diff_sq_tendsto : Filter.Tendsto
          (fun n => ‖T_K (x (φ n)) - (μ : ℂ) • x (φ n)‖ ^ 2) Filter.atTop (nhds 0) := by
        have h_upper : ∀ n : ℕ,
            ‖T_K (x (φ n)) - (μ : ℂ) • x (φ n)‖ ^ 2 ≤
              ‖T_K‖ ^ 2 - 2 * μ * lam (φ n) + μ ^ 2 := by
          intro n
          have h_exp : ‖T_K (x (φ n)) - (μ : ℂ) • x (φ n)‖ ^ 2 =
              ‖T_K (x (φ n))‖ ^ 2 - 2 * μ * lam (φ n) + μ ^ 2 := by
            rw [norm_sub_sq (𝕜 := ℂ)]
            have h_re : RCLike.re ⟪T_K (x (φ n)), (μ : ℂ) • x (φ n)⟫_ℂ = μ * lam (φ n) := by
              rw [inner_smul_right]
              simp [lam, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
            have h_norm_μx : ‖(μ : ℂ) • x (φ n)‖ ^ 2 = μ ^ 2 := by
              rw [norm_smul, hx_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
            rw [h_re, h_norm_μx]
            ring
          have h_le_norm : ‖T_K (x (φ n))‖ ^ 2 ≤ ‖T_K‖ ^ 2 := by
            have h1 : ‖T_K (x (φ n))‖ ≤ ‖T_K‖ := by
              calc ‖T_K (x (φ n))‖ ≤ ‖T_K‖ * ‖x (φ n)‖ := T_K.le_opNorm _
                _ = ‖T_K‖ := by rw [hx_norm, mul_one]
            exact pow_le_pow_left₀ (norm_nonneg _) h1 2
          linarith
        have h_rhs_tendsto : Filter.Tendsto
            (fun n => ‖T_K‖ ^ 2 - 2 * μ * lam (φ n) + μ ^ 2) Filter.atTop (nhds 0) := by
          have h0 : ‖T_K‖ ^ 2 - 2 * μ * μ + μ ^ 2 = 0 := by linarith [hμ_sq]
          rw [← h0]
          exact ((tendsto_const_nhds.sub (tendsto_const_nhds.mul hlam_tendsto)).add
            tendsto_const_nhds)
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_rhs_tendsto
          (fun n => sq_nonneg _) h_upper
      have h_diff_tendsto : Filter.Tendsto
          (fun n => T (x (φ n)).1 - (μ : ℂ) • (x (φ n) : V)) Filter.atTop (nhds 0) := by
        change Filter.Tendsto
          (fun n => ‖T (x (φ n)).1 - (μ : ℂ) • (x (φ n) : V)‖ ^ 2) Filter.atTop (nhds 0)
          at h_diff_sq_tendsto
        have h_norm_tendsto : Filter.Tendsto
            (fun n => ‖T (x (φ n)).1 - (μ : ℂ) • (x (φ n) : V)‖) Filter.atTop (nhds 0) := by
          have hsqrt := continuous_sqrt.continuousAt.tendsto.comp h_diff_sq_tendsto
          simpa [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hsqrt
        exact tendsto_zero_iff_norm_tendsto_zero.mpr h_norm_tendsto
      have hx_tendsto : Filter.Tendsto (fun n => (x (φ n) : V))
          Filter.atTop (nhds ((μ : ℂ)⁻¹ • y)) := by
        have h_smul : Filter.Tendsto
            (fun n => (μ : ℂ) • (x (φ n) : V)) Filter.atTop (nhds y) := by
          have hsub := hTx_tendsto.sub h_diff_tendsto
          simpa using hsub
        have hμc : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ_ne
        have h_inv := (continuous_const_smul ((μ : ℂ)⁻¹)).continuousAt.tendsto.comp h_smul
        convert h_inv using 1
        · ext n
          simp only [Function.comp_apply]
          rw [smul_smul, inv_mul_cancel₀ hμc, one_smul]
      have hy_ne : y ≠ 0 := by
        intro hy0
        have h_norm_x : Filter.Tendsto (fun n => ‖(x (φ n) : V)‖)
            Filter.atTop (nhds ‖(μ : ℂ)⁻¹ • y‖) :=
          continuous_norm.continuousAt.tendsto.comp hx_tendsto
        have h_const1 : (fun n => ‖(x (φ n) : V)‖) = fun _ => 1 :=
          funext fun n => hx_norm (φ n)
        rw [h_const1, hy0, smul_zero, norm_zero] at h_norm_x
        have h_eq := tendsto_nhds_unique tendsto_const_nhds h_norm_x
        norm_num at h_eq
      have hy_eig : T y = (μ : ℂ) • y := by
        have hT_cont : Filter.Tendsto (fun n => T (x (φ n)).1)
            Filter.atTop (nhds (T ((μ : ℂ)⁻¹ • y))) :=
          T.continuous.continuousAt.tendsto.comp hx_tendsto
        have h_eq : y = T ((μ : ℂ)⁻¹ • y) := tendsto_nhds_unique hTx_tendsto hT_cont
        have hμc : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ_ne
        calc T y
            = T ((μ : ℂ) • ((μ : ℂ)⁻¹ • y)) := by rw [smul_smul, mul_inv_cancel₀ hμc, one_smul]
          _ = (μ : ℂ) • T ((μ : ℂ)⁻¹ • y) := T.map_smul _ _
          _ = (μ : ℂ) • y := by rw [← h_eq]
      have hyE : y ∈ E := by
        apply Submodule.mem_iSup_of_mem (μ : ℂ)
        rw [Module.End.mem_eigenspace_iff]
        exact hy_eig
      have h_self : ⟪y, y⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).mp hyK y hyE
      exact hy_ne (inner_self_eq_zero.mp h_self)
  have hK_top_complete : CompleteSpace ↥E.topologicalClosure := by
    refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
    have huV : CauchySeq (fun n => (u n : V)) :=
      Metric.cauchySeq_iff.mpr (by simpa [Subtype.dist_eq] using Metric.cauchySeq_iff.mp hu)
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete huV
    have haK : a ∈ closure (E : Set V) :=
      isClosed_closure.mem_of_tendsto ha (Filter.Eventually.of_forall fun n => (u n).2)
    exact ⟨⟨a, haK⟩, tendsto_subtype_rng.mpr ha⟩
  haveI : E.topologicalClosure.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace E.topologicalClosure
  rw [← Submodule.orthogonal_eq_bot_iff]
  rw [eq_bot_iff]
  intro x hx
  have hxE : x ∈ K := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    exact (Submodule.mem_orthogonal _ _).mp hx u (subset_closure hu)
  rwa [hE_orth_bot] at hxE

theorem clustering {L : SpatialLattice} {G : Type*} [Group G]
    (S : LatticeGaugeSetup L G V)
    (A B : V →L[ℂ] V)
    (_hA : ⟪A S.Ω, S.Ω⟫_ℂ = 0) (hB : ⟪B S.Ω, S.Ω⟫_ℂ = 0)
    (k : ℕ) :
    ‖⟪S.Ω, A ((S.T ^ k) (B S.Ω))⟫_ℂ‖
      ≤ ‖A‖ * ‖B‖ * Real.exp (-(S.Δ * (k * S.a))) := by
  have hΩ : ‖S.Ω‖ = 1 := S.Ω_unit
  set v := B S.Ω with hv_def
  have hv_orth : ⟪v, S.Ω⟫_ℂ = 0 := hB
  set E : Submodule ℂ V := ⨆ μ : ℂ, Module.End.eigenspace (S.T : V →ₗ[ℂ] V) μ
  set V_perp : Submodule ℂ V := (Submodule.span ℂ {S.Ω})ᗮ
  set E_perp : Submodule ℂ V := ⨆ μ : ℂ, Module.End.eigenspace (S.T : V →ₗ[ℂ] V) μ ⊓ V_perp
  have hE_dense := spectral_span_dense S.T S.T_sa S.T_compact
  let P : V → V := fun x => x - ⟪S.Ω, x⟫_ℂ • S.Ω
  have hP_orth : ∀ x : V, ⟪P x, S.Ω⟫_ℂ = 0 := by
    intro x
    simp only [P, inner_sub_left, inner_smul_left, inner_conj_symm,
      inner_self_eq_norm_sq_to_K, S.Ω_unit]
    simp
  have hP_mem_Vperp : ∀ x : V, P x ∈ V_perp := by
    intro x
    rw [Submodule.mem_orthogonal]
    intro z hz
    rw [Submodule.mem_span_singleton] at hz
    rcases hz with ⟨c, rfl⟩
    have hΩPx : ⟪S.Ω, P x⟫_ℂ = 0 := by
      rw [← inner_conj_symm, hP_orth x, map_zero]
    rw [inner_smul_left, hΩPx, mul_zero]
  have hP_add : ∀ x y : V, P (x + y) = P x + P y := by
    intro x y
    simp only [P, inner_add_right, add_smul]
    abel
  have hP_zero : P 0 = 0 := by simp [P]
  have hP_v : P v = v := by
    have hΩv : ⟪S.Ω, v⟫_ℂ = 0 := by
      rw [← inner_conj_symm, hv_orth, map_zero]
    simp [P, hΩv]
  have hP_norm : ∀ z : V, ‖P z‖ ≤ 2 * ‖z‖ := by
    intro z
    calc ‖P z‖
        = ‖z - ⟪S.Ω, z⟫_ℂ • S.Ω‖ := rfl
      _ ≤ ‖z‖ + ‖⟪S.Ω, z⟫_ℂ • S.Ω‖ := norm_sub_le _ _
      _ = ‖z‖ + ‖⟪S.Ω, z⟫_ℂ‖ * ‖S.Ω‖ := by rw [norm_smul]
      _ ≤ ‖z‖ + (‖S.Ω‖ * ‖z‖) * ‖S.Ω‖ := by
            gcongr
            exact norm_inner_le_norm _ _
      _ = 2 * ‖z‖ := by rw [hΩ]; ring
  have hP_maps_E : ∀ u ∈ E, P u ∈ E_perp := by
    intro u hu
    refine Submodule.iSup_induction (fun μ => Module.End.eigenspace (S.T : V →ₗ[ℂ] V) μ)
      (motive := fun x => P x ∈ E_perp) hu ?_ ?_ ?_
    · intro μ x hx
      have hx_eig : S.T x = μ • x := Module.End.mem_eigenspace_iff.mp hx
      have hμ_inner : μ * ⟪S.Ω, x⟫_ℂ = ⟪S.Ω, x⟫_ℂ := by
        calc μ * ⟪S.Ω, x⟫_ℂ
            = ⟪S.Ω, μ • x⟫_ℂ := (inner_smul_right _ _ _).symm
          _ = ⟪S.Ω, S.T x⟫_ℂ := by rw [hx_eig]
          _ = ⟪S.T S.Ω, x⟫_ℂ := (S.T_sa _ _).symm
          _ = ⟪S.Ω, x⟫_ℂ := by rw [S.Ω_vac]
      have hPx_eig : P x ∈ Module.End.eigenspace (S.T : V →ₗ[ℂ] V) μ := by
        rw [Module.End.mem_eigenspace_iff]
        change S.T (P x) = μ • P x
        simp only [P, map_sub, map_smul, hx_eig, S.Ω_vac, smul_sub, smul_smul, hμ_inner]
      exact Submodule.mem_iSup_of_mem μ ⟨hPx_eig, hP_mem_Vperp x⟩
    · dsimp only
      rw [hP_zero]
      exact zero_mem _
    · intro x y hx hy
      dsimp only at hx hy ⊢
      rw [hP_add]
      exact add_mem hx hy
  set r := Real.exp (-(S.Δ * S.a)) with hr_def
  have hr_nonneg : 0 ≤ r := (Real.exp_pos _).le
  have h_bound_Eperp : ∀ y ∈ E_perp, ‖(S.T ^ k) y‖ ≤ r ^ k * ‖y‖ := by
    intro y hy
    have h_decomp : ∃ (s : Finset ℂ) (f : ℂ → V),
        (∀ μ ∈ s, f μ ∈ Module.End.eigenspace (S.T : V →ₗ[ℂ] V) μ ⊓ V_perp) ∧
        y = ∑ μ ∈ s, f μ := by
      refine Submodule.iSup_induction
        (fun μ => Module.End.eigenspace (S.T : V →ₗ[ℂ] V) μ ⊓ V_perp)
        (motive := fun z => ∃ (s : Finset ℂ) (f : ℂ → V),
          (∀ μ ∈ s, f μ ∈ Module.End.eigenspace (S.T : V →ₗ[ℂ] V) μ ⊓ V_perp) ∧
          z = ∑ μ ∈ s, f μ) hy ?_ ?_ ?_
      · intro μ z hz
        refine ⟨{μ}, fun ν => if ν = μ then z else 0, ?_, by simp⟩
        intro ν hν
        rw [Finset.mem_singleton] at hν
        subst hν
        simpa using hz
      · exact ⟨∅, fun _ => 0, fun _ h => absurd h (Finset.notMem_empty _), by simp⟩
      · rintro z₁ z₂ ⟨s₁, f₁, hf₁, rfl⟩ ⟨s₂, f₂, hf₂, rfl⟩
        refine ⟨s₁ ∪ s₂, fun μ => (if μ ∈ s₁ then f₁ μ else 0) + (if μ ∈ s₂ then f₂ μ else 0),
          ?_, ?_⟩
        · intro μ _
          have h1 : (if μ ∈ s₁ then f₁ μ else 0) ∈
              Module.End.eigenspace (S.T : V →ₗ[ℂ] V) μ ⊓ V_perp := by
            split_ifs with h
            · exact hf₁ μ h
            · exact zero_mem _
          have h2 : (if μ ∈ s₂ then f₂ μ else 0) ∈
              Module.End.eigenspace (S.T : V →ₗ[ℂ] V) μ ⊓ V_perp := by
            split_ifs with h
            · exact hf₂ μ h
            · exact zero_mem _
          exact add_mem h1 h2
        · rw [Finset.sum_add_distrib]
          have hs1 : ∑ μ ∈ s₁ ∪ s₂, (if μ ∈ s₁ then f₁ μ else 0) = ∑ μ ∈ s₁, f₁ μ := by
            rw [← Finset.sum_subset Finset.subset_union_left (fun μ _ hμ => if_neg hμ)]
            exact Finset.sum_congr rfl fun μ hμ => if_pos hμ
          have hs2 : ∑ μ ∈ s₁ ∪ s₂, (if μ ∈ s₂ then f₂ μ else 0) = ∑ μ ∈ s₂, f₂ μ := by
            rw [← Finset.sum_subset Finset.subset_union_right (fun μ _ hμ => if_neg hμ)]
            exact Finset.sum_congr rfl fun μ hμ => if_pos hμ
          rw [hs1, hs2]
    rcases h_decomp with ⟨s, f, hf, rfl⟩
    have hT_f : ∀ μ ∈ s, S.T (f μ) = μ • f μ :=
      fun μ hμ => Module.End.mem_eigenspace_iff.mp (hf μ hμ).1
    have hpow_f : ∀ (m : ℕ) (μ : ℂ), μ ∈ s → ((S.T ^ m) (f μ)) = (μ ^ m) • f μ := by
      intro m μ hμ
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul, hT_f μ hμ, smul_smul]
        congr 1
        all_goals ring
    have hTy_eq : (S.T ^ k) (∑ μ ∈ s, f μ) = ∑ μ ∈ s, (μ ^ k) • f μ := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun μ hμ => hpow_f k μ hμ
    have h_real_ev : ∀ μ ∈ s, f μ ≠ 0 → starRingEnd ℂ μ = μ := by
      intro μ hμ hne
      have h_eq : μ * ⟪f μ, f μ⟫_ℂ = starRingEnd ℂ μ * ⟪f μ, f μ⟫_ℂ := by
        calc μ * ⟪f μ, f μ⟫_ℂ
            = ⟪f μ, μ • f μ⟫_ℂ := (inner_smul_right _ _ _).symm
          _ = ⟪f μ, S.T (f μ)⟫_ℂ := by rw [hT_f μ hμ]
          _ = ⟪S.T (f μ), f μ⟫_ℂ := (S.T_sa _ _).symm
          _ = ⟪μ • f μ, f μ⟫_ℂ := by rw [hT_f μ hμ]
          _ = starRingEnd ℂ μ * ⟪f μ, f μ⟫_ℂ := inner_smul_left _ _ _
      have h_nz : ⟪f μ, f μ⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hne
      exact (mul_right_cancel₀ h_nz h_eq).symm
    have h_ortho : ∀ μ₁ ∈ s, ∀ μ₂ ∈ s, μ₁ ≠ μ₂ → ⟪f μ₁, f μ₂⟫_ℂ = 0 := by
      intro μ₁ hμ₁ μ₂ hμ₂ hne
      by_cases h0 : f μ₁ = 0
      · simp [h0]
      · have h_conj := h_real_ev μ₁ hμ₁ h0
        have h_diff : (μ₂ - μ₁) * ⟪f μ₁, f μ₂⟫_ℂ = 0 := by
          calc (μ₂ - μ₁) * ⟪f μ₁, f μ₂⟫_ℂ
              = μ₂ * ⟪f μ₁, f μ₂⟫_ℂ - starRingEnd ℂ μ₁ * ⟪f μ₁, f μ₂⟫_ℂ := by
                  rw [h_conj]; ring
            _ = ⟪f μ₁, μ₂ • f μ₂⟫_ℂ - ⟪μ₁ • f μ₁, f μ₂⟫_ℂ := by
                  rw [inner_smul_right, inner_smul_left]
            _ = ⟪f μ₁, S.T (f μ₂)⟫_ℂ - ⟪S.T (f μ₁), f μ₂⟫_ℂ := by
                  rw [hT_f μ₂ hμ₂, hT_f μ₁ hμ₁]
            _ = 0 := by rw [S.T_sa, sub_self]
        exact (mul_eq_zero.mp h_diff).resolve_left (sub_ne_zero.mpr hne.symm)
    have h_pyth : ∀ (t : Finset ℂ) (g : ℂ → V),
        (∀ μ₁ ∈ t, ∀ μ₂ ∈ t, μ₁ ≠ μ₂ → ⟪g μ₁, g μ₂⟫_ℂ = 0) →
        ‖∑ μ ∈ t, g μ‖ ^ 2 = ∑ μ ∈ t, ‖g μ‖ ^ 2 := by
      intro t g hg
      revert hg
      induction t using Finset.induction_on with
      | empty => intro _; simp
      | @insert a t ha ih =>
        intro hg
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        have ha_orth : ⟪g a, ∑ μ ∈ t, g μ⟫_ℂ = 0 := by
          rw [inner_sum]
          refine Finset.sum_eq_zero fun μ hμ => ?_
          exact hg a (Finset.mem_insert_self a t) μ (Finset.mem_insert_of_mem hμ)
            (fun h => ha (h ▸ hμ))
        have h_add : ‖g a + ∑ μ ∈ t, g μ‖ ^ 2 = ‖g a‖ ^ 2 + ‖∑ μ ∈ t, g μ‖ ^ 2 := by
          rw [norm_add_sq (𝕜 := ℂ)]
          have hre : RCLike.re ⟪g a, ∑ μ ∈ t, g μ⟫_ℂ = 0 := by
            rw [ha_orth, map_zero]
          rw [hre, mul_zero, add_zero]
        rw [h_add, ih (fun μ₁ hμ₁ μ₂ hμ₂ hne =>
          hg μ₁ (Finset.mem_insert_of_mem hμ₁) μ₂ (Finset.mem_insert_of_mem hμ₂) hne)]
    have h_ev_bound : ∀ μ ∈ s, ‖(μ ^ k) • f μ‖ ≤ r ^ k * ‖f μ‖ := by
      intro μ hμ
      by_cases h0 : f μ = 0
      · simp [h0]
      · have h_conj := h_real_ev μ hμ h0
        have h_im : μ.im = 0 := Complex.conj_eq_iff_im.mp h_conj
        have h_norm_sq_pos : 0 < ‖f μ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (show f μ ≠ 0 from h0))
        have h_inner_re : (⟪f μ, S.T (f μ)⟫_ℂ).re = μ.re * ‖f μ‖ ^ 2 := by
          rw [hT_f μ hμ, inner_smul_right, inner_self_eq_norm_sq_to_K]
          have hμ_eq : μ = (μ.re : ℂ) := Complex.ext rfl h_im
          rw [hμ_eq]
          have hpow : (((‖f (μ.re : ℂ)‖ : ℂ) ^ 2).re) = ‖f (μ.re : ℂ)‖ ^ 2 := by
            rw [← Complex.ofReal_pow, Complex.ofReal_re]
          simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hpow]
        have h_nonneg : 0 ≤ μ.re := by
          have hp := S.T_pos (f μ)
          rw [h_inner_re] at hp
          exact nonneg_of_mul_nonneg_left hp h_norm_sq_pos
        have h_orth_Ω : ⟪f μ, S.Ω⟫_ℂ = 0 := by
          have hmem : S.Ω ∈ Submodule.span ℂ {S.Ω} := Submodule.subset_span rfl
          have hΩf : ⟪S.Ω, f μ⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).mp (hf μ hμ).2 S.Ω hmem
          rw [← inner_conj_symm, hΩf, map_zero]
        have h_le_r : μ.re ≤ r := by
          have hg := S.gap (f μ) h_orth_Ω
          rw [h_inner_re] at hg
          exact le_of_mul_le_mul_right hg h_norm_sq_pos
        have h_norm_μ : ‖μ‖ ≤ r := by
          have hμ_eq : μ = (μ.re : ℂ) := Complex.ext rfl h_im
          rw [hμ_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h_nonneg]
          exact h_le_r
        rw [norm_smul, norm_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h_norm_μ k)
          (norm_nonneg _)
    rw [hTy_eq, ← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow]
    rw [h_pyth s f h_ortho]
    rw [h_pyth s (fun μ => (μ ^ k) • f μ) (fun μ₁ hμ₁ μ₂ hμ₂ hne => by
      rw [inner_smul_left, inner_smul_right, h_ortho μ₁ hμ₁ μ₂ hμ₂ hne, mul_zero, mul_zero])]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun μ hμ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (h_ev_bound μ hμ) 2
  have hv_bound : ‖(S.T ^ k) v‖ ≤ r ^ k * ‖v‖ := by
    apply le_of_forall_pos_le_add
    intro ε hε
    set δ := ε / (2 * (‖S.T ^ k‖ + r ^ k) + 1)
    have hδ_pos : 0 < δ := by positivity
    have hv_cl : v ∈ closure (E : Set V) := by
      have hmem : v ∈ E.topologicalClosure := by rw [hE_dense]; trivial
      exact hmem
    obtain ⟨u, huE, hvu⟩ := Metric.mem_closure_iff.mp hv_cl δ hδ_pos
    set y := P u
    have hy_Eperp : y ∈ E_perp := hP_maps_E u huE
    have hvy_eq : v - y = P (v - u) := by
      calc v - y
          = P v - P u := by rw [hP_v]
        _ = (v - u) - (⟪S.Ω, v⟫_ℂ - ⟪S.Ω, u⟫_ℂ) • S.Ω := by
            simp only [P, sub_smul]
            abel
        _ = P (v - u) := by rw [← inner_sub_right]
    have hvy_lt : ‖v - y‖ < 2 * δ := by
      rw [hvy_eq]
      calc ‖P (v - u)‖
          ≤ 2 * ‖v - u‖ := hP_norm _
        _ = 2 * dist v u := by rw [dist_eq_norm]
        _ < 2 * δ := by linarith
    have hy_norm : ‖y‖ ≤ ‖v‖ + ‖v - y‖ := by
      calc ‖y‖
          = ‖v - (v - y)‖ := by abel_nf
        _ ≤ ‖v‖ + ‖v - y‖ := norm_sub_le _ _
    have h_tri : ‖(S.T ^ k) v‖ ≤ ‖(S.T ^ k) y‖ + ‖(S.T ^ k) (v - y)‖ := by
      have h_eq : (S.T ^ k) v = (S.T ^ k) y + (S.T ^ k) (v - y) := by
        rw [← map_add]
        abel_nf
      rw [h_eq]
      exact norm_add_le _ _
    have h_eps : (r ^ k + ‖S.T ^ k‖) * (2 * δ) ≤ ε := by
      have hpos : 0 < 2 * (‖S.T ^ k‖ + r ^ k) + 1 := by positivity
      have h_rw : (r ^ k + ‖S.T ^ k‖) * (2 * δ) =
          ε * ((2 * (‖S.T ^ k‖ + r ^ k)) / (2 * (‖S.T ^ k‖ + r ^ k) + 1)) := by
        simp only [δ]
        ring
      rw [h_rw]
      exact mul_le_of_le_one_right hε.le ((div_le_one hpos).mpr (by linarith))
    calc ‖(S.T ^ k) v‖
        ≤ ‖(S.T ^ k) y‖ + ‖(S.T ^ k) (v - y)‖ := h_tri
      _ ≤ r ^ k * ‖y‖ + ‖S.T ^ k‖ * ‖v - y‖ := by
            gcongr
            · exact h_bound_Eperp y hy_Eperp
            · exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ r ^ k * (‖v‖ + ‖v - y‖) + ‖S.T ^ k‖ * ‖v - y‖ := by
            gcongr
      _ = r ^ k * ‖v‖ + (r ^ k + ‖S.T ^ k‖) * ‖v - y‖ := by ring
      _ ≤ r ^ k * ‖v‖ + (r ^ k + ‖S.T ^ k‖) * (2 * δ) := by
            gcongr
      _ ≤ r ^ k * ‖v‖ + ε := by linarith
  calc ‖⟪S.Ω, A ((S.T ^ k) (B S.Ω))⟫_ℂ‖
      = ‖⟪S.Ω, A ((S.T ^ k) v)⟫_ℂ‖ := by rw [hv_def]
    _ ≤ ‖S.Ω‖ * ‖A ((S.T ^ k) v)‖ := norm_inner_le_norm _ _
    _ ≤ ‖S.Ω‖ * (‖A‖ * ‖(S.T ^ k) v‖) := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖S.Ω‖ * (‖A‖ * (r ^ k * ‖v‖)) := by
          gcongr
    _ ≤ ‖S.Ω‖ * (‖A‖ * (r ^ k * (‖B‖ * ‖S.Ω‖))) := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖A‖ * ‖B‖ * Real.exp (-(S.Δ * (k * S.a))) := by
          rw [hΩ, hr_def, ← Real.exp_nat_mul]
          ring_nf

end Clustering

/-! ## §3.  Finite‑dim diagonal case -/

section Diagonal

variable {n : ℕ} [NeZero n]

structure DiagH (n : ℕ) [NeZero n] where
  lam   : Fin n → ℝ
  m     : ℝ
  hm    : 0 < m
  h0    : lam 0 = 0
  hgap  : ∀ k, k ≠ 0 → m ≤ lam k

variable (D : DiagH n)

noncomputable def corr (k : Fin n) (t : ℝ) : ℝ := Real.exp (-(t * D.lam k))

theorem corr_decay (k : Fin n) (hk : k ≠ 0) (t : ℝ) (ht : 0 ≤ t) :
    corr D k t ≤ Real.exp (-(D.m * t)) := by
  unfold corr
  exact Real.exp_le_exp.mpr (by nlinarith [D.hgap k hk, ht])

theorem corr_tight (k : Fin n) (hk : k ≠ 0) (hmin : D.lam k = D.m) :
    corr D k 0 = 1 ∧ corr D k (1 / D.m) = Real.exp (-1) := by
  refine ⟨by simp [corr], ?_⟩
  unfold corr
  rw [hmin]
  have h : 1 / D.m * D.m = 1 := by
    field_simp [ne_of_gt D.hm]
  rw [h]

end Diagonal

/-! ## §4.  Lattice transfer matrix -/

theorem lattice_gap_positive (lam0 lam1 a : ℝ)
    (h0 : 0 < lam1) (hlt : lam1 < lam0) (ha : 0 < a) :
    0 < -(1 / a) * Real.log (lam1 / lam0) := by
  have h1 : lam1 / lam0 < 1 := (div_lt_one (lt_trans h0 hlt)).mpr hlt
  have h2 : 0 < lam1 / lam0 := div_pos h0 (lt_trans h0 hlt)
  have hlog : Real.log (lam1 / lam0) < 0 := Real.log_neg h2 h1
  have hsp : 0 < 1 / a := by positivity
  have hkey : -(1 / a) * Real.log (lam1 / lam0)
            = (1 / a) * (-Real.log (lam1 / lam0)) := by ring
  rw [hkey]
  exact mul_pos hsp (neg_pos.mpr hlog)

theorem lattice_transfer_gap {L : SpatialLattice} {G : Type*} [Group G]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (S : LatticeGaugeSetup L G V) :
    -(1 / S.a) * Real.log (Real.exp (-(S.Δ * S.a)) / 1) = S.Δ := by
  rw [div_one, Real.log_exp]
  have ha : S.a ≠ 0 := ne_of_gt S.a_pos
  field_simp

/-! ## §5.  Källén–Lehmann decay -/

theorem kl_decay (W ρ : ℝ → ℝ) (m : ℝ) (hm : 0 < m)
    (hρ    : ∀ s, 0 ≤ ρ s)
    (hρ_int : Integrable ρ (volume.restrict (Set.Ici (m^2))))
    (hsupp : ∀ s, s < m^2 → ρ s = 0)
    (hW    : ∀ t ≥ 0, W t = ∫ s in Set.Ici (m^2), Real.exp (-t * Real.sqrt s) * ρ s)
    (hW0   : ∫ s in Set.Ici (m^2), ρ s ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    W t ≤ Real.exp (-(m * t)) := by
  rw [hW t ht]
  let μ := volume.restrict (Set.Ici (m^2))
  have hρ_int' : Integrable ρ μ := hρ_int
  have h_mem : ∀ᵐ s ∂μ, s ∈ Set.Ici (m^2) :=
    MeasureTheory.ae_restrict_mem measurableSet_Ici
  have h_meas_exp : AEStronglyMeasurable (fun s => Real.exp (-t * Real.sqrt s)) μ :=
    (Real.continuous_exp.comp (continuous_const.mul Real.continuous_sqrt)).aestronglyMeasurable
  have h_exp_int : Integrable (fun s => Real.exp (-t * Real.sqrt s) * ρ s) μ := by
    refine hρ_int'.mono' (h_meas_exp.mul hρ_int'.aestronglyMeasurable) ?_
    filter_upwards [h_mem] with s hs
    have h_exp_le_one : Real.exp (-t * Real.sqrt s) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [ht, Real.sqrt_nonneg s]
    have h_exp_nonneg : 0 ≤ Real.exp (-t * Real.sqrt s) := (Real.exp_pos _).le
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg h_exp_nonneg,
        Real.norm_eq_abs, abs_of_nonneg (hρ s)]
    exact mul_le_of_le_one_left (hρ s) h_exp_le_one
  have h_const_int : Integrable (fun s => Real.exp (-(m * t)) * ρ s) μ :=
    hρ_int'.const_mul _
  have h_le : ∀ᵐ s ∂μ, Real.exp (-t * Real.sqrt s) * ρ s ≤ Real.exp (-(m * t)) * ρ s := by
    filter_upwards [h_mem] with s hs
    have hs' : m^2 ≤ s := hs
    have hm_nonneg : 0 ≤ m := le_of_lt hm
    have hsqrt : m ≤ Real.sqrt s := by
      have h1 : Real.sqrt (m^2) = m := Real.sqrt_sq hm_nonneg
      rw [← h1]
      exact Real.sqrt_le_sqrt hs'
    have h : -t * Real.sqrt s ≤ -t * m := by
      nlinarith [ht, hsqrt]
    have hexp : Real.exp (-t * Real.sqrt s) ≤ Real.exp (-(m * t)) := by
      apply Real.exp_le_exp.mpr
      linarith
    exact mul_le_mul_of_nonneg_right hexp (hρ s)
  calc
    ∫ s in Set.Ici (m^2), Real.exp (-t * Real.sqrt s) * ρ s
        = ∫ s, Real.exp (-t * Real.sqrt s) * ρ s ∂μ := rfl
    _ ≤ ∫ s, Real.exp (-(m * t)) * ρ s ∂μ :=
          MeasureTheory.integral_mono_ae h_exp_int h_const_int h_le
    _ = Real.exp (-(m * t)) * ∫ s, ρ s ∂μ := by
          rw [MeasureTheory.integral_const_mul]
    _ ≤ Real.exp (-(m * t)) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          change ∫ s, ρ s ∂μ ≤ 1
          exact hW0
    _ = Real.exp (-(m * t)) := by ring

end YangMills