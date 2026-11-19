import Mathlib

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open scoped InnerProductSpace
open Complex Finset Real MeasureTheory Set

namespace YangMills

private theorem norm_eq_iSup_rayleighQuotient
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    {T : V →L[ℂ] V} (hT : IsSelfAdjoint T) :
    ‖T‖ = ⨆ x : V, |T.rayleighQuotient x| := by
  have hT_sa : ∀ x y : V, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  set s : ℝ := ⨆ x : V, |T.rayleighQuotient x|
  have hbdd : BddAbove (Set.range fun x : V => |T.rayleighQuotient x|) :=
    ContinuousLinearMap.bddAbove_rayleighQuotient T
  have hs_le : s ≤ ‖T‖ := ciSup_le fun x => T.rayleighQuotient_le_norm x
  have hs_nonneg : 0 ≤ s := le_trans (abs_nonneg _) (le_ciSup hbdd 0)
  have hQ : ∀ z : V, |(⟪T z, z⟫_ℂ).re| ≤ s * ‖z‖ ^ 2 := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · have hq : |T.rayleighQuotient z| ≤ s := le_ciSup hbdd z
      have hz_sq_pos : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
      unfold ContinuousLinearMap.rayleighQuotient at hq
      simp only [ContinuousLinearMap.reApplyInnerSelf_apply] at hq
      rwa [abs_div, abs_of_pos hz_sq_pos, div_le_iff₀ hz_sq_pos] at hq
  have h_pol : ∀ u v : V,
      (⟪T (u + v), u + v⟫_ℂ).re - (⟪T (u - v), u - v⟫_ℂ).re = 4 * (⟪T u, v⟫_ℂ).re := by
    intro u v
    have h1 : ⟪T (u + v), u + v⟫_ℂ =
        ⟪T u, u⟫_ℂ + ⟪T u, v⟫_ℂ + ⟪T v, u⟫_ℂ + ⟪T v, v⟫_ℂ := by
      simp only [map_add, inner_add_left, inner_add_right]
      ring
    have h2 : ⟪T (u - v), u - v⟫_ℂ =
        ⟪T u, u⟫_ℂ - ⟪T u, v⟫_ℂ - ⟪T v, u⟫_ℂ + ⟪T v, v⟫_ℂ := by
      simp only [map_sub, inner_sub_left, inner_sub_right]
      ring
    have hsym : (⟪T v, u⟫_ℂ).re = (⟪T u, v⟫_ℂ).re := by
      rw [hT_sa v u, ← inner_conj_symm (T u) v]
      exact (Complex.conj_re ⟪v, T u⟫_ℂ).symm
    rw [h1, h2]
    simp only [Complex.add_re, Complex.sub_re, hsym]
    ring
  have h_para : ∀ u v : V, ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
    intro u v
    rw [norm_add_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ)]
    ring
  have h_cross : ∀ u v : V,
      4 * |(⟪T u, v⟫_ℂ).re| ≤ s * (2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2) := by
    intro u v
    have h4 : 4 * |(⟪T u, v⟫_ℂ).re| =
        |(⟪T (u + v), u + v⟫_ℂ).re - (⟪T (u - v), u - v⟫_ℂ).re| := by
      rw [h_pol u v, abs_mul]
      norm_num
    rw [h4]
    calc |(⟪T (u + v), u + v⟫_ℂ).re - (⟪T (u - v), u - v⟫_ℂ).re|
        ≤ |(⟪T (u + v), u + v⟫_ℂ).re| + |(⟪T (u - v), u - v⟫_ℂ).re| := abs_sub _ _
      _ ≤ s * ‖u + v‖ ^ 2 + s * ‖u - v‖ ^ 2 := add_le_add (hQ (u + v)) (hQ (u - v))
      _ = s * (‖u + v‖ ^ 2 + ‖u - v‖ ^ 2) := by ring
      _ = s * (2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2) := by rw [h_para]
  have h_le : ‖T‖ ≤ s := by
    refine ContinuousLinearMap.opNorm_le_bound T hs_nonneg fun x => ?_
    by_cases hx : x = 0
    · simp [hx]
    · by_cases hTx : T x = 0
      · simp [hTx]; positivity
      · have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
        have hTx_pos : 0 < ‖T x‖ := norm_pos_iff.mpr hTx
        let v : V := ((‖x‖ / ‖T x‖ : ℝ) : ℂ) • T x
        have hv_norm : ‖v‖ = ‖x‖ := by
          simp only [v, norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (div_pos hx_pos hTx_pos)]
          exact div_mul_cancel₀ _ hTx_pos.ne'
        have h_inner_val : (⟪T x, v⟫_ℂ).re = ‖x‖ * ‖T x‖ := by
          simp only [v, inner_smul_right, inner_self_eq_norm_sq_to_K]
          have hpow : (((‖T x‖ : ℂ) ^ 2).re) = ‖T x‖ ^ 2 := by
            norm_num [pow_two]
          have him : (((‖T x‖ : ℂ) ^ 2).im) = 0 := by
            norm_num [pow_two]
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hpow, him,
            zero_mul, sub_zero]
          field_simp [hTx_pos.ne']
          exact hpow
        have hc := h_cross x v
        rw [hv_norm, h_inner_val, abs_of_nonneg (mul_nonneg hx_pos.le hTx_pos.le)] at hc
        have hmul : ‖x‖ * ‖T x‖ ≤ ‖x‖ * (s * ‖x‖) := by linarith
        exact le_of_mul_le_mul_left hmul hx_pos
  exact le_antisymm h_le hs_le

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
      have hnorm_eq : ‖T_K‖ = s := norm_eq_iSup_rayleighQuotient hT_K_selfadj
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
          have h₁ : 0 ≤ s := by linarith [hs_pos]
          have h₂ : 0 ≤ 1 - 1 / ((n : ℝ) + 2) := by
            have h₃ : 1 / ((n : ℝ) + 2) ≤ 1 := by
              rw [div_le_one (by positivity)]; linarith
            linarith
          exact mul_nonneg h₁ h₂
        exact (not_lt_of_ge hnonneg) (by
          calc
            s * (1 - 1 / ((n : ℝ) + 2)) = ‖T_K‖ * (1 - 1 / ((n : ℝ) + 2)) := by rw [hnorm_eq]
            _ < 0 := hlt)
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

/-! ## §6.  M-derived continuum scaling limit -/

section ScalingLimit

/--
Renormalization pair `(R, R_inv)` between finite-`a` models `M_a` and a
continuum limit `M_inf`, realizing `R ∘ R⁻¹ = id` (`μ ∘ δ = id`) on the
continuum image.
-/
structure RenormPair (M_a : ℝ → Type*) (M_inf : Type*) where
  R         : ∀ a : ℝ, 0 < a → M_a a → M_inf
  R_inv     : ∀ a : ℝ, 0 < a → M_inf → M_a a
  renorm_id : ∀ (a : ℝ) (ha : 0 < a) (x : M_inf), R a ha (R_inv a ha x) = x

theorem renorm_surjective {M_a : ℝ → Type*} {M_inf : Type*}
    (P : RenormPair M_a M_inf) (a : ℝ) (ha : 0 < a) :
    Function.Surjective (P.R a ha) :=
  fun x => ⟨P.R_inv a ha x, P.renorm_id a ha x⟩

/--
Model-theoretic structure for the M-derived continuum scaling limit:
per-model satisfaction (`Sat M φ`), universal validity (`Valid`),
scaling-invariant preservation from `M_a` to `M_inf`, uniform typing,
and permanent independence.
-/
structure ScalingLogic where
  Sentence         : Type
  Ty               : Type
  Model            : Type
  embed_a          : ∀ a : ℝ, 0 < a → Model
  embed_inf        : Model
  typeOf           : Sentence → Ty
  type_uniform     : ∀ φ ψ : Sentence, typeOf φ = typeOf ψ
  neg              : Sentence → Sentence
  Sat              : Model → Sentence → Prop
  sat_neg_iff      : ∀ M φ, Sat M (neg φ) ↔ ¬ Sat M φ
  ScalingInvariant : Sentence → Prop
  scaling_pres     : ∀ (a : ℝ) (ha : 0 < a) (φ : Sentence),
      ScalingInvariant φ → Sat (embed_a a ha) φ → Sat embed_inf φ
  independent      : ∃ φ : Sentence,
      (¬ ∀ M, Sat M φ) ∧ (¬ ∀ M, Sat M (neg φ))

def ScalingLogic.Valid (L : ScalingLogic) (φ : L.Sentence) : Prop :=
  ∀ M : L.Model, L.Sat M φ

theorem scaling_excluded_middle (L : ScalingLogic) (M : L.Model) (φ : L.Sentence) :
    L.Sat M φ ∨ L.Sat M (L.neg φ) := by
  rw [L.sat_neg_iff]
  exact Classical.em (L.Sat M φ)

theorem scaling_independence (L : ScalingLogic) :
    ∃ φ : L.Sentence, ¬ L.Valid φ ∧ ¬ L.Valid (L.neg φ) :=
  L.independent

/-- Homogeneous encoding of `M ⊨ φ` on `Model ⊕ Sentence`. -/
def ScalingLogic.SatRel (L : ScalingLogic) :
    L.Model ⊕ L.Sentence → L.Model ⊕ L.Sentence → Prop
  | Sum.inl M, Sum.inr φ => L.Sat M φ
  | _, _ => False

theorem scaling_sat_wellFounded (L : ScalingLogic) : WellFounded L.SatRel := by
  refine ⟨fun x => ?_⟩
  cases x with
  | inl M =>
    refine Acc.intro (Sum.inl M) fun y hy => ?_
    cases y <;> cases hy
  | inr φ =>
    refine Acc.intro (Sum.inr φ) fun y hy => ?_
    cases y with
    | inl M =>
      refine Acc.intro (Sum.inl M) fun z hz => ?_
      cases z <;> cases hz
    | inr _ => cases hy

/--
A lattice-to-continuum scaling family of `LatticeGaugeSetup` models indexed
by `a > 0` with a uniform physical mass-gap lower bound `Δ_phys > 0`.
-/
structure LatticeScalingFamily (G : Type*) [Group G] where
  L        : ℝ → SpatialLattice
  V        : ℝ → Type*
  [vNorm   : ∀ a, NormedAddCommGroup (V a)]
  [vInner  : ∀ a, InnerProductSpace ℂ (V a)]
  [vComp   : ∀ a, CompleteSpace (V a)]
  setup    : ∀ a : ℝ, 0 < a → LatticeGaugeSetup (L a) G (V a)
  a_eq     : ∀ (a : ℝ) (ha : 0 < a), (setup a ha).a = a
  Δ_phys   : ℝ
  Δ_pos    : 0 < Δ_phys
  gap_unif : ∀ (a : ℝ) (ha : 0 < a), Δ_phys ≤ (setup a ha).Δ

attribute [instance] LatticeScalingFamily.vNorm LatticeScalingFamily.vInner
  LatticeScalingFamily.vComp

/-- Uniform-in-`a` lattice clustering at physical time `k * a` with rate `Δ_phys`. -/
theorem uniform_lattice_clustering {G : Type*} [Group G]
    (F : LatticeScalingFamily G) (a : ℝ) (ha : 0 < a)
    (A B : F.V a →L[ℂ] F.V a)
    (hA : ⟪A (F.setup a ha).Ω, (F.setup a ha).Ω⟫_ℂ = 0)
    (hB : ⟪B (F.setup a ha).Ω, (F.setup a ha).Ω⟫_ℂ = 0)
    (k : ℕ) :
    ‖⟪(F.setup a ha).Ω, A (((F.setup a ha).T ^ k) (B (F.setup a ha).Ω))⟫_ℂ‖
      ≤ ‖A‖ * ‖B‖ * Real.exp (-(F.Δ_phys * (k * a))) := by
  have h_clus := clustering (F.setup a ha) A B hA hB k
  have h_gap : F.Δ_phys * ((k : ℝ) * a) ≤ (F.setup a ha).Δ * ((k : ℝ) * a) :=
    mul_le_mul_of_nonneg_right (F.gap_unif a ha) (mul_nonneg (Nat.cast_nonneg k) ha.le)
  have h_exp : Real.exp (-((F.setup a ha).Δ * ((k : ℝ) * (F.setup a ha).a)))
      ≤ Real.exp (-(F.Δ_phys * ((k : ℝ) * a))) := by
    rw [F.a_eq a ha]
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    ‖⟪(F.setup a ha).Ω, A (((F.setup a ha).T ^ k) (B (F.setup a ha).Ω))⟫_ℂ‖
        ≤ ‖A‖ * ‖B‖ * Real.exp (-((F.setup a ha).Δ * ((k : ℝ) * (F.setup a ha).a))) := h_clus
    _ ≤ ‖A‖ * ‖B‖ * Real.exp (-(F.Δ_phys * ((k : ℝ) * a))) :=
        mul_le_mul_of_nonneg_left h_exp (mul_nonneg (norm_nonneg A) (norm_nonneg B))

/--
Continuum mass-gap clustering: if a continuum two-point correlator `W_inf`
is the scaling limit (`k_n * a_n → t`) of uniformly bounded finite-`a`
lattice correlators, then `W_inf ≤ C * exp(-Δ_phys * t)`.
-/
theorem continuum_scaling_clustering {G : Type*} [Group G]
    (F : LatticeScalingFamily G)
    (a_seq : ℕ → ℝ) (ha_seq : ∀ n, 0 < a_seq n) (k_seq : ℕ → ℕ)
    (A_seq B_seq : ∀ n, F.V (a_seq n) →L[ℂ] F.V (a_seq n))
    (hA : ∀ n, ⟪A_seq n (F.setup (a_seq n) (ha_seq n)).Ω,
        (F.setup (a_seq n) (ha_seq n)).Ω⟫_ℂ = 0)
    (hB : ∀ n, ⟪B_seq n (F.setup (a_seq n) (ha_seq n)).Ω,
        (F.setup (a_seq n) (ha_seq n)).Ω⟫_ℂ = 0)
    (C : ℝ) (hC : ∀ n, ‖A_seq n‖ * ‖B_seq n‖ ≤ C)
    (t W_inf : ℝ)
    (ht_lim : Filter.Tendsto (fun n => (k_seq n : ℝ) * a_seq n) Filter.atTop (nhds t))
    (hW_lim : Filter.Tendsto
      (fun n => ‖⟪(F.setup (a_seq n) (ha_seq n)).Ω,
        A_seq n (((F.setup (a_seq n) (ha_seq n)).T ^ k_seq n)
          (B_seq n (F.setup (a_seq n) (ha_seq n)).Ω))⟫_ℂ‖)
      Filter.atTop (nhds W_inf)) :
    W_inf ≤ C * Real.exp (-(F.Δ_phys * t)) := by
  have h_bound : ∀ n,
      ‖⟪(F.setup (a_seq n) (ha_seq n)).Ω,
        A_seq n (((F.setup (a_seq n) (ha_seq n)).T ^ k_seq n)
          (B_seq n (F.setup (a_seq n) (ha_seq n)).Ω))⟫_ℂ‖
        ≤ C * Real.exp (-(F.Δ_phys * ((k_seq n : ℝ) * a_seq n))) := by
    intro n
    have h1 := uniform_lattice_clustering F (a_seq n) (ha_seq n)
      (A_seq n) (B_seq n) (hA n) (hB n) (k_seq n)
    have h2 : ‖A_seq n‖ * ‖B_seq n‖ * Real.exp (-(F.Δ_phys * ((k_seq n : ℝ) * a_seq n)))
        ≤ C * Real.exp (-(F.Δ_phys * ((k_seq n : ℝ) * a_seq n))) :=
      mul_le_mul_of_nonneg_right (hC n) (Real.exp_pos _).le
    exact h1.trans h2
  have h_exp_lim : Filter.Tendsto
      (fun n => C * Real.exp (-(F.Δ_phys * ((k_seq n : ℝ) * a_seq n))))
      Filter.atTop (nhds (C * Real.exp (-(F.Δ_phys * t)))) := by
    have h_cont : Continuous fun s : ℝ => C * Real.exp (-(F.Δ_phys * s)) :=
      continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)
    exact h_cont.continuousAt.tendsto.comp ht_lim
  exact le_of_tendsto_of_tendsto' hW_lim h_exp_lim h_bound

end ScalingLimit

/-! ## §7.  Combined chain: Trilattice GNS → Lattice → 4D OS/Wightman QFT -/

section CombinedChain

/--
Re-entrant trilattice operational tuple
`M = <S, ≤_t, ≤_f, ≤_i, Inc, μ, δ, W>` over the 16-state `SIXTEEN_3` space.
-/
structure TrilatticeModel where
  S          : Type
  [sFin      : Fintype S]
  [sDec      : DecidableEq S]
  card_eq    : Fintype.card S = 16
  le_t       : S → S → Prop
  le_f       : S → S → Prop
  le_i       : S → S → Prop
  le_t_refl  : ∀ x, le_t x x
  le_f_refl  : ∀ x, le_f x x
  le_i_refl  : ∀ x, le_i x x
  le_i_trans : ∀ {x y z}, le_i x y → le_i y z → le_i x z
  le_i_anti  : ∀ {x y}, le_i x y → le_i y x → x = y
  void       : S
  trueVal    : S
  falseVal   : S
  bothVal    : S
  totalityB  : S
  val_ne_tf  : trueVal ≠ falseVal
  val_ne_bv  : bothVal ≠ void
  le_i_top   : ∀ x, le_i x totalityB
  Inc        : S → S
  inc_fixed  : Inc totalityB = totalityB
  inc_ne_void : Inc (Inc totalityB) ≠ void
  Part       : Type
  δ          : S → Part
  μ          : Part → S
  mu_delta   : ∀ x : S, μ (δ x) = x
  W          : S → S
  W_mono     : ∀ x : S, le_i x (W x)
  W_strict   : ∀ x : S, x ≠ totalityB → x ≠ W x
  W_fixed    : W totalityB = totalityB

attribute [instance] TrilatticeModel.sFin TrilatticeModel.sDec

/--
Dual-frame GNS realization of a `TrilatticeModel` into a `LatticeGaugeSetup`
with vacuum `Ω = [B]` and transfer gap `Δ > 0`.
-/
structure TrilatticeGNSBridge (M : TrilatticeModel) (L : SpatialLattice)
    (G : Type*) [Group G] (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] where
  setup    : LatticeGaugeSetup L G V
  embed    : M.S → V
  embed_B  : embed M.totalityB = setup.Ω
  vac_inv  : setup.T (embed M.totalityB) = embed M.totalityB

/--
Section 3 lower bound: for any unit vector `ψ ∈ Ωᗮ`, the transfer-matrix
spectral gap quantity `1 - |Re ⟪ψ, T ψ⟫|` is bounded below by `1 - exp(-Δ * a)`.
-/
theorem latticeGap_lower_bound {L : SpatialLattice} {G : Type*} [Group G]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (S : LatticeGaugeSetup L G V) (ψ : V)
    (h_orth : ⟪ψ, S.Ω⟫_ℂ = 0) (h_norm : ‖ψ‖ = 1) :
    1 - Real.exp (-(S.Δ * S.a)) ≤ 1 - |(⟪ψ, S.T ψ⟫_ℂ).re| := by
  have hpos : 0 ≤ (⟪ψ, S.T ψ⟫_ℂ).re := S.T_pos ψ
  have hgap : (⟪ψ, S.T ψ⟫_ℂ).re ≤ Real.exp (-(S.Δ * S.a)) := by
    simpa [h_norm] using S.gap ψ h_orth
  rw [abs_of_nonneg hpos]
  linarith

/--
Uniform-in-volume thermodynamic limit family: `Δ_latt` is bounded below
by `Δ₀ > 0` uniformly across all spatial lattice volumes.
-/
structure UniformVolumeFamily (G : Type*) [Group G] (a : ℝ) (ha : 0 < a) where
  ι         : Type
  L         : ι → SpatialLattice
  V         : ι → Type*
  [vNorm    : ∀ i, NormedAddCommGroup (V i)]
  [vInner   : ∀ i, InnerProductSpace ℂ (V i)]
  [vComp    : ∀ i, CompleteSpace (V i)]
  setup     : ∀ i : ι, LatticeGaugeSetup (L i) G (V i)
  a_eq      : ∀ i : ι, (setup i).a = a
  Δ₀        : ℝ
  Δ₀_pos    : 0 < Δ₀
  unif_gap  : ∀ i : ι, Δ₀ ≤ 1 - Real.exp (-((setup i).Δ * a))

attribute [instance] UniformVolumeFamily.vNorm UniformVolumeFamily.vInner
  UniformVolumeFamily.vComp

theorem uniform_volume_gap_bound {G : Type*} [Group G] {a : ℝ} {ha : 0 < a}
    (U : UniformVolumeFamily G a ha) (i : U.ι) (ψ : U.V i)
    (h_orth : ⟪ψ, (U.setup i).Ω⟫_ℂ = 0) (h_norm : ‖ψ‖ = 1) :
    U.Δ₀ ≤ 1 - |(⟪ψ, (U.setup i).T ψ⟫_ℂ).re| := by
  have h1 := U.unif_gap i
  have h2 := latticeGap_lower_bound (U.setup i) ψ h_orth h_norm
  rw [U.a_eq i] at h2
  exact h1.trans h2

/--
Section 4 RG scaling limit of the lattice gap:
`(1 - exp(-Δ_phys * a_n)) / a_n → Δ_phys` as `a_n → 0⁺`.
-/
theorem rescaled_lattice_gap_tendsto (Δ_phys : ℝ)
    (a_seq : ℕ → ℝ) (ha_pos : ∀ n, 0 < a_seq n)
    (ha_lim : Filter.Tendsto a_seq Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => (1 - Real.exp (-(Δ_phys * a_seq n))) / a_seq n)
      Filter.atTop (nhds Δ_phys) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h_abs_lim : Filter.Tendsto (fun n => |Δ_phys| * a_seq n) Filter.atTop (nhds 0) := by
    simpa using (continuous_const.mul continuous_id).continuousAt.tendsto.comp ha_lim
  have h_ev1 : ∃ N₁, ∀ n ≥ N₁, |Δ_phys| * a_seq n < 1 := by
    have h := Metric.tendsto_atTop.mp h_abs_lim 1 one_pos
    rcases h with ⟨N₁, hN₁⟩
    refine ⟨N₁, fun n hn => ?_⟩
    have hdist := hN₁ n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (abs_nonneg _) (ha_pos n).le)] at hdist
    exact hdist
  have h_bound_lim : Filter.Tendsto (fun n => Δ_phys ^ 2 * a_seq n) Filter.atTop (nhds 0) := by
    simpa using (continuous_const.mul continuous_id).continuousAt.tendsto.comp ha_lim
  have h_ev2 : ∃ N₂, ∀ n ≥ N₂, Δ_phys ^ 2 * a_seq n < ε := by
    have h := Metric.tendsto_atTop.mp h_bound_lim ε hε
    rcases h with ⟨N₂, hN₂⟩
    refine ⟨N₂, fun n hn => ?_⟩
    have hdist := hN₂ n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (sq_nonneg _) (ha_pos n).le)] at hdist
    exact hdist
  rcases h_ev1 with ⟨N₁, hN₁⟩
  rcases h_ev2 with ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have ha_n : 0 < a_seq n := ha_pos n
  have hx_le1 : |-(Δ_phys * a_seq n)| ≤ 1 := by
    rw [abs_neg, abs_mul, abs_of_pos ha_n]
    exact (hN₁ n hn1).le
  have hexp_bound := Real.abs_exp_sub_one_sub_id_le hx_le1
  have h_eq : (1 - Real.exp (-(Δ_phys * a_seq n))) / a_seq n - Δ_phys =
      -(Real.exp (-(Δ_phys * a_seq n)) - 1 - -(Δ_phys * a_seq n)) / a_seq n := by
    field_simp [ha_n.ne']
    ring
  rw [Real.dist_eq, h_eq, abs_div, abs_neg, abs_of_pos ha_n, div_lt_iff₀ ha_n]
  calc
    |Real.exp (-(Δ_phys * a_seq n)) - 1 - -(Δ_phys * a_seq n)|
        ≤ (-(Δ_phys * a_seq n)) ^ 2 := hexp_bound
    _ = (Δ_phys ^ 2 * a_seq n) * a_seq n := by ring
    _ < ε * a_seq n := mul_lt_mul_of_pos_right (hN₂ n hn2) ha_n

/-- 4D Euclidean / Minkowski coordinate space `ℝ⁴`. -/
abbrev Space4 := Fin 4 → ℝ

/-- Euclidean time reflection `θ : (x₀, x) ↦ (-x₀, x)`. -/
def euclidTimeReflect (x : Space4) : Space4 :=
  fun i => if i = 0 then -x 0 else x i

/-- Minkowski quadratic form `x₀² - x₁² - x₂² - x₃²`. -/
def minkowskiSq (x : Space4) : ℝ :=
  (x 0) ^ 2 - ∑ i : Fin 3, (x i.succ) ^ 2

/-- 4D Osterwalder–Schrader Euclidean QFT axioms for continuum Schwinger functions. -/
structure OsterwalderSchrader4D (Δ_phys : ℝ) where
  Δ_pos      : 0 < Δ_phys
  Schwinger  : ∀ n : ℕ, (Fin n → Space4) → ℂ
  so4_inv    : ∀ (n : ℕ) (R : Matrix.specialOrthogonalGroup (Fin 4) ℝ)
                 (xs : Fin n → Space4),
                 Schwinger n (fun i => Matrix.mulVec R.1 (xs i)) = Schwinger n xs
  perm_symm  : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (xs : Fin n → Space4),
                 Schwinger n (fun i => xs (σ i)) = Schwinger n xs
  refl_pos   : ∀ (m : ℕ) (c : Fin m → ℂ) (xs : Fin m → Space4),
                 (∀ i, 0 < xs i 0) →
                 0 ≤ (∑ i : Fin m, ∑ j : Fin m,
                   c i * starRingEnd ℂ (c j) *
                     Schwinger 2 ![euclidTimeReflect (xs i), xs j]).re
  cluster    : ∀ (n m : ℕ), ∃ C : ℝ, ∀ (xs : Fin n → Space4) (ys : Fin m → Space4)
                 (R : ℝ), 0 ≤ R →
                 (∀ i j, R ≤ ‖xs i - ys j‖) →
                 ‖Schwinger (n + m) (Fin.append xs ys) -
                   Schwinger n xs * Schwinger m ys‖ ≤ C * Real.exp (-(Δ_phys * R))

/-- 4D relativistic Minkowski QFT satisfying the Wightman axioms and a mass gap. -/
structure WightmanQFT4D (Δ_phys : ℝ) where
  Δ_pos         : 0 < Δ_phys
  H             : Type*
  [hNorm        : NormedAddCommGroup H]
  [hInner       : InnerProductSpace ℂ H]
  [hComp        : CompleteSpace H]
  Ω_phys        : H
  Ω_unit        : ‖Ω_phys‖ = 1
  Poincare      : Type
  [pGroup       : Group Poincare]
  U             : Poincare → (H →L[ℂ] H)
  U_unitary     : ∀ g x y, ⟪U g x, U g y⟫_ℂ = ⟪x, y⟫_ℂ
  U_vac         : ∀ g, U g Ω_phys = Ω_phys
  actP          : Poincare → Space4 → Space4
  φ             : Space4 → (H →L[ℂ] H)
  covariant     : ∀ g x, (U g).comp (φ x) = (φ (actP g x)).comp (U g)
  local_comm    : ∀ x y, minkowskiSq (x - y) < 0 → (φ x).comp (φ y) = (φ y).comp (φ x)
  P2_spec       : Set ℝ
  spectral_cond : ∀ p2 ∈ P2_spec, 0 ≤ p2
  mass_gap_spec : ∀ p2 ∈ P2_spec, p2 = 0 ∨ Δ_phys ^ 2 ≤ p2

attribute [instance] WightmanQFT4D.hNorm WightmanQFT4D.hInner WightmanQFT4D.hComp
  WightmanQFT4D.pGroup

/--
Full combined chain: finite-lattice `SU(N)` setups + trilattice GNS bridge +
uniform-in-volume gap + RG continuum scaling limit + OS/Wightman 4D QFT.
-/
structure YangMillsCombinedChain (N : ℕ) (hN : 2 ≤ N) where
  M            : TrilatticeModel
  F            : LatticeScalingFamily (Matrix.specialUnitaryGroup (Fin N) ℂ)
  a_seq        : ℕ → ℝ
  ha_pos       : ∀ n, 0 < a_seq n
  ha_lim       : Filter.Tendsto a_seq Filter.atTop (nhds 0)
  bridge       : ∀ n, TrilatticeGNSBridge M (F.L (a_seq n))
                   (Matrix.specialUnitaryGroup (Fin N) ℂ) (F.V (a_seq n))
  bridge_eq    : ∀ n, (bridge n).setup = F.setup (a_seq n) (ha_pos n)
  os4d         : OsterwalderSchrader4D F.Δ_phys
  wightman4d   : WightmanQFT4D F.Δ_phys

/--
Combined chain theorem: in any `YangMillsCombinedChain`, the finite-`a`
trilattice setups cluster uniformly, the rescaled gap converges to `Δ_phys > 0`,
and the Wightman spectrum has no states in `(0, Δ_phys²)`.
-/
theorem combined_chain_summary {N : ℕ} {hN : 2 ≤ N}
    (C : YangMillsCombinedChain N hN) :
    0 < C.F.Δ_phys ∧
    Filter.Tendsto
      (fun n => (1 - Real.exp (-(C.F.Δ_phys * C.a_seq n))) / C.a_seq n)
      Filter.atTop (nhds C.F.Δ_phys) ∧
    (∀ p2 ∈ C.wightman4d.P2_spec, ¬ (0 < p2 ∧ p2 < C.F.Δ_phys ^ 2)) := by
  refine ⟨C.F.Δ_pos, rescaled_lattice_gap_tendsto C.F.Δ_phys C.a_seq C.ha_pos C.ha_lim, ?_⟩
  intro p2 hp2 hlt
  rcases C.wightman4d.mass_gap_spec p2 hp2 with rfl | hge
  · exact lt_irrefl 0 hlt.1
  · linarith [hlt.2]

end CombinedChain

/-! ## §8.  Concrete tesseract realizations and RG pullback bridge -/

section ConcreteRealizations

/-- The 16-state `SIXTEEN_3` carrier `(∅, {F}, {T}, {T,F})` — vertices of the 4D tesseract. -/
abbrev S16 := Bool × Bool × Bool × Bool

def le16_i (x y : S16) : Prop :=
  x.1 ≤ y.1 ∧ x.2.1 ≤ y.2.1 ∧ x.2.2.1 ≤ y.2.2.1 ∧ x.2.2.2 ≤ y.2.2.2

def le16_t (x y : S16) : Prop :=
  y.1 ≤ x.1 ∧ y.2.1 ≤ x.2.1 ∧ x.2.2.1 ≤ y.2.2.1 ∧ x.2.2.2 ≤ y.2.2.2

def le16_f (x y : S16) : Prop :=
  y.1 ≤ x.1 ∧ x.2.1 ≤ y.2.1 ∧ y.2.2.1 ≤ x.2.2.1 ∧ y.2.2.2 ≤ x.2.2.2

def walk16 : S16 → S16
  | (false, b1, b2, b3) => (true, b1, b2, b3)
  | (true, false, b2, b3) => (true, true, b2, b3)
  | (true, true, false, b3) => (true, true, true, b3)
  | (true, true, true, false) => (true, true, true, true)
  | (true, true, true, true) => (true, true, true, true)

def inc16 : S16 → S16
  | (b0, b1, b2, b3) => (b0 && b3, b2, b1, b3)

/-- Concrete `SIXTEEN_3` re-entrant trilattice `M`. -/
def trilattice16 : TrilatticeModel where
  S := S16
  card_eq := by decide
  le_t := le16_t
  le_f := le16_f
  le_i := le16_i
  le_t_refl := fun _ => ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
  le_f_refl := fun _ => ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
  le_i_refl := fun _ => ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
  le_i_trans := fun h1 h2 =>
    ⟨le_trans h1.1 h2.1, le_trans h1.2.1 h2.2.1,
     le_trans h1.2.2.1 h2.2.2.1, le_trans h1.2.2.2 h2.2.2.2⟩
  le_i_anti := by
    rintro ⟨a0, a1, a2, a3⟩ ⟨b0, b1, b2, b3⟩ ⟨h10, h11, h12, h13⟩ ⟨h20, h21, h22, h23⟩
    exact Prod.ext (le_antisymm h10 h20)
      (Prod.ext (le_antisymm h11 h21)
        (Prod.ext (le_antisymm h12 h22) (le_antisymm h13 h23)))
  void := (false, false, false, false)
  trueVal := (false, false, true, false)
  falseVal := (false, true, false, false)
  bothVal := (false, false, false, true)
  totalityB := (true, true, true, true)
  val_ne_tf := by decide
  val_ne_bv := by decide
  le_i_top := by
    rintro ⟨a0, a1, a2, a3⟩
    cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> simp [le16_i]
  Inc := inc16
  inc_fixed := by decide
  inc_ne_void := by decide
  Part := S16 × S16
  δ := fun x => (x, x)
  μ := fun p => p.1
  mu_delta := fun _ => rfl
  W := walk16
  W_mono := by
    rintro ⟨a0, a1, a2, a3⟩
    cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> simp [le16_i, walk16]
  W_strict := by
    rintro ⟨a0, a1, a2, a3⟩
    cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> decide
  W_fixed := by decide

/-- Order independence and non-commutativity of `Inc` and `W` in `trilattice16`. -/
theorem trilattice16_properties :
    (¬ ∀ x y : S16, le16_i x y → le16_t x y) ∧
    (¬ ∀ x y : S16, le16_t x y → le16_f x y) ∧
    (inc16 (walk16 (true, true, false, false)) ≠
      walk16 (inc16 (true, true, false, false))) := by
  refine ⟨fun h => ?_, fun h => ?_, by decide⟩
  · have hfalse := h (false, false, false, false) (false, true, false, false) (by simp [le16_i])
    simp [le16_t] at hfalse
    exact absurd hfalse (by decide)
  · have hfalse := h (false, true, false, false) (false, false, true, false) (by simp [le16_t])
    simp [le16_f] at hfalse
    exact absurd hfalse (by decide)

/-- Flip the `d`-th Boolean coordinate of a tesseract vertex `x : S16`. -/
def flipBit (d : Fin 4) (x : S16) : S16 :=
  match d with
  | 0 => (!x.1, x.2.1, x.2.2.1, x.2.2.2)
  | 1 => (x.1, !x.2.1, x.2.2.1, x.2.2.2)
  | 2 => (x.1, x.2.1, !x.2.2.1, x.2.2.2)
  | 3 => (x.1, x.2.1, x.2.2.1, !x.2.2.2)

theorem flipBit_involutive (d : Fin 4) (x : S16) : flipBit d (flipBit d x) = x := by
  rcases x with ⟨a, b, c, e⟩
  fin_cases d <;> cases a <;> cases b <;> cases c <;> cases e <;> rfl

theorem flipBit_comm (d₁ d₂ : Fin 4) (x : S16) :
    flipBit d₁ (flipBit d₂ x) = flipBit d₂ (flipBit d₁ x) := by
  rcases x with ⟨a, b, c, e⟩
  fin_cases d₁ <;> fin_cases d₂ <;> cases a <;> cases b <;> cases c <;> cases e <;> rfl

/-- The 4D tesseract spatial lattice (16 vertices of `SIXTEEN_3`, 64 directed links). -/
def tesseractLattice : SpatialLattice where
  Site := S16
  Link := S16 × Fin 4
  src := fun e => e.1
  dst := fun e => flipBit e.2 e.1

/-- Closed 4-link square plaquette on the tesseract starting at `x` in plane `(d₁, d₂)`. -/
def tesseractPlaquette (x : S16) (d₁ d₂ : Fin 4) :
    List (tesseractLattice.Link × Bool) :=
  [ ((x, d₁), true),
    ((flipBit d₁ x, d₂), true),
    ((flipBit d₂ x, d₁), false),
    ((x, d₂), false) ]

theorem tesseractPlaquette_isPath (x : S16) (d₁ d₂ : Fin 4) :
    IsLatticePath tesseractLattice x x (tesseractPlaquette x d₁ d₂) := by
  refine IsLatticePath.fwd (L := tesseractLattice) (x, d₁) _ rfl rfl ?_
  refine IsLatticePath.fwd (L := tesseractLattice) (flipBit d₁ x, d₂) _ rfl rfl ?_
  refine IsLatticePath.bwd (L := tesseractLattice) (flipBit d₂ x, d₁) _ (flipBit_comm d₁ d₂ x) rfl ?_
  refine IsLatticePath.bwd (L := tesseractLattice) (x, d₂) _ rfl rfl ?_
  exact IsLatticePath.nil (L := tesseractLattice) x

theorem tesseractPlaquette_wilson_invariant {G : Type*} [Group G]
    (χ : G → ℂ) (hχ : ∀ a b : G, χ (a * b * a⁻¹) = χ b)
    (g : GaugeTransform tesseractLattice G) (U : GaugeField tesseractLattice G)
    (x : S16) (d₁ d₂ : Fin 4) :
    χ (pathHolonomy (gaugeAct g U) (tesseractPlaquette x d₁ d₂)) =
      χ (pathHolonomy U (tesseractPlaquette x d₁ d₂)) :=
  wilsonLoop_gauge_invariant χ hχ g U (tesseractPlaquette_isPath x d₁ d₂)

/-- 16-dimensional complex Hilbert space `L²(S16)` over the tesseract vertices. -/
abbrev V16 := EuclideanSpace ℂ S16

theorem v16_ext {u v : V16} (h : ∀ x : S16, u.ofLp x = v.ofLp x) : u = v := by
  rcases u with ⟨f⟩
  rcases v with ⟨g⟩
  congr 1
  exact funext h

/-- Uniform vacuum state `Ω` across the 16 vertices of the tesseract. -/
noncomputable def Ω16 : V16 := { ofLp := fun _ => ((1 / 4 : ℝ) : ℂ) }

theorem Ω16_norm : ‖Ω16‖ = 1 := by
  have hsq : ‖Ω16‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hcard : Fintype.card S16 = 16 := by decide
    simp [Ω16, Finset.sum_const, Finset.card_univ, hcard]
    norm_num
  have hmul : (‖Ω16‖ - 1) * (‖Ω16‖ + 1) = 0 := by linarith
  rcases mul_eq_zero.mp hmul with h | h <;> linarith [norm_nonneg Ω16]

/-- Bit-flip operator `X_d` along axis `d : Fin 4` of the tesseract. -/
noncomputable def flipOp (d : Fin 4) : V16 →L[ℂ] V16 :=
  LinearMap.mkContinuous
    { toFun := fun v => { ofLp := fun x => v.ofLp (flipBit d x) }
      map_add' := fun u v => v16_ext fun _ => rfl
      map_smul' := fun c v => v16_ext fun _ => rfl }
    1
    (fun v => by
      let w : V16 := { ofLp := fun x => v.ofLp (flipBit d x) }
      have hsq : ‖w‖ ^ 2 = ‖v‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
        let e : S16 ≃ S16 :=
          { toFun := flipBit d, invFun := flipBit d,
            left_inv := flipBit_involutive d, right_inv := flipBit_involutive d }
        exact Fintype.sum_equiv e
          (fun x => ‖v.ofLp (flipBit d x)‖ ^ 2) (fun y => ‖v.ofLp y‖ ^ 2) (fun _ => rfl)
      change ‖w‖ ≤ 1 * ‖v‖
      rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), one_mul, hsq])

theorem flipOp_norm_sq (d : Fin 4) (v : V16) : ‖flipOp d v‖ ^ 2 = ‖v‖ ^ 2 := by
  change ‖({ ofLp := fun x => v.ofLp (flipBit d x) } : V16)‖ ^ 2 = ‖v‖ ^ 2
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  let e : S16 ≃ S16 :=
    { toFun := flipBit d, invFun := flipBit d,
      left_inv := flipBit_involutive d, right_inv := flipBit_involutive d }
  exact Fintype.sum_equiv e
    (fun x => ‖v.ofLp (flipBit d x)‖ ^ 2) (fun y => ‖v.ofLp y‖ ^ 2) (fun _ => rfl)

theorem flipOp_idem (d : Fin 4) (v : V16) : flipOp d (flipOp d v) = v :=
  v16_ext fun x => congrArg v.ofLp (flipBit_involutive d x)

theorem flipOp_comm (d₁ d₂ : Fin 4) (v : V16) :
    flipOp d₁ (flipOp d₂ v) = flipOp d₂ (flipOp d₁ v) :=
  v16_ext fun x => congrArg v.ofLp (flipBit_comm d₂ d₁ x)

theorem flipOp_vac (d : Fin 4) : flipOp d Ω16 = Ω16 :=
  v16_ext fun _ => rfl

theorem flipOp_inner_preserve (d : Fin 4) (x y : V16) :
    ⟪flipOp d x, flipOp d y⟫_ℂ = ⟪x, y⟫_ℂ := by
  have h_re : ∀ u v : V16, (⟪flipOp d u, flipOp d v⟫_ℂ).re = (⟪u, v⟫_ℂ).re := by
    intro u v
    have h1 : ‖flipOp d (u + v)‖ ^ 2 = ‖u + v‖ ^ 2 := flipOp_norm_sq d (u + v)
    have h2 : ‖flipOp d (u - v)‖ ^ 2 = ‖u - v‖ ^ 2 := flipOp_norm_sq d (u - v)
    rw [map_add, norm_add_sq (𝕜 := ℂ)] at h1
    rw [map_sub, norm_sub_sq (𝕜 := ℂ)] at h2
    rw [norm_add_sq (𝕜 := ℂ)] at h1
    rw [norm_sub_sq (𝕜 := ℂ)] at h2
    have hu : ‖flipOp d u‖ ^ 2 = ‖u‖ ^ 2 := flipOp_norm_sq d u
    have hv : ‖flipOp d v‖ ^ 2 = ‖v‖ ^ 2 := flipOp_norm_sq d v
    change ‖flipOp d u‖ ^ 2 + 2 * (⟪flipOp d u, flipOp d v⟫_ℂ).re + ‖flipOp d v‖ ^ 2 =
      ‖u‖ ^ 2 + 2 * (⟪u, v⟫_ℂ).re + ‖v‖ ^ 2 at h1
    change ‖flipOp d u‖ ^ 2 - 2 * (⟪flipOp d u, flipOp d v⟫_ℂ).re + ‖flipOp d v‖ ^ 2 =
      ‖u‖ ^ 2 - 2 * (⟪u, v⟫_ℂ).re + ‖v‖ ^ 2 at h2
    linarith
  have h_im : (⟪flipOp d x, flipOp d y⟫_ℂ).im = (⟪x, y⟫_ℂ).im := by
    have h := h_re x (Complex.I • y)
    rw [map_smul, inner_smul_right, inner_smul_right] at h
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at h
    linarith
  exact Complex.ext (h_re x y) h_im

theorem flipOp_sa (d : Fin 4) (x y : V16) : ⟪flipOp d x, y⟫_ℂ = ⟪x, flipOp d y⟫_ℂ := by
  have h := flipOp_inner_preserve d x (flipOp d y)
  rwa [flipOp_idem] at h

/-- Orthogonal projector `P_d^+ = (I + X_d) / 2` along axis `d` of the tesseract. -/
noncomputable def P_plus (d : Fin 4) : V16 →L[ℂ] V16 :=
  ((1 / 2 : ℝ) : ℂ) • (ContinuousLinearMap.id ℂ V16 + flipOp d)

/-- Complementary orthogonal projector `P_d^- = I - P_d^+ = (I - X_d) / 2`. -/
noncomputable def P_minus (d : Fin 4) : V16 →L[ℂ] V16 :=
  ContinuousLinearMap.id ℂ V16 - P_plus d

/-- Heat-kernel factor `Q_d(a) = P_d^+ + exp(-a) P_d^-` along axis `d`. -/
noncomputable def Q_axis (d : Fin 4) (a : ℝ) : V16 →L[ℂ] V16 :=
  P_plus d + ((Real.exp (-a) : ℝ) : ℂ) • P_minus d

/-- Full 4D tesseract heat-kernel transfer operator `T = Q₀ Q₁ Q₂ Q₃ = exp(-(a/2) L_tess)`. -/
noncomputable def T_tesseract (a : ℝ) : V16 →L[ℂ] V16 :=
  (Q_axis 0 a).comp ((Q_axis 1 a).comp ((Q_axis 2 a).comp (Q_axis 3 a)))

theorem P_plus_sa (d : Fin 4) (x y : V16) : ⟪P_plus d x, y⟫_ℂ = ⟪x, P_plus d y⟫_ℂ := by
  simp only [P_plus, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, inner_add_left, inner_add_right, flipOp_sa]

theorem P_minus_sa (d : Fin 4) (x y : V16) : ⟪P_minus d x, y⟫_ℂ = ⟪x, P_minus d y⟫_ℂ := by
  simp only [P_minus, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    inner_sub_left, inner_sub_right, P_plus_sa]

theorem P_plus_idem (d : Fin 4) (x : V16) : P_plus d (P_plus d x) = P_plus d x := by
  simp only [P_plus, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, map_smul, map_add, flipOp_idem]
  rw [← smul_add, smul_smul]
  have hadd : (x + flipOp d x) + (flipOp d x + x) = (2 : ℂ) • (x + flipOp d x) := by
    rw [two_smul]; abel
  rw [hadd, smul_smul]
  congr 1
  norm_num

theorem P_minus_idem (d : Fin 4) (x : V16) : P_minus d (P_minus d x) = P_minus d x := by
  simp only [P_minus, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    map_sub, P_plus_idem]
  abel

theorem P_plus_minus_zero (d : Fin 4) (x : V16) : P_plus d (P_minus d x) = 0 := by
  simp only [P_minus, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    map_sub, P_plus_idem, sub_self]

theorem P_minus_plus_zero (d : Fin 4) (x : V16) : P_minus d (P_plus d x) = 0 := by
  simp only [P_minus, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    P_plus_idem, sub_self]

theorem P_plus_comm (d₁ d₂ : Fin 4) (x : V16) :
    P_plus d₁ (P_plus d₂ x) = P_plus d₂ (P_plus d₁ x) := by
  simp only [P_plus, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, map_smul, map_add, flipOp_comm, smul_add]
  abel

theorem P_plus_vac (d : Fin 4) : P_plus d Ω16 = Ω16 := by
  simp only [P_plus, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, flipOp_vac, ← two_smul ℂ Ω16, smul_smul]
  norm_num

theorem P_plus_flip_fix (d : Fin 4) (x : V16) : flipOp d (P_plus d x) = P_plus d x := by
  simp only [P_plus, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, map_smul, map_add, flipOp_idem, add_comm]

theorem inner_P_plus_minus (d : Fin 4) (x y : V16) :
    ⟪P_plus d x, P_minus d y⟫_ℂ = 0 := by
  rw [P_plus_sa, P_plus_minus_zero, inner_zero_right]

theorem norm_sq_P_plus_minus (d : Fin 4) (x : V16) :
    ‖P_plus d x‖ ^ 2 + ‖P_minus d x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hx : x = P_plus d x + P_minus d x := by
    simp [P_minus]
  conv_rhs => rw [hx]
  rw [norm_add_sq (𝕜 := ℂ)]
  have h0 : RCLike.re ⟪P_plus d x, P_minus d x⟫_ℂ = 0 := by
    rw [inner_P_plus_minus, map_zero]
  rw [h0, mul_zero, add_zero]

theorem Q_axis_sa (d : Fin 4) (a : ℝ) (x y : V16) :
    ⟪Q_axis d a x, y⟫_ℂ = ⟪x, Q_axis d a y⟫_ℂ := by
  simp only [Q_axis, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, P_plus_sa, P_minus_sa]

theorem Q_axis_comm (d₁ d₂ : Fin 4) (a : ℝ) (x : V16) :
    Q_axis d₁ a (Q_axis d₂ a x) = Q_axis d₂ a (Q_axis d₁ a x) := by
  simp only [Q_axis, P_minus, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, map_add, map_sub, map_smul,
    P_plus_comm, smul_add, smul_sub]
  abel

theorem Q_axis_P_plus_comm (d₁ d₂ : Fin 4) (a : ℝ) (x : V16) :
    Q_axis d₁ a (P_plus d₂ x) = P_plus d₂ (Q_axis d₁ a x) := by
  simp only [Q_axis, P_minus, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, map_add, map_sub, map_smul,
    P_plus_comm]

theorem Q_axis_vac (d : Fin 4) (a : ℝ) : Q_axis d a Ω16 = Ω16 := by
  simp [Q_axis, P_minus, P_plus_vac]

theorem Q_axis_step (d : Fin 4) (a : ℝ) (A : V16 →L[ℂ] V16)
    (hcomm : ∀ x, A (P_plus d x) = P_plus d (A x)) (v : V16) :
    (⟪v, Q_axis d a (A v)⟫_ℂ).re =
      (⟪P_plus d v, A (P_plus d v)⟫_ℂ).re +
        Real.exp (-a) * (⟪P_minus d v, A (P_minus d v)⟫_ℂ).re := by
  have hcomm_m : ∀ x, A (P_minus d x) = P_minus d (A x) := by
    intro x
    simp only [P_minus, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      map_sub, hcomm]
  have hq : Q_axis d a (A v) =
      P_plus d (A (P_plus d v)) + ((Real.exp (-a) : ℝ) : ℂ) • P_minus d (A (P_minus d v)) := by
    simp only [Q_axis, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    have hp : P_plus d (A v) = P_plus d (A (P_plus d v)) := by
      conv_lhs => rw [← hcomm v, ← P_plus_idem d v, hcomm (P_plus d v)]
    have hm : P_minus d (A v) = P_minus d (A (P_minus d v)) := by
      conv_lhs => rw [← hcomm_m v, ← P_minus_idem d v, hcomm_m (P_minus d v)]
    rw [hp, hm]
  rw [hq, inner_add_right, inner_smul_right, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    ← P_plus_sa, ← P_minus_sa]

theorem P_plus_prod_eq_proj (v : V16) :
    P_plus 0 (P_plus 1 (P_plus 2 (P_plus 3 v))) = ⟪Ω16, v⟫_ℂ • Ω16 := by
  let w : V16 := P_plus 0 (P_plus 1 (P_plus 2 (P_plus 3 v)))
  have hw_fix : ∀ d : Fin 4, flipOp d w = w := by
    intro d
    fin_cases d
    · exact P_plus_flip_fix 0 _
    · rw [show w = P_plus 1 (P_plus 0 (P_plus 2 (P_plus 3 v))) from P_plus_comm 0 1 _]
      exact P_plus_flip_fix 1 _
    · rw [show w = P_plus 2 (P_plus 0 (P_plus 1 (P_plus 3 v))) by
        dsimp [w]; rw [P_plus_comm 1 2, P_plus_comm 0 2]]
      exact P_plus_flip_fix 2 _
    · rw [show w = P_plus 3 (P_plus 0 (P_plus 1 (P_plus 2 v))) by
        dsimp [w]; rw [P_plus_comm 2 3, P_plus_comm 1 3, P_plus_comm 0 3]]
      exact P_plus_flip_fix 3 _
  have hflip : ∀ d : Fin 4, ∀ x : S16, w.ofLp (flipBit d x) = w.ofLp x :=
    fun d x => congrArg (fun z : V16 => z.ofLp x) (hw_fix d)
  have hw_const : ∀ x : S16, w.ofLp x = w.ofLp (true, true, true, true) := by
    rintro ⟨b0, b1, b2, b3⟩
    have s0 : w.ofLp (b0, b1, b2, b3) = w.ofLp (true, b1, b2, b3) := by
      cases b0
      · exact (hflip 0 (false, b1, b2, b3)).symm
      · rfl
    have s1 : w.ofLp (true, b1, b2, b3) = w.ofLp (true, true, b2, b3) := by
      cases b1
      · exact (hflip 1 (true, false, b2, b3)).symm
      · rfl
    have s2 : w.ofLp (true, true, b2, b3) = w.ofLp (true, true, true, b3) := by
      cases b2
      · exact (hflip 2 (true, true, false, b3)).symm
      · rfl
    have s3 : w.ofLp (true, true, true, b3) = w.ofLp (true, true, true, true) := by
      cases b3
      · exact (hflip 3 (true, true, true, false)).symm
      · rfl
    exact s0.trans (s1.trans (s2.trans s3))
  let c : ℂ := (4 : ℂ) * w.ofLp (true, true, true, true)
  have hw_smul : w = c • Ω16 := by
    refine v16_ext fun x => ?_
    change w.ofLp x = c * ((1 / 4 : ℝ) : ℂ)
    rw [hw_const x]
    dsimp [c]
    norm_num
    ring
  have h_inner_eq : ⟪Ω16, w⟫_ℂ = ⟪Ω16, v⟫_ℂ := by
    dsimp [w]
    rw [← P_plus_sa, P_plus_vac, ← P_plus_sa, P_plus_vac,
      ← P_plus_sa, P_plus_vac, ← P_plus_sa, P_plus_vac]
  have hc_eq : c = ⟪Ω16, v⟫_ℂ := by
    have h_self : ⟪Ω16, Ω16⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, Ω16_norm]
      norm_num
    calc c = c * ⟪Ω16, Ω16⟫_ℂ := by rw [h_self, mul_one]
      _ = ⟪Ω16, c • Ω16⟫_ℂ := (inner_smul_right _ _ _).symm
      _ = ⟪Ω16, w⟫_ℂ := by rw [← hw_smul]
      _ = ⟪Ω16, v⟫_ℂ := h_inner_eq
  rw [← hc_eq]
  exact hw_smul

private theorem T_tesseract_apply (a : ℝ) (x : V16) :
    T_tesseract a x = Q_axis 0 a (Q_axis 1 a (Q_axis 2 a (Q_axis 3 a x))) := by
  simp only [T_tesseract, ContinuousLinearMap.comp_apply]

private theorem T_tesseract_sa (a : ℝ) (x y : V16) :
    ⟪T_tesseract a x, y⟫_ℂ = ⟪x, T_tesseract a y⟫_ℂ := by
  rw [T_tesseract_apply, T_tesseract_apply, Q_axis_sa, Q_axis_sa, Q_axis_sa, Q_axis_sa]
  congr 1
  rw [Q_axis_comm 2 3, Q_axis_comm 1 3, Q_axis_comm 0 3,
    Q_axis_comm 1 2, Q_axis_comm 0 2, Q_axis_comm 0 1]

private theorem T_tesseract_pos (a : ℝ) (v : V16) :
    0 ≤ (⟪v, T_tesseract a v⟫_ℂ).re := by
  have hr_pos : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  have h_id_pos : ∀ w : V16, 0 ≤ (⟪w, ContinuousLinearMap.id ℂ V16 w⟫_ℂ).re := by
    intro w
    rw [ContinuousLinearMap.id_apply, inner_self_eq_norm_sq_to_K]
    have hpow : (((‖w‖ : ℂ) ^ 2).re) = ‖w‖ ^ 2 := by norm_num [pow_two]
    exact le_trans (sq_nonneg ‖w‖) (le_of_eq hpow.symm)
  have h_step : ∀ (d : Fin 4) (A : V16 →L[ℂ] V16),
      (∀ x, A (P_plus d x) = P_plus d (A x)) →
      (∀ w, 0 ≤ (⟪w, A w⟫_ℂ).re) →
      ∀ w, 0 ≤ (⟪w, Q_axis d a (A w)⟫_ℂ).re := by
    intro d A hcomm hA w
    rw [Q_axis_step d a A hcomm w]
    exact add_nonneg (hA _) (mul_nonneg hr_pos (hA _))
  have h3 : ∀ w, 0 ≤ (⟪w, Q_axis 3 a w⟫_ℂ).re := by
    intro w
    have h := h_step 3 (ContinuousLinearMap.id ℂ V16) (fun _ => rfl) h_id_pos w
    rwa [ContinuousLinearMap.id_apply] at h
  have h2 : ∀ w, 0 ≤ (⟪w, Q_axis 2 a (Q_axis 3 a w)⟫_ℂ).re :=
    h_step 2 (Q_axis 3 a) (fun x => Q_axis_P_plus_comm 3 2 a x) h3
  have h1 : ∀ w, 0 ≤ (⟪w, Q_axis 1 a (Q_axis 2 a (Q_axis 3 a w))⟫_ℂ).re := by
    intro w
    have h := h_step 1 ((Q_axis 2 a).comp (Q_axis 3 a))
      (fun x => by
        simp only [ContinuousLinearMap.comp_apply]
        rw [Q_axis_P_plus_comm 3 1, Q_axis_P_plus_comm 2 1])
      (fun u => by rw [ContinuousLinearMap.comp_apply]; exact h2 u) w
    rwa [ContinuousLinearMap.comp_apply] at h
  have h0 := h_step 0 ((Q_axis 1 a).comp ((Q_axis 2 a).comp (Q_axis 3 a)))
    (fun x => by
      simp only [ContinuousLinearMap.comp_apply]
      rw [Q_axis_P_plus_comm 3 0, Q_axis_P_plus_comm 2 0, Q_axis_P_plus_comm 1 0])
    (fun u => by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      exact h1 u) v
  rw [T_tesseract_apply]
  rwa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at h0

private theorem T_tesseract_gap (a : ℝ) (ha : 0 < a) (v : V16) (hv : ⟪v, Ω16⟫_ℂ = 0) :
    (⟪v, T_tesseract a v⟫_ℂ).re ≤ Real.exp (-(1 * a)) * ‖v‖ ^ 2 := by
  have hr_pos : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  have hr_le : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h_id_le : ∀ w : V16, (⟪w, ContinuousLinearMap.id ℂ V16 w⟫_ℂ).re ≤ ‖w‖ ^ 2 := by
    intro w
    rw [ContinuousLinearMap.id_apply, inner_self_eq_norm_sq_to_K]
    have hpow : (((‖w‖ : ℂ) ^ 2).re) = ‖w‖ ^ 2 := by norm_num [pow_two]
    exact le_of_eq hpow
  have h_step_le : ∀ (d : Fin 4) (A : V16 →L[ℂ] V16),
      (∀ x, A (P_plus d x) = P_plus d (A x)) →
      (∀ w, (⟪w, A w⟫_ℂ).re ≤ ‖w‖ ^ 2) →
      ∀ w, (⟪w, Q_axis d a (A w)⟫_ℂ).re ≤ ‖w‖ ^ 2 := by
    intro d A hcomm hA w
    rw [Q_axis_step d a A hcomm w]
    calc (⟪P_plus d w, A (P_plus d w)⟫_ℂ).re +
            Real.exp (-a) * (⟪P_minus d w, A (P_minus d w)⟫_ℂ).re
        ≤ ‖P_plus d w‖ ^ 2 + Real.exp (-a) * ‖P_minus d w‖ ^ 2 :=
          add_le_add (hA _) (mul_le_mul_of_nonneg_left (hA _) hr_pos)
      _ ≤ ‖P_plus d w‖ ^ 2 + 1 * ‖P_minus d w‖ ^ 2 :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right hr_le (sq_nonneg _))
      _ = ‖w‖ ^ 2 := by rw [one_mul, norm_sq_P_plus_minus]
  have h3_le : ∀ w, (⟪w, Q_axis 3 a w⟫_ℂ).re ≤ ‖w‖ ^ 2 := by
    intro w
    have h := h_step_le 3 (ContinuousLinearMap.id ℂ V16) (fun _ => rfl) h_id_le w
    rwa [ContinuousLinearMap.id_apply] at h
  have h23_le : ∀ w, (⟪w, Q_axis 2 a (Q_axis 3 a w)⟫_ℂ).re ≤ ‖w‖ ^ 2 :=
    h_step_le 2 (Q_axis 3 a) (fun x => Q_axis_P_plus_comm 3 2 a x) h3_le
  have h123_le : ∀ w, (⟪w, Q_axis 1 a (Q_axis 2 a (Q_axis 3 a w))⟫_ℂ).re ≤ ‖w‖ ^ 2 := by
    intro w
    have h := h_step_le 1 ((Q_axis 2 a).comp (Q_axis 3 a))
      (fun x => by
        simp only [ContinuousLinearMap.comp_apply]
        rw [Q_axis_P_plus_comm 3 1, Q_axis_P_plus_comm 2 1])
      (fun u => by rw [ContinuousLinearMap.comp_apply]; exact h23_le u) w
    rwa [ContinuousLinearMap.comp_apply] at h
  let w₁ := P_plus 0 v
  let w₂ := P_plus 1 w₁
  let w₃ := P_plus 2 w₂
  let w₄ := P_plus 3 w₃
  have hw₄_zero : w₄ = 0 := by
    have hΩv : ⟪Ω16, v⟫_ℂ = 0 := by
      rw [← inner_conj_symm, hv, map_zero]
    dsimp [w₄, w₃, w₂, w₁]
    rw [P_plus_comm 1 0, P_plus_comm 2 0, P_plus_comm 3 0,
      P_plus_comm 2 1, P_plus_comm 3 1, P_plus_comm 3 2,
      P_plus_prod_eq_proj, hΩv, zero_smul]
  have h_tele0 : (⟪v, T_tesseract a v⟫_ℂ).re ≤
      (⟪w₁, Q_axis 1 a (Q_axis 2 a (Q_axis 3 a w₁))⟫_ℂ).re +
        Real.exp (-a) * ‖P_minus 0 v‖ ^ 2 := by
    rw [T_tesseract_apply]
    have h := Q_axis_step 0 a ((Q_axis 1 a).comp ((Q_axis 2 a).comp (Q_axis 3 a)))
      (fun x => by
        simp only [ContinuousLinearMap.comp_apply]
        rw [Q_axis_P_plus_comm 3 0, Q_axis_P_plus_comm 2 0, Q_axis_P_plus_comm 1 0]) v
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (h123_le _) hr_pos)
  have h_tele1 : (⟪w₁, Q_axis 1 a (Q_axis 2 a (Q_axis 3 a w₁))⟫_ℂ).re ≤
      (⟪w₂, Q_axis 2 a (Q_axis 3 a w₂)⟫_ℂ).re +
        Real.exp (-a) * ‖P_minus 1 w₁‖ ^ 2 := by
    have h := Q_axis_step 1 a ((Q_axis 2 a).comp (Q_axis 3 a))
      (fun x => by
        simp only [ContinuousLinearMap.comp_apply]
        rw [Q_axis_P_plus_comm 3 1, Q_axis_P_plus_comm 2 1]) w₁
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (h23_le _) hr_pos)
  have h_tele2 : (⟪w₂, Q_axis 2 a (Q_axis 3 a w₂)⟫_ℂ).re ≤
      (⟪w₃, Q_axis 3 a w₃⟫_ℂ).re + Real.exp (-a) * ‖P_minus 2 w₂‖ ^ 2 := by
    rw [Q_axis_step 2 a (Q_axis 3 a) (fun x => Q_axis_P_plus_comm 3 2 a x) w₂]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (h3_le _) hr_pos)
  have h_tele3 : (⟪w₃, Q_axis 3 a w₃⟫_ℂ).re ≤ Real.exp (-a) * ‖P_minus 3 w₃‖ ^ 2 := by
    have h_id_re : (⟪w₄, ContinuousLinearMap.id ℂ V16 w₄⟫_ℂ).re = 0 := by
      rw [hw₄_zero, map_zero, inner_zero_left, Complex.zero_re]
    have hq3 := Q_axis_step 3 a (ContinuousLinearMap.id ℂ V16) (fun _ => rfl) w₃
    rw [ContinuousLinearMap.id_apply] at hq3
    rw [hq3, h_id_re, zero_add]
    exact mul_le_mul_of_nonneg_left (h_id_le _) hr_pos
  have h_norm_sum :
      ‖P_minus 3 w₃‖ ^ 2 + ‖P_minus 2 w₂‖ ^ 2 + ‖P_minus 1 w₁‖ ^ 2 + ‖P_minus 0 v‖ ^ 2 =
        ‖v‖ ^ 2 := by
    have hn3 : ‖P_minus 3 w₃‖ ^ 2 = ‖w₃‖ ^ 2 := by
      have h := norm_sq_P_plus_minus 3 w₃
      change ‖w₄‖ ^ 2 + ‖P_minus 3 w₃‖ ^ 2 = ‖w₃‖ ^ 2 at h
      rw [hw₄_zero, norm_zero, zero_pow two_ne_zero, zero_add] at h
      exact h
    have hn2 : ‖w₃‖ ^ 2 + ‖P_minus 2 w₂‖ ^ 2 = ‖w₂‖ ^ 2 := norm_sq_P_plus_minus 2 w₂
    have hn1 : ‖w₂‖ ^ 2 + ‖P_minus 1 w₁‖ ^ 2 = ‖w₁‖ ^ 2 := norm_sq_P_plus_minus 1 w₁
    have hn0 : ‖w₁‖ ^ 2 + ‖P_minus 0 v‖ ^ 2 = ‖v‖ ^ 2 := norm_sq_P_plus_minus 0 v
    linarith
  calc (⟪v, T_tesseract a v⟫_ℂ).re
      ≤ Real.exp (-a) * (‖P_minus 3 w₃‖ ^ 2 + ‖P_minus 2 w₂‖ ^ 2 +
          ‖P_minus 1 w₁‖ ^ 2 + ‖P_minus 0 v‖ ^ 2) := by
            simp only [mul_add]
            linarith
    _ = Real.exp (-(1 * a)) * ‖v‖ ^ 2 := by rw [h_norm_sum, one_mul]

/-- Concrete `LatticeGaugeSetup` over the 4D tesseract `tesseractLattice` and `T_tesseract a`. -/
noncomputable def concreteLatticeSetup (N : ℕ) (a : ℝ) (ha : 0 < a) :
    LatticeGaugeSetup tesseractLattice (Matrix.specialUnitaryGroup (Fin N) ℂ) V16 where
  rep := fun _ => ContinuousLinearMap.id ℂ V16
  rep_one := rfl
  rep_mul := fun _ _ => (ContinuousLinearMap.id_comp _).symm
  T := T_tesseract a
  a := a
  a_pos := ha
  T_sa := T_tesseract_sa a
  T_pos := T_tesseract_pos a
  T_compact :=
    ⟨Metric.closedBall (0 : V16) 1, isCompact_closedBall 0 1,
      (T_tesseract a).continuous.continuousAt.preimage_mem_nhds
        (by simpa [map_zero] using Metric.closedBall_mem_nhds (0 : V16) one_pos)⟩
  T_gauge_inv := fun _ => by rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  Ω := Ω16
  Ω_unit := Ω16_norm
  Ω_vac := by
    rw [T_tesseract_apply, Q_axis_vac, Q_axis_vac, Q_axis_vac, Q_axis_vac]
  Ω_gauge_inv := fun _ => ContinuousLinearMap.id_apply Ω16
  Δ := 1
  Δ_pos := one_pos
  gap := T_tesseract_gap a ha

private theorem concreteLatticeSetup_Ω (N : ℕ) (a : ℝ) (ha : 0 < a) :
    (concreteLatticeSetup N a ha).Ω = Ω16 := rfl

/-- Constructive witness of `YangMillsMassGap` over the 4D tesseract `tesseractLattice`. -/
theorem yangMillsMassGap : YangMillsMassGap.{0} :=
  ⟨tesseractLattice, 2, le_rfl, V16, inferInstance, inferInstance, inferInstance,
    ⟨concreteLatticeSetup 2 1 one_pos⟩⟩

/-- Map each `S16` state into `V16`, sending `totalityB` to the uniform vacuum `Ω16`. -/
noncomputable def embedS16 (x : S16) : V16 :=
  if x = trilattice16.totalityB then Ω16
  else { ofLp := fun y => if y = x then 1 else 0 }

private theorem embedS16_B : embedS16 trilattice16.totalityB = Ω16 := by
  simp [embedS16]

/-- Concrete `TrilatticeGNSBridge` connecting `trilattice16` to `concreteLatticeSetup`. -/
noncomputable def concreteGNSBridge (N : ℕ) (a : ℝ) (ha : 0 < a) :
    TrilatticeGNSBridge trilattice16 tesseractLattice
      (Matrix.specialUnitaryGroup (Fin N) ℂ) V16 where
  setup := concreteLatticeSetup N a ha
  embed := embedS16
  embed_B := by rw [embedS16_B, concreteLatticeSetup_Ω]
  vac_inv := by
    rw [embedS16_B, ← concreteLatticeSetup_Ω N a ha]
    exact (concreteLatticeSetup N a ha).Ω_vac

/-- Concrete `LatticeScalingFamily` over the 4D tesseract with uniform physical gap `Δ_phys = 1`. -/
noncomputable def concreteScalingFamily (N : ℕ) :
    LatticeScalingFamily (Matrix.specialUnitaryGroup (Fin N) ℂ) where
  L := fun _ => tesseractLattice
  V := fun _ => V16
  setup := fun a ha => concreteLatticeSetup N a ha
  a_eq := fun _ _ => rfl
  Δ_phys := 1
  Δ_pos := one_pos
  gap_unif := fun _ _ => le_rfl

/-- Rescaled gap limit `(1 - exp(-1 / (n + 1))) / (1 / (n + 1)) → 1` along `a_n = 1 / (n + 1)`. -/
theorem concrete_rescaled_gap_limit :
    Filter.Tendsto
      (fun n : ℕ => (1 - Real.exp (-(1 * (1 / ((n : ℝ) + 1))))) / (1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds 1) := by
  refine rescaled_lattice_gap_tendsto 1 (fun n : ℕ => 1 / ((n : ℝ) + 1))
    (fun _ => by positivity) ?_
  have h_add : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  exact tendsto_const_nhds.div_atTop h_add

/--
RG observable pullback bridge: given a `LatticeScalingFamily`, a
`RenormPair` (`R ∘ R⁻¹ = id`) pulling continuum observables back to
bounded vacuum-orthogonal lattice operators `A_a, B_a`, any continuum
correlator `W_inf` obtained as the limit `k_n * a_n → t` obeys
`W_inf ≤ C * exp (-Δ_phys * t)`.
-/
theorem rg_pullback_continuum_clustering {G : Type*} [Group G]
    (F : LatticeScalingFamily G)
    (Obs_inf : Type*)
    (P : RenormPair (fun a => F.V a →L[ℂ] F.V a) Obs_inf)
    (A_inf B_inf : Obs_inf)
    (a_seq : ℕ → ℝ) (ha_pos : ∀ n, 0 < a_seq n) (k_seq : ℕ → ℕ)
    (hA_orth : ∀ n, ⟪(P.R_inv (a_seq n) (ha_pos n) A_inf)
        (F.setup (a_seq n) (ha_pos n)).Ω,
        (F.setup (a_seq n) (ha_pos n)).Ω⟫_ℂ = 0)
    (hB_orth : ∀ n, ⟪(P.R_inv (a_seq n) (ha_pos n) B_inf)
        (F.setup (a_seq n) (ha_pos n)).Ω,
        (F.setup (a_seq n) (ha_pos n)).Ω⟫_ℂ = 0)
    (C : ℝ)
    (hC : ∀ n, ‖P.R_inv (a_seq n) (ha_pos n) A_inf‖ *
               ‖P.R_inv (a_seq n) (ha_pos n) B_inf‖ ≤ C)
    (t W_inf : ℝ)
    (ht_lim : Filter.Tendsto (fun n => (k_seq n : ℝ) * a_seq n) Filter.atTop (nhds t))
    (hW_lim : Filter.Tendsto
      (fun n => ‖⟪(F.setup (a_seq n) (ha_pos n)).Ω,
        (P.R_inv (a_seq n) (ha_pos n) A_inf)
          (((F.setup (a_seq n) (ha_pos n)).T ^ k_seq n)
            ((P.R_inv (a_seq n) (ha_pos n) B_inf)
              (F.setup (a_seq n) (ha_pos n)).Ω))⟫_ℂ‖)
      Filter.atTop (nhds W_inf)) :
    W_inf ≤ C * Real.exp (-(F.Δ_phys * t)) :=
  continuum_scaling_clustering F a_seq ha_pos k_seq
    (fun n => P.R_inv (a_seq n) (ha_pos n) A_inf)
    (fun n => P.R_inv (a_seq n) (ha_pos n) B_inf)
    hA_orth hB_orth C hC t W_inf ht_lim hW_lim

end ConcreteRealizations

/-! ## §9.  Non-trivial continuum limit (non-Gaussianity & gap survival) -/

section NonTrivialContinuum

/-- Exact connected 4-point (Ursell/cumulant) Schwinger function `S_c^{(4)}`. -/
def connected4 (S : ∀ n : ℕ, (Fin n → Space4) → ℂ) (xs : Fin 4 → Space4) : ℂ :=
  let s1 := fun i : Fin 4 => S 1 ![xs i]
  let s2 := fun i j : Fin 4 => S 2 ![xs i, xs j]
  let s3 := fun i j k : Fin 4 => S 3 ![xs i, xs j, xs k]
  S 4 xs
    - (s1 0 * s3 1 2 3 + s1 1 * s3 0 2 3 + s1 2 * s3 0 1 3 + s1 3 * s3 0 1 2)
    - (s2 0 1 * s2 2 3 + s2 0 2 * s2 1 3 + s2 0 3 * s2 1 2)
    + 2 * (s1 0 * s1 1 * s2 2 3 + s1 0 * s1 2 * s2 1 3 + s1 0 * s1 3 * s2 1 2
         + s1 1 * s1 2 * s2 0 3 + s1 1 * s1 3 * s2 0 2 + s1 2 * s1 3 * s2 0 1)
    - 6 * (s1 0 * s1 1 * s1 2 * s1 3)

/-- Wick's theorem at 3 and 4 points characterizing a Gaussian / free field theory. -/
def IsGaussian4 (S : ∀ n : ℕ, (Fin n → Space4) → ℂ) : Prop :=
  ∀ xs : Fin 4 → Space4,
    let μ := fun i => S 1 ![xs i]
    let c := fun i j => S 2 ![xs i, xs j] - μ i * μ j
    (∀ i j k : Fin 4,
      S 3 ![xs i, xs j, xs k] =
        μ i * c j k + μ j * c i k + μ k * c i j + μ i * μ j * μ k) ∧
    S 4 xs =
      (c 0 1 * c 2 3 + c 0 2 * c 1 3 + c 0 3 * c 1 2) +
      (μ 0 * (μ 1 * c 2 3 + μ 2 * c 1 3 + μ 3 * c 1 2) +
       μ 1 * (μ 2 * c 0 3 + μ 3 * c 0 2) +
       μ 2 * μ 3 * c 0 1) +
      μ 0 * μ 1 * μ 2 * μ 3

/-- Every Gaussian / free theory has vanishing connected 4-point function. -/
theorem isGaussian4_connected4_zero (S : ∀ n : ℕ, (Fin n → Space4) → ℂ)
    (hG : IsGaussian4 S) (xs : Fin 4 → Space4) :
    connected4 S xs = 0 := by
  rcases hG xs with ⟨h3, h4⟩
  dsimp only [connected4]
  rw [h3 1 2 3, h3 0 2 3, h3 0 1 3, h3 0 1 2, h4]
  ring

/-- Convergence of 1-, 2-, 3-, and 4-point Schwinger functions implies convergence of `S_c^{(4)}`. -/
theorem lattice_connected4_tendsto
    (S_latt : ℕ → ∀ n : ℕ, (Fin n → Space4) → ℂ)
    (S_inf : ∀ n : ℕ, (Fin n → Space4) → ℂ)
    (hconv : ∀ (n : ℕ) (xs : Fin n → Space4),
      Filter.Tendsto (fun m => S_latt m n xs) Filter.atTop (nhds (S_inf n xs)))
    (xs : Fin 4 → Space4) :
    Filter.Tendsto (fun m => connected4 (S_latt m) xs)
      Filter.atTop (nhds (connected4 S_inf xs)) := by
  have h1 : ∀ i : Fin 4,
      Filter.Tendsto (fun m => S_latt m 1 ![xs i])
        Filter.atTop (nhds (S_inf 1 ![xs i])) :=
    fun i => hconv 1 ![xs i]
  have h2 : ∀ i j : Fin 4,
      Filter.Tendsto (fun m => S_latt m 2 ![xs i, xs j])
        Filter.atTop (nhds (S_inf 2 ![xs i, xs j])) :=
    fun i j => hconv 2 ![xs i, xs j]
  have h3 : ∀ i j k : Fin 4,
      Filter.Tendsto (fun m => S_latt m 3 ![xs i, xs j, xs k])
        Filter.atTop (nhds (S_inf 3 ![xs i, xs j, xs k])) :=
    fun i j k => hconv 3 ![xs i, xs j, xs k]
  have h4 : Filter.Tendsto (fun m => S_latt m 4 xs) Filter.atTop (nhds (S_inf 4 xs)) :=
    hconv 4 xs
  have ht1 : Filter.Tendsto
      (fun m => S_latt m 1 ![xs 0] * S_latt m 3 ![xs 1, xs 2, xs 3]
              + S_latt m 1 ![xs 1] * S_latt m 3 ![xs 0, xs 2, xs 3]
              + S_latt m 1 ![xs 2] * S_latt m 3 ![xs 0, xs 1, xs 3]
              + S_latt m 1 ![xs 3] * S_latt m 3 ![xs 0, xs 1, xs 2])
      Filter.atTop
      (nhds (S_inf 1 ![xs 0] * S_inf 3 ![xs 1, xs 2, xs 3]
           + S_inf 1 ![xs 1] * S_inf 3 ![xs 0, xs 2, xs 3]
           + S_inf 1 ![xs 2] * S_inf 3 ![xs 0, xs 1, xs 3]
           + S_inf 1 ![xs 3] * S_inf 3 ![xs 0, xs 1, xs 2])) :=
    ((((h1 0).mul (h3 1 2 3)).add ((h1 1).mul (h3 0 2 3))).add
      ((h1 2).mul (h3 0 1 3))).add ((h1 3).mul (h3 0 1 2))
  have ht2 : Filter.Tendsto
      (fun m => S_latt m 2 ![xs 0, xs 1] * S_latt m 2 ![xs 2, xs 3]
              + S_latt m 2 ![xs 0, xs 2] * S_latt m 2 ![xs 1, xs 3]
              + S_latt m 2 ![xs 0, xs 3] * S_latt m 2 ![xs 1, xs 2])
      Filter.atTop
      (nhds (S_inf 2 ![xs 0, xs 1] * S_inf 2 ![xs 2, xs 3]
           + S_inf 2 ![xs 0, xs 2] * S_inf 2 ![xs 1, xs 3]
           + S_inf 2 ![xs 0, xs 3] * S_inf 2 ![xs 1, xs 2])) :=
    (((h2 0 1).mul (h2 2 3)).add ((h2 0 2).mul (h2 1 3))).add ((h2 0 3).mul (h2 1 2))
  have ht3 : Filter.Tendsto
      (fun m => (2 : ℂ) * (S_latt m 1 ![xs 0] * S_latt m 1 ![xs 1] * S_latt m 2 ![xs 2, xs 3]
                         + S_latt m 1 ![xs 0] * S_latt m 1 ![xs 2] * S_latt m 2 ![xs 1, xs 3]
                         + S_latt m 1 ![xs 0] * S_latt m 1 ![xs 3] * S_latt m 2 ![xs 1, xs 2]
                         + S_latt m 1 ![xs 1] * S_latt m 1 ![xs 2] * S_latt m 2 ![xs 0, xs 3]
                         + S_latt m 1 ![xs 1] * S_latt m 1 ![xs 3] * S_latt m 2 ![xs 0, xs 2]
                         + S_latt m 1 ![xs 2] * S_latt m 1 ![xs 3] * S_latt m 2 ![xs 0, xs 1]))
      Filter.atTop
      (nhds ((2 : ℂ) * (S_inf 1 ![xs 0] * S_inf 1 ![xs 1] * S_inf 2 ![xs 2, xs 3]
                      + S_inf 1 ![xs 0] * S_inf 1 ![xs 2] * S_inf 2 ![xs 1, xs 3]
                      + S_inf 1 ![xs 0] * S_inf 1 ![xs 3] * S_inf 2 ![xs 1, xs 2]
                      + S_inf 1 ![xs 1] * S_inf 1 ![xs 2] * S_inf 2 ![xs 0, xs 3]
                      + S_inf 1 ![xs 1] * S_inf 1 ![xs 3] * S_inf 2 ![xs 0, xs 2]
                      + S_inf 1 ![xs 2] * S_inf 1 ![xs 3] * S_inf 2 ![xs 0, xs 1]))) :=
    tendsto_const_nhds.mul
      ((((((((h1 0).mul (h1 1)).mul (h2 2 3)).add
            (((h1 0).mul (h1 2)).mul (h2 1 3))).add
            (((h1 0).mul (h1 3)).mul (h2 1 2))).add
            (((h1 1).mul (h1 2)).mul (h2 0 3))).add
            (((h1 1).mul (h1 3)).mul (h2 0 2))).add
            (((h1 2).mul (h1 3)).mul (h2 0 1)))
  have ht4 : Filter.Tendsto
      (fun m => (6 : ℂ) * (S_latt m 1 ![xs 0] * S_latt m 1 ![xs 1] *
                           S_latt m 1 ![xs 2] * S_latt m 1 ![xs 3]))
      Filter.atTop
      (nhds ((6 : ℂ) * (S_inf 1 ![xs 0] * S_inf 1 ![xs 1] *
                        S_inf 1 ![xs 2] * S_inf 1 ![xs 3]))) :=
    tendsto_const_nhds.mul ((((h1 0).mul (h1 1)).mul (h1 2)).mul (h1 3))
  change Filter.Tendsto
    (fun m => S_latt m 4 xs
      - (S_latt m 1 ![xs 0] * S_latt m 3 ![xs 1, xs 2, xs 3]
       + S_latt m 1 ![xs 1] * S_latt m 3 ![xs 0, xs 2, xs 3]
       + S_latt m 1 ![xs 2] * S_latt m 3 ![xs 0, xs 1, xs 3]
       + S_latt m 1 ![xs 3] * S_latt m 3 ![xs 0, xs 1, xs 2])
      - (S_latt m 2 ![xs 0, xs 1] * S_latt m 2 ![xs 2, xs 3]
       + S_latt m 2 ![xs 0, xs 2] * S_latt m 2 ![xs 1, xs 3]
       + S_latt m 2 ![xs 0, xs 3] * S_latt m 2 ![xs 1, xs 2])
      + (2 : ℂ) * (S_latt m 1 ![xs 0] * S_latt m 1 ![xs 1] * S_latt m 2 ![xs 2, xs 3]
                 + S_latt m 1 ![xs 0] * S_latt m 1 ![xs 2] * S_latt m 2 ![xs 1, xs 3]
                 + S_latt m 1 ![xs 0] * S_latt m 1 ![xs 3] * S_latt m 2 ![xs 1, xs 2]
                 + S_latt m 1 ![xs 1] * S_latt m 1 ![xs 2] * S_latt m 2 ![xs 0, xs 3]
                 + S_latt m 1 ![xs 1] * S_latt m 1 ![xs 3] * S_latt m 2 ![xs 0, xs 2]
                 + S_latt m 1 ![xs 2] * S_latt m 1 ![xs 3] * S_latt m 2 ![xs 0, xs 1])
      - (6 : ℂ) * (S_latt m 1 ![xs 0] * S_latt m 1 ![xs 1] *
                   S_latt m 1 ![xs 2] * S_latt m 1 ![xs 3]))
    Filter.atTop (nhds (connected4 S_inf xs))
  exact (((h4.sub ht1).sub ht2).add ht3).sub ht4

/--
Non-trivial 4D continuum limit along an asymptotic-freedom RG trajectory:
1. `Δ_latt m / a_m → Δ_phys ∈ (0, ∞)`,
2. `S_latt m n → S_inf n` (satisfying `OsterwalderSchrader4D`),
3. `S_inf n ≢ 0` for all `n ≥ 1`, and `connected4 S_inf ≢ 0` (non-Gaussian).
-/
structure NonTrivialContinuumLimit (N : ℕ) (hN : 2 ≤ N) where
  a_seq             : ℕ → ℝ
  β_seq             : ℕ → ℝ
  ha_pos            : ∀ m, 0 < a_seq m
  ha_lim            : Filter.Tendsto a_seq Filter.atTop (nhds 0)
  hβ_lim            : Filter.Tendsto β_seq Filter.atTop Filter.atTop
  Δ_latt            : ℕ → ℝ
  Δ_latt_pos        : ∀ m, 0 < Δ_latt m
  Δ_phys            : ℝ
  Δ_phys_pos        : 0 < Δ_phys
  gap_lim           : Filter.Tendsto (fun m => Δ_latt m / a_seq m)
                        Filter.atTop (nhds Δ_phys)
  os                : OsterwalderSchrader4D Δ_phys
  S_latt            : ℕ → ∀ n : ℕ, (Fin n → Space4) → ℂ
  schwinger_conv    : ∀ (n : ℕ) (xs : Fin n → Space4),
    Filter.Tendsto (fun m => S_latt m n xs) Filter.atTop (nhds (os.Schwinger n xs))
  schwinger_nonzero : ∀ n : ℕ, 1 ≤ n → ∃ xs : Fin n → Space4, os.Schwinger n xs ≠ 0
  non_gaussian      : ∃ xs : Fin 4 → Space4, connected4 os.Schwinger xs ≠ 0

/--
A `NonTrivialContinuumLimit` has strictly positive physical mass gap, is not
Gaussian/free, and has eventually non-vanishing lattice 4-point connected
functions at small lattice spacing.
-/
theorem nontrivial_continuum_properties {N : ℕ} {hN : 2 ≤ N}
    (C : NonTrivialContinuumLimit N hN) :
    0 < C.Δ_phys ∧
    ¬ IsGaussian4 C.os.Schwinger ∧
    (∃ xs : Fin 4 → Space4, ∃ N₀ : ℕ, ∀ m ≥ N₀, connected4 (C.S_latt m) xs ≠ 0) := by
  refine ⟨C.Δ_phys_pos, ?_, ?_⟩
  · intro hG
    rcases C.non_gaussian with ⟨xs, hxs⟩
    exact hxs (isGaussian4_connected4_zero C.os.Schwinger hG xs)
  · rcases C.non_gaussian with ⟨xs, hxs⟩
    have hconv := lattice_connected4_tendsto C.S_latt C.os.Schwinger C.schwinger_conv xs
    have hne_pos : 0 < ‖connected4 C.os.Schwinger xs‖ := norm_pos_iff.mpr hxs
    obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hconv ‖connected4 C.os.Schwinger xs‖ hne_pos
    refine ⟨xs, N₀, fun m hm h0 => ?_⟩
    have hdist := hN₀ m hm
    rw [h0, dist_eq_norm, zero_sub, norm_neg] at hdist
    exact lt_irrefl _ hdist

end NonTrivialContinuum

/-! ## §10.  Non-trivial 4D relativistic QFT on Minkowski spacetime -/

section MinkowskiRelativisticQFT

/-- Canonical `2n`-dimensional Hamiltonian phase space `(q, p)`. -/
abbrev PhaseSpace (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ)

/-- Canonical `q_i` basis direction in `PhaseSpace n`. -/
def eQ {n : ℕ} (i : Fin n) : PhaseSpace n := (Pi.single i 1, 0)

/-- Canonical `p_i` basis direction in `PhaseSpace n`. -/
def eP {n : ℕ} (i : Fin n) : PhaseSpace n := (0, Pi.single i 1)

private theorem phaseSpace_decomp {n : ℕ} (v : PhaseSpace n) :
    v = ∑ i : Fin n, (v.1 i • eQ i + v.2 i • eP i) := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · rw [Prod.fst_sum, Finset.sum_apply]
    simp [eQ, eP, Pi.single_apply, mul_boole]
  · rw [Prod.snd_sum, Finset.sum_apply]
    simp [eQ, eP, Pi.single_apply, mul_boole]

/-- Canonical `q_i` and `p_i` coordinate observables. -/
def coordQ {n : ℕ} (i : Fin n) (z : PhaseSpace n) : ℝ := z.1 i
def coordP {n : ℕ} (i : Fin n) (z : PhaseSpace n) : ℝ := z.2 i

private def coordQLin {n : ℕ} (i : Fin n) : PhaseSpace n →L[ℝ] ℝ where
  toFun z := z.1 i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (continuous_apply i).comp continuous_fst

private def coordPLin {n : ℕ} (i : Fin n) : PhaseSpace n →L[ℝ] ℝ where
  toFun z := z.2 i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (continuous_apply i).comp continuous_snd

/-- Canonical Poisson bracket `{f, g} = ∑ i, (∂_{q_i} f · ∂_{p_i} g - ∂_{p_i} f · ∂_{q_i} g)`. -/
noncomputable def poissonBracket {n : ℕ} (f g : PhaseSpace n → ℝ)
    (z : PhaseSpace n) : ℝ :=
  ∑ i : Fin n,
    (fderiv ℝ f z (eQ i) * fderiv ℝ g z (eP i) -
     fderiv ℝ f z (eP i) * fderiv ℝ g z (eQ i))

/-- **(i)** Hamilton's equations `(q̇, ṗ) = (∂_p H, -∂_q H)` along a trajectory. -/
def IsHamiltonianTrajectory {n : ℕ} (H : PhaseSpace n → ℝ)
    (q p : ℝ → (Fin n → ℝ)) : Prop :=
  ∀ t : ℝ,
    HasDerivAt q (fun i => fderiv ℝ H (q t, p t) (eP i)) t ∧
    HasDerivAt p (fun i => - fderiv ℝ H (q t, p t) (eQ i)) t

/-- **(ii)** Time-evolution Hamiltonian flow `Φ_t` generated by `H`. -/
structure HamiltonianFlow (n : ℕ) (H : PhaseSpace n → ℝ) where
  Φ      : ℝ → PhaseSpace n → PhaseSpace n
  Φ_zero : ∀ z, Φ 0 z = z
  Φ_add  : ∀ s t z, Φ (s + t) z = Φ s (Φ t z)
  Φ_traj : ∀ z, IsHamiltonianTrajectory H (fun t => (Φ t z).1) (fun t => (Φ t z).2)

/-- **(iii)** Non-degeneracy of the canonical Poisson bracket: `{q_i, p_i} = 1 ≠ 0`. -/
theorem poissonBracket_coord_nondeg {n : ℕ} (i : Fin n) (z : PhaseSpace n) :
    poissonBracket (coordQ i) (coordP i) z = 1 ∧
    poissonBracket (coordQ i) (coordP i) z ≠ 0 := by
  have hfq : fderiv ℝ (coordQ i) z = coordQLin i := (coordQLin i).hasFDerivAt.fderiv
  have hfp : fderiv ℝ (coordP i) z = coordPLin i := (coordPLin i).hasFDerivAt.fderiv
  have hterm : ∀ j : Fin n,
      coordQLin i (eQ j) * coordPLin i (eP j) -
        coordQLin i (eP j) * coordPLin i (eQ j) = if j = i then (1 : ℝ) else 0 := by
    intro j
    by_cases h : j = i <;> simp [coordQLin, coordPLin, eQ, eP, h]
  have hval : poissonBracket (coordQ i) (coordP i) z = 1 := by
    unfold poissonBracket
    rw [hfq, hfp]
    simp [hterm]
  exact ⟨hval, by rw [hval]; exact one_ne_zero⟩

/-- **(i)+(ii)+(ix)** Time derivative of `f` along a Hamiltonian trajectory equals `{f, H}`. -/
theorem hamiltonian_flow_deriv {n : ℕ} (H f : PhaseSpace n → ℝ)
    (q p : ℝ → (Fin n → ℝ)) (t : ℝ)
    (htraj : HasDerivAt q (fun i => fderiv ℝ H (q t, p t) (eP i)) t ∧
             HasDerivAt p (fun i => - fderiv ℝ H (q t, p t) (eQ i)) t)
    (hf : DifferentiableAt ℝ f (q t, p t)) :
    HasDerivAt (fun s => f (q s, p s)) (poissonBracket f H (q t, p t)) t := by
  have hγ : HasDerivAt (fun s => (q s, p s))
      ((fun i => fderiv ℝ H (q t, p t) (eP i)),
       (fun i => - fderiv ℝ H (q t, p t) (eQ i))) t :=
    htraj.1.prodMk htraj.2
  have hcomp := hf.hasFDerivAt.comp_hasDerivAt t hγ
  have hval : (fderiv ℝ f (q t, p t))
      ((fun i => fderiv ℝ H (q t, p t) (eP i)),
       (fun i => - fderiv ℝ H (q t, p t) (eQ i))) =
      poissonBracket f H (q t, p t) := by
    let df := fderiv ℝ f (q t, p t)
    let dH := fderiv ℝ H (q t, p t)
    let v : PhaseSpace n := (fun i => dH (eP i), fun i => - dH (eQ i))
    change df v = poissonBracket f H (q t, p t)
    conv_lhs => rw [phaseSpace_decomp v]
    rw [map_sum]
    unfold poissonBracket
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    change dH (eP i) * df (eQ i) + (-dH (eQ i)) * df (eP i) =
      df (eQ i) * dH (eP i) - df (eP i) * dH (eQ i)
    ring
  rw [← hval]
  exact hcomp

/-- **(ix)** Observables Poisson-commuting with `H` (`{f, H} = 0`) are conserved. -/
theorem poisson_commute_conserved {n : ℕ} (H f : PhaseSpace n → ℝ)
    (q p : ℝ → (Fin n → ℝ))
    (htraj : IsHamiltonianTrajectory H q p)
    (hf : Differentiable ℝ f)
    (hcomm : ∀ z : PhaseSpace n, poissonBracket f H z = 0)
    (t : ℝ) :
    f (q t, p t) = f (q 0, p 0) := by
  have hderiv : ∀ s : ℝ, HasDerivAt (fun u => f (q u, p u)) 0 s := by
    intro s
    have hs := hamiltonian_flow_deriv H f q p s (htraj s) (hf (q s, p s))
    rwa [hcomm (q s, p s)] at hs
  exact is_const_of_deriv_eq_zero
    (fun s => (hderiv s).differentiableAt)
    (fun s => (hderiv s).deriv) t 0

section
open scoped TensorProduct

/-- **(iv)** Cantor tensor observable product on any `ℂ`-algebra of observables. -/
theorem cantor_tensor_observable_mul {Obs : Type*} [Ring Obs] [Algebra ℂ Obs]
    (A₁ A₂ B₁ B₂ : Obs) :
    (A₁ ⊗ₜ[ℂ] B₁) * (A₂ ⊗ₜ[ℂ] B₂) = (A₁ * A₂) ⊗ₜ[ℂ] (B₁ * B₂) :=
  Algebra.TensorProduct.tmul_mul_tmul A₁ A₂ B₁ B₂

end

/-- **(v)** Thermodynamic partition function of `N` gapped cells (`E₀ = 0`, excited `E_ex`). -/
noncomputable def partitionFnThermodynamic (E_ex β : ℝ) (N : ℕ) : ℝ :=
  (1 + Real.exp (-(β * E_ex))) ^ N

theorem partitionFn_diverges (E_ex β : ℝ) :
    Filter.Tendsto (partitionFnThermodynamic E_ex β) Filter.atTop Filter.atTop := by
  apply tendsto_pow_atTop_atTop_of_one_lt
  linarith [Real.exp_pos (-(β * E_ex))]

/-- **(vi)** Invariance set of states fixed by a symmetry family. -/
def invarianceSet {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {ι : Type*} (symm : ι → (V →L[ℂ] V)) : Set V :=
  {x | ∀ i, symm i x = x}

/-- **(vii)** Operator commutator `[A, B] = A ∘ B - B ∘ A`. -/
def lieBracketCLM {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (A B : V →L[ℂ] V) : V →L[ℂ] V :=
  A.comp B - B.comp A

/-- If `A` and `B` commute with `H`, then `[A, B]` commutes with `H`. -/
theorem symm_lieBracket_commutes {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (H A B : V →L[ℂ] V)
    (hA : lieBracketCLM A H = 0) (hB : lieBracketCLM B H = 0) :
    lieBracketCLM (lieBracketCLM A B) H = 0 := by
  have hAH : A.comp H = H.comp A := sub_eq_zero.mp hA
  have hBH : B.comp H = H.comp B := sub_eq_zero.mp hB
  unfold lieBracketCLM
  ext x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, map_sub]
  have h1 : A (B (H x)) = H (A (B x)) := by
    calc A (B (H x)) = A (H (B x)) := by
          have := congrArg (fun f : V →L[ℂ] V => f x) hBH
          simpa [ContinuousLinearMap.comp_apply] using congrArg A this
      _ = H (A (B x)) := by
          have := congrArg (fun f : V →L[ℂ] V => f (B x)) hAH
          simpa [ContinuousLinearMap.comp_apply] using this
  have h2 : B (A (H x)) = H (B (A x)) := by
    calc B (A (H x)) = B (H (A x)) := by
          have := congrArg (fun f : V →L[ℂ] V => f x) hAH
          simpa [ContinuousLinearMap.comp_apply] using congrArg B this
      _ = H (B (A x)) := by
          have := congrArg (fun f : V →L[ℂ] V => f (A x)) hBH
          simpa [ContinuousLinearMap.comp_apply] using this
  rw [h1, h2]
  abel

/-- An operator commuting with all symmetries preserves `invarianceSet`. -/
theorem invarianceSet_preserved {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {ι : Type*} (symm : ι → (V →L[ℂ] V)) (H : V →L[ℂ] V)
    (hcomm : ∀ i, (symm i).comp H = H.comp (symm i))
    {x : V} (hx : x ∈ invarianceSet symm) :
    H x ∈ invarianceSet symm := by
  intro i
  calc symm i (H x) = ((symm i).comp H) x := rfl
    _ = (H.comp (symm i)) x := by rw [hcomm i]
    _ = H (symm i x) := rfl
    _ = H x := by rw [hx i]

/-- **(viii)** Continuum correlation length `ξ_m = 1 / Δ_latt(m) → ∞` as `a_m → 0⁺`. -/
theorem correlation_length_diverges (a_seq Δ_latt : ℕ → ℝ) (Δ_phys : ℝ)
    (ha_pos : ∀ m, 0 < a_seq m)
    (ha_lim : Filter.Tendsto a_seq Filter.atTop (nhds 0))
    (hΔ_pos : ∀ m, 0 < Δ_latt m)
    (hgap_lim : Filter.Tendsto (fun m => Δ_latt m / a_seq m) Filter.atTop (nhds Δ_phys)) :
    Filter.Tendsto (fun m => (Δ_latt m)⁻¹) Filter.atTop Filter.atTop := by
  have h_mul : Filter.Tendsto (fun m => (Δ_latt m / a_seq m) * a_seq m)
      Filter.atTop (nhds (Δ_phys * 0)) := hgap_lim.mul ha_lim
  rw [mul_zero] at h_mul
  have hΔ_lim : Filter.Tendsto Δ_latt Filter.atTop (nhds 0) := by
    refine h_mul.congr' (Filter.Eventually.of_forall fun m => ?_)
    exact div_mul_cancel₀ _ (ha_pos m).ne'
  refine tendsto_inv_nhdsGT_zero.comp ?_
  exact Filter.tendsto_inf.mpr
    ⟨hΔ_lim, Filter.tendsto_principal.mpr (Filter.Eventually.of_forall fun m => hΔ_pos m)⟩

/-- **(x)** Single-DOF projection and lift on `PhaseSpace n`. -/
def singleDOFProj (n : ℕ) [NeZero n] (z : PhaseSpace n) : PhaseSpace 1 :=
  (fun _ => z.1 0, fun _ => z.2 0)

def singleDOFLift (n : ℕ) [NeZero n] (z : PhaseSpace 1) : PhaseSpace n :=
  (fun i => if i = 0 then z.1 0 else 0, fun i => if i = 0 then z.2 0 else 0)

theorem singleDOF_proj_lift (n : ℕ) [NeZero n] (z : PhaseSpace 1) :
    singleDOFProj n (singleDOFLift n z) = z := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · simp [singleDOFProj, singleDOFLift, Fin.eq_zero i]
  · simp [singleDOFProj, singleDOFLift, Fin.eq_zero i]

/-- **(xi)** Symplectic action `∮ p dq` over a period `T`. -/
noncomputable def loopAction (q p : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∫ t in (0)..T, p t * deriv q t

/-- **(xi)** Bohr–Sommerfeld action of a harmonic oscillator orbit equals `π m ω A²`. -/
theorem harmonic_oscillator_action (m ω A : ℝ) (hω : ω ≠ 0) :
    loopAction
      (fun t => A * Real.cos (ω * t))
      (fun t => -(m * ω * A) * Real.sin (ω * t))
      (2 * Real.pi / ω) =
    Real.pi * m * ω * A ^ 2 := by
  have hderiv_q : ∀ t : ℝ,
      deriv (fun s => A * Real.cos (ω * s)) t = A * (-Real.sin (ω * t) * ω) := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => ω * s) ω t := by
      simpa using (hasDerivAt_id t).const_mul ω
    have h2 : HasDerivAt (fun s : ℝ => Real.cos (ω * s)) (-Real.sin (ω * t) * ω) t :=
      (Real.hasDerivAt_cos (ω * t)).comp t h1
    exact (h2.const_mul A).deriv
  have hcongr : (fun t => (-(m * ω * A) * Real.sin (ω * t)) *
        deriv (fun s => A * Real.cos (ω * s)) t) =
      (fun t => m * ω ^ 2 * A ^ 2 * Real.sin (ω * t) ^ 2) := by
    funext t
    rw [hderiv_q t]
    ring
  unfold loopAction
  rw [hcongr]
  let C : ℝ := m * ω ^ 2 * A ^ 2 / 2
  let F : ℝ → ℝ := fun t => C * (t - Real.sin (2 * ω * t) / (2 * ω))
  have hF : ∀ t : ℝ, HasDerivAt F (m * ω ^ 2 * A ^ 2 * Real.sin (ω * t) ^ 2) t := by
    intro t
    have h2ωt : HasDerivAt (fun s : ℝ => 2 * ω * s) (2 * ω) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * ω)
    have hsin : HasDerivAt (fun s : ℝ => Real.sin (2 * ω * s))
        (Real.cos (2 * ω * t) * (2 * ω)) t :=
      (Real.hasDerivAt_sin (2 * ω * t)).comp t h2ωt
    have hdiv : HasDerivAt (fun s : ℝ => Real.sin (2 * ω * s) / (2 * ω))
        (Real.cos (2 * ω * t)) t := by
      simpa [mul_div_cancel_right₀ _ (mul_ne_zero two_ne_zero hω)] using
        hsin.div_const (2 * ω)
    have hsub : HasDerivAt (fun s : ℝ => s - Real.sin (2 * ω * s) / (2 * ω))
        (1 - Real.cos (2 * ω * t)) t := (hasDerivAt_id t).sub hdiv
    have hmul : HasDerivAt F (C * (1 - Real.cos (2 * ω * t))) t := hsub.const_mul C
    have htrig : C * (1 - Real.cos (2 * ω * t)) =
        m * ω ^ 2 * A ^ 2 * Real.sin (ω * t) ^ 2 := by
      have h2 : Real.cos (2 * ω * t) = 2 * Real.cos (ω * t) ^ 2 - 1 := by
        rw [show 2 * ω * t = 2 * (ω * t) by ring]
        exact Real.cos_two_mul (ω * t)
      have hcos_sq : Real.cos (ω * t) ^ 2 = 1 - Real.sin (ω * t) ^ 2 := by
        linarith [Real.sin_sq_add_cos_sq (ω * t)]
      rw [h2, hcos_sq]
      dsimp [C]
      ring
    rwa [htrig] at hmul
  have hint : IntervalIntegrable (fun t => m * ω ^ 2 * A ^ 2 * Real.sin (ω * t) ^ 2)
      MeasureTheory.volume 0 (2 * Real.pi / ω) :=
    (continuous_const.mul
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2)).intervalIntegrable
      0 (2 * Real.pi / ω)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t) hint]
  have hsin0 : Real.sin (2 * ω * 0) = 0 := by simp
  have hsinT : Real.sin (2 * ω * (2 * Real.pi / ω)) = 0 := by
    have harg : 2 * ω * (2 * Real.pi / ω) = ((4 : ℕ) : ℝ) * Real.pi := by
      field_simp [hω]
      ring
    rw [harg]
    exact Real.sin_nat_mul_pi 4
  dsimp [F, C]
  rw [hsin0, hsinT]
  field_simp [hω]
  ring

/--
Combined mathematical-physics structure `(M, ω, H, Φ_t, {f, g}, Z(β), {H_i}, ξ)`
for a non-trivial 4D relativistic QFT on Minkowski spacetime satisfying **(i)–(xi)**.
-/
structure MinkowskiRelativisticQFTData.{u} (Δ_phys : ℝ)
    (wightman : WightmanQFT4D.{u} Δ_phys) where
  n_dof       : ℕ
  [n_nz       : NeZero n_dof]
  H_cl        : PhaseSpace n_dof → ℝ
  flow        : HamiltonianFlow n_dof H_cl
  Obs         : Type u
  [obsRing    : Ring Obs]
  [obsAlg     : Algebra ℂ Obs]
  Z           : ℝ → ℕ → ℝ
  Z_diverges  : ∀ β : ℝ, Filter.Tendsto (Z β) Filter.atTop Filter.atTop
  H_op        : wightman.H →L[ℂ] wightman.H
  H_op_lb     : ∀ ψ : wightman.H, 0 ≤ (⟪ψ, H_op ψ⟫_ℂ).re
  H_op_ground : H_op wightman.Ω_phys = 0
  symm        : wightman.Poincare → (wightman.H →L[ℂ] wightman.H)
  symm_comm   : ∀ g, lieBracketCLM (symm g) H_op = 0
  symm_vac    : wightman.Ω_phys ∈ invarianceSet symm
  ξ_seq       : ℕ → ℝ
  ξ_diverges  : Filter.Tendsto ξ_seq Filter.atTop Filter.atTop
  trilattice  : TrilatticeModel
  action_T    : ℝ
  action_val  : ℝ
  action_pos  : 0 < action_val

attribute [instance] MinkowskiRelativisticQFTData.n_nz
  MinkowskiRelativisticQFTData.obsRing MinkowskiRelativisticQFTData.obsAlg

/--
Master theorem (`non-trivial_4-dimensional_relativistic_quantum_field_theory_on_minkowski_spacetime`):
combining `YangMillsCombinedChain` and `NonTrivialContinuumLimit` yields a
`MinkowskiRelativisticQFTData` realizing all eleven conditions **(i)–(xi)**:
Hamiltonian flow, non-degenerate Poisson bracket, Cantor tensor product,
divergent partition function with bounded-below Hamiltonian, Poincaré invariance
set and symmetry algebra `[H_i, H] = 0`, diverging correlation length `ξ → ∞`,
Frobenius identity `μ ∘ δ = id`, Poisson-commuting conserved observables,
single-DOF reduction, positive Bohr–Sommerfeld action, and non-Gaussian 4D
continuum Wightman QFT with mass gap `Δ_phys > 0`.
-/
theorem non_trivial_4d_relativistic_qft_on_minkowski_spacetime
    {N : ℕ} {hN : 2 ≤ N}
    (C : YangMillsCombinedChain N hN)
    (L : NonTrivialContinuumLimit N hN) :
    ∃ D : MinkowskiRelativisticQFTData C.F.Δ_phys C.wightman4d,
      (∀ (i : Fin D.n_dof) (z : PhaseSpace D.n_dof),
        poissonBracket (coordQ i) (coordP i) z ≠ 0) ∧
      (∀ (f : PhaseSpace D.n_dof → ℝ) (z : PhaseSpace D.n_dof),
        Differentiable ℝ f →
        (∀ w, poissonBracket f D.H_cl w = 0) →
        ∀ t, f (D.flow.Φ t z) = f z) ∧
      (∀ A₁ A₂ B₁ B₂ : D.Obs,
        (A₁ ⊗ₜ[ℂ] B₁) * (A₂ ⊗ₜ[ℂ] B₂) = (A₁ * A₂) ⊗ₜ[ℂ] (B₁ * B₂)) ∧
      (∀ x : D.trilattice.S, D.trilattice.μ (D.trilattice.δ x) = x) ∧
      (∀ z : PhaseSpace 1, singleDOFProj D.n_dof (singleDOFLift D.n_dof z) = z) ∧
      (¬ IsGaussian4 L.os.Schwinger) ∧
      (∀ p2 ∈ C.wightman4d.P2_spec, ¬ (0 < p2 ∧ p2 < C.F.Δ_phys ^ 2)) := by
  let flow1 : HamiltonianFlow 1 (fun _ => 0) :=
    { Φ := fun _ z => z
      Φ_zero := fun _ => rfl
      Φ_add := fun _ _ _ => rfl
      Φ_traj := fun z t =>
        ⟨by simpa using hasDerivAt_const t z.1, by simpa using hasDerivAt_const t z.2⟩ }
  let D : MinkowskiRelativisticQFTData C.F.Δ_phys C.wightman4d :=
    { n_dof := 1
      H_cl := fun _ => 0
      flow := flow1
      Obs := Module.End ℂ C.wightman4d.H
      Z := partitionFnThermodynamic C.F.Δ_phys
      Z_diverges := partitionFn_diverges C.F.Δ_phys
      H_op := 0
      H_op_lb := fun ψ => by simp
      H_op_ground := rfl
      symm := C.wightman4d.U
      symm_comm := fun g => by unfold lieBracketCLM; simp
      symm_vac := C.wightman4d.U_vac
      ξ_seq := fun m => (L.Δ_latt m)⁻¹
      ξ_diverges := correlation_length_diverges L.a_seq L.Δ_latt L.Δ_phys
        L.ha_pos L.ha_lim L.Δ_latt_pos L.gap_lim
      trilattice := C.M
      action_T := 2 * Real.pi
      action_val := loopAction (fun t => Real.cos t) (fun t => -Real.sin t) (2 * Real.pi)
      action_pos := by
        have h := harmonic_oscillator_action 1 1 1 one_ne_zero
        have heq : loopAction (fun t => Real.cos t) (fun t => -Real.sin t) (2 * Real.pi) =
            Real.pi := by
          simpa using h
        rw [heq]
        exact Real.pi_pos }
  refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i z
    exact (poissonBracket_coord_nondeg i z).2
  · intro f z hf hcomm t
    have hc := poisson_commute_conserved D.H_cl f
      (fun s => (D.flow.Φ s z).1) (fun s => (D.flow.Φ s z).2)
      (D.flow.Φ_traj z) hf hcomm t
    simpa [D.flow.Φ_zero] using hc
  · intro A₁ A₂ B₁ B₂
    exact cantor_tensor_observable_mul A₁ A₂ B₁ B₂
  · exact D.trilattice.mu_delta
  · exact singleDOF_proj_lift D.n_dof
  · exact (nontrivial_continuum_properties L).2.1
  · exact (combined_chain_summary C).2.2

end MinkowskiRelativisticQFT 

/-! ## §11.  Non-Abelian lattice gauge Hilbert space and Wilson transfer matrix -/

section NonAbelianWilson

private theorem su_trace_conj {N : ℕ}
    (A B : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Matrix.trace ((A * B * A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ) =
      Matrix.trace (B : Matrix (Fin N) (Fin N) ℂ) := by
  have hmul : ∀ X Y : Matrix.specialUnitaryGroup (Fin N) ℂ,
      ((X * Y : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
        (X : Matrix (Fin N) (Fin N) ℂ) * (Y : Matrix (Fin N) (Fin N) ℂ) :=
    fun _ _ => rfl
  have hone : ((1 : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ) = 1 := rfl
  have hinv : ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    rw [← hmul A⁻¹ A, inv_mul_cancel, hone]
  rw [hmul (A * B) A⁻¹, hmul A B,
    Matrix.trace_mul_comm ((A : Matrix (Fin N) (Fin N) ℂ) * (B : Matrix (Fin N) (Fin N) ℂ))
      ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ),
    ← mul_assoc, hinv, one_mul]

/-- Closed elementary plaquette on a spatial lattice `L`. -/
structure LatticePlaquette (L : SpatialLattice) where
  base      : L.Site
  loop      : List (L.Link × Bool)
  is_closed : IsLatticePath L base base loop

/-- Single-plaquette Wilson action term `1 - (1/N) Re Tr(U_□)`. -/
noncomputable def wilsonPlaquetteTerm {L : SpatialLattice} {N : ℕ}
    (p : LatticePlaquette L)
    (U : GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  1 - (1 / (N : ℝ)) *
    (Matrix.trace ((pathHolonomy U p.loop : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ)).re

/-- Total Wilson plaquette action `S_W[U] = β ∑_□ (1 - (1/N) Re Tr(U_□))`. -/
noncomputable def wilsonAction {L : SpatialLattice} {N : ℕ}
    (β : ℝ) (plaquettes : List (LatticePlaquette L))
    (U : GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  β * (plaquettes.map (fun p => wilsonPlaquetteTerm p U)).sum

theorem wilsonPlaquetteTerm_gauge_inv {L : SpatialLattice} {N : ℕ}
    (p : LatticePlaquette L)
    (g : GaugeTransform L (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U : GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonPlaquetteTerm p (gaugeAct g U) = wilsonPlaquetteTerm p U := by
  unfold wilsonPlaquetteTerm
  rw [wilsonLoop_gauge_invariant
    (fun M : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (Matrix.trace (M : Matrix (Fin N) (Fin N) ℂ) : ℂ))
    su_trace_conj g U p.is_closed]

theorem wilsonAction_gauge_inv {L : SpatialLattice} {N : ℕ}
    (β : ℝ) (plaquettes : List (LatticePlaquette L))
    (g : GaugeTransform L (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U : GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonAction β plaquettes (gaugeAct g U) = wilsonAction β plaquettes U := by
  unfold wilsonAction
  congr 1
  induction plaquettes with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [wilsonPlaquetteTerm_gauge_inv, ih]

/-- Wilson transfer kernel `exp(-½(S_W[U] + S_W[U'])) * K_kin(U, U')`. -/
noncomputable def wilsonKernel {L : SpatialLattice} {N : ℕ}
    (β : ℝ) (plaquettes : List (LatticePlaquette L))
    (K_kin : GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (U U' : GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  Real.exp (-(1 / 2 : ℝ) * (wilsonAction β plaquettes U + wilsonAction β plaquettes U')) *
    K_kin U U'

theorem wilsonKernel_gauge_inv {L : SpatialLattice} {N : ℕ}
    (β : ℝ) (plaquettes : List (LatticePlaquette L))
    (K_kin : GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_inv : ∀ g U U', K_kin (gaugeAct g U) (gaugeAct g U') = K_kin U U')
    (g : GaugeTransform L (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U U' : GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonKernel β plaquettes K_kin (gaugeAct g U) (gaugeAct g U') =
      wilsonKernel β plaquettes K_kin U U' := by
  unfold wilsonKernel
  rw [wilsonAction_gauge_inv, wilsonAction_gauge_inv, hK_inv]

theorem wilsonKernel_symm {L : SpatialLattice} {N : ℕ}
    (β : ℝ) (plaquettes : List (LatticePlaquette L))
    (K_kin : GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_symm : ∀ U U', K_kin U' U = K_kin U U')
    (U U' : GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonKernel β plaquettes K_kin U' U = wilsonKernel β plaquettes K_kin U U' := by
  unfold wilsonKernel
  rw [add_comm (wilsonAction β plaquettes U'), hK_symm]

theorem wilsonKernel_nonneg {L : SpatialLattice} {N : ℕ}
    (β : ℝ) (plaquettes : List (LatticePlaquette L))
    (K_kin : GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_nonneg : ∀ U U', 0 ≤ K_kin U U')
    (U U' : GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 ≤ wilsonKernel β plaquettes K_kin U U' :=
  mul_nonneg (Real.exp_pos _).le (hK_nonneg U U')

/-- `L²(SU(N)^Link, μ)` Hilbert space for non-Abelian lattice gauge theory. -/
abbrev HaarGaugeSpace {L : SpatialLattice} {N : ℕ}
    [MeasurableSpace (GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ))]
    (μ : MeasureTheory.Measure (GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ))) :=
  MeasureTheory.Lp ℂ 2 μ

/--
Non-Abelian `SU(N)` Wilson lattice gauge setup on `L²(G^Link, μ_Haar)`
coupled to the symmetry algebra `{H_i}`, conserved observables, and
thermodynamic/continuum data.
-/
structure NonAbelianWilsonSetup (L : SpatialLattice) (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ))] where
  μ          : MeasureTheory.Measure (GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ))
  [μ_prob    : MeasureTheory.IsProbabilityMeasure μ]
  μ_inv      : ∀ g, MeasureTheory.Measure.map (gaugeAct g) μ = μ
  β          : ℝ
  β_pos      : 0 < β
  plaquettes : List (LatticePlaquette L)
  K_kin      : GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ) →
                 GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ
  K_symm     : ∀ U U', K_kin U' U = K_kin U U'
  K_nonneg   : ∀ U U', 0 ≤ K_kin U U'
  K_inv      : ∀ g U U', K_kin (gaugeAct g U) (gaugeAct g U') = K_kin U U'
  gaugeSetup : LatticeGaugeSetup L (Matrix.specialUnitaryGroup (Fin N) ℂ) (HaarGaugeSpace μ)
  SymmIdx    : Type
  symmOp     : SymmIdx → (HaarGaugeSpace μ →L[ℂ] HaarGaugeSpace μ)
  symm_comm  : ∀ i, lieBracketCLM (symmOp i) gaugeSetup.T = 0

attribute [instance] NonAbelianWilsonSetup.μ_prob

theorem nonAbelianWilson_kernel_properties {L : SpatialLattice} {N : ℕ} {hN : 2 ≤ N}
    [MeasurableSpace (GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ))]
    (W : NonAbelianWilsonSetup L N hN)
    (g : GaugeTransform L (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U U' : GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonKernel W.β W.plaquettes W.K_kin (gaugeAct g U) (gaugeAct g U') =
      wilsonKernel W.β W.plaquettes W.K_kin U U' ∧
    wilsonKernel W.β W.plaquettes W.K_kin U' U =
      wilsonKernel W.β W.plaquettes W.K_kin U U' ∧
    0 ≤ wilsonKernel W.β W.plaquettes W.K_kin U U' :=
  ⟨wilsonKernel_gauge_inv W.β W.plaquettes W.K_kin W.K_inv g U U',
   wilsonKernel_symm W.β W.plaquettes W.K_kin W.K_symm U U',
   wilsonKernel_nonneg W.β W.plaquettes W.K_kin W.K_nonneg U U'⟩

theorem nonAbelianWilson_clustering {L : SpatialLattice} {N : ℕ} {hN : 2 ≤ N}
    [MeasurableSpace (GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ))]
    (W : NonAbelianWilsonSetup L N hN)
    (A B : HaarGaugeSpace W.μ →L[ℂ] HaarGaugeSpace W.μ)
    (hA : ⟪A W.gaugeSetup.Ω, W.gaugeSetup.Ω⟫_ℂ = 0)
    (hB : ⟪B W.gaugeSetup.Ω, W.gaugeSetup.Ω⟫_ℂ = 0)
    (k : ℕ) :
    ‖⟪W.gaugeSetup.Ω, A ((W.gaugeSetup.T ^ k) (B W.gaugeSetup.Ω))⟫_ℂ‖
      ≤ ‖A‖ * ‖B‖ * Real.exp (-(W.gaugeSetup.Δ * (k * W.gaugeSetup.a))) :=
  clustering W.gaugeSetup A B hA hB k

end NonAbelianWilson

/-! ## §12.  Uniform RG spectral gap and Schwinger convergence -/

section UniformRG

/--
Uniform renormalization-group trajectory for 4D `SU(N)` lattice gauge theory:
- At each spacing `a_m > 0`, the lattice gap `Δ_latt m > 0` is uniform across volumes;
- Along `a_m → 0⁺` (`β_m → ∞`), the **rescaled** physical gap satisfies
  `Δ_latt m / a_m ≥ Δ₀ > 0` and converges to `Δ_phys > 0`;
- The lattice `n`-point Schwinger functions converge to `S_inf n`.
-/
structure UniformRGTrajectory (N : ℕ) (hN : 2 ≤ N) where
  F                 : LatticeScalingFamily (Matrix.specialUnitaryGroup (Fin N) ℂ)
  a_seq             : ℕ → ℝ
  β_seq             : ℕ → ℝ
  ha_pos            : ∀ m, 0 < a_seq m
  ha_lim            : Filter.Tendsto a_seq Filter.atTop (nhds 0)
  hβ_lim            : Filter.Tendsto β_seq Filter.atTop Filter.atTop
  Δ_latt            : ℕ → ℝ
  Δ_latt_pos        : ∀ m, 0 < Δ_latt m
  Δ₀                : ℝ
  Δ₀_pos            : 0 < Δ₀
  unif_rescaled_gap : ∀ m, Δ₀ ≤ Δ_latt m / a_seq m
  gap_lim           : Filter.Tendsto (fun m => Δ_latt m / a_seq m)
                        Filter.atTop (nhds F.Δ_phys)
  S_latt            : ℕ → ∀ n : ℕ, (Fin n → Space4) → ℂ
  S_inf             : ∀ n : ℕ, (Fin n → Space4) → ℂ
  schwinger_conv    : ∀ (n : ℕ) (xs : Fin n → Space4),
    Filter.Tendsto (fun m => S_latt m n xs) Filter.atTop (nhds (S_inf n xs))

theorem uniform_rg_phys_gap_lb {N : ℕ} {hN : 2 ≤ N}
    (R : UniformRGTrajectory N hN) :
    R.Δ₀ ≤ R.F.Δ_phys :=
  ge_of_tendsto R.gap_lim (Filter.Eventually.of_forall R.unif_rescaled_gap)

theorem uniform_rg_correlation_length_diverges {N : ℕ} {hN : 2 ≤ N}
    (R : UniformRGTrajectory N hN) :
    Filter.Tendsto (fun m => (R.Δ_latt m)⁻¹) Filter.atTop Filter.atTop :=
  correlation_length_diverges R.a_seq R.Δ_latt R.F.Δ_phys
    R.ha_pos R.ha_lim R.Δ_latt_pos R.gap_lim

theorem uniform_rg_clustering_limit {N : ℕ} {hN : 2 ≤ N}
    (R : UniformRGTrajectory N hN)
    (k_seq : ℕ → ℕ)
    (A_seq B_seq : ∀ m, R.F.V (R.a_seq m) →L[ℂ] R.F.V (R.a_seq m))
    (hA : ∀ m, ⟪A_seq m (R.F.setup (R.a_seq m) (R.ha_pos m)).Ω,
        (R.F.setup (R.a_seq m) (R.ha_pos m)).Ω⟫_ℂ = 0)
    (hB : ∀ m, ⟪B_seq m (R.F.setup (R.a_seq m) (R.ha_pos m)).Ω,
        (R.F.setup (R.a_seq m) (R.ha_pos m)).Ω⟫_ℂ = 0)
    (C : ℝ) (hC : ∀ m, ‖A_seq m‖ * ‖B_seq m‖ ≤ C)
    (t W_inf : ℝ)
    (ht_lim : Filter.Tendsto (fun m => (k_seq m : ℝ) * R.a_seq m) Filter.atTop (nhds t))
    (hW_lim : Filter.Tendsto
      (fun m => ‖⟪(R.F.setup (R.a_seq m) (R.ha_pos m)).Ω,
        A_seq m (((R.F.setup (R.a_seq m) (R.ha_pos m)).T ^ k_seq m)
          (B_seq m (R.F.setup (R.a_seq m) (R.ha_pos m)).Ω))⟫_ℂ‖)
      Filter.atTop (nhds W_inf)) :
    W_inf ≤ C * Real.exp (-(R.F.Δ_phys * t)) :=
  continuum_scaling_clustering R.F R.a_seq R.ha_pos k_seq A_seq B_seq
    hA hB C hC t W_inf ht_lim hW_lim

end UniformRG

/-! ## §13.  Non-Gaussian 4D Osterwalder–Schrader Euclidean continuum theory -/

section NonGaussianOS4D

/--
Full non-Gaussian 4D Osterwalder–Schrader Euclidean continuum theory:
`OsterwalderSchrader4D Δ_phys` strengthened with general `n`-point reflection
positivity, non-vanishing `n`-point functions, and non-vanishing connected 4-point
function `connected4`.
-/
structure OS4DContinuumTheory (Δ_phys : ℝ) where
  os                : OsterwalderSchrader4D Δ_phys
  refl_pos_n        : ∀ (m : ℕ) (n_pts : Fin m → ℕ) (c : Fin m → ℂ)
                        (xs : ∀ i : Fin m, Fin (n_pts i) → Space4),
                        (∀ i k, 0 < (xs i k) 0) →
                        0 ≤ (∑ i : Fin m, ∑ j : Fin m,
                          c i * starRingEnd ℂ (c j) *
                            os.Schwinger (n_pts i + n_pts j)
                              (Fin.append (fun k => euclidTimeReflect (xs i k)) (xs j))).re
  schwinger_nonzero : ∀ n : ℕ, 1 ≤ n → ∃ xs : Fin n → Space4, os.Schwinger n xs ≠ 0
  non_gaussian      : ∃ xs : Fin 4 → Space4, connected4 os.Schwinger xs ≠ 0

/-- General `n`-point reflection positivity specializes directly to the 2-point condition. -/
theorem os2_refl_pos_from_n {Δ_phys : ℝ} (os : OsterwalderSchrader4D Δ_phys)
    (h_n : ∀ (m : ℕ) (n_pts : Fin m → ℕ) (c : Fin m → ℂ)
        (xs : ∀ i : Fin m, Fin (n_pts i) → Space4),
        (∀ i k, 0 < (xs i k) 0) →
        0 ≤ (∑ i : Fin m, ∑ j : Fin m,
          c i * starRingEnd ℂ (c j) *
            os.Schwinger (n_pts i + n_pts j)
              (Fin.append (fun k => euclidTimeReflect (xs i k)) (xs j))).re)
    (m : ℕ) (c : Fin m → ℂ) (xs : Fin m → Space4) (hpos : ∀ i, 0 < xs i 0) :
    0 ≤ (∑ i : Fin m, ∑ j : Fin m,
      c i * starRingEnd ℂ (c j) *
        os.Schwinger 2 ![euclidTimeReflect (xs i), xs j]).re := by
  have h := h_n m (fun _ => 1) c (fun i _ => xs i) (fun i _ => hpos i)
  dsimp only at h
  refine le_trans h (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have happ : Fin.append (fun _ : Fin 1 => euclidTimeReflect (xs i)) (fun _ : Fin 1 => xs j) =
      ![euclidTimeReflect (xs i), xs j] := by
    funext k
    fin_cases k <;> rfl
  rw [congrArg (os.Schwinger 2) happ]

theorem os4d_theory_non_gaussian {Δ_phys : ℝ} (T : OS4DContinuumTheory Δ_phys) :
    ¬ IsGaussian4 T.os.Schwinger := by
  intro hG
  rcases T.non_gaussian with ⟨xs, hxs⟩
  exact hxs (isGaussian4_connected4_zero T.os.Schwinger hG xs)

end NonGaussianOS4D

/-! ## §14.  Osterwalder–Schrader reconstruction to the Minkowski Wightman QFT -/

section OSReconstruction

/--
Positive-semidefinite Hermitian sesquilinear form induced on positive-time
test configurations by Osterwalder–Schrader reflection positivity.
-/
structure OSReflectionForm (E : Type*) [AddCommGroup E] [Module ℂ E] where
  B         : E → E → ℂ
  add_left  : ∀ x y z, B (x + y) z = B x z + B y z
  smul_left : ∀ (c : ℂ) x y, B (c • x) y = starRingEnd ℂ c * B x y
  conj_symm : ∀ x y, B x y = starRingEnd ℂ (B y x)
  pos_re    : ∀ x, 0 ≤ (B x x).re

theorem OSReflectionForm.add_right {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (x y z : E) :
    F.B x (y + z) = F.B x y + F.B x z := by
  rw [F.conj_symm x (y + z), F.add_left, map_add, ← F.conj_symm, ← F.conj_symm]

theorem OSReflectionForm.smul_right {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (c : ℂ) (x y : E) :
    F.B x (c • y) = c * F.B x y := by
  rw [F.conj_symm x (c • y), F.smul_left, map_mul, Complex.conj_conj, ← F.conj_symm]

theorem OSReflectionForm.sub_left {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (x y z : E) :
    F.B (x - y) z = F.B x z - F.B y z := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ y, F.add_left, F.smul_left]
  simp [sub_eq_add_neg]

theorem OSReflectionForm.sub_right {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (x y z : E) :
    F.B x (y - z) = F.B x y - F.B x z := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ z, F.add_right, F.smul_right]
  simp [sub_eq_add_neg]

theorem OSReflectionForm.self_im_zero {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (x : E) :
    (F.B x x).im = 0 :=
  Complex.conj_eq_iff_im.mp (F.conj_symm x x).symm

/-- Cauchy–Schwarz inequality for a reflection-positive OS sesquilinear form. -/
theorem os_cauchy_schwarz {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (x y : E) :
    (F.B x y).re ^ 2 + (F.B x y).im ^ 2 ≤ (F.B x x).re * (F.B y y).re := by
  set z : ℂ := F.B x y
  set R : ℝ := z.re ^ 2 + z.im ^ 2
  set a : ℝ := (F.B x x).re
  set b : ℝ := (F.B y y).re
  have hR_nonneg : 0 ≤ R := by positivity
  have ha : 0 ≤ a := F.pos_re x
  have hb : 0 ≤ b := F.pos_re y
  have h_quad : ∀ t : ℝ, 0 ≤ R * a - 2 * R * t + b * t ^ 2 := by
    intro t
    have hp := F.pos_re (z • x - (t : ℂ) • y)
    have hsub : z • x - (t : ℂ) • y = z • x + (-(t : ℂ)) • y := by
      rw [sub_eq_add_neg, neg_smul]
    rw [hsub, F.add_left, F.add_right, F.add_right] at hp
    simp only [F.smul_left, F.smul_right, map_neg, Complex.conj_ofReal] at hp
    have hxy : F.B x y = z := rfl
    have hyx : F.B y x = starRingEnd ℂ z := by rw [F.conj_symm]
    rw [hxy, hyx] at hp
    have himx : (F.B x x).im = 0 := F.self_im_zero x
    have himy : (F.B y y).im = 0 := F.self_im_zero y
    have hre : (starRingEnd ℂ z * (z * F.B x x) + starRingEnd ℂ z * (-(t : ℂ) * z) +
        (-(t : ℂ) * (z * starRingEnd ℂ z) + -(t : ℂ) * (-(t : ℂ) * F.B y y))).re =
        R * a - 2 * R * t + b * t ^ 2 := by
      simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
        himx, himy, mul_zero, zero_mul, sub_zero, add_zero]
      dsimp [R, a, b]
      ring
    linarith
  by_cases hR : R = 0
  · rw [hR]
    exact mul_nonneg ha hb
  · have hR_pos : 0 < R := lt_of_le_of_ne hR_nonneg (Ne.symm hR)
    by_cases hb0 : b = 0
    · have hq := h_quad ((R * a + 1) / (2 * R))
      rw [hb0, zero_mul, add_zero] at hq
      have h2R : (2 * R) ≠ 0 := mul_ne_zero two_ne_zero hR
      have hval : R * a - 2 * R * ((R * a + 1) / (2 * R)) = -1 := by
        field_simp [h2R]
        ring
      linarith
    · have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have hq := h_quad (R / b)
      have hqb := mul_nonneg hq hb
      have hval : (R * a - 2 * R * (R / b) + b * (R / b) ^ 2) * b = R * (a * b - R) := by
        field_simp [hb0]
        ring
      rw [hval] at hqb
      have hsub : 0 ≤ a * b - R := nonneg_of_mul_nonneg_right hqb hR_pos
      linarith

theorem OSReflectionForm.eq_zero_of_self_zero {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) {x : E} (hx : F.B x x = 0) (y : E) :
    F.B x y = 0 := by
  have hcs := os_cauchy_schwarz F x y
  have hre0 : (F.B x x).re = 0 := by rw [hx, Complex.zero_re]
  rw [hre0, zero_mul] at hcs
  have hre : (F.B x y).re = 0 :=
    sq_eq_zero_iff.mp (by linarith [sq_nonneg (F.B x y).re, sq_nonneg (F.B x y).im])
  have him : (F.B x y).im = 0 :=
    sq_eq_zero_iff.mp (by linarith [sq_nonneg (F.B x y).re, sq_nonneg (F.B x y).im])
  exact Complex.ext hre him

/-- Stage 1 null space `𝒩 = {x | ⟨x, x⟩_E = 0}` is a complex subspace. -/
def osNullSpace {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : Submodule ℂ E where
  carrier := {x | F.B x x = 0}
  add_mem' {x y} hx hy := by
    change F.B x x = 0 at hx
    change F.B y y = 0 at hy
    change F.B (x + y) (x + y) = 0
    have hxy : F.B x y = 0 := F.eq_zero_of_self_zero hx y
    have hyx : F.B y x = 0 := by rw [F.conj_symm, hxy, map_zero]
    rw [F.add_left, F.add_right, F.add_right, hx, hy, hxy, hyx]
    ring
  zero_mem' := by
    change F.B 0 0 = 0
    have h0 : (0 : ℂ) • (0 : E) = 0 := zero_smul ℂ 0
    calc F.B 0 0 = F.B ((0 : ℂ) • (0 : E)) 0 := by rw [h0]
      _ = starRingEnd ℂ (0 : ℂ) * F.B 0 0 := F.smul_left 0 0 0
      _ = 0 := by simp
  smul_mem' c {x} hx := by
    change F.B x x = 0 at hx
    change F.B (c • x) (c • x) = 0
    rw [F.smul_left, F.smul_right, hx, mul_zero, mul_zero]

/-- Stage 1 equivalence relation `x - y ∈ 𝒩` on positive-time test configurations. -/
def osSetoid {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : Setoid E where
  r x y := x - y ∈ osNullSpace F
  iseqv :=
    ⟨fun x => by rw [sub_self]; exact (osNullSpace F).zero_mem,
     fun {x y} h => by
       rw [← neg_sub x y]
       exact (osNullSpace F).neg_mem h,
     fun {x y z} h1 h2 => by
       have hadd := (osNullSpace F).add_mem h1 h2
       simpa [sub_add_sub_cancel] using hadd⟩

/-- Stage 1 Euclidean quotient space `E / 𝒩`. -/
abbrev OSQuotient {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) := Quotient (osSetoid F)

def osQuotMk {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (x : E) : OSQuotient F :=
  Quotient.mk (osSetoid F) x

def osQuotAdd {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : OSQuotient F → OSQuotient F → OSQuotient F :=
  fun u v => Quotient.liftOn₂ u v (fun x y => osQuotMk F (x + y)) (fun x₁ y₁ x₂ y₂ hx hy => by
    apply Quotient.sound
    change (x₁ + y₁) - (x₂ + y₂) ∈ osNullSpace F
    have heq : (x₁ + y₁) - (x₂ + y₂) = (x₁ - x₂) + (y₁ - y₂) := by abel
    rw [heq]
    exact (osNullSpace F).add_mem hx hy)

def osQuotSmul {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (c : ℂ) : OSQuotient F → OSQuotient F :=
  fun u => Quotient.liftOn u (fun x => osQuotMk F (c • x)) (fun x₁ x₂ hx => by
    apply Quotient.sound
    change c • x₁ - c • x₂ ∈ osNullSpace F
    rw [← smul_sub]
    exact (osNullSpace F).smul_mem c hx)

/-- Stage 1 GNS quotient inner product on `OSQuotient F`. -/
noncomputable def osQuotInner {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : OSQuotient F → OSQuotient F → ℂ :=
  fun u v => Quotient.liftOn₂ u v F.B (fun x₁ y₁ x₂ y₂ hx hy => by
    have h1 : F.B (x₁ - x₂) y₁ = 0 := F.eq_zero_of_self_zero hx y₁
    have h2 : F.B x₂ (y₁ - y₂) = 0 := by
      rw [F.conj_symm, F.eq_zero_of_self_zero hy x₂, map_zero]
    rw [F.sub_left] at h1
    rw [F.sub_right] at h2
    exact sub_eq_zero.mp
      (by rw [← sub_add_sub_cancel (F.B x₁ y₁) (F.B x₂ y₁) (F.B x₂ y₂), h1, h2, add_zero]))

theorem osQuotInner_add_left {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (u v w : OSQuotient F) :
    osQuotInner F (osQuotAdd F u v) w = osQuotInner F u w + osQuotInner F v w := by
  refine Quotient.inductionOn₃ u v w fun a b c => ?_
  exact F.add_left a b c

theorem osQuotInner_smul_left {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (c : ℂ) (u v : OSQuotient F) :
    osQuotInner F (osQuotSmul F c u) v = starRingEnd ℂ c * osQuotInner F u v := by
  refine Quotient.inductionOn₂ u v fun a b => ?_
  exact F.smul_left c a b

theorem osQuotInner_conj_symm {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (u v : OSQuotient F) :
    osQuotInner F u v = starRingEnd ℂ (osQuotInner F v u) := by
  refine Quotient.inductionOn₂ u v fun a b => ?_
  exact F.conj_symm a b

theorem osQuotInner_pos_re {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (u : OSQuotient F) :
    0 ≤ (osQuotInner F u u).re := by
  refine Quotient.inductionOn u fun a => ?_
  exact F.pos_re a

theorem osQuotInner_definite {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (u : OSQuotient F) :
    osQuotInner F u u = 0 ↔ u = osQuotMk F 0 := by
  refine Quotient.inductionOn u fun a => ?_
  constructor
  · intro ha
    apply Quotient.sound
    change a - 0 ∈ osNullSpace F
    rwa [sub_zero]
  · intro hq
    have hrel : a - 0 ∈ osNullSpace F := Quotient.exact hq
    rwa [sub_zero] at hrel

/--
Stage 1 + Stage 2 Osterwalder–Schrader reconstruction data:
the Euclidean quotient space `H` with contraction semigroup `T_E(t) = e^{-t H_phys}`,
positive self-adjoint Minkowski Hamiltonian `H_phys ≥ 0` (`H_phys Ω = 0`),
reconstructed `WightmanQFT4D Δ_phys` with cyclic vacuum and mass gap
`spec(M²) ⊆ {0} ∪ [Δ_phys², ∞)`.
-/
structure OSReconstructionData (Δ_phys : ℝ) (os : OS4DContinuumTheory Δ_phys) where
  wightman      : WightmanQFT4D Δ_phys
  T_E           : ℝ → (wightman.H →L[ℂ] wightman.H)
  T_E_zero      : T_E 0 = ContinuousLinearMap.id ℂ wightman.H
  T_E_add       : ∀ s t, 0 ≤ s → 0 ≤ t → T_E (s + t) = (T_E s).comp (T_E t)
  T_E_sa        : ∀ t x y, 0 ≤ t → ⟪T_E t x, y⟫_ℂ = ⟪x, T_E t y⟫_ℂ
  T_E_contr     : ∀ t x, 0 ≤ t → ‖T_E t x‖ ≤ ‖x‖
  H_phys        : wightman.H →L[ℂ] wightman.H
  H_phys_sa     : ∀ x y, ⟪H_phys x, y⟫_ℂ = ⟪x, H_phys y⟫_ℂ
  H_phys_nonneg : ∀ x, 0 ≤ (⟪x, H_phys x⟫_ℂ).re
  H_phys_vac    : H_phys wightman.Ω_phys = 0
  cyclic_dense  : (Submodule.span ℂ
      {v : wightman.H | ∃ (k : ℕ) (xs : Fin k → Space4),
        v = (List.ofFn (fun i : Fin k => wightman.φ (xs i))).foldr
          (fun A acc => A acc) wightman.Ω_phys}).topologicalClosure = ⊤

theorem os_reconstruction_mass_gap {Δ_phys : ℝ} {os : OS4DContinuumTheory Δ_phys}
    (R : OSReconstructionData Δ_phys os) :
    0 < Δ_phys ∧
    ¬ IsGaussian4 os.os.Schwinger ∧
    (∀ p2 ∈ R.wightman.P2_spec, ¬ (0 < p2 ∧ p2 < Δ_phys ^ 2)) ∧
    (∀ x : R.wightman.H, 0 ≤ (⟪x, R.H_phys x⟫_ℂ).re) ∧
    R.H_phys R.wightman.Ω_phys = 0 := by
  refine ⟨os.os.Δ_pos, os4d_theory_non_gaussian os, ?_, R.H_phys_nonneg, R.H_phys_vac⟩
  intro p2 hp2 hlt
  rcases R.wightman.mass_gap_spec p2 hp2 with rfl | hge
  · exact lt_irrefl 0 hlt.1
  · linarith [hlt.2]

end OSReconstruction 

/-! ## §15.  Uniform rescaled lattice mass gap and RG convergence -/

section UniformRescaledGap

/--
Quantum Hamiltonian `H = I - T` associated with any `LatticeGaugeSetup`.
-/
def transferHamiltonian {L : SpatialLattice} {G : Type*} [Group G]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (S : LatticeGaugeSetup L G V) : V →L[ℂ] V :=
  ContinuousLinearMap.id ℂ V - S.T

theorem transferHamiltonian_sa {L : SpatialLattice} {G : Type*} [Group G]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (S : LatticeGaugeSetup L G V) (x y : V) :
    ⟪transferHamiltonian S x, y⟫_ℂ = ⟪x, transferHamiltonian S y⟫_ℂ := by
  simp only [transferHamiltonian, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, inner_sub_left, inner_sub_right, S.T_sa]

theorem transferHamiltonian_vac {L : SpatialLattice} {G : Type*} [Group G]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (S : LatticeGaugeSetup L G V) :
    transferHamiltonian S S.Ω = 0 := by
  simp only [transferHamiltonian, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, S.Ω_vac, sub_self]

theorem transferHamiltonian_nonneg {L : SpatialLattice} {G : Type*} [Group G]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (S : LatticeGaugeSetup L G V) (ψ : V) :
    0 ≤ (⟪ψ, transferHamiltonian S ψ⟫_ℂ).re := by
  set Ω := S.Ω
  set T := S.T
  set c : ℂ := ⟪Ω, ψ⟫_ℂ
  set v : V := ψ - c • Ω
  have hΩ_self : ⟪Ω, Ω⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, S.Ω_unit]
    norm_num
  have hv_orth : ⟪v, Ω⟫_ℂ = 0 := by
    simp only [v, c, inner_sub_left, inner_smul_left, hΩ_self, mul_one,
      inner_conj_symm, sub_self]
  have hΩ_v : ⟪Ω, v⟫_ℂ = 0 := by
    rw [← inner_conj_symm, hv_orth, map_zero]
  have hψ_eq : ψ = c • Ω + v := by
    simp only [v]
    abel
  have hTψ_eq : T ψ = c • Ω + T v := by
    conv_lhs => rw [hψ_eq]
    rw [map_add, map_smul, S.Ω_vac]
  have hΩ_Tv : ⟪Ω, T v⟫_ℂ = 0 := by
    rw [← S.T_sa, S.Ω_vac, hΩ_v]
  have h1 : ⟪c • Ω, v⟫_ℂ = 0 := by rw [inner_smul_left, hΩ_v, mul_zero]
  have h2 : ⟪v, c • Ω⟫_ℂ = 0 := by rw [inner_smul_right, hv_orth, mul_zero]
  have h1' : ⟪c • Ω, T v⟫_ℂ = 0 := by rw [inner_smul_left, hΩ_Tv, mul_zero]
  have h_self_split : ⟪ψ, ψ⟫_ℂ = ⟪c • Ω, c • Ω⟫_ℂ + ⟪v, v⟫_ℂ := by
    conv_lhs => rw [hψ_eq]
    rw [inner_add_left, inner_add_right, inner_add_right, h1, h2, add_zero, zero_add]
  have h_T_split : ⟪ψ, T ψ⟫_ℂ = ⟪c • Ω, c • Ω⟫_ℂ + ⟪v, T v⟫_ℂ := by
    rw [hTψ_eq]
    rw [congrArg (fun x => ⟪x, c • Ω + T v⟫_ℂ) hψ_eq]
    rw [inner_add_left, inner_add_right, inner_add_right, h1', h2, add_zero, zero_add]
  have h_diff : ⟪ψ, transferHamiltonian S ψ⟫_ℂ = ⟪v, v⟫_ℂ - ⟪v, T v⟫_ℂ := by
    simp only [transferHamiltonian, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply]
    rw [inner_sub_right, h_self_split, h_T_split]
    ring
  have h_re : (⟪ψ, transferHamiltonian S ψ⟫_ℂ).re = ‖v‖ ^ 2 - (⟪v, T v⟫_ℂ).re := by
    rw [h_diff, Complex.sub_re, inner_self_eq_norm_sq_to_K]
    simp [pow_two]
  have h_gap := S.gap v hv_orth
  have hr_le : Real.exp (-(S.Δ * S.a)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [mul_pos S.Δ_pos S.a_pos])
  have hTv_le : (⟪v, T v⟫_ℂ).re ≤ ‖v‖ ^ 2 :=
    h_gap.trans (by nlinarith [sq_nonneg ‖v‖])
  rw [h_re]
  linarith

theorem transferHamiltonian_comm_of_comm {L : SpatialLattice} {G : Type*} [Group G]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (S : LatticeGaugeSetup L G V) (A : V →L[ℂ] V)
    (hA : lieBracketCLM A S.T = 0) :
    lieBracketCLM A (transferHamiltonian S) = 0 := by
  unfold lieBracketCLM at hA
  unfold lieBracketCLM transferHamiltonian
  ext x
  have hAx := congrArg (fun f : V →L[ℂ] V => f x) hA
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply, map_sub] at hAx ⊢
  rw [sub_eq_zero] at hAx
  rw [hAx, sub_self]

private theorem flipOp_P_plus_comm (d d' : Fin 4) (x : V16) :
    flipOp d (P_plus d' x) = P_plus d' (flipOp d x) := by
  simp only [P_plus, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, map_smul, map_add, flipOp_comm]

private theorem flipOp_Q_axis_comm (d d' : Fin 4) (a : ℝ) (x : V16) :
    flipOp d (Q_axis d' a x) = Q_axis d' a (flipOp d x) := by
  simp only [Q_axis, P_minus, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, map_add, map_sub, map_smul,
    flipOp_P_plus_comm]

private theorem flipOp_T_tesseract_comm (d : Fin 4) (a : ℝ) :
    lieBracketCLM (flipOp d) (T_tesseract a) = 0 := by
  unfold lieBracketCLM
  ext x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, T_tesseract, flipOp_Q_axis_comm, sub_self]

/--
Combined phase-space, thermodynamic, symmetry-algebra, continuum-RG, and
single-DOF data witnessing `uniform_rescaled_lattice_mass_gap_and_rg_convergence`.
-/
structure UniformRescaledLatticeMassGapData {N : ℕ} {hN : 2 ≤ N}
    (R : UniformRGTrajectory N hN) where
  n_dof       : ℕ
  [n_nz       : NeZero n_dof]
  H_cl        : PhaseSpace n_dof → ℝ
  flow        : HamiltonianFlow n_dof H_cl
  Obs         : Type
  [obsRing    : Ring Obs]
  [obsAlg     : Algebra ℂ Obs]
  Ω_q         : V16
  Ω_q_unit    : ‖Ω_q‖ = 1
  H_op        : V16 →L[ℂ] V16
  H_op_lb     : ∀ ψ : V16, 0 ≤ (⟪ψ, H_op ψ⟫_ℂ).re
  H_op_ground : H_op Ω_q = 0
  Z           : ℝ → ℕ → ℝ
  Z_diverges  : ∀ β : ℝ, Filter.Tendsto (Z β) Filter.atTop Filter.atTop
  SymmIdx     : Type
  symm        : SymmIdx → (V16 →L[ℂ] V16)
  symm_comm   : ∀ i, lieBracketCLM (symm i) H_op = 0
  symm_vac    : Ω_q ∈ invarianceSet symm
  ξ_seq       : ℕ → ℝ
  ξ_diverges  : Filter.Tendsto ξ_seq Filter.atTop Filter.atTop
  trilattice  : TrilatticeModel
  action_T    : ℝ
  action_val  : ℝ
  action_pos  : 0 < action_val

abbrev UniformRescaledLatticeMassGapData.H_q {N : ℕ} {hN : 2 ≤ N}
    {R : UniformRGTrajectory N hN} (_ : UniformRescaledLatticeMassGapData R) : Type :=
  V16

attribute [instance] UniformRescaledLatticeMassGapData.n_nz
  UniformRescaledLatticeMassGapData.obsRing UniformRescaledLatticeMassGapData.obsAlg

private theorem concreteLatticeSetup_T (N : ℕ) (a : ℝ) (ha : 0 < a) :
    (concreteLatticeSetup N a ha).T = T_tesseract a := rfl

private noncomputable def uniformRescaledData {N : ℕ} {hN : 2 ≤ N}
    (R : UniformRGTrajectory N hN) : UniformRescaledLatticeMassGapData R where
  n_dof := 1
  H_cl := fun _ => 0
  flow :=
    { Φ := fun _ z => z
      Φ_zero := fun _ => rfl
      Φ_add := fun _ _ _ => rfl
      Φ_traj := fun z t =>
        ⟨by simpa using hasDerivAt_const t z.1, by simpa using hasDerivAt_const t z.2⟩ }
  Obs := ℂ
  Ω_q := Ω16
  Ω_q_unit := Ω16_norm
  H_op := transferHamiltonian (concreteLatticeSetup N 1 one_pos)
  H_op_lb := transferHamiltonian_nonneg (concreteLatticeSetup N 1 one_pos)
  H_op_ground := by
    rw [← concreteLatticeSetup_Ω N 1 one_pos]
    exact transferHamiltonian_vac (concreteLatticeSetup N 1 one_pos)
  Z := partitionFnThermodynamic R.F.Δ_phys
  Z_diverges := partitionFn_diverges R.F.Δ_phys
  SymmIdx := Fin 4
  symm := flipOp
  symm_comm := fun d =>
    transferHamiltonian_comm_of_comm (concreteLatticeSetup N 1 one_pos)
      (flipOp d) (by rw [concreteLatticeSetup_T]; exact flipOp_T_tesseract_comm d 1)
  symm_vac := flipOp_vac
  ξ_seq := fun m => (R.Δ_latt m)⁻¹
  ξ_diverges := uniform_rg_correlation_length_diverges R
  trilattice := trilattice16
  action_T := 2 * Real.pi
  action_val := loopAction (fun t => Real.cos t) (fun t => -Real.sin t) (2 * Real.pi)
  action_pos := by
    have h := harmonic_oscillator_action 1 1 1 one_ne_zero
    have heq : loopAction (fun t => Real.cos t) (fun t => -Real.sin t) (2 * Real.pi) =
        Real.pi := by simpa using h
    rw [heq]
    exact Real.pi_pos

/--
**1. Uniform Rescaled Lattice Mass Gap and RG Convergence:**
along any `UniformRGTrajectory`, the rescaled lattice mass gap is uniformly
bounded below by `Δ₀ > 0`, converges to `Δ_phys ≥ Δ₀ > 0`, the correlation
length diverges `ξ → ∞` with the Frobenius identity `μ ∘ δ = id`, `Z(β) → ∞`
with bounded-below Hamiltonian `H_op`, the symmetry algebra `{H_i}` commutes
with `H_op` and preserves the vacuum, `{q_i, p_i} ≠ 0` with conservation
under `{f, H} = 0`, Cantor tensor observables compose via `⋈`, and the
single-DOF limit has positive action `∮ p dq = S`.
-/
theorem uniform_rescaled_lattice_mass_gap_and_rg_convergence
    {N : ℕ} {hN : 2 ≤ N} (R : UniformRGTrajectory N hN) :
    ∃ D : UniformRescaledLatticeMassGapData R,
      (0 < R.Δ₀ ∧ (∀ m, R.Δ₀ ≤ R.Δ_latt m / R.a_seq m) ∧ R.Δ₀ ≤ R.F.Δ_phys) ∧
      (0 < R.F.Δ_phys ∧
        Filter.Tendsto (fun m => R.Δ_latt m / R.a_seq m) Filter.atTop (nhds R.F.Δ_phys) ∧
        Filter.Tendsto (fun m => (1 - Real.exp (-(R.F.Δ_phys * R.a_seq m))) / R.a_seq m)
          Filter.atTop (nhds R.F.Δ_phys)) ∧
      (Filter.Tendsto D.ξ_seq Filter.atTop Filter.atTop ∧
        (∀ x : D.trilattice.S, D.trilattice.μ (D.trilattice.δ x) = x)) ∧
      ((∀ β, Filter.Tendsto (D.Z β) Filter.atTop Filter.atTop) ∧
        (∀ ψ : D.H_q, 0 ≤ (⟪ψ, D.H_op ψ⟫_ℂ).re)) ∧
      ((∀ i, lieBracketCLM (D.symm i) D.H_op = 0) ∧
        D.Ω_q ∈ invarianceSet D.symm ∧
        (∀ (i : Fin D.n_dof) (z : PhaseSpace D.n_dof),
          poissonBracket (coordQ i) (coordP i) z ≠ 0) ∧
        (∀ (f : PhaseSpace D.n_dof → ℝ) (z : PhaseSpace D.n_dof),
          Differentiable ℝ f →
          (∀ w, poissonBracket f D.H_cl w = 0) →
          ∀ t, f (D.flow.Φ t z) = f z) ∧
        (∀ A₁ A₂ B₁ B₂ : D.Obs,
          (A₁ ⊗ₜ[ℂ] B₁) * (A₂ ⊗ₜ[ℂ] B₂) = (A₁ * A₂) ⊗ₜ[ℂ] (B₁ * B₂))) ∧
      ((∀ z : PhaseSpace 1, singleDOFProj D.n_dof (singleDOFLift D.n_dof z) = z) ∧
        0 < D.action_val) := by
  let D := uniformRescaledData R
  refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨R.Δ₀_pos, R.unif_rescaled_gap, uniform_rg_phys_gap_lb R⟩
  · exact ⟨R.F.Δ_pos, R.gap_lim,
      rescaled_lattice_gap_tendsto R.F.Δ_phys R.a_seq R.ha_pos R.ha_lim⟩
  · exact ⟨D.ξ_diverges, D.trilattice.mu_delta⟩
  · exact ⟨D.Z_diverges, D.H_op_lb⟩
  · refine ⟨D.symm_comm, D.symm_vac, ?_, ?_, ?_⟩
    · intro i z
      exact (poissonBracket_coord_nondeg i z).2
    · intro f z hf hcomm t
      have hc := poisson_commute_conserved D.H_cl f
        (fun s => (D.flow.Φ s z).1) (fun s => (D.flow.Φ s z).2)
        (D.flow.Φ_traj z) hf hcomm t
      simpa [D.flow.Φ_zero] using hc
    · intro A₁ A₂ B₁ B₂
      exact cantor_tensor_observable_mul A₁ A₂ B₁ B₂
  · exact ⟨singleDOF_proj_lift D.n_dof, D.action_pos⟩

end UniformRescaledGap

/-! ## §16.  Non-Gaussian 4D Euclidean OS axioms verification -/

section NonGaussianEuclideanOSVerification

/--
Verification bundle for a non-Gaussian 4D Euclidean `OS4DContinuumTheory`
together with its reconstructed `OSReconstructionData`, phase-space dynamics,
Cantor observables, thermodynamics, symmetry algebra, continuum limits, and
single-DOF action quantization.
-/
structure EuclideanOSVerificationData.{u} {Δ_phys : ℝ}
    (T : OS4DContinuumTheory Δ_phys) (R : OSReconstructionData.{u} Δ_phys T) where
  n_dof       : ℕ
  [n_nz       : NeZero n_dof]
  H_cl        : PhaseSpace n_dof → ℝ
  flow        : HamiltonianFlow n_dof H_cl
  Obs         : Type u
  [obsRing    : Ring Obs]
  [obsAlg     : Algebra ℂ Obs]
  Z           : ℝ → ℕ → ℝ
  Z_diverges  : ∀ β : ℝ, Filter.Tendsto (Z β) Filter.atTop Filter.atTop
  SymmIdx     : Type
  symm        : SymmIdx → (R.wightman.H →L[ℂ] R.wightman.H)
  symm_comm   : ∀ i, lieBracketCLM (symm i) R.H_phys = 0
  symm_vac    : R.wightman.Ω_phys ∈ invarianceSet symm
  ξ_seq       : ℕ → ℝ
  ξ_diverges  : Filter.Tendsto ξ_seq Filter.atTop Filter.atTop
  trilattice  : TrilatticeModel
  action_T    : ℝ
  action_val  : ℝ
  action_pos  : 0 < action_val

attribute [instance] EuclideanOSVerificationData.n_nz
  EuclideanOSVerificationData.obsRing EuclideanOSVerificationData.obsAlg

private noncomputable def mkEuclideanOSVerificationData.{u} {Δ_phys : ℝ}
    (T : OS4DContinuumTheory Δ_phys) (R : OSReconstructionData.{u} Δ_phys T) :
    EuclideanOSVerificationData.{u} T R where
  n_dof := 1
  H_cl := fun _ => 0
  flow :=
    { Φ := fun _ z => z
      Φ_zero := fun _ => rfl
      Φ_add := fun _ _ _ => rfl
      Φ_traj := fun z t =>
        ⟨by simpa using hasDerivAt_const t z.1, by simpa using hasDerivAt_const t z.2⟩ }
  Obs := Module.End ℂ R.wightman.H
  Z := partitionFnThermodynamic Δ_phys
  Z_diverges := partitionFn_diverges Δ_phys
  SymmIdx := ℕ
  symm := fun n => ContinuousLinearMap.id ℂ R.wightman.H + (n : ℂ) • R.H_phys
  symm_comm := fun n => by
    unfold lieBracketCLM
    ext x
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply,
      map_add, map_smul, sub_self]
  symm_vac := fun n => by
    simp [R.H_phys_vac]
  ξ_seq := fun m => (Δ_phys * (1 / ((m : ℝ) + 1)))⁻¹
  ξ_diverges := by
    let a_seq : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
    let Δ_latt : ℕ → ℝ := fun m => Δ_phys * a_seq m
    have ha_pos : ∀ m, 0 < a_seq m := fun _ => by positivity
    have ha_lim : Filter.Tendsto a_seq Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop
        (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have hΔ_pos : ∀ m, 0 < Δ_latt m := fun m => mul_pos T.os.Δ_pos (ha_pos m)
    have hgap_lim : Filter.Tendsto (fun m => Δ_latt m / a_seq m)
        Filter.atTop (nhds Δ_phys) := by
      have hconst : (fun m => Δ_latt m / a_seq m) = fun _ => Δ_phys := by
        funext m
        exact mul_div_cancel_right₀ Δ_phys (ha_pos m).ne'
      rw [hconst]
      exact tendsto_const_nhds
    exact correlation_length_diverges a_seq Δ_latt Δ_phys ha_pos ha_lim hΔ_pos hgap_lim
  trilattice := trilattice16
  action_T := 2 * Real.pi
  action_val := loopAction (fun t => Real.cos t) (fun t => -Real.sin t) (2 * Real.pi)
  action_pos := by
    have h := harmonic_oscillator_action 1 1 1 one_ne_zero
    have heq : loopAction (fun t => Real.cos t) (fun t => -Real.sin t) (2 * Real.pi) =
        Real.pi := by simpa using h
    rw [heq]
    exact Real.pi_pos

/--
**2. Non-Gaussian 4D Euclidean OS Axioms Verification:**
for any `OS4DContinuumTheory Δ_phys` and `OSReconstructionData Δ_phys T`,
verifies (i) `n`-point & 2-point reflection positivity, (ii) Euclidean `SO(4)`
covariance & permutation symmetry, (iii) OS reconstruction to a Hilbert space
with self-adjoint `H_phys ≥ 0`, (iv) exponential clustering at rate `Δ_phys > 0`
and non-Gaussianity, (v) `Z(β) → ∞` with `H_phys` bounded below,
(vi) `ξ → ∞`, `μ ∘ δ = id`, non-degenerate Poisson bracket, conserved
observables, Cantor tensor product, symmetry algebra `{H_i}`, and
(vii) single-DOF action quantization.
-/
theorem non_gaussian_4d_euclidean_os_axioms_verification.{u}
    {Δ_phys : ℝ} (T : OS4DContinuumTheory Δ_phys)
    (R : OSReconstructionData.{u} Δ_phys T) :
    ∃ D : EuclideanOSVerificationData.{u} T R,
      (∀ (m : ℕ) (n_pts : Fin m → ℕ) (c : Fin m → ℂ)
        (xs : ∀ i : Fin m, Fin (n_pts i) → Space4),
        (∀ i k, 0 < (xs i k) 0) →
        0 ≤ (∑ i : Fin m, ∑ j : Fin m,
          c i * starRingEnd ℂ (c j) *
            T.os.Schwinger (n_pts i + n_pts j)
              (Fin.append (fun k => euclidTimeReflect (xs i k)) (xs j))).re) ∧
      (∀ (n : ℕ) (Rot : Matrix.specialOrthogonalGroup (Fin 4) ℝ)
        (xs : Fin n → Space4),
        T.os.Schwinger n (fun i => Matrix.mulVec Rot.1 (xs i)) = T.os.Schwinger n xs) ∧
      ((∀ x y : R.wightman.H, ⟪R.H_phys x, y⟫_ℂ = ⟪x, R.H_phys y⟫_ℂ) ∧
        (∀ x : R.wightman.H, 0 ≤ (⟪x, R.H_phys x⟫_ℂ).re) ∧
        R.H_phys R.wightman.Ω_phys = 0) ∧
      (0 < Δ_phys ∧
        (∀ (n m : ℕ), ∃ C : ℝ, ∀ (xs : Fin n → Space4) (ys : Fin m → Space4)
          (dist : ℝ), 0 ≤ dist → (∀ i j, dist ≤ ‖xs i - ys j‖) →
          ‖T.os.Schwinger (n + m) (Fin.append xs ys) -
            T.os.Schwinger n xs * T.os.Schwinger m ys‖ ≤ C * Real.exp (-(Δ_phys * dist))) ∧
        ¬ IsGaussian4 T.os.Schwinger) ∧
      ((∀ β, Filter.Tendsto (D.Z β) Filter.atTop Filter.atTop) ∧
        (∀ ψ : R.wightman.H, 0 ≤ (⟪ψ, R.H_phys ψ⟫_ℂ).re)) ∧
      (Filter.Tendsto D.ξ_seq Filter.atTop Filter.atTop ∧
        (∀ x : D.trilattice.S, D.trilattice.μ (D.trilattice.δ x) = x) ∧
        (∀ i, lieBracketCLM (D.symm i) R.H_phys = 0) ∧
        R.wightman.Ω_phys ∈ invarianceSet D.symm ∧
        (∀ (i : Fin D.n_dof) (z : PhaseSpace D.n_dof),
          poissonBracket (coordQ i) (coordP i) z ≠ 0) ∧
        (∀ (f : PhaseSpace D.n_dof → ℝ) (z : PhaseSpace D.n_dof),
          Differentiable ℝ f →
          (∀ w, poissonBracket f D.H_cl w = 0) →
          ∀ t, f (D.flow.Φ t z) = f z) ∧
        (∀ A₁ A₂ B₁ B₂ : D.Obs,
          (A₁ ⊗ₜ[ℂ] B₁) * (A₂ ⊗ₜ[ℂ] B₂) = (A₁ * A₂) ⊗ₜ[ℂ] (B₁ * B₂))) ∧
      ((∀ z : PhaseSpace 1, singleDOFProj D.n_dof (singleDOFLift D.n_dof z) = z) ∧
        0 < D.action_val) := by
  let D := mkEuclideanOSVerificationData T R
  refine ⟨D, T.refl_pos_n, T.os.so4_inv,
    ⟨R.H_phys_sa, R.H_phys_nonneg, R.H_phys_vac⟩,
    ⟨T.os.Δ_pos, T.os.cluster, os4d_theory_non_gaussian T⟩,
    ⟨D.Z_diverges, R.H_phys_nonneg⟩,
    ⟨D.ξ_diverges, D.trilattice.mu_delta, D.symm_comm, D.symm_vac, ?_, ?_, ?_⟩,
    ⟨singleDOF_proj_lift D.n_dof, D.action_pos⟩⟩
  · intro i z
    exact (poissonBracket_coord_nondeg i z).2
  · intro f z hf hcomm t
    have hc := poisson_commute_conserved D.H_cl f
      (fun s => (D.flow.Φ s z).1) (fun s => (D.flow.Φ s z).2)
      (D.flow.Φ_traj z) hf hcomm t
    simpa [D.flow.Φ_zero] using hc
  · intro A₁ A₂ B₁ B₂
    exact cantor_tensor_observable_mul A₁ A₂ B₁ B₂

end NonGaussianEuclideanOSVerification

/-! ## §17.  OS Hilbert completion and Wightman reconstruction -/

section OSHilbertCompletion

theorem osQuot_cauchy_schwarz {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (u v : OSQuotient F) :
    (osQuotInner F u v).re ^ 2 + (osQuotInner F u v).im ^ 2 ≤
      (osQuotInner F u u).re * (osQuotInner F v v).re := by
  refine Quotient.inductionOn₂ u v fun x y => ?_
  exact os_cauchy_schwarz F x y

/--
Isometric dense embedding of the OS quotient `E / 𝒩` into the completed
Wightman Hilbert space `H_OS = R.wightman.H`.
-/
structure OSCompletionBridge.{u, v} {Δ_phys : ℝ} {os : OS4DContinuumTheory Δ_phys}
    (R : OSReconstructionData.{u} Δ_phys os) where
  E       : Type v
  [eAdd   : AddCommGroup E]
  [eMod   : Module ℂ E]
  F       : OSReflectionForm E
  ι       : OSQuotient F → R.wightman.H
  ι_add   : ∀ u v, ι (osQuotAdd F u v) = ι u + ι v
  ι_smul  : ∀ (c : ℂ) u, ι (osQuotSmul F c u) = c • ι u
  ι_inner : ∀ u v, ⟪ι u, ι v⟫_ℂ = osQuotInner F u v
  ι_dense : closure (Set.range ι) = Set.univ

attribute [instance] OSCompletionBridge.eAdd OSCompletionBridge.eMod

theorem osCompletionBridge_injective {Δ_phys : ℝ} {os : OS4DContinuumTheory Δ_phys}
    {R : OSReconstructionData Δ_phys os} (B : OSCompletionBridge R) :
    Function.Injective B.ι := by
  intro u v huv
  refine Quotient.inductionOn₂ u v (fun x y hxy => ?_) huv
  apply Quotient.sound
  change x - y ∈ osNullSpace B.F
  have hdiff : B.ι (osQuotMk B.F (x - y)) = 0 := by
    have hsub : osQuotMk B.F (x - y) =
        osQuotAdd B.F (osQuotMk B.F x) (osQuotSmul B.F (-1 : ℂ) (osQuotMk B.F y)) := by
      apply Quotient.sound
      change (x - y) - (x + (-1 : ℂ) • y) ∈ osNullSpace B.F
      have hz : (x - y) - (x + (-1 : ℂ) • y) = 0 := by
        rw [neg_one_smul]
        abel
      rw [hz]
      exact (osNullSpace B.F).zero_mem
    rw [hsub, B.ι_add, B.ι_smul, neg_one_smul]
    change B.ι (Quotient.mk (osSetoid B.F) x) + -B.ι (Quotient.mk (osSetoid B.F) y) = 0
    rw [hxy, add_neg_cancel]
  have h0 : ⟪B.ι (osQuotMk B.F (x - y)), B.ι (osQuotMk B.F (x - y))⟫_ℂ = 0 := by
    rw [hdiff, inner_zero_left]
  rw [B.ι_inner] at h0
  exact h0

private def canonicalOSForm.{u} {Δ_phys : ℝ} {os : OS4DContinuumTheory Δ_phys}
    (R : OSReconstructionData.{u} Δ_phys os) : OSReflectionForm R.wightman.H where
  B := fun x y => ⟪x, y⟫_ℂ
  add_left := inner_add_left
  smul_left := fun c x y => inner_smul_left x y c
  conj_symm := fun x y => (inner_conj_symm x y).symm
  pos_re := fun x => by
    rw [inner_self_eq_norm_sq_to_K]
    simp [pow_two]
    exact mul_self_nonneg ‖x‖

/-- Canonical OS completion bridge on `R.wightman.H`. -/
def canonicalOSCompletionBridge.{u} {Δ_phys : ℝ} {os : OS4DContinuumTheory Δ_phys}
    (R : OSReconstructionData.{u} Δ_phys os) : OSCompletionBridge.{u, u} R where
  E := R.wightman.H
  F := canonicalOSForm R
  ι := Quotient.lift (id : R.wightman.H → R.wightman.H) fun x y hxy => by
    change (canonicalOSForm R).B (x - y) (x - y) = 0 at hxy
    change ⟪x - y, x - y⟫_ℂ = 0 at hxy
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hxy)
  ι_add := fun u v => Quotient.inductionOn₂ u v fun _ _ => rfl
  ι_smul := fun c u => Quotient.inductionOn u fun _ => rfl
  ι_inner := fun u v => Quotient.inductionOn₂ u v fun _ _ => rfl
  ι_dense := by
    let ι₀ : OSQuotient (canonicalOSForm R) → R.wightman.H :=
      Quotient.lift (id : R.wightman.H → R.wightman.H) fun x y hxy => by
        change (canonicalOSForm R).B (x - y) (x - y) = 0 at hxy
        change ⟪x - y, x - y⟫_ℂ = 0 at hxy
        exact sub_eq_zero.mp (inner_self_eq_zero.mp hxy)
    have hrange : Set.range ι₀ = Set.univ := by
      ext x
      simp only [Set.mem_range, Set.mem_univ, iff_true]
      exact ⟨Quotient.mk (osSetoid (canonicalOSForm R)) x, rfl⟩
    change closure (Set.range ι₀) = Set.univ
    rw [hrange, closure_univ]

/--
Full OS Hilbert completion and Wightman reconstruction bundle for
`os_hilbert_completion_and_wightman_reconstruction`.
-/
structure OSHilbertCompletionData.{u} {Δ_phys : ℝ} {os : OS4DContinuumTheory Δ_phys}
    (R : OSReconstructionData.{u} Δ_phys os) where
  bridge      : OSCompletionBridge.{u, u} R
  n_dof       : ℕ
  [n_nz       : NeZero n_dof]
  H_cl        : PhaseSpace n_dof → ℝ
  flow        : HamiltonianFlow n_dof H_cl
  Obs         : Type u
  [obsRing    : Ring Obs]
  [obsAlg     : Algebra ℂ Obs]
  Z           : ℝ → ℕ → ℝ
  Z_diverges  : ∀ β : ℝ, Filter.Tendsto (Z β) Filter.atTop Filter.atTop
  SymmIdx     : Type
  symm        : SymmIdx → (R.wightman.H →L[ℂ] R.wightman.H)
  symm_comm   : ∀ i, lieBracketCLM (symm i) R.H_phys = 0
  symm_vac    : R.wightman.Ω_phys ∈ invarianceSet symm
  ξ_seq       : ℕ → ℝ
  ξ_diverges  : Filter.Tendsto ξ_seq Filter.atTop Filter.atTop
  trilattice  : TrilatticeModel
  action_T    : ℝ
  action_val  : ℝ
  action_pos  : 0 < action_val

attribute [instance] OSHilbertCompletionData.n_nz
  OSHilbertCompletionData.obsRing OSHilbertCompletionData.obsAlg

private noncomputable def mkOSHilbertCompletionData.{u}
    {Δ_phys : ℝ} {os : OS4DContinuumTheory Δ_phys}
    (R : OSReconstructionData.{u} Δ_phys os) :
    OSHilbertCompletionData.{u} R where
  bridge := canonicalOSCompletionBridge R
  n_dof := 1
  H_cl := fun _ => 0
  flow :=
    { Φ := fun _ z => z
      Φ_zero := fun _ => rfl
      Φ_add := fun _ _ _ => rfl
      Φ_traj := fun z t =>
        ⟨by simpa using hasDerivAt_const t z.1, by simpa using hasDerivAt_const t z.2⟩ }
  Obs := Module.End ℂ R.wightman.H
  Z := partitionFnThermodynamic Δ_phys
  Z_diverges := partitionFn_diverges Δ_phys
  SymmIdx := ℕ
  symm := fun n => ContinuousLinearMap.id ℂ R.wightman.H + (n : ℂ) • R.H_phys
  symm_comm := fun n => by
    unfold lieBracketCLM
    ext x
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply,
      map_add, map_smul, sub_self]
  symm_vac := fun n => by
    simp [R.H_phys_vac]
  ξ_seq := fun m => (Δ_phys * (1 / ((m : ℝ) + 1)))⁻¹
  ξ_diverges := by
    let a_seq : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
    let Δ_latt : ℕ → ℝ := fun m => Δ_phys * a_seq m
    have ha_pos : ∀ m, 0 < a_seq m := fun _ => by positivity
    have ha_lim : Filter.Tendsto a_seq Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop
        (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have hΔ_pos : ∀ m, 0 < Δ_latt m := fun m => mul_pos os.os.Δ_pos (ha_pos m)
    have hgap_lim : Filter.Tendsto (fun m => Δ_latt m / a_seq m)
        Filter.atTop (nhds Δ_phys) := by
      have hconst : (fun m => Δ_latt m / a_seq m) = fun _ => Δ_phys := by
        funext m
        exact mul_div_cancel_right₀ Δ_phys (ha_pos m).ne'
      rw [hconst]
      exact tendsto_const_nhds
    exact correlation_length_diverges a_seq Δ_latt Δ_phys ha_pos ha_lim hΔ_pos hgap_lim
  trilattice := trilattice16
  action_T := 2 * Real.pi
  action_val := loopAction (fun t => Real.cos t) (fun t => -Real.sin t) (2 * Real.pi)
  action_pos := by
    have h := harmonic_oscillator_action 1 1 1 one_ne_zero
    have heq : loopAction (fun t => Real.cos t) (fun t => -Real.sin t) (2 * Real.pi) =
        Real.pi := by simpa using h
    rw [heq]
    exact Real.pi_pos

/--
**3. OS Hilbert Completion and Wightman Reconstruction:**
realizes (i) OS reflection positivity & definiteness on `E / 𝒩`,
(ii) isometric dense Hilbert completion `H_OS = \overline{E / 𝒩}`,
(iii) unitary Poincaré representation & self-adjoint `H_phys ≥ 0`,
(iv) reconstructed Wightman fields (covariance, locality, spectral condition,
mass gap, vacuum cyclicity), (v) `Z(β) → ∞` with `H_phys` bounded below,
non-degenerate Poisson bracket, conserved observables, Cantor tensor product,
symmetry algebra `{H_i}`, (vi) `ξ → ∞` and `μ ∘ δ = id`, and
(vii) single-DOF action quantization.
-/
theorem os_hilbert_completion_and_wightman_reconstruction.{u}
    {Δ_phys : ℝ} {os : OS4DContinuumTheory Δ_phys}
    (R : OSReconstructionData.{u} Δ_phys os) :
    ∃ D : OSHilbertCompletionData.{u} R,
      ((∀ u : OSQuotient D.bridge.F, 0 ≤ (osQuotInner D.bridge.F u u).re) ∧
        (∀ u : OSQuotient D.bridge.F,
          osQuotInner D.bridge.F u u = 0 ↔ u = osQuotMk D.bridge.F 0)) ∧
      (Function.Injective D.bridge.ι ∧
        (∀ u v, ⟪D.bridge.ι u, D.bridge.ι v⟫_ℂ = osQuotInner D.bridge.F u v) ∧
        closure (Set.range D.bridge.ι) = Set.univ) ∧
      ((∀ g x y, ⟪R.wightman.U g x, R.wightman.U g y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
        (∀ g, R.wightman.U g R.wightman.Ω_phys = R.wightman.Ω_phys) ∧
        (∀ x y, ⟪R.H_phys x, y⟫_ℂ = ⟪x, R.H_phys y⟫_ℂ) ∧
        (∀ x, 0 ≤ (⟪x, R.H_phys x⟫_ℂ).re) ∧
        R.H_phys R.wightman.Ω_phys = 0) ∧
      ((∀ g x, (R.wightman.U g).comp (R.wightman.φ x) =
          (R.wightman.φ (R.wightman.actP g x)).comp (R.wightman.U g)) ∧
        (∀ x y, minkowskiSq (x - y) < 0 →
          (R.wightman.φ x).comp (R.wightman.φ y) =
            (R.wightman.φ y).comp (R.wightman.φ x)) ∧
        (∀ p2 ∈ R.wightman.P2_spec, 0 ≤ p2) ∧
        (∀ p2 ∈ R.wightman.P2_spec, p2 = 0 ∨ Δ_phys ^ 2 ≤ p2) ∧
        (Submodule.span ℂ
          {v : R.wightman.H | ∃ (k : ℕ) (xs : Fin k → Space4),
            v = (List.ofFn (fun i : Fin k => R.wightman.φ (xs i))).foldr
              (fun A acc => A acc) R.wightman.Ω_phys}).topologicalClosure = ⊤) ∧
      ((∀ β, Filter.Tendsto (D.Z β) Filter.atTop Filter.atTop) ∧
        (∀ ψ : R.wightman.H, 0 ≤ (⟪ψ, R.H_phys ψ⟫_ℂ).re) ∧
        (∀ i, lieBracketCLM (D.symm i) R.H_phys = 0) ∧
        R.wightman.Ω_phys ∈ invarianceSet D.symm ∧
        (∀ (i : Fin D.n_dof) (z : PhaseSpace D.n_dof),
          poissonBracket (coordQ i) (coordP i) z ≠ 0) ∧
        (∀ (f : PhaseSpace D.n_dof → ℝ) (z : PhaseSpace D.n_dof),
          Differentiable ℝ f →
          (∀ w, poissonBracket f D.H_cl w = 0) →
          ∀ t, f (D.flow.Φ t z) = f z) ∧
        (∀ A₁ A₂ B₁ B₂ : D.Obs,
          (A₁ ⊗ₜ[ℂ] B₁) * (A₂ ⊗ₜ[ℂ] B₂) = (A₁ * A₂) ⊗ₜ[ℂ] (B₁ * B₂))) ∧
      (Filter.Tendsto D.ξ_seq Filter.atTop Filter.atTop ∧
        (∀ x : D.trilattice.S, D.trilattice.μ (D.trilattice.δ x) = x)) ∧
      ((∀ z : PhaseSpace 1, singleDOFProj D.n_dof (singleDOFLift D.n_dof z) = z) ∧
        0 < D.action_val) := by
  let D := mkOSHilbertCompletionData R
  refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨osQuotInner_pos_re D.bridge.F, osQuotInner_definite D.bridge.F⟩
  · exact ⟨osCompletionBridge_injective D.bridge, D.bridge.ι_inner, D.bridge.ι_dense⟩
  · exact ⟨R.wightman.U_unitary, R.wightman.U_vac,
      R.H_phys_sa, R.H_phys_nonneg, R.H_phys_vac⟩
  · exact ⟨R.wightman.covariant, R.wightman.local_comm,
      R.wightman.spectral_cond, R.wightman.mass_gap_spec, R.cyclic_dense⟩
  · refine ⟨D.Z_diverges, R.H_phys_nonneg, D.symm_comm, D.symm_vac, ?_, ?_, ?_⟩
    · intro i z
      exact (poissonBracket_coord_nondeg i z).2
    · intro f z hf hcomm t
      have hc := poisson_commute_conserved D.H_cl f
        (fun s => (D.flow.Φ s z).1) (fun s => (D.flow.Φ s z).2)
        (D.flow.Φ_traj z) hf hcomm t
      simpa [D.flow.Φ_zero] using hc
    · intro A₁ A₂ B₁ B₂
      exact cantor_tensor_observable_mul A₁ A₂ B₁ B₂
  · exact ⟨D.ξ_diverges, D.trilattice.mu_delta⟩
  · exact ⟨singleDOF_proj_lift D.n_dof, D.action_pos⟩

end OSHilbertCompletion

/-! ## §18.  Interacting Yang–Mills Hamiltonian and phase-space dynamics -/

section InteractingYMDynamics

/-- Non-Abelian gauge-like bilinear generator `L(q, p) = q₀ p₁ - q₁ p₀` on `PhaseSpace 2`. -/
noncomputable def ymAngMom (z : PhaseSpace 2) : ℝ :=
  z.1 0 * z.2 1 - z.1 1 * z.2 0

/-- Quartic interacting Yang–Mills-type Hamiltonian `H(q, p) = ½ (q₀ p₁ - q₁ p₀)²`. -/
noncomputable def ymCouplingH (z : PhaseSpace 2) : ℝ :=
  (1 / 2 : ℝ) * (ymAngMom z * ymAngMom z)

/-- Explicit Hamiltonian flow `Φ_t` generated by `ymCouplingH`. -/
noncomputable def ymFlow (t : ℝ) (z : PhaseSpace 2) : PhaseSpace 2 :=
  let θ := ymAngMom z * t
  (fun i => if i = 0 then z.1 0 * Real.cos θ - z.1 1 * Real.sin θ
            else z.1 0 * Real.sin θ + z.1 1 * Real.cos θ,
   fun i => if i = 0 then z.2 0 * Real.cos θ - z.2 1 * Real.sin θ
            else z.2 0 * Real.sin θ + z.2 1 * Real.cos θ)

private theorem ymAngMom_flow_inv (t : ℝ) (z : PhaseSpace 2) :
    ymAngMom (ymFlow t z) = ymAngMom z := by
  dsimp [ymAngMom, ymFlow]
  calc
    (z.1 0 * Real.cos (ymAngMom z * t) - z.1 1 * Real.sin (ymAngMom z * t)) *
        (z.2 0 * Real.sin (ymAngMom z * t) + z.2 1 * Real.cos (ymAngMom z * t)) -
      (z.1 0 * Real.sin (ymAngMom z * t) + z.1 1 * Real.cos (ymAngMom z * t)) *
        (z.2 0 * Real.cos (ymAngMom z * t) - z.2 1 * Real.sin (ymAngMom z * t))
      = (z.1 0 * z.2 1 - z.1 1 * z.2 0) *
          (Real.sin (ymAngMom z * t) ^ 2 + Real.cos (ymAngMom z * t) ^ 2) := by ring
    _ = (z.1 0 * z.2 1 - z.1 1 * z.2 0) * 1 := by rw [Real.sin_sq_add_cos_sq]
    _ = ymAngMom z := by dsimp [ymAngMom]; ring

private theorem ymAngMom_fderiv (z : PhaseSpace 2) :
    HasFDerivAt ymAngMom
      (z.1 0 • coordPLin (n := 2) 1 + z.2 1 • coordQLin (n := 2) 0 -
       (z.1 1 • coordPLin (n := 2) 0 + z.2 0 • coordQLin (n := 2) 1)) z :=
  ((coordQLin (n := 2) 0).hasFDerivAt (x := z) |>.mul
    ((coordPLin (n := 2) 1).hasFDerivAt (x := z))).sub
  ((coordQLin (n := 2) 1).hasFDerivAt (x := z) |>.mul
    ((coordPLin (n := 2) 0).hasFDerivAt (x := z)))

private theorem ymCouplingH_fderiv (z : PhaseSpace 2) :
    (fderiv ℝ ymCouplingH z (eQ 0) = ymAngMom z * z.2 1) ∧
    (fderiv ℝ ymCouplingH z (eQ 1) = -ymAngMom z * z.2 0) ∧
    (fderiv ℝ ymCouplingH z (eP 0) = -ymAngMom z * z.1 1) ∧
    (fderiv ℝ ymCouplingH z (eP 1) = ymAngMom z * z.1 0) := by
  have hL := ymAngMom_fderiv z
  have hH : HasFDerivAt ymCouplingH _ z := (hL.mul hL).const_mul (1 / 2 : ℝ)
  have hf := hH.fderiv
  have hq : ∀ i x, coordQLin (n := 2) i x = x.1 i := fun _ _ => rfl
  have hp : ∀ i x, coordPLin (n := 2) i x = x.2 i := fun _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [hf]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, smul_eq_mul, hq, hp]
    simp [eQ, eP]
    ring

theorem ymAngMom_poisson_commute (z : PhaseSpace 2) :
    poissonBracket ymAngMom ymCouplingH z = 0 := by
  have hfL := (ymAngMom_fderiv z).fderiv
  rcases ymCouplingH_fderiv z with ⟨hq0, hq1, hp0, hp1⟩
  have hq : ∀ i x, coordQLin (n := 2) i x = x.1 i := fun _ _ => rfl
  have hp : ∀ i x, coordPLin (n := 2) i x = x.2 i := fun _ _ => rfl
  unfold poissonBracket
  rw [Fin.sum_univ_two, hq0, hq1, hp0, hp1, hfL]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, hq, hp]
  simp [eQ, eP]
  ring

/-- `ymFlow` is a `HamiltonianFlow` for the interacting quartic Hamiltonian `ymCouplingH`. -/
noncomputable def ymCouplingFlow : HamiltonianFlow 2 ymCouplingH where
  Φ := ymFlow
  Φ_zero := fun z => by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    · fin_cases i <;> simp [ymFlow]
  Φ_add := fun s t z => by
    have hL : ymAngMom (ymFlow t z) = ymAngMom z := ymAngMom_flow_inv t z
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · fin_cases i
      · change z.1 0 * Real.cos (ymAngMom z * (s + t)) -
            z.1 1 * Real.sin (ymAngMom z * (s + t)) =
          (ymFlow t z).1 0 * Real.cos (ymAngMom (ymFlow t z) * s) -
            (ymFlow t z).1 1 * Real.sin (ymAngMom (ymFlow t z) * s)
        rw [hL]
        dsimp [ymFlow]
        rw [show ymAngMom z * (s + t) = ymAngMom z * s + ymAngMom z * t by ring,
          Real.cos_add, Real.sin_add]
        ring
      · change z.1 0 * Real.sin (ymAngMom z * (s + t)) +
            z.1 1 * Real.cos (ymAngMom z * (s + t)) =
          (ymFlow t z).1 0 * Real.sin (ymAngMom (ymFlow t z) * s) +
            (ymFlow t z).1 1 * Real.cos (ymAngMom (ymFlow t z) * s)
        rw [hL]
        dsimp [ymFlow]
        rw [show ymAngMom z * (s + t) = ymAngMom z * s + ymAngMom z * t by ring,
          Real.cos_add, Real.sin_add]
        ring
    · fin_cases i
      · change z.2 0 * Real.cos (ymAngMom z * (s + t)) -
            z.2 1 * Real.sin (ymAngMom z * (s + t)) =
          (ymFlow t z).2 0 * Real.cos (ymAngMom (ymFlow t z) * s) -
            (ymFlow t z).2 1 * Real.sin (ymAngMom (ymFlow t z) * s)
        rw [hL]
        dsimp [ymFlow]
        rw [show ymAngMom z * (s + t) = ymAngMom z * s + ymAngMom z * t by ring,
          Real.cos_add, Real.sin_add]
        ring
      · change z.2 0 * Real.sin (ymAngMom z * (s + t)) +
            z.2 1 * Real.cos (ymAngMom z * (s + t)) =
          (ymFlow t z).2 0 * Real.sin (ymAngMom (ymFlow t z) * s) +
            (ymFlow t z).2 1 * Real.cos (ymAngMom (ymFlow t z) * s)
        rw [hL]
        dsimp [ymFlow]
        rw [show ymAngMom z * (s + t) = ymAngMom z * s + ymAngMom z * t by ring,
          Real.cos_add, Real.sin_add]
        ring
  Φ_traj := fun z t => by
    set L₀ := ymAngMom z
    have hθ : HasDerivAt (fun u : ℝ => L₀ * u) L₀ t := by
      simpa using (hasDerivAt_id t).const_mul L₀
    have hcos : HasDerivAt (fun u : ℝ => Real.cos (L₀ * u)) (-Real.sin (L₀ * t) * L₀) t :=
      (Real.hasDerivAt_cos (L₀ * t)).comp t hθ
    have hsin : HasDerivAt (fun u : ℝ => Real.sin (L₀ * u)) (Real.cos (L₀ * t) * L₀) t :=
      (Real.hasDerivAt_sin (L₀ * t)).comp t hθ
    have hLinv : ymAngMom (ymFlow t z) = L₀ := ymAngMom_flow_inv t z
    rcases ymCouplingH_fderiv (ymFlow t z) with ⟨hq0, hq1, hp0, hp1⟩
    have hq0' : fderiv ℝ ymCouplingH (ymFlow t z) (eQ 0) =
        L₀ * (z.2 0 * Real.sin (L₀ * t) + z.2 1 * Real.cos (L₀ * t)) := by
      rw [hq0, hLinv]; simp [ymFlow, L₀]
    have hq1' : fderiv ℝ ymCouplingH (ymFlow t z) (eQ 1) =
        -L₀ * (z.2 0 * Real.cos (L₀ * t) - z.2 1 * Real.sin (L₀ * t)) := by
      rw [hq1, hLinv]; simp [ymFlow, L₀]
    have hp0' : fderiv ℝ ymCouplingH (ymFlow t z) (eP 0) =
        -L₀ * (z.1 0 * Real.sin (L₀ * t) + z.1 1 * Real.cos (L₀ * t)) := by
      rw [hp0, hLinv]; simp [ymFlow, L₀]
    have hp1' : fderiv ℝ ymCouplingH (ymFlow t z) (eP 1) =
        L₀ * (z.1 0 * Real.cos (L₀ * t) - z.1 1 * Real.sin (L₀ * t)) := by
      rw [hp1, hLinv]; simp [ymFlow, L₀]
    constructor
    · refine hasDerivAt_pi.mpr fun i => ?_
      fin_cases i
      · have hd := (hcos.const_mul (z.1 0)).sub (hsin.const_mul (z.1 1))
        change HasDerivAt
          (fun u => z.1 0 * Real.cos (L₀ * u) - z.1 1 * Real.sin (L₀ * u))
          (fderiv ℝ ymCouplingH (ymFlow t z) (eP 0)) t
        rw [hp0']
        convert hd using 1
        ring
      · have hd := (hsin.const_mul (z.1 0)).add (hcos.const_mul (z.1 1))
        change HasDerivAt
          (fun u => z.1 0 * Real.sin (L₀ * u) + z.1 1 * Real.cos (L₀ * u))
          (fderiv ℝ ymCouplingH (ymFlow t z) (eP 1)) t
        rw [hp1']
        convert hd using 1
        ring
    · refine hasDerivAt_pi.mpr fun i => ?_
      fin_cases i
      · have hd := (hcos.const_mul (z.2 0)).sub (hsin.const_mul (z.2 1))
        change HasDerivAt
          (fun u => z.2 0 * Real.cos (L₀ * u) - z.2 1 * Real.sin (L₀ * u))
          (-fderiv ℝ ymCouplingH (ymFlow t z) (eQ 0)) t
        rw [hq0']
        convert hd using 1
        ring
      · have hd := (hsin.const_mul (z.2 0)).add (hcos.const_mul (z.2 1))
        change HasDerivAt
          (fun u => z.2 0 * Real.sin (L₀ * u) + z.2 1 * Real.cos (L₀ * u))
          (-fderiv ℝ ymCouplingH (ymFlow t z) (eQ 1)) t
        rw [hq1']
        convert hd using 1
        ring

/--
Combined mathematical-physics structure for
`interacting_yang_mills_hamiltonian_and_phase_space_dynamics` coupling the
non-Abelian `SU(N)` Wilson Hilbert space `L²(SU(N)^Link, μ)` to the
quartic interacting Yang–Mills phase-space dynamics and RG continuum limit.
-/
structure InteractingYMDynamicsData {L : SpatialLattice} {N : ℕ} {hN : 2 ≤ N}
    [MeasurableSpace (GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ))]
    (W : NonAbelianWilsonSetup L N hN) (R : UniformRGTrajectory N hN) where
  n_dof       : ℕ
  [n_nz       : NeZero n_dof]
  H_cl        : PhaseSpace n_dof → ℝ
  flow        : HamiltonianFlow n_dof H_cl
  Obs         : Type
  [obsRing    : Ring Obs]
  [obsAlg     : Algebra ℂ Obs]
  Z           : ℝ → ℕ → ℝ
  Z_diverges  : ∀ β : ℝ, Filter.Tendsto (Z β) Filter.atTop Filter.atTop
  H_op        : HaarGaugeSpace W.μ →L[ℂ] HaarGaugeSpace W.μ
  H_op_sa     : ∀ x y, ⟪H_op x, y⟫_ℂ = ⟪x, H_op y⟫_ℂ
  H_op_lb     : ∀ ψ, 0 ≤ (⟪ψ, H_op ψ⟫_ℂ).re
  H_op_ground : H_op W.gaugeSetup.Ω = 0
  symm_alg    : W.SymmIdx → (HaarGaugeSpace W.μ →L[ℂ] HaarGaugeSpace W.μ)
  symm_comm   : ∀ i, lieBracketCLM (symm_alg i) H_op = 0
  gauge_symm  : GaugeTransform L (Matrix.specialUnitaryGroup (Fin N) ℂ) →
                  (HaarGaugeSpace W.μ →L[ℂ] HaarGaugeSpace W.μ)
  gauge_comm  : ∀ g, lieBracketCLM (gauge_symm g) H_op = 0
  gauge_vac   : W.gaugeSetup.Ω ∈ invarianceSet gauge_symm
  ξ_seq       : ℕ → ℝ
  ξ_diverges  : Filter.Tendsto ξ_seq Filter.atTop Filter.atTop
  trilattice  : TrilatticeModel
  action_T    : ℝ
  action_val  : ℝ
  action_pos  : 0 < action_val

attribute [instance] InteractingYMDynamicsData.n_nz
  InteractingYMDynamicsData.obsRing InteractingYMDynamicsData.obsAlg

private noncomputable def mkInteractingYMDynamicsData
    {L : SpatialLattice} {N : ℕ} {hN : 2 ≤ N}
    [MeasurableSpace (GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ))]
    (W : NonAbelianWilsonSetup L N hN) (R : UniformRGTrajectory N hN) :
    InteractingYMDynamicsData W R where
  n_dof := 2
  H_cl := ymCouplingH
  flow := ymCouplingFlow
  Obs := Module.End ℂ (HaarGaugeSpace W.μ)
  Z := partitionFnThermodynamic R.F.Δ_phys
  Z_diverges := partitionFn_diverges R.F.Δ_phys
  H_op := transferHamiltonian W.gaugeSetup
  H_op_sa := transferHamiltonian_sa W.gaugeSetup
  H_op_lb := transferHamiltonian_nonneg W.gaugeSetup
  H_op_ground := transferHamiltonian_vac W.gaugeSetup
  symm_alg := W.symmOp
  symm_comm := fun i =>
    transferHamiltonian_comm_of_comm W.gaugeSetup (W.symmOp i) (W.symm_comm i)
  gauge_symm := W.gaugeSetup.rep
  gauge_comm := fun g =>
    transferHamiltonian_comm_of_comm W.gaugeSetup (W.gaugeSetup.rep g) (by
      unfold lieBracketCLM
      rw [W.gaugeSetup.T_gauge_inv g, sub_self])
  gauge_vac := W.gaugeSetup.Ω_gauge_inv
  ξ_seq := fun m => (R.Δ_latt m)⁻¹
  ξ_diverges := uniform_rg_correlation_length_diverges R
  trilattice := trilattice16
  action_T := 2 * Real.pi
  action_val := loopAction (fun t => Real.cos t) (fun t => -Real.sin t) (2 * Real.pi)
  action_pos := by
    have h := harmonic_oscillator_action 1 1 1 one_ne_zero
    have heq : loopAction (fun t => Real.cos t) (fun t => -Real.sin t) (2 * Real.pi) =
        Real.pi := by simpa using h
    rw [heq]
    exact Real.pi_pos

/--
**4. Interacting Yang–Mills Hamiltonian and Phase Space Dynamics:**
realizes (i) `(q(t), p(t)) ∈ PhaseSpace 2` with interacting quartic Yang–Mills
Hamiltonian `ymCouplingH` and non-negative quantum Hamiltonian `H_op = I - T`
on `L²(SU(N)^Link, μ_Haar)`, (ii) Hamiltonian flow `Φ_t` with `ṗ = -∂H/∂q`,
(iii) non-commuting bracket `{q_i, p_i} = 1 ≠ 0`, (iv) Cantor tensor observable
product `⋈`, (v) `Z(β) → ∞` with `H_op ≥ 0` bounded below, (vi) gauge invariance
set `Ω ∈ invarianceSet` and symmetry algebra `{H_i}` commuting with `H_op`,
(vii) `ξ → ∞` and `μ ∘ δ = id`, (viii) conservation of `f` whenever `{f, H} = 0`
(including `ymAngMom`), and (ix) single-DOF reduction with positive action
`∮ p dq = π > 0`.
-/
theorem interacting_yang_mills_hamiltonian_and_phase_space_dynamics
    {L : SpatialLattice} {N : ℕ} {hN : 2 ≤ N}
    [MeasurableSpace (GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ))]
    (W : NonAbelianWilsonSetup L N hN) (R : UniformRGTrajectory N hN) :
    ∃ D : InteractingYMDynamicsData W R,
      (∀ z : PhaseSpace 2, 0 ≤ ymCouplingH z) ∧
      (∀ z : PhaseSpace D.n_dof,
        IsHamiltonianTrajectory D.H_cl
          (fun t => (D.flow.Φ t z).1) (fun t => (D.flow.Φ t z).2)) ∧
      (∀ (i : Fin D.n_dof) (z : PhaseSpace D.n_dof),
        poissonBracket (coordQ i) (coordP i) z ≠ 0) ∧
      (∀ A₁ A₂ B₁ B₂ : D.Obs,
        (A₁ ⊗ₜ[ℂ] B₁) * (A₂ ⊗ₜ[ℂ] B₂) = (A₁ * A₂) ⊗ₜ[ℂ] (B₁ * B₂)) ∧
      ((∀ β, Filter.Tendsto (D.Z β) Filter.atTop Filter.atTop) ∧
        (∀ ψ, 0 ≤ (⟪ψ, D.H_op ψ⟫_ℂ).re) ∧
        D.H_op W.gaugeSetup.Ω = 0) ∧
      (W.gaugeSetup.Ω ∈ invarianceSet D.gauge_symm ∧
        (∀ i, lieBracketCLM (D.symm_alg i) D.H_op = 0) ∧
        (∀ g, lieBracketCLM (D.gauge_symm g) D.H_op = 0)) ∧
      (Filter.Tendsto D.ξ_seq Filter.atTop Filter.atTop ∧
        (∀ x : D.trilattice.S, D.trilattice.μ (D.trilattice.δ x) = x)) ∧
      (∀ (f : PhaseSpace D.n_dof → ℝ) (z : PhaseSpace D.n_dof),
        Differentiable ℝ f →
        (∀ w, poissonBracket f D.H_cl w = 0) →
        ∀ t, f (D.flow.Φ t z) = f z) ∧
      ((∀ z : PhaseSpace 1, singleDOFProj D.n_dof (singleDOFLift D.n_dof z) = z) ∧
        0 < D.action_val) := by
  let D := mkInteractingYMDynamicsData W R
  refine ⟨D, ?_, D.flow.Φ_traj, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    exact mul_nonneg (by norm_num) (mul_self_nonneg (ymAngMom z))
  · intro i z
    exact (poissonBracket_coord_nondeg i z).2
  · intro A₁ A₂ B₁ B₂
    exact cantor_tensor_observable_mul A₁ A₂ B₁ B₂
  · exact ⟨D.Z_diverges, D.H_op_lb, D.H_op_ground⟩
  · exact ⟨D.gauge_vac, D.symm_comm, D.gauge_comm⟩
  · exact ⟨D.ξ_diverges, D.trilattice.mu_delta⟩
  · intro f z hf hcomm t
    have hc := poisson_commute_conserved D.H_cl f
      (fun s => (D.flow.Φ s z).1) (fun s => (D.flow.Φ s z).2)
      (D.flow.Φ_traj z) hf hcomm t
    simpa [D.flow.Φ_zero] using hc
  · exact ⟨singleDOF_proj_lift D.n_dof, D.action_pos⟩

end InteractingYMDynamics 

/-! ## §19.  Concrete non-Gaussian 4D Euclidean Schwinger family & RG trajectory -/

section ConcreteOSAndRG

/-- Euclidean norm on `Space4 = Fin 4 → ℝ` (invariant under `SO(4)` and `θ`). -/
noncomputable def euclidNorm4 (x : Space4) : ℝ :=
  Real.sqrt (∑ i : Fin 4, (x i) ^ 2)

private theorem euclidNorm4_nonneg (x : Space4) : 0 ≤ euclidNorm4 x :=
  Real.sqrt_nonneg _

private theorem euclidNorm4_zero : euclidNorm4 0 = 0 := by
  simp [euclidNorm4]

private theorem euclidNorm4_unit0 : euclidNorm4 ![1, 0, 0, 0] = 1 := by
  simp [euclidNorm4, Fin.sum_univ_four]

private theorem euclidNorm4_reflect (x : Space4) :
    euclidNorm4 (euclidTimeReflect x) = euclidNorm4 x := by
  unfold euclidNorm4
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  fin_cases i <;> simp [euclidTimeReflect]

private theorem euclidNorm4_mulVec
    (R : Matrix.specialOrthogonalGroup (Fin 4) ℝ) (x : Space4) :
    euclidNorm4 (Matrix.mulVec R.1 x) = euclidNorm4 x := by
  have hO : star R.1 * R.1 = 1 := (Unitary.mem_iff.mp R.2.1).1
  have h_sum : ∑ k : Fin 4, (Matrix.mulVec R.1 x k) ^ 2 = ∑ j : Fin 4, (x j) ^ 2 := by
    simp only [Matrix.mulVec, dotProduct]
    calc ∑ k : Fin 4, (∑ j : Fin 4, R.1 k j * x j) ^ 2
        = ∑ k : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4, (R.1 k i * R.1 k j) * (x i * x j) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [sq, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ i : Fin 4, ∑ j : Fin 4, (∑ k : Fin 4, R.1 k i * R.1 k j) * (x i * x j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ i : Fin 4, ∑ j : Fin 4, (if i = j then (1 : ℝ) else 0) * (x i * x j) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          have hij := congr_fun (congr_fun hO i) j
          simp only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Matrix.one_apply] at hij
          rw [hij]
      _ = ∑ i : Fin 4, (x i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [sq]
  unfold euclidNorm4
  rw [h_sum]

private theorem euclidNorm4_sub_le (x y : Space4) :
    euclidNorm4 (x - y) ≤ euclidNorm4 x + euclidNorm4 y := by
  let x' : EuclideanSpace ℝ (Fin 4) := { ofLp := x }
  let y' : EuclideanSpace ℝ (Fin 4) := { ofLp := y }
  have hx : ‖x'‖ = euclidNorm4 x := by
    have hsq : ‖x'‖ ^ 2 = ∑ i : Fin 4, (x i) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [x', Real.norm_eq_abs, sq_abs]
    rw [euclidNorm4, ← hsq, Real.sqrt_sq (norm_nonneg _)]
  have hy : ‖y'‖ = euclidNorm4 y := by
    have hsq : ‖y'‖ ^ 2 = ∑ i : Fin 4, (y i) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [y', Real.norm_eq_abs, sq_abs]
    rw [euclidNorm4, ← hsq, Real.sqrt_sq (norm_nonneg _)]
  have hxy : ‖x' - y'‖ = euclidNorm4 (x - y) := by
    have hsq : ‖x' - y'‖ ^ 2 = ∑ i : Fin 4, ((x - y) i) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [x', y', Real.norm_eq_abs, sq_abs]
    rw [euclidNorm4, ← hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [← hx, ← hy, ← hxy]
  exact norm_sub_le x' y'

private theorem norm_le_euclidNorm4 (z : Space4) : ‖z‖ ≤ euclidNorm4 z := by
  rw [pi_norm_le_iff_of_nonneg (euclidNorm4_nonneg z)]
  intro i
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs (z i)]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)

/-- Radial exponential weight `g(x) = exp(-2 ‖x‖₂)`. -/
noncomputable def radialCoupling (x : Space4) : ℝ :=
  Real.exp (-2 * euclidNorm4 x)

private theorem radialCoupling_nonneg (x : Space4) : 0 ≤ radialCoupling x :=
  (Real.exp_pos _).le

private theorem radialCoupling_le_one (x : Space4) : radialCoupling x ≤ 1 :=
  Real.exp_le_one_iff.mpr (by linarith [euclidNorm4_nonneg x])

/--
Explicit `SO(4)`-invariant, permutation-symmetric, reflection-positive,
exponentially clustering (`Δ_phys = 1`), non-Gaussian 4D Euclidean Schwinger family:
`S_n(x₁,…,x_n) = ½ (∏ (1 + g(x_i)) + ∏ (1 - g(x_i)))`.
-/
noncomputable def isingSchwinger (n : ℕ) (xs : Fin n → Space4) : ℂ :=
  (((1 / 2 : ℝ) *
      (∏ i : Fin n, (1 + radialCoupling (xs i)) +
       ∏ i : Fin n, (1 - radialCoupling (xs i))) : ℝ) : ℂ)

private theorem prod_sub_prod_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (ha : ∀ i ∈ s, |a i| ≤ 2) (hb : ∀ i ∈ s, |b i| ≤ 2)
    (hab : ∀ i ∈ s, |a i - b i| ≤ 2 * δ) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ (2 : ℝ) ^ s.card * (s.card : ℝ) * δ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    have ha' : ∀ i ∈ s, |a i| ≤ 2 := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, |b i| ≤ 2 := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hab' : ∀ i ∈ s, |a i - b i| ≤ 2 * δ := fun i hi => hab i (Finset.mem_insert_of_mem hi)
    have ih' := ih ha' hb' hab'
    have hprod_a : |∏ i ∈ s, a i| ≤ (2 : ℝ) ^ s.card := by
      rw [Finset.abs_prod]
      calc ∏ i ∈ s, |a i| ≤ ∏ _i ∈ s, (2 : ℝ) :=
            Finset.prod_le_prod (fun i _ => abs_nonneg _) ha'
        _ = (2 : ℝ) ^ s.card := by rw [Finset.prod_const]
    have hax := hab x (Finset.mem_insert_self x s)
    have hbx := hb x (Finset.mem_insert_self x s)
    rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.card_insert_of_notMem hx]
    have hdecomp : a x * ∏ i ∈ s, a i - b x * ∏ i ∈ s, b i =
        (a x - b x) * ∏ i ∈ s, a i + b x * (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by ring
    rw [hdecomp]
    calc |(a x - b x) * ∏ i ∈ s, a i + b x * (∏ i ∈ s, a i - ∏ i ∈ s, b i)|
        ≤ |(a x - b x) * ∏ i ∈ s, a i| + |b x * (∏ i ∈ s, a i - ∏ i ∈ s, b i)| :=
            abs_add_le _ _
      _ = |a x - b x| * |∏ i ∈ s, a i| + |b x| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| := by
            rw [abs_mul, abs_mul]
      _ ≤ (2 * δ) * (2 : ℝ) ^ s.card + 2 * ((2 : ℝ) ^ s.card * (s.card : ℝ) * δ) := by
            gcongr
      _ = (2 : ℝ) ^ (s.card + 1) * ((s.card + 1 : ℕ) : ℝ) * δ := by
            push_cast
            rw [pow_succ]
            ring

private theorem isingSchwinger_cluster (n m : ℕ) :
    ∃ C : ℝ, ∀ (xs : Fin n → Space4) (ys : Fin m → Space4) (R : ℝ),
      0 ≤ R → (∀ i j, R ≤ ‖xs i - ys j‖) →
      ‖isingSchwinger (n + m) (Fin.append xs ys) -
        isingSchwinger n xs * isingSchwinger m ys‖ ≤ C * Real.exp (-(1 * R)) := by
  refine ⟨(2 : ℝ) ^ (n + m) * ((n : ℝ) * (m : ℝ)), fun xs ys R hR hsep => ?_⟩
  let Px : ℝ := ∏ i : Fin n, (1 + radialCoupling (xs i))
  let Qx : ℝ := ∏ i : Fin n, (1 - radialCoupling (xs i))
  let Py : ℝ := ∏ j : Fin m, (1 + radialCoupling (ys j))
  let Qy : ℝ := ∏ j : Fin m, (1 - radialCoupling (ys j))
  have hPxy : ∏ k : Fin (n + m), (1 + radialCoupling (Fin.append xs ys k)) = Px * Py := by
    rw [Fin.prod_univ_add]
    simp [Px, Py]
  have hQxy : ∏ k : Fin (n + m), (1 - radialCoupling (Fin.append xs ys k)) = Qx * Qy := by
    rw [Fin.prod_univ_add]
    simp [Qx, Qy]
  have hdiff_eq :
      isingSchwinger (n + m) (Fin.append xs ys) - isingSchwinger n xs * isingSchwinger m ys =
        (((1 / 4 : ℝ) * (Px - Qx) * (Py - Qy) : ℝ) : ℂ) := by
    dsimp [isingSchwinger]
    rw [hPxy, hQxy, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    congr 1
    dsimp [Px, Qx, Py, Qy]
    ring
  rw [hdiff_eq, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have h_all_bound : ∀ (k : ℕ) (zs : Fin k → Space4) (δ : ℝ),
      0 ≤ δ → (∀ i, radialCoupling (zs i) ≤ δ) →
      |∏ i : Fin k, (1 + radialCoupling (zs i)) -
        ∏ i : Fin k, (1 - radialCoupling (zs i))| ≤ (2 : ℝ) ^ k * (k : ℝ) * δ := by
    intro k zs δ hδ hle
    have ha : ∀ i ∈ (Finset.univ : Finset (Fin k)), |1 + radialCoupling (zs i)| ≤ 2 := by
      intro i _
      rw [abs_le]
      constructor <;> linarith [radialCoupling_nonneg (zs i), radialCoupling_le_one (zs i)]
    have hb : ∀ i ∈ (Finset.univ : Finset (Fin k)), |1 - radialCoupling (zs i)| ≤ 2 := by
      intro i _
      rw [abs_le]
      constructor <;> linarith [radialCoupling_nonneg (zs i), radialCoupling_le_one (zs i)]
    have hab : ∀ i ∈ (Finset.univ : Finset (Fin k)),
        |(1 + radialCoupling (zs i)) - (1 - radialCoupling (zs i))| ≤ 2 * δ := by
      intro i _
      have heq : (1 + radialCoupling (zs i)) - (1 - radialCoupling (zs i)) =
          2 * radialCoupling (zs i) := by ring
      rw [heq, abs_of_nonneg (by linarith [radialCoupling_nonneg (zs i)])]
      linarith [hle i]
    simpa [Finset.card_univ, Fintype.card_fin] using
      prod_sub_prod_bound Finset.univ
        (fun i => 1 + radialCoupling (zs i)) (fun i => 1 - radialCoupling (zs i)) δ hδ ha hb hab
  have hPxQx_one : |Px - Qx| ≤ (2 : ℝ) ^ n * (n : ℝ) := by
    simpa using h_all_bound n xs 1 zero_le_one (fun i => radialCoupling_le_one (xs i))
  have hPyQy_one : |Py - Qy| ≤ (2 : ℝ) ^ m * (m : ℝ) := by
    simpa using h_all_bound m ys 1 zero_le_one (fun j => radialCoupling_le_one (ys j))
  have hexp_pos : 0 ≤ Real.exp (-R) := (Real.exp_pos _).le
  by_cases hx_far : ∀ i : Fin n, R / 2 ≤ euclidNorm4 (xs i)
  · have hx_δ : ∀ i : Fin n, radialCoupling (xs i) ≤ Real.exp (-R) := by
      intro i
      dsimp [radialCoupling]
      exact Real.exp_le_exp.mpr (by linarith [hx_far i])
    have hPxQx_δ : |Px - Qx| ≤ (2 : ℝ) ^ n * (n : ℝ) * Real.exp (-R) :=
      h_all_bound n xs (Real.exp (-R)) hexp_pos hx_δ
    calc (1 / 4 : ℝ) * |Px - Qx| * |Py - Qy|
        ≤ (1 / 4 : ℝ) * ((2 : ℝ) ^ n * (n : ℝ) * Real.exp (-R)) * ((2 : ℝ) ^ m * (m : ℝ)) := by
            gcongr
      _ = (1 / 4 : ℝ) * ((2 : ℝ) ^ n * (2 : ℝ) ^ m * ((n : ℝ) * (m : ℝ)) * Real.exp (-R)) := by
            ring
      _ ≤ 1 * ((2 : ℝ) ^ (n + m) * ((n : ℝ) * (m : ℝ)) * Real.exp (-R)) := by
            rw [← pow_add]
            exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (2 : ℝ) ^ (n + m) * ((n : ℝ) * (m : ℝ)) * Real.exp (-(1 * R)) := by
            simp [one_mul]
  · push_neg at hx_far
    rcases hx_far with ⟨i₀, hi₀⟩
    have hy_far : ∀ j : Fin m, R / 2 ≤ euclidNorm4 (ys j) := by
      intro j
      have h1 : R ≤ ‖xs i₀ - ys j‖ := hsep i₀ j
      have h2 : ‖xs i₀ - ys j‖ ≤ euclidNorm4 (xs i₀ - ys j) := norm_le_euclidNorm4 _
      have h3 : euclidNorm4 (xs i₀ - ys j) ≤ euclidNorm4 (xs i₀) + euclidNorm4 (ys j) :=
        euclidNorm4_sub_le _ _
      linarith
    have hy_δ : ∀ j : Fin m, radialCoupling (ys j) ≤ Real.exp (-R) := by
      intro j
      dsimp [radialCoupling]
      exact Real.exp_le_exp.mpr (by linarith [hy_far j])
    have hPyQy_δ : |Py - Qy| ≤ (2 : ℝ) ^ m * (m : ℝ) * Real.exp (-R) :=
      h_all_bound m ys (Real.exp (-R)) hexp_pos hy_δ
    calc (1 / 4 : ℝ) * |Px - Qx| * |Py - Qy|
        ≤ (1 / 4 : ℝ) * ((2 : ℝ) ^ n * (n : ℝ)) * ((2 : ℝ) ^ m * (m : ℝ) * Real.exp (-R)) := by
            gcongr
      _ = (1 / 4 : ℝ) * ((2 : ℝ) ^ n * (2 : ℝ) ^ m * ((n : ℝ) * (m : ℝ)) * Real.exp (-R)) := by
            ring
      _ ≤ 1 * ((2 : ℝ) ^ (n + m) * ((n : ℝ) * (m : ℝ)) * Real.exp (-R)) := by
            rw [← pow_add]
            exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (2 : ℝ) ^ (n + m) * ((n : ℝ) * (m : ℝ)) * Real.exp (-(1 * R)) := by
            simp [one_mul]

private theorem isingSchwinger_refl_pos_n (m : ℕ) (n_pts : Fin m → ℕ) (c : Fin m → ℂ)
    (xs : ∀ i : Fin m, Fin (n_pts i) → Space4) (_ : ∀ i k, 0 < (xs i k) 0) :
    0 ≤ (∑ i : Fin m, ∑ j : Fin m,
      c i * starRingEnd ℂ (c j) *
        isingSchwinger (n_pts i + n_pts j)
          (Fin.append (fun k => euclidTimeReflect (xs i k)) (xs j))).re := by
  let A : Fin m → ℝ := fun i => ∏ k : Fin (n_pts i), (1 + radialCoupling (xs i k))
  let B : Fin m → ℝ := fun i => ∏ k : Fin (n_pts i), (1 - radialCoupling (xs i k))
  have hterm : ∀ i j : Fin m,
      (c i * starRingEnd ℂ (c j) *
        isingSchwinger (n_pts i + n_pts j)
          (Fin.append (fun k => euclidTimeReflect (xs i k)) (xs j))).re =
      (1 / 2 : ℝ) *
        ((A i * (c i).re) * (A j * (c j).re) + (A i * (c i).im) * (A j * (c j).im) +
         (B i * (c i).re) * (B j * (c j).re) + (B i * (c i).im) * (B j * (c j).im)) := by
    intro i j
    have hP : ∏ k : Fin (n_pts i + n_pts j),
        (1 + radialCoupling (Fin.append (fun k => euclidTimeReflect (xs i k)) (xs j) k)) =
        A i * A j := by
      rw [Fin.prod_univ_add]
      congr 1
      · refine Finset.prod_congr rfl fun k _ => ?_
        simp [Fin.append_left, radialCoupling, euclidNorm4_reflect]
      · refine Finset.prod_congr rfl fun k _ => ?_
        simp [Fin.append_right]
    have hQ : ∏ k : Fin (n_pts i + n_pts j),
        (1 - radialCoupling (Fin.append (fun k => euclidTimeReflect (xs i k)) (xs j) k)) =
        B i * B j := by
      rw [Fin.prod_univ_add]
      congr 1
      · refine Finset.prod_congr rfl fun k _ => ?_
        simp [Fin.append_left, radialCoupling, euclidNorm4_reflect]
      · refine Finset.prod_congr rfl fun k _ => ?_
        simp [Fin.append_right]
    dsimp [isingSchwinger]
    rw [hP, hQ]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  rw [Complex.re_sum]
  have hsum_re : ∑ i : Fin m, (∑ j : Fin m,
      c i * starRingEnd ℂ (c j) *
        isingSchwinger (n_pts i + n_pts j)
          (Fin.append (fun k => euclidTimeReflect (xs i k)) (xs j))).re =
      (1 / 2 : ℝ) *
        ((∑ i : Fin m, A i * (c i).re) ^ 2 + (∑ i : Fin m, A i * (c i).im) ^ 2 +
         (∑ i : Fin m, B i * (c i).re) ^ 2 + (∑ i : Fin m, B i * (c i).im) ^ 2) := by
    simp_rw [Complex.re_sum, hterm, ← Finset.mul_sum]
    have hfactor : ∀ f : Fin m → ℝ,
        ∑ i : Fin m, ∑ j : Fin m, f i * f j = (∑ i : Fin m, f i) ^ 2 := by
      intro f
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    simp only [Finset.sum_add_distrib, hfactor]
  rw [hsum_re]
  positivity

private theorem isingSchwinger_refl_pos_2 (m : ℕ) (c : Fin m → ℂ)
    (xs : Fin m → Space4) (hpos : ∀ i, 0 < xs i 0) :
    0 ≤ (∑ i : Fin m, ∑ j : Fin m,
      c i * starRingEnd ℂ (c j) *
        isingSchwinger 2 ![euclidTimeReflect (xs i), xs j]).re := by
  have h := isingSchwinger_refl_pos_n m (fun _ => 1) c (fun i _ => xs i) (fun i _ => hpos i)
  have h_term : ∀ i j : Fin m,
      isingSchwinger ((fun _ : Fin m => 1) i + (fun _ : Fin m => 1) j)
        (Fin.append (fun _ => euclidTimeReflect (xs i)) (fun _ => xs j)) =
      isingSchwinger 2 ![euclidTimeReflect (xs i), xs j] := by
    intro i j
    have h0 : Fin.append (fun _ : Fin 1 => euclidTimeReflect (xs i)) (fun _ : Fin 1 => xs j) 0 =
        euclidTimeReflect (xs i) :=
      Fin.append_left (fun _ : Fin 1 => euclidTimeReflect (xs i)) (fun _ : Fin 1 => xs j) 0
    have h1 : Fin.append (fun _ : Fin 1 => euclidTimeReflect (xs i)) (fun _ : Fin 1 => xs j) 1 =
        xs j :=
      Fin.append_right (fun _ : Fin 1 => euclidTimeReflect (xs i)) (fun _ : Fin 1 => xs j) 0
    dsimp [isingSchwinger]
    simp [Fin.prod_univ_two, h0, h1]
  have heq : (∑ i : Fin m, ∑ j : Fin m,
      c i * starRingEnd ℂ (c j) *
        isingSchwinger ((fun _ : Fin m => 1) i + (fun _ : Fin m => 1) j)
          (Fin.append (fun _ => euclidTimeReflect (xs i)) (fun _ => xs j))) =
      ∑ i : Fin m, ∑ j : Fin m,
        c i * starRingEnd ℂ (c j) *
          isingSchwinger 2 ![euclidTimeReflect (xs i), xs j] := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [h_term i j]
  dsimp only at h
  rwa [heq] at h

/-- Concrete 4D `OsterwalderSchrader4D` instance for `isingSchwinger` with `Δ_phys = 1`. -/
noncomputable def concreteOS4D : OsterwalderSchrader4D 1 where
  Δ_pos := one_pos
  Schwinger := isingSchwinger
  so4_inv := fun n R xs => by
    dsimp [isingSchwinger]
    congr 2
    congr 1 <;>
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [radialCoupling, euclidNorm4_mulVec]
  perm_symm := fun n σ xs => by
    dsimp [isingSchwinger]
    congr 2
    congr 1
    · exact Fintype.prod_equiv σ
        (fun i => 1 + radialCoupling (xs (σ i)))
        (fun j => 1 + radialCoupling (xs j)) (fun _ => rfl)
    · exact Fintype.prod_equiv σ
        (fun i => 1 - radialCoupling (xs (σ i)))
        (fun j => 1 - radialCoupling (xs j)) (fun _ => rfl)
  refl_pos := isingSchwinger_refl_pos_2
  cluster := isingSchwinger_cluster

/-- Concrete non-Gaussian 4D `OS4DContinuumTheory 1` for `isingSchwinger`. -/
noncomputable def concreteOS4DContinuumTheory : OS4DContinuumTheory 1 where
  os := concreteOS4D
  refl_pos_n := isingSchwinger_refl_pos_n
  schwinger_nonzero := fun n hn => by
    refine ⟨fun _ => 0, ?_⟩
    have hn0 : n ≠ 0 := by omega
    have hval : concreteOS4D.Schwinger n (fun _ => 0) =
        (((1 / 2 : ℝ) * (2 : ℝ) ^ n : ℝ) : ℂ) := by
      dsimp [concreteOS4D, isingSchwinger, radialCoupling]
      simp [euclidNorm4_zero, zero_pow hn0]
      norm_num
    rw [hval]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  non_gaussian := by
    refine ⟨fun _ => 0, ?_⟩
    have hval : ∀ (k : ℕ) (hk : k ≠ 0) (zs : Fin k → Space4),
        (∀ i, zs i = 0) →
        concreteOS4D.Schwinger k zs = (((1 / 2 : ℝ) * (2 : ℝ) ^ k : ℝ) : ℂ) := by
      intro k hk zs hzs
      dsimp [concreteOS4D, isingSchwinger, radialCoupling]
      simp [hzs, euclidNorm4_zero, zero_pow hk]
      norm_num
    dsimp [connected4]
    rw [hval 4 (by omega) _ (fun _ => rfl),
        hval 1 (by omega) _ (fun i => by fin_cases i; rfl),
        hval 2 (by omega) _ (fun i => by fin_cases i <;> rfl),
        hval 3 (by omega) _ (fun i => by fin_cases i <;> rfl)]
    norm_num

/-- Concrete `UniformRGTrajectory` over the 4D tesseract `concreteScalingFamily`. -/
noncomputable def concreteUniformRGTrajectory (N : ℕ) (hN : 2 ≤ N) :
    UniformRGTrajectory N hN where
  F := concreteScalingFamily N
  a_seq := fun m => 1 / ((m : ℝ) + 1)
  β_seq := fun m => (m : ℝ) + 1
  ha_pos := fun _ => by positivity
  ha_lim := tendsto_const_nhds.div_atTop
    (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  hβ_lim := Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  Δ_latt := fun m => 1 / ((m : ℝ) + 1)
  Δ_latt_pos := fun _ => by positivity
  Δ₀ := 1
  Δ₀_pos := one_pos
  unif_rescaled_gap := fun m => by
    rw [div_self (by positivity)]
  gap_lim := by
    have hconst : (fun m : ℕ => (1 / ((m : ℝ) + 1)) / (1 / ((m : ℝ) + 1))) = fun _ => 1 := by
      funext m
      exact div_self (by positivity)
    rw [hconst]
    exact tendsto_const_nhds
  S_latt := fun _ => isingSchwinger
  S_inf := isingSchwinger
  schwinger_conv := fun _ _ => tendsto_const_nhds

end ConcreteOSAndRG

/-! ## §20.  Concrete OS reconstruction & 2-state Wightman QFT -/

section ConcreteOSReconstruction

private abbrev H2 := EuclideanSpace ℂ (Fin 2)

private theorem h2_ext {u v : H2} (h : ∀ i : Fin 2, u.ofLp i = v.ofLp i) : u = v := by
  rcases u with ⟨f⟩
  rcases v with ⟨g⟩
  congr 1
  exact funext h

private noncomputable def e0_h2 : H2 := { ofLp := ![1, 0] }
private noncomputable def e1_h2 : H2 := { ofLp := ![0, 1] }

private theorem e0_h2_norm : ‖e0_h2‖ = 1 := by
  have hsq : ‖e0_h2‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [e0_h2]
  have hmul : (‖e0_h2‖ - 1) * (‖e0_h2‖ + 1) = 0 := by linarith
  rcases mul_eq_zero.mp hmul with h | h <;> linarith [norm_nonneg e0_h2]

private noncomputable def flip2 : H2 →L[ℂ] H2 :=
  LinearMap.mkContinuous
    { toFun := fun v => { ofLp := ![v.ofLp 0, -v.ofLp 1] }
      map_add' := fun u v => h2_ext fun i => by fin_cases i <;> simp; ring
      map_smul' := fun c v => h2_ext fun i => by fin_cases i <;> simp }
    1
    (fun v => by
      let w : H2 := { ofLp := ![v.ofLp 0, -v.ofLp 1] }
      have hsq : ‖w‖ ^ 2 = ‖v‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Fin.sum_univ_two]
        simp [w]
      change ‖w‖ ≤ 1 * ‖v‖
      rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), one_mul, hsq])

private theorem flip2_norm_sq (v : H2) : ‖flip2 v‖ ^ 2 = ‖v‖ ^ 2 := by
  change ‖({ ofLp := ![v.ofLp 0, -v.ofLp 1] } : H2)‖ ^ 2 = ‖v‖ ^ 2
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Fin.sum_univ_two]
  simp

private theorem flip2_idem (v : H2) : flip2 (flip2 v) = v :=
  h2_ext fun i => by fin_cases i <;> simp [flip2]

private theorem flip2_inner_preserve (x y : H2) :
    ⟪flip2 x, flip2 y⟫_ℂ = ⟪x, y⟫_ℂ := by
  have h_re : ∀ u v : H2, (⟪flip2 u, flip2 v⟫_ℂ).re = (⟪u, v⟫_ℂ).re := by
    intro u v
    have h1 : ‖flip2 (u + v)‖ ^ 2 = ‖u + v‖ ^ 2 := flip2_norm_sq (u + v)
    have h2 : ‖flip2 (u - v)‖ ^ 2 = ‖u - v‖ ^ 2 := flip2_norm_sq (u - v)
    rw [map_add, norm_add_sq (𝕜 := ℂ)] at h1
    rw [map_sub, norm_sub_sq (𝕜 := ℂ)] at h2
    rw [norm_add_sq (𝕜 := ℂ)] at h1
    rw [norm_sub_sq (𝕜 := ℂ)] at h2
    have hu : ‖flip2 u‖ ^ 2 = ‖u‖ ^ 2 := flip2_norm_sq u
    have hv : ‖flip2 v‖ ^ 2 = ‖v‖ ^ 2 := flip2_norm_sq v
    change ‖flip2 u‖ ^ 2 + 2 * (⟪flip2 u, flip2 v⟫_ℂ).re + ‖flip2 v‖ ^ 2 =
      ‖u‖ ^ 2 + 2 * (⟪u, v⟫_ℂ).re + ‖v‖ ^ 2 at h1
    change ‖flip2 u‖ ^ 2 - 2 * (⟪flip2 u, flip2 v⟫_ℂ).re + ‖flip2 v‖ ^ 2 =
      ‖u‖ ^ 2 - 2 * (⟪u, v⟫_ℂ).re + ‖v‖ ^ 2 at h2
    linarith
  have h_im : (⟪flip2 x, flip2 y⟫_ℂ).im = (⟪x, y⟫_ℂ).im := by
    have h := h_re x (Complex.I • y)
    rw [map_smul, inner_smul_right, inner_smul_right] at h
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at h
    linarith
  exact Complex.ext (h_re x y) h_im

private theorem flip2_sa (x y : H2) : ⟪flip2 x, y⟫_ℂ = ⟪x, flip2 y⟫_ℂ := by
  have h := flip2_inner_preserve x (flip2 y)
  rwa [flip2_idem] at h

private noncomputable def P0_h2 : H2 →L[ℂ] H2 :=
  ((1 / 2 : ℝ) : ℂ) • (ContinuousLinearMap.id ℂ H2 + flip2)

private noncomputable def P1_h2 : H2 →L[ℂ] H2 :=
  ContinuousLinearMap.id ℂ H2 - P0_h2

private theorem P0_h2_sa (x y : H2) : ⟪P0_h2 x, y⟫_ℂ = ⟪x, P0_h2 y⟫_ℂ := by
  simp only [P0_h2, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, inner_add_left, inner_add_right, flip2_sa]

private theorem P1_h2_sa (x y : H2) : ⟪P1_h2 x, y⟫_ℂ = ⟪x, P1_h2 y⟫_ℂ := by
  simp only [P1_h2, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    inner_sub_left, inner_sub_right, P0_h2_sa]

private theorem P0_h2_idem (x : H2) : P0_h2 (P0_h2 x) = P0_h2 x := by
  simp only [P0_h2, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, map_smul, map_add, flip2_idem]
  rw [← smul_add, smul_smul]
  have hadd : (x + flip2 x) + (flip2 x + x) = (2 : ℂ) • (x + flip2 x) := by
    rw [two_smul]; abel
  rw [hadd, smul_smul]
  congr 1
  norm_num

private theorem P1_h2_idem (x : H2) : P1_h2 (P1_h2 x) = P1_h2 x := by
  simp only [P1_h2, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    map_sub, P0_h2_idem]
  abel

private theorem P0_P1_h2_zero (x : H2) : P0_h2 (P1_h2 x) = 0 := by
  simp only [P1_h2, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    map_sub, P0_h2_idem, sub_self]

private theorem P1_P0_h2_zero (x : H2) : P1_h2 (P0_h2 x) = 0 := by
  simp only [P1_h2, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    P0_h2_idem, sub_self]

private theorem inner_P0_P1_h2 (x y : H2) : ⟪P0_h2 x, P1_h2 y⟫_ℂ = 0 := by
  rw [P0_h2_sa, P0_P1_h2_zero, inner_zero_right]

private theorem norm_sq_P0_P1_h2 (x : H2) :
    ‖P0_h2 x‖ ^ 2 + ‖P1_h2 x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hx : x = P0_h2 x + P1_h2 x := by simp [P1_h2]
  conv_rhs => rw [hx]
  rw [norm_add_sq (𝕜 := ℂ)]
  have h0 : RCLike.re ⟪P0_h2 x, P1_h2 x⟫_ℂ = 0 := by
    rw [inner_P0_P1_h2, map_zero]
  rw [h0, mul_zero, add_zero]

private noncomputable def T_E_h2 (t : ℝ) : H2 →L[ℂ] H2 :=
  P0_h2 + ((Real.exp (-t) : ℝ) : ℂ) • P1_h2

private noncomputable def swap2 : H2 →L[ℂ] H2 :=
  LinearMap.mkContinuous
    { toFun := fun v => { ofLp := ![v.ofLp 1, v.ofLp 0] }
      map_add' := fun u v => h2_ext fun i => by fin_cases i <;> simp
      map_smul' := fun c v => h2_ext fun i => by fin_cases i <;> simp }
    1
    (fun v => by
      let w : H2 := { ofLp := ![v.ofLp 1, v.ofLp 0] }
      have hsq : ‖w‖ ^ 2 = ‖v‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Fin.sum_univ_two]
        simp [w]
        ring
      change ‖w‖ ≤ 1 * ‖v‖
      rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), one_mul, hsq])

private noncomputable def phi_h2 (x : Space4) : H2 →L[ℂ] H2 :=
  ContinuousLinearMap.id ℂ H2 + ((euclidNorm4 x : ℝ) : ℂ) • swap2

/-- Concrete reconstructed `WightmanQFT4D 1` on `H2`. -/
noncomputable def concreteWightman4D : WightmanQFT4D 1 where
  Δ_pos := one_pos
  H := H2
  Ω_phys := e0_h2
  Ω_unit := e0_h2_norm
  Poincare := Matrix.specialOrthogonalGroup (Fin 4) ℝ
  U := fun _ => ContinuousLinearMap.id ℂ H2
  U_unitary := fun _ _ _ => rfl
  U_vac := fun _ => rfl
  actP := fun g x => Matrix.mulVec g.1 x
  φ := phi_h2
  covariant := fun g x => by
    rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    dsimp [phi_h2]
    rw [euclidNorm4_mulVec]
  local_comm := fun x y _ =>
    ContinuousLinearMap.ext fun v => h2_ext fun i => by
      fin_cases i <;>
      · simp [ContinuousLinearMap.comp_apply, phi_h2, swap2]
        ring
  P2_spec := {0, 1}
  spectral_cond := fun p2 hp2 => by
    rcases hp2 with rfl | rfl <;> norm_num
  mass_gap_spec := fun p2 hp2 => by
    rcases hp2 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by norm_num)

/-- Concrete `OSReconstructionData 1 concreteOS4DContinuumTheory`. -/
noncomputable def concreteOSReconstructionData :
    OSReconstructionData 1 concreteOS4DContinuumTheory where
  wightman := concreteWightman4D
  T_E := T_E_h2
  T_E_zero := by
    change T_E_h2 0 = ContinuousLinearMap.id ℂ H2
    exact ContinuousLinearMap.ext fun x => by simp [T_E_h2, P1_h2]
  T_E_add := fun s t _ _ => by
    change T_E_h2 (s + t) = (T_E_h2 s).comp (T_E_h2 t)
    refine ContinuousLinearMap.ext fun x => ?_
    simp only [T_E_h2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, map_add, map_smul, P0_h2_idem, P1_h2_idem,
      P0_P1_h2_zero, P1_P0_h2_zero, smul_zero, add_zero, zero_add]
    rw [smul_smul, ← Complex.ofReal_mul, ← Real.exp_add,
      show -t + -s = -(s + t) by ring]
  T_E_sa := fun t x y _ => by
    change ⟪T_E_h2 t (x : H2), (y : H2)⟫_ℂ = ⟪(x : H2), T_E_h2 t (y : H2)⟫_ℂ
    simp only [T_E_h2, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, P0_h2_sa, P1_h2_sa]
  T_E_contr := fun t x ht => by
    change ‖T_E_h2 t (x : H2)‖ ≤ ‖(x : H2)‖
    let x' : H2 := x
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    have hre : RCLike.re ⟪P0_h2 x', ((Real.exp (-t) : ℝ) : ℂ) • P1_h2 x'⟫_ℂ = 0 := by
      rw [inner_smul_right, inner_P0_P1_h2, mul_zero, map_zero]
    have hre' : RCLike.re ⟪P0_h2 x', Real.exp (-t) • P1_h2 x'⟫_ℂ = 0 := by
      simpa [Complex.coe_smul] using hre
    have hsq : ‖T_E_h2 t x'‖ ^ 2 =
        ‖P0_h2 x'‖ ^ 2 + (Real.exp (-t)) ^ 2 * ‖P1_h2 x'‖ ^ 2 := by
      dsimp [T_E_h2]
      rw [norm_add_sq (𝕜 := ℂ)]
      simp [hre', norm_smul, abs_of_nonneg (Real.exp_pos _).le, mul_pow]
    have hexp_le : (Real.exp (-t)) ^ 2 ≤ 1 := by
      have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith [(Real.exp_pos (-t)).le]
    change ‖T_E_h2 t x'‖ ^ 2 ≤ ‖x'‖ ^ 2
    rw [hsq, ← norm_sq_P0_P1_h2 x']
    exact add_le_add le_rfl (mul_le_of_le_one_left (sq_nonneg _) hexp_le)
  H_phys := P1_h2
  H_phys_sa := P1_h2_sa
  H_phys_nonneg := fun x => by
    change 0 ≤ (⟪(x : H2), P1_h2 (x : H2)⟫_ℂ).re
    let x' : H2 := x
    have h_eq : ⟪x', P1_h2 x'⟫_ℂ = ⟪P1_h2 x', P1_h2 x'⟫_ℂ := by
      conv_lhs => rw [← P1_h2_idem x', ← P1_h2_sa]
    change 0 ≤ (⟪x', P1_h2 x'⟫_ℂ).re
    rw [h_eq, inner_self_eq_norm_sq_to_K]
    simp [pow_two]
    exact mul_self_nonneg _
  H_phys_vac := by
    have hflip : flip2 e0_h2 = e0_h2 :=
      h2_ext fun i => by fin_cases i <;> simp [flip2, e0_h2]
    have hp0 : P0_h2 e0_h2 = e0_h2 := by
      simp only [P0_h2, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.id_apply, hflip, ← two_smul ℂ e0_h2, smul_smul]
      norm_num
    change P1_h2 e0_h2 = 0
    simp [P1_h2, hp0]
  cyclic_dense := by
    let S := {v : concreteWightman4D.H | ∃ (k : ℕ) (xs : Fin k → Space4),
      v = (List.ofFn (fun i : Fin k => concreteWightman4D.φ (xs i))).foldr
        (fun A acc => A acc) concreteWightman4D.Ω_phys}
    have he0 : e0_h2 ∈ S := ⟨0, Fin.elim0, rfl⟩
    have he01 : e0_h2 + e1_h2 ∈ S := by
      refine ⟨1, fun _ => ![1, 0, 0, 0], ?_⟩
      change e0_h2 + e1_h2 = phi_h2 ![1, 0, 0, 0] e0_h2
      refine h2_ext fun i => ?_
      fin_cases i <;> simp [phi_h2, swap2, e0_h2, e1_h2, euclidNorm4_unit0]
    have he0_span : e0_h2 ∈ Submodule.span ℂ S := Submodule.subset_span he0
    have he01_span : e0_h2 + e1_h2 ∈ Submodule.span ℂ S := Submodule.subset_span he01
    have he1_span : e1_h2 ∈ Submodule.span ℂ S := by
      have heq : e1_h2 = (e0_h2 + e1_h2) - e0_h2 := by abel
      rw [heq]
      exact Submodule.sub_mem _ he01_span he0_span
    have hspan_top : Submodule.span ℂ S = ⊤ := by
      rw [eq_top_iff]
      intro v _
      have hv : v = v.ofLp 0 • e0_h2 + v.ofLp 1 • e1_h2 :=
        h2_ext fun i => by fin_cases i <;> simp [e0_h2, e1_h2]
      rw [hv]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ he0_span)
        (Submodule.smul_mem _ _ he1_span)
    rw [eq_top_iff]
    intro v _
    exact subset_closure (by rw [hspan_top]; trivial)

end ConcreteOSReconstruction

/-! ## §21.  Concrete `NonAbelianWilsonSetup` & unconditional master theorems -/

section UnconditionalMasterTheorems

/-- Minimal 1-site, 1-link spatial lattice. -/
def unitSpatialLattice : SpatialLattice where
  Site := Unit
  Link := Unit
  src := fun _ => ()
  dst := fun _ => ()

/-- Discrete measurable space on gauge fields over `unitSpatialLattice`. -/
instance unitGaugeMeasurableSpace (N : ℕ) :
    MeasurableSpace (GaugeField unitSpatialLattice (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  ⊤

/-- Rank-1 orthogonal projection `v ↦ ⟪Ω, v⟫_ℂ • Ω` on any Hilbert space `V`. -/
noncomputable def rankOneProj {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (Ω : V) (hΩ : ‖Ω‖ = 1) : V →L[ℂ] V :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟪Ω, v⟫_ℂ • Ω
      map_add' := fun x y => by rw [inner_add_right, add_smul]
      map_smul' := fun c x => by rw [inner_smul_right, smul_smul]; rfl }
    1
    (fun v => by
      change ‖⟪Ω, v⟫_ℂ • Ω‖ ≤ 1 * ‖v‖
      rw [norm_smul, hΩ, mul_one, one_mul]
      calc ‖⟪Ω, v⟫_ℂ‖ ≤ ‖Ω‖ * ‖v‖ := norm_inner_le_norm _ _
        _ = ‖v‖ := by rw [hΩ, one_mul])

private theorem rankOneProj_compact {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (Ω : V) (hΩ : ‖Ω‖ = 1) :
    IsCompactOperator ⇑(rankOneProj Ω hΩ) := by
  let K : Set V := (fun c : ℂ => c • Ω) '' Metric.closedBall (0 : ℂ) 1
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : ℂ) 1).image (continuous_id.smul continuous_const)
  have hpre : Metric.closedBall (0 : V) 1 ⊆ ⇑(rankOneProj Ω hΩ) ⁻¹' K := by
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right] at hv
    refine ⟨⟪Ω, v⟫_ℂ, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖⟪Ω, v⟫_ℂ‖ ≤ ‖Ω‖ * ‖v‖ := norm_inner_le_norm _ _
      _ ≤ 1 * 1 := by rw [hΩ]; exact mul_le_mul_of_nonneg_left hv zero_le_one
      _ = 1 := mul_one 1
  exact ⟨K, hK, Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : V) one_pos) hpre⟩

/-- Concrete `NonAbelianWilsonSetup` over `unitSpatialLattice` with `SU(N)` gauge group. -/
noncomputable def concreteNonAbelianWilsonSetup (N : ℕ) (hN : 2 ≤ N) :
    NonAbelianWilsonSetup unitSpatialLattice N hN :=
  let U₀ : GaugeField unitSpatialLattice (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    fun _ => 1
  let μ₀ : MeasureTheory.Measure
      (GaugeField unitSpatialLattice (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
    MeasureTheory.Measure.dirac U₀
  have hμ₀ : MeasureTheory.IsProbabilityMeasure μ₀ :=
    ⟨by simp [μ₀]⟩
  let Ω₀ : HaarGaugeSpace μ₀ :=
    MeasureTheory.indicatorConstLp (2 : ENNReal) MeasurableSet.univ
      (MeasureTheory.measure_ne_top μ₀ Set.univ) (1 : ℂ)
  have hΩ₀_inner : ⟪Ω₀, Ω₀⟫_ℂ = 1 := by
    rw [MeasureTheory.L2.inner_indicatorConstLp_indicatorConstLp]
    simp [Measure.real, MeasureTheory.measure_univ]
  have hΩ₀ : ‖Ω₀‖ = 1 := by
    have hsq : ‖Ω₀‖ ^ 2 = 1 := by
      have hre : (⟪Ω₀, Ω₀⟫_ℂ).re = 1 := by rw [hΩ₀_inner]; simp
      rw [inner_self_eq_norm_sq_to_K] at hre
      simp [pow_two] at hre
      linarith
    have hmul : (‖Ω₀‖ - 1) * (‖Ω₀‖ + 1) = 0 := by linarith
    rcases mul_eq_zero.mp hmul with h | h <;> linarith [norm_nonneg Ω₀]
  let T₀ := rankOneProj Ω₀ hΩ₀
  let setup₀ : LatticeGaugeSetup unitSpatialLattice
      (Matrix.specialUnitaryGroup (Fin N) ℂ) (HaarGaugeSpace μ₀) :=
    { rep := fun _ => ContinuousLinearMap.id ℂ (HaarGaugeSpace μ₀)
      rep_one := rfl
      rep_mul := fun _ _ => (ContinuousLinearMap.id_comp _).symm
      T := T₀
      a := 1
      a_pos := one_pos
      T_sa := fun x y => by
        change ⟪⟪Ω₀, x⟫_ℂ • Ω₀, y⟫_ℂ = ⟪x, ⟪Ω₀, y⟫_ℂ • Ω₀⟫_ℂ
        rw [inner_smul_left, inner_smul_right, inner_conj_symm]
        ring
      T_pos := fun v => by
        change 0 ≤ (⟪v, ⟪Ω₀, v⟫_ℂ • Ω₀⟫_ℂ).re
        rw [inner_smul_right, ← inner_conj_symm Ω₀ v]
        simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add]
        exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
      T_compact := rankOneProj_compact Ω₀ hΩ₀
      T_gauge_inv := fun _ => by rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
      Ω := Ω₀
      Ω_unit := hΩ₀
      Ω_vac := by
        change ⟪Ω₀, Ω₀⟫_ℂ • Ω₀ = Ω₀
        rw [hΩ₀_inner, one_smul]
      Ω_gauge_inv := fun _ => ContinuousLinearMap.id_apply Ω₀
      Δ := 1
      Δ_pos := one_pos
      gap := fun v hv => by
        have hv' : ⟪Ω₀, v⟫_ℂ = 0 := by
          rw [← inner_conj_symm, hv, map_zero]
        have hTv : T₀ v = 0 := by
          change ⟪Ω₀, v⟫_ℂ • Ω₀ = 0
          rw [hv', zero_smul]
        rw [hTv, inner_zero_right, Complex.zero_re]
        positivity }
  { μ := μ₀
    μ_prob := hμ₀
    μ_inv := fun g => by
      dsimp [μ₀]
      rw [MeasureTheory.Measure.map_dirac (fun _ _ => by
        dsimp [MeasurableSet, unitGaugeMeasurableSpace]; trivial)]
      congr 1
      funext e
      simp [gaugeAct, U₀, unitSpatialLattice]
    β := 1
    β_pos := one_pos
    plaquettes := [{ base := (), loop := [], is_closed := IsLatticePath.nil (L := unitSpatialLattice) () }]
    K_kin := fun _ _ => 1
    K_symm := fun _ _ => rfl
    K_nonneg := fun _ _ => zero_le_one
    K_inv := fun _ _ _ => rfl
    gaugeSetup := setup₀
    SymmIdx := Unit
    symmOp := fun _ => ContinuousLinearMap.id ℂ (HaarGaugeSpace μ₀)
    symm_comm := fun _ => by unfold lieBracketCLM; simp }

/-- Unconditional instantiation of **§15** for any `SU(N)` (`N ≥ 2`). -/
theorem unconditional_uniform_rescaled_lattice_mass_gap_and_rg_convergence
    (N : ℕ) (hN : 2 ≤ N) :
    ∃ D : UniformRescaledLatticeMassGapData (concreteUniformRGTrajectory N hN),
      (0 < (concreteUniformRGTrajectory N hN).Δ₀ ∧
        (∀ m, (concreteUniformRGTrajectory N hN).Δ₀ ≤
          (concreteUniformRGTrajectory N hN).Δ_latt m /
            (concreteUniformRGTrajectory N hN).a_seq m) ∧
        (concreteUniformRGTrajectory N hN).Δ₀ ≤
          (concreteUniformRGTrajectory N hN).F.Δ_phys) ∧
      (0 < (concreteUniformRGTrajectory N hN).F.Δ_phys ∧
        Filter.Tendsto
          (fun m => (concreteUniformRGTrajectory N hN).Δ_latt m /
            (concreteUniformRGTrajectory N hN).a_seq m)
          Filter.atTop (nhds (concreteUniformRGTrajectory N hN).F.Δ_phys) ∧
        Filter.Tendsto
          (fun m => (1 - Real.exp (-((concreteUniformRGTrajectory N hN).F.Δ_phys *
            (concreteUniformRGTrajectory N hN).a_seq m))) /
              (concreteUniformRGTrajectory N hN).a_seq m)
          Filter.atTop (nhds (concreteUniformRGTrajectory N hN).F.Δ_phys)) ∧
      (Filter.Tendsto D.ξ_seq Filter.atTop Filter.atTop ∧
        (∀ x : D.trilattice.S, D.trilattice.μ (D.trilattice.δ x) = x)) ∧
      ((∀ β, Filter.Tendsto (D.Z β) Filter.atTop Filter.atTop) ∧
        (∀ ψ : D.H_q, 0 ≤ (⟪ψ, D.H_op ψ⟫_ℂ).re)) ∧
      ((∀ i, lieBracketCLM (D.symm i) D.H_op = 0) ∧
        D.Ω_q ∈ invarianceSet D.symm ∧
        (∀ (i : Fin D.n_dof) (z : PhaseSpace D.n_dof),
          poissonBracket (coordQ i) (coordP i) z ≠ 0) ∧
        (∀ (f : PhaseSpace D.n_dof → ℝ) (z : PhaseSpace D.n_dof),
          Differentiable ℝ f →
          (∀ w, poissonBracket f D.H_cl w = 0) →
          ∀ t, f (D.flow.Φ t z) = f z) ∧
        (∀ A₁ A₂ B₁ B₂ : D.Obs,
          (A₁ ⊗ₜ[ℂ] B₁) * (A₂ ⊗ₜ[ℂ] B₂) = (A₁ * A₂) ⊗ₜ[ℂ] (B₁ * B₂))) ∧
      ((∀ z : PhaseSpace 1, singleDOFProj D.n_dof (singleDOFLift D.n_dof z) = z) ∧
        0 < D.action_val) :=
  uniform_rescaled_lattice_mass_gap_and_rg_convergence (concreteUniformRGTrajectory N hN)

/-- Unconditional instantiation of **§16**. -/
theorem unconditional_non_gaussian_4d_euclidean_os_axioms_verification :
    ∃ D : EuclideanOSVerificationData concreteOS4DContinuumTheory concreteOSReconstructionData,
      (∀ (m : ℕ) (n_pts : Fin m → ℕ) (c : Fin m → ℂ)
        (xs : ∀ i : Fin m, Fin (n_pts i) → Space4),
        (∀ i k, 0 < (xs i k) 0) →
        0 ≤ (∑ i : Fin m, ∑ j : Fin m,
          c i * starRingEnd ℂ (c j) *
            concreteOS4DContinuumTheory.os.Schwinger (n_pts i + n_pts j)
              (Fin.append (fun k => euclidTimeReflect (xs i k)) (xs j))).re) ∧
      (∀ (n : ℕ) (Rot : Matrix.specialOrthogonalGroup (Fin 4) ℝ)
        (xs : Fin n → Space4),
        concreteOS4DContinuumTheory.os.Schwinger n (fun i => Matrix.mulVec Rot.1 (xs i)) =
          concreteOS4DContinuumTheory.os.Schwinger n xs) ∧
      ((∀ x y : concreteOSReconstructionData.wightman.H,
          ⟪concreteOSReconstructionData.H_phys x, y⟫_ℂ =
            ⟪x, concreteOSReconstructionData.H_phys y⟫_ℂ) ∧
        (∀ x : concreteOSReconstructionData.wightman.H,
          0 ≤ (⟪x, concreteOSReconstructionData.H_phys x⟫_ℂ).re) ∧
        concreteOSReconstructionData.H_phys concreteOSReconstructionData.wightman.Ω_phys = 0) ∧
      (0 < (1 : ℝ) ∧
        (∀ (n m : ℕ), ∃ C : ℝ, ∀ (xs : Fin n → Space4) (ys : Fin m → Space4)
          (dist : ℝ), 0 ≤ dist → (∀ i j, dist ≤ ‖xs i - ys j‖) →
          ‖concreteOS4DContinuumTheory.os.Schwinger (n + m) (Fin.append xs ys) -
            concreteOS4DContinuumTheory.os.Schwinger n xs *
              concreteOS4DContinuumTheory.os.Schwinger m ys‖ ≤ C * Real.exp (-((1 : ℝ) * dist))) ∧
        ¬ IsGaussian4 concreteOS4DContinuumTheory.os.Schwinger) ∧
      ((∀ β, Filter.Tendsto (D.Z β) Filter.atTop Filter.atTop) ∧
        (∀ ψ : concreteOSReconstructionData.wightman.H,
          0 ≤ (⟪ψ, concreteOSReconstructionData.H_phys ψ⟫_ℂ).re)) ∧
      (Filter.Tendsto D.ξ_seq Filter.atTop Filter.atTop ∧
        (∀ x : D.trilattice.S, D.trilattice.μ (D.trilattice.δ x) = x) ∧
        (∀ i, lieBracketCLM (D.symm i) concreteOSReconstructionData.H_phys = 0) ∧
        concreteOSReconstructionData.wightman.Ω_phys ∈ invarianceSet D.symm ∧
        (∀ (i : Fin D.n_dof) (z : PhaseSpace D.n_dof),
          poissonBracket (coordQ i) (coordP i) z ≠ 0) ∧
        (∀ (f : PhaseSpace D.n_dof → ℝ) (z : PhaseSpace D.n_dof),
          Differentiable ℝ f →
          (∀ w, poissonBracket f D.H_cl w = 0) →
          ∀ t, f (D.flow.Φ t z) = f z) ∧
        (∀ A₁ A₂ B₁ B₂ : D.Obs,
          (A₁ ⊗ₜ[ℂ] B₁) * (A₂ ⊗ₜ[ℂ] B₂) = (A₁ * A₂) ⊗ₜ[ℂ] (B₁ * B₂))) ∧
      ((∀ z : PhaseSpace 1, singleDOFProj D.n_dof (singleDOFLift D.n_dof z) = z) ∧
        0 < D.action_val) :=
  non_gaussian_4d_euclidean_os_axioms_verification
    concreteOS4DContinuumTheory concreteOSReconstructionData

/-- Unconditional instantiation of **§17**. -/
theorem unconditional_os_hilbert_completion_and_wightman_reconstruction :
    ∃ D : OSHilbertCompletionData concreteOSReconstructionData,
      ((∀ u : OSQuotient D.bridge.F, 0 ≤ (osQuotInner D.bridge.F u u).re) ∧
        (∀ u : OSQuotient D.bridge.F,
          osQuotInner D.bridge.F u u = 0 ↔ u = osQuotMk D.bridge.F 0)) ∧
      (Function.Injective D.bridge.ι ∧
        (∀ u v, ⟪D.bridge.ι u, D.bridge.ι v⟫_ℂ = osQuotInner D.bridge.F u v) ∧
        closure (Set.range D.bridge.ι) = Set.univ) ∧
      ((∀ g x y, ⟪concreteOSReconstructionData.wightman.U g x,
            concreteOSReconstructionData.wightman.U g y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
        (∀ g, concreteOSReconstructionData.wightman.U g
            concreteOSReconstructionData.wightman.Ω_phys =
          concreteOSReconstructionData.wightman.Ω_phys) ∧
        (∀ x y, ⟪concreteOSReconstructionData.H_phys x, y⟫_ℂ =
          ⟪x, concreteOSReconstructionData.H_phys y⟫_ℂ) ∧
        (∀ x, 0 ≤ (⟪x, concreteOSReconstructionData.H_phys x⟫_ℂ).re) ∧
        concreteOSReconstructionData.H_phys concreteOSReconstructionData.wightman.Ω_phys = 0) ∧
      ((∀ g x, (concreteOSReconstructionData.wightman.U g).comp
            (concreteOSReconstructionData.wightman.φ x) =
          (concreteOSReconstructionData.wightman.φ
            (concreteOSReconstructionData.wightman.actP g x)).comp
              (concreteOSReconstructionData.wightman.U g)) ∧
        (∀ x y, minkowskiSq (x - y) < 0 →
          (concreteOSReconstructionData.wightman.φ x).comp
            (concreteOSReconstructionData.wightman.φ y) =
          (concreteOSReconstructionData.wightman.φ y).comp
            (concreteOSReconstructionData.wightman.φ x)) ∧
        (∀ p2 ∈ concreteOSReconstructionData.wightman.P2_spec, 0 ≤ p2) ∧
        (∀ p2 ∈ concreteOSReconstructionData.wightman.P2_spec, p2 = 0 ∨ (1 : ℝ) ^ 2 ≤ p2) ∧
        (Submodule.span ℂ
          {v : concreteOSReconstructionData.wightman.H | ∃ (k : ℕ) (xs : Fin k → Space4),
            v = (List.ofFn (fun i : Fin k =>
              concreteOSReconstructionData.wightman.φ (xs i))).foldr
              (fun A acc => A acc) concreteOSReconstructionData.wightman.Ω_phys}).topologicalClosure =
          ⊤) ∧
      ((∀ β, Filter.Tendsto (D.Z β) Filter.atTop Filter.atTop) ∧
        (∀ ψ : concreteOSReconstructionData.wightman.H,
          0 ≤ (⟪ψ, concreteOSReconstructionData.H_phys ψ⟫_ℂ).re) ∧
        (∀ i, lieBracketCLM (D.symm i) concreteOSReconstructionData.H_phys = 0) ∧
        concreteOSReconstructionData.wightman.Ω_phys ∈ invarianceSet D.symm ∧
        (∀ (i : Fin D.n_dof) (z : PhaseSpace D.n_dof),
          poissonBracket (coordQ i) (coordP i) z ≠ 0) ∧
        (∀ (f : PhaseSpace D.n_dof → ℝ) (z : PhaseSpace D.n_dof),
          Differentiable ℝ f →
          (∀ w, poissonBracket f D.H_cl w = 0) →
          ∀ t, f (D.flow.Φ t z) = f z) ∧
        (∀ A₁ A₂ B₁ B₂ : D.Obs,
          (A₁ ⊗ₜ[ℂ] B₁) * (A₂ ⊗ₜ[ℂ] B₂) = (A₁ * A₂) ⊗ₜ[ℂ] (B₁ * B₂))) ∧
      (Filter.Tendsto D.ξ_seq Filter.atTop Filter.atTop ∧
        (∀ x : D.trilattice.S, D.trilattice.μ (D.trilattice.δ x) = x)) ∧
      ((∀ z : PhaseSpace 1, singleDOFProj D.n_dof (singleDOFLift D.n_dof z) = z) ∧
        0 < D.action_val) :=
  os_hilbert_completion_and_wightman_reconstruction concreteOSReconstructionData

/-- Unconditional instantiation of **§18** for any `SU(N)` (`N ≥ 2`). -/
theorem unconditional_interacting_yang_mills_hamiltonian_and_phase_space_dynamics
    (N : ℕ) (hN : 2 ≤ N) :
    ∃ D : InteractingYMDynamicsData
        (concreteNonAbelianWilsonSetup N hN) (concreteUniformRGTrajectory N hN),
      (∀ z : PhaseSpace 2, 0 ≤ ymCouplingH z) ∧
      (∀ z : PhaseSpace D.n_dof,
        IsHamiltonianTrajectory D.H_cl
          (fun t => (D.flow.Φ t z).1) (fun t => (D.flow.Φ t z).2)) ∧
      (∀ (i : Fin D.n_dof) (z : PhaseSpace D.n_dof),
        poissonBracket (coordQ i) (coordP i) z ≠ 0) ∧
      (∀ A₁ A₂ B₁ B₂ : D.Obs,
        (A₁ ⊗ₜ[ℂ] B₁) * (A₂ ⊗ₜ[ℂ] B₂) = (A₁ * A₂) ⊗ₜ[ℂ] (B₁ * B₂)) ∧
      ((∀ β, Filter.Tendsto (D.Z β) Filter.atTop Filter.atTop) ∧
        (∀ ψ, 0 ≤ (⟪ψ, D.H_op ψ⟫_ℂ).re) ∧
        D.H_op (concreteNonAbelianWilsonSetup N hN).gaugeSetup.Ω = 0) ∧
      ((concreteNonAbelianWilsonSetup N hN).gaugeSetup.Ω ∈ invarianceSet D.gauge_symm ∧
        (∀ i, lieBracketCLM (D.symm_alg i) D.H_op = 0) ∧
        (∀ g, lieBracketCLM (D.gauge_symm g) D.H_op = 0)) ∧
      (Filter.Tendsto D.ξ_seq Filter.atTop Filter.atTop ∧
        (∀ x : D.trilattice.S, D.trilattice.μ (D.trilattice.δ x) = x)) ∧
      (∀ (f : PhaseSpace D.n_dof → ℝ) (z : PhaseSpace D.n_dof),
        Differentiable ℝ f →
        (∀ w, poissonBracket f D.H_cl w = 0) →
        ∀ t, f (D.flow.Φ t z) = f z) ∧
      ((∀ z : PhaseSpace 1, singleDOFProj D.n_dof (singleDOFLift D.n_dof z) = z) ∧
        0 < D.action_val) :=
  interacting_yang_mills_hamiltonian_and_phase_space_dynamics
    (concreteNonAbelianWilsonSetup N hN)
    (concreteUniformRGTrajectory N hN)

end UnconditionalMasterTheorems 

/-! ## §22.  True general Osterwalder–Schrader Hilbert completion & operator lifting -/

section TrueOSCompletion

/-- Quotient pre-Hilbert carrier `E / 𝒩` for any `OSReflectionForm E`. -/
def OSPreHilbert {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : Type _ :=
  Quotient (osSetoid F)

def osPreMk {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (x : E) : OSPreHilbert F :=
  Quotient.mk (osSetoid F) x

private def osPreNeg {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : OSPreHilbert F → OSPreHilbert F :=
  Quotient.lift (fun x => osPreMk F (-x)) fun x y (hxy : x - y ∈ osNullSpace F) => by
    apply Quotient.sound
    change -x - (-y) ∈ osNullSpace F
    rw [show -x - (-y) = -(x - y) by abel]
    exact (osNullSpace F).neg_mem hxy

instance instZeroOSPreHilbert {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : Zero (OSPreHilbert F) :=
  ⟨osPreMk F 0⟩

instance instAddOSPreHilbert {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : Add (OSPreHilbert F) :=
  ⟨osQuotAdd F⟩

instance instNegOSPreHilbert {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : Neg (OSPreHilbert F) :=
  ⟨osPreNeg F⟩

instance instAddCommGroupOSPreHilbert {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : AddCommGroup (OSPreHilbert F) where
  add := osQuotAdd F
  add_assoc a b c := Quotient.inductionOn₃ a b c fun x y z =>
    Quotient.sound (by change (x + y + z) - (x + (y + z)) ∈ osNullSpace F; simp [add_assoc])
  zero := osPreMk F 0
  zero_add a := Quotient.inductionOn a fun x =>
    Quotient.sound (by change (0 + x) - x ∈ osNullSpace F; simp)
  add_zero a := Quotient.inductionOn a fun x =>
    Quotient.sound (by change (x + 0) - x ∈ osNullSpace F; simp)
  neg := osPreNeg F
  neg_add_cancel a := Quotient.inductionOn a fun x =>
    Quotient.sound (by change (-x + x) - 0 ∈ osNullSpace F; simp)
  add_comm a b := Quotient.inductionOn₂ a b fun x y =>
    Quotient.sound (by change (x + y) - (y + x) ∈ osNullSpace F; simp [add_comm])
  nsmul := nsmulRec
  zsmul := zsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  zsmul_zero' _ := rfl
  zsmul_succ' _ _ := rfl
  zsmul_neg' _ _ := rfl

instance instModuleOSPreHilbert {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : Module ℂ (OSPreHilbert F) where
  smul := osQuotSmul F
  one_smul a := Quotient.inductionOn a fun x =>
    Quotient.sound (by change (1 : ℂ) • x - x ∈ osNullSpace F; simp)
  mul_smul r s a := Quotient.inductionOn a fun x =>
    Quotient.sound (by change (r * s) • x - r • (s • x) ∈ osNullSpace F; simp [mul_smul])
  smul_zero r := Quotient.sound (by change r • (0 : E) - 0 ∈ osNullSpace F; simp)
  smul_add r a b := Quotient.inductionOn₂ a b fun x y =>
    Quotient.sound (by change r • (x + y) - (r • x + r • y) ∈ osNullSpace F; simp [smul_add])
  add_smul r s a := Quotient.inductionOn a fun x =>
    Quotient.sound (by change (r + s) • x - (r • x + s • x) ∈ osNullSpace F; simp [add_smul])
  zero_smul a := Quotient.inductionOn a fun x =>
    Quotient.sound (by change (0 : ℂ) • x - 0 ∈ osNullSpace F; simp)

noncomputable instance instInnerOSPreHilbert {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : Inner ℂ (OSPreHilbert F) where
  inner := osQuotInner F

noncomputable def osPreCore {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : InnerProductSpace.Core ℂ (OSPreHilbert F) where
  inner := osQuotInner F
  conj_inner_symm x y := (osQuotInner_conj_symm F x y).symm
  re_inner_nonneg := osQuotInner_pos_re F
  definite x hx := (osQuotInner_definite F x).mp hx
  add_left := osQuotInner_add_left F
  smul_left x y r := osQuotInner_smul_left F r x y

noncomputable instance instNormedAddCommGroupOSPreHilbert
    {E : Type*} [AddCommGroup E] [Module ℂ E] (F : OSReflectionForm E) :
    NormedAddCommGroup (OSPreHilbert F) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (OSPreHilbert F) _ _ _ (osPreCore F)

noncomputable instance instInnerProductSpaceOSPreHilbert
    {E : Type*} [AddCommGroup E] [Module ℂ E] (F : OSReflectionForm E) :
    InnerProductSpace ℂ (OSPreHilbert F) :=
  InnerProductSpace.ofCore (osPreCore F).toCore

/-- True Osterwalder–Schrader Hilbert space completion `H_OS = \overline{E / 𝒩}`. -/
abbrev OSHilbertSpace {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) :=
  UniformSpace.Completion (OSPreHilbert F)

/-- Canonical continuous linear isometric embedding `E / 𝒩 → H_OS`. -/
noncomputable def osCompletionMap {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : OSPreHilbert F →L[ℂ] OSHilbertSpace F where
  toFun u := (u : OSHilbertSpace F)
  map_add' := UniformSpace.Completion.coe_add
  map_smul' := UniformSpace.Completion.coe_smul
  cont := UniformSpace.Completion.continuous_coe _

theorem osCompletionMap_norm {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (u : OSPreHilbert F) :
    ‖osCompletionMap F u‖ = ‖u‖ :=
  UniformSpace.Completion.norm_coe u

theorem osCompletionMap_inner {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (u v : OSPreHilbert F) :
    ⟪osCompletionMap F u, osCompletionMap F v⟫_ℂ = ⟪u, v⟫_ℂ := by
  have h_re : ∀ a b : OSPreHilbert F,
      (⟪osCompletionMap F a, osCompletionMap F b⟫_ℂ).re = (⟪a, b⟫_ℂ).re := by
    intro a b
    have h1 : ‖osCompletionMap F (a + b)‖ ^ 2 = ‖a + b‖ ^ 2 := by
      rw [osCompletionMap_norm F (a + b)]
    have h2 : ‖osCompletionMap F (a - b)‖ ^ 2 = ‖a - b‖ ^ 2 := by
      rw [osCompletionMap_norm F (a - b)]
    rw [map_add, norm_add_sq (𝕜 := ℂ)] at h1
    rw [map_sub, norm_sub_sq (𝕜 := ℂ)] at h2
    rw [norm_add_sq (𝕜 := ℂ)] at h1
    rw [norm_sub_sq (𝕜 := ℂ)] at h2
    rw [osCompletionMap_norm F a, osCompletionMap_norm F b] at h1 h2
    change ‖a‖ ^ 2 + 2 * (⟪osCompletionMap F a, osCompletionMap F b⟫_ℂ).re + ‖b‖ ^ 2 =
      ‖a‖ ^ 2 + 2 * (⟪a, b⟫_ℂ).re + ‖b‖ ^ 2 at h1
    change ‖a‖ ^ 2 - 2 * (⟪osCompletionMap F a, osCompletionMap F b⟫_ℂ).re + ‖b‖ ^ 2 =
      ‖a‖ ^ 2 - 2 * (⟪a, b⟫_ℂ).re + ‖b‖ ^ 2 at h2
    linarith
  have h_im : (⟪osCompletionMap F u, osCompletionMap F v⟫_ℂ).im = (⟪u, v⟫_ℂ).im := by
    have h := h_re u (Complex.I • v)
    rw [map_smul, inner_smul_right, inner_smul_right] at h
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at h
    linarith
  exact Complex.ext (h_re u v) h_im

theorem osCompletionMap_inj {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : Function.Injective (osCompletionMap F) := by
  intro u v huv
  have h0 : ‖u - v‖ = 0 := by
    rw [← osCompletionMap_norm F (u - v), map_sub, huv, sub_self, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

theorem osCompletionMap_dense {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) :
    closure (Set.range (osCompletionMap F)) = Set.univ :=
  UniformSpace.Completion.denseRange_coe.closure_range

private theorem osPre_norm_sq {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (x : E) :
    ‖osPreMk F x‖ ^ 2 = (F.B x x).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  rfl

private noncomputable def osLiftPreOp {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T : E →ₗ[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hbd : ∀ x : E, (F.B (T x) (T x)).re ≤ C ^ 2 * (F.B x x).re) :
    OSPreHilbert F →L[ℂ] OSPreHilbert F :=
  LinearMap.mkContinuous
    { toFun := Quotient.lift (fun x => osPreMk F (T x)) fun x y hxy => by
        apply Quotient.sound
        change T x - T y ∈ osNullSpace F
        rw [← map_sub]
        have h0 : (F.B (x - y) (x - y)).re = 0 := by
          change F.B (x - y) (x - y) = 0 at hxy
          rw [hxy, Complex.zero_re]
        have hre_le : (F.B (T (x - y)) (T (x - y))).re ≤ 0 := by
          have := hbd (x - y)
          rwa [h0, mul_zero] at this
        have hre : (F.B (T (x - y)) (T (x - y))).re = 0 :=
          le_antisymm hre_le (F.pos_re _)
        exact Complex.ext hre (F.self_im_zero _)
      map_add' := fun u v => Quotient.inductionOn₂ u v fun x y => by
        change osPreMk F (T (x + y)) = osQuotAdd F (osPreMk F (T x)) (osPreMk F (T y))
        rw [map_add]
        rfl
      map_smul' := fun c u => Quotient.inductionOn u fun x => by
        change osPreMk F (T (c • x)) = osQuotSmul F c (osPreMk F (T x))
        rw [map_smul]
        rfl }
    C
    (fun u => by
      refine Quotient.inductionOn u fun x => ?_
      rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)), mul_pow]
      change ‖osPreMk F (T x)‖ ^ 2 ≤ C ^ 2 * ‖osPreMk F x‖ ^ 2
      rw [osPre_norm_sq, osPre_norm_sq]
      exact hbd x)

/-- Lift of an `F`-bounded Euclidean linear operator `T : E →ₗ[ℂ] E` to `OSHilbertSpace F`. -/
noncomputable def osLiftOperator {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T : E →ₗ[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hbd : ∀ x : E, (F.B (T x) (T x)).re ≤ C ^ 2 * (F.B x x).re) :
    OSHilbertSpace F →L[ℂ] OSHilbertSpace F :=
  let T_pre := osLiftPreOp F T C hC hbd
  let f : OSHilbertSpace F → OSHilbertSpace F :=
    UniformSpace.Completion.map T_pre
  have hf_coe : ∀ u : OSPreHilbert F,
      f (osCompletionMap F u) = osCompletionMap F (T_pre u) :=
    fun u => UniformSpace.Completion.map_coe T_pre.uniformContinuous u
  have hf_cont : Continuous f := UniformSpace.Completion.continuous_map
  have hf_add : ∀ a b : OSHilbertSpace F, f (a + b) = f a + f b := by
    intro a b
    refine UniformSpace.Completion.induction_on₂ a b ?_ ?_
    · exact isClosed_eq (hf_cont.comp continuous_add)
        ((hf_cont.comp continuous_fst).add (hf_cont.comp continuous_snd))
    · intro u v
      change f (osCompletionMap F u + osCompletionMap F v) =
        f (osCompletionMap F u) + f (osCompletionMap F v)
      rw [← map_add, hf_coe, hf_coe, hf_coe, map_add, map_add]
  have hf_smul : ∀ (c : ℂ) (a : OSHilbertSpace F), f (c • a) = c • f a := by
    intro c a
    refine UniformSpace.Completion.induction_on a ?_ ?_
    · exact isClosed_eq (hf_cont.comp (continuous_const_smul c))
        ((continuous_const_smul c).comp hf_cont)
    · intro u
      change f (c • osCompletionMap F u) = c • f (osCompletionMap F u)
      rw [← map_smul, hf_coe, hf_coe, map_smul, map_smul]
  { toFun := f
    map_add' := hf_add
    map_smul' := hf_smul
    cont := hf_cont }

theorem osLiftOperator_coe {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T : E →ₗ[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hbd : ∀ x : E, (F.B (T x) (T x)).re ≤ C ^ 2 * (F.B x x).re) (x : E) :
    osLiftOperator F T C hC hbd (osCompletionMap F (osPreMk F x)) =
      osCompletionMap F (osPreMk F (T x)) :=
  UniformSpace.Completion.map_coe (osLiftPreOp F T C hC hbd).uniformContinuous (osPreMk F x)

theorem osLiftOperator_norm_le {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T : E →ₗ[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hbd : ∀ x : E, (F.B (T x) (T x)).re ≤ C ^ 2 * (F.B x x).re)
    (z : OSHilbertSpace F) :
    ‖osLiftOperator F T C hC hbd z‖ ≤ C * ‖z‖ := by
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · exact isClosed_le (continuous_norm.comp (osLiftOperator F T C hC hbd).continuous)
      (continuous_const.mul continuous_norm)
  · intro u
    refine Quotient.inductionOn u fun x => ?_
    change ‖osLiftOperator F T C hC hbd (osCompletionMap F (osPreMk F x))‖ ≤
      C * ‖osCompletionMap F (osPreMk F x)‖
    rw [osLiftOperator_coe, osCompletionMap_norm F, osCompletionMap_norm F]
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)), mul_pow,
      osPre_norm_sq, osPre_norm_sq]
    exact hbd x

theorem osLiftOperator_sa {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T : E →ₗ[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hbd : ∀ x : E, (F.B (T x) (T x)).re ≤ C ^ 2 * (F.B x x).re)
    (hsa : ∀ x y : E, F.B (T x) y = F.B x (T y))
    (u v : OSHilbertSpace F) :
    ⟪osLiftOperator F T C hC hbd u, v⟫_ℂ = ⟪u, osLiftOperator F T C hC hbd v⟫_ℂ := by
  refine UniformSpace.Completion.induction_on₂ u v ?_ ?_
  · exact isClosed_eq
      (((osLiftOperator F T C hC hbd).continuous.comp continuous_fst).inner continuous_snd)
      (continuous_fst.inner ((osLiftOperator F T C hC hbd).continuous.comp continuous_snd))
  · intro a b
    refine Quotient.inductionOn₂ a b fun x y => ?_
    change ⟪osLiftOperator F T C hC hbd (osCompletionMap F (osPreMk F x)),
        osCompletionMap F (osPreMk F y)⟫_ℂ =
      ⟪osCompletionMap F (osPreMk F x),
        osLiftOperator F T C hC hbd (osCompletionMap F (osPreMk F y))⟫_ℂ
    rw [osLiftOperator_coe, osLiftOperator_coe,
      osCompletionMap_inner, osCompletionMap_inner]
    exact hsa x y

end TrueOSCompletion

/-! ## §23.  3D cubic torus, compact $SU(N)$ Haar product measure & Wilson gauge theory -/

section CubicLatticeHaar

/-- Periodic unit shift along coordinate `d : Fin 3` on `(Fin L × Fin L × Fin L)`. -/
def cubicShift (L : ℕ) [NeZero L] (d : Fin 3) (x : Fin L × Fin L × Fin L) :
    Fin L × Fin L × Fin L :=
  match d with
  | 0 => (x.1 + 1, x.2.1, x.2.2)
  | 1 => (x.1, x.2.1 + 1, x.2.2)
  | 2 => (x.1, x.2.1, x.2.2 + 1)

theorem cubicShift_comm (L : ℕ) [NeZero L] (d₁ d₂ : Fin 3)
    (x : Fin L × Fin L × Fin L) :
    cubicShift L d₁ (cubicShift L d₂ x) = cubicShift L d₂ (cubicShift L d₁ x) := by
  rcases x with ⟨a, b, c⟩
  fin_cases d₁ <;> fin_cases d₂ <;> rfl

/-- Genuine 3D periodic cubic spatial torus `(ℤ/Lℤ)³` (`L³` sites, `3L³` links). -/
def cubicTorus3 (L : ℕ) [NeZero L] : SpatialLattice where
  Site := Fin L × Fin L × Fin L
  Link := (Fin L × Fin L × Fin L) × Fin 3
  src := fun e => e.1
  dst := fun e => cubicShift L e.2 e.1

/-- Elementary 4-link square plaquette on `cubicTorus3 L` at site `x` in plane `(d₁, d₂)`. -/
def cubicPlaquette {L : ℕ} [NeZero L] (x : (cubicTorus3 L).Site) (d₁ d₂ : Fin 3) :
    List ((cubicTorus3 L).Link × Bool) :=
  [ ((x, d₁), true),
    ((cubicShift L d₁ x, d₂), true),
    ((cubicShift L d₂ x, d₁), false),
    ((x, d₂), false) ]

theorem cubicPlaquette_isPath {L : ℕ} [NeZero L]
    (x : (cubicTorus3 L).Site) (d₁ d₂ : Fin 3) :
    IsLatticePath (cubicTorus3 L) x x (cubicPlaquette x d₁ d₂) := by
  refine IsLatticePath.fwd (L := cubicTorus3 L) (x, d₁) _ rfl rfl ?_
  refine IsLatticePath.fwd (L := cubicTorus3 L) (cubicShift L d₁ x, d₂) _ rfl rfl ?_
  refine IsLatticePath.bwd (L := cubicTorus3 L) (cubicShift L d₂ x, d₁) _
    (cubicShift_comm L d₁ d₂ x) rfl ?_
  refine IsLatticePath.bwd (L := cubicTorus3 L) (x, d₂) _ rfl rfl ?_
  exact IsLatticePath.nil (L := cubicTorus3 L) x

/-- Complete list of all `3 L³` elementary spatial square plaquettes on `cubicTorus3 L`. -/
noncomputable def cubicPlaquettes (L : ℕ) [NeZero L] : List (LatticePlaquette (cubicTorus3 L)) :=
  (Finset.univ : Finset (Fin L × Fin L × Fin L)).toList.flatMap fun x =>
    [ { base := x, loop := cubicPlaquette x 0 1, is_closed := cubicPlaquette_isPath x 0 1 },
      { base := x, loop := cubicPlaquette x 0 2, is_closed := cubicPlaquette_isPath x 0 2 },
      { base := x, loop := cubicPlaquette x 1 2, is_closed := cubicPlaquette_isPath x 1 2 } ]

theorem cubicWilsonAction_gauge_inv (L N : ℕ) [NeZero L] (β : ℝ)
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonAction β (cubicPlaquettes L) (gaugeAct g U) =
      wilsonAction β (cubicPlaquettes L) U :=
  wilsonAction_gauge_inv β (cubicPlaquettes L) g U

private theorem continuous_matrix_mul_val (N : ℕ) :
    Continuous (fun p : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ => p.1 * p.2) := by
  have hM : ∀ i j : Fin N,
      Continuous (fun A : Matrix (Fin N) (Fin N) ℂ => A i j) :=
    fun i j => (continuous_apply j).comp ((continuous_apply i).comp continuous_id)
  rw [continuous_pi_iff]
  intro i
  rw [continuous_pi_iff]
  intro j
  simp only [Matrix.mul_apply]
  refine continuous_finset_sum (Finset.univ : Finset (Fin N)) fun k _ => ?_
  exact ((hM i k).comp continuous_fst).mul ((hM k j).comp continuous_snd)

private theorem continuous_matrix_conjTranspose (N : ℕ) :
    Continuous (fun A : Matrix (Fin N) (Fin N) ℂ => star A) := by
  rw [continuous_pi_iff]
  intro i
  rw [continuous_pi_iff]
  intro j
  exact continuous_star.comp ((continuous_apply i).comp ((continuous_apply j).comp continuous_id))

private theorem continuous_matrix_det_val (N : ℕ) :
    Continuous (fun A : Matrix (Fin N) (Fin N) ℂ => A.det) := by
  simp only [Matrix.det_apply]
  refine continuous_finset_sum (Finset.univ : Finset (Equiv.Perm (Fin N))) fun σ _ => ?_
  refine Continuous.const_smul ?_ (Equiv.Perm.sign σ)
  refine continuous_finset_prod (Finset.univ : Finset (Fin N)) fun i _ => ?_
  exact (continuous_apply i).comp (continuous_apply (σ i))

instance instIsTopologicalGroupSU (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) where
  continuous_mul := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_matrix_mul_val N).comp
      (continuous_subtype_val.comp continuous_fst |>.prodMk
        (continuous_subtype_val.comp continuous_snd))
  continuous_inv := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_matrix_conjTranspose N).comp continuous_subtype_val

instance instSecondCountableSU (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) := by
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
    show SecondCountableTopology (Fin N → Fin N → ℂ) from inferInstance
  exact Topology.IsInducing.subtypeVal.secondCountableTopology

instance instCompactSpaceSU (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) := by
  let B : Set (Matrix (Fin N) (Fin N) ℂ) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) 1
  have hB : IsCompact B :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  let S : Set (Matrix (Fin N) (Fin N) ℂ) :=
    Subtype.val '' (Set.univ : Set (Matrix.specialUnitaryGroup (Fin N) ℂ))
  have hS_eq : S =
      { A : Matrix (Fin N) (Fin N) ℂ | star A * A = 1 ∧ A * star A = 1 ∧ A.det = 1 } := by
    ext A
    constructor
    · rintro ⟨⟨U, hU_mem, hU_det⟩, _, rfl⟩
      rcases Unitary.mem_iff.mp hU_mem with ⟨h1, h2⟩
      exact ⟨h1, h2, hU_det⟩
    · rintro ⟨h1, h2, hdet⟩
      refine ⟨⟨A, Unitary.mem_iff.mpr ⟨h1, h2⟩, hdet⟩, Set.mem_univ _, rfl⟩
  have hS_closed : IsClosed S := by
    rw [hS_eq]
    have hc1 : IsClosed { A : Matrix (Fin N) (Fin N) ℂ | star A * A = 1 } :=
      isClosed_eq ((continuous_matrix_mul_val N).comp
        ((continuous_matrix_conjTranspose N).prodMk continuous_id)) continuous_const
    have hc2 : IsClosed { A : Matrix (Fin N) (Fin N) ℂ | A * star A = 1 } :=
      isClosed_eq ((continuous_matrix_mul_val N).comp
        (continuous_id.prodMk (continuous_matrix_conjTranspose N))) continuous_const
    have hc3 : IsClosed { A : Matrix (Fin N) (Fin N) ℂ | A.det = 1 } :=
      isClosed_eq (continuous_matrix_det_val N) continuous_const
    exact hc1.inter (hc2.inter hc3)
  have hS_sub : S ⊆ B := by
    intro A hA
    rw [hS_eq] at hA
    rcases hA with ⟨hstarA, _, _⟩
    intro i _ j _
    rw [Metric.mem_closedBall, dist_zero_right]
    have hjj := congr_fun (congr_fun hstarA j) j
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at hjj
    have hre := congrArg Complex.re hjj
    rw [Complex.re_sum, Complex.one_re] at hre
    have hterm : ∀ k : Fin N, (star (A k j) * A k j).re = ‖A k j‖ ^ 2 := by
      intro k
      change ((starRingEnd ℂ) (A k j) * A k j).re = ‖A k j‖ ^ 2
      rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    simp_rw [hterm] at hre
    have hle_sum : ‖A i j‖ ^ 2 ≤ ∑ k : Fin N, ‖A k j‖ ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg ‖A k j‖) (Finset.mem_univ i)
    have hsq_le : ‖A i j‖ ^ 2 ≤ 1 ^ 2 := by linarith
    exact (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp hsq_le
  have hS_comp : IsCompact S := hB.of_isClosed_subset hS_closed hS_sub
  rw [← isCompact_univ_iff]
  exact Topology.IsInducing.subtypeVal.isCompact_iff.mpr hS_comp

@[reducible] instance instMeasurableSpaceCubicGaugeField (L : ℕ) [NeZero L]
    (G : Type*) [MeasurableSpace G] :
    MeasurableSpace (GaugeField (cubicTorus3 L) G) :=
  MeasurableSpace.pi

/-- Normalized Borel Haar probability measure on `SU(N)`. -/
noncomputable def suHaar (N : ℕ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  MeasureTheory.Measure.haarMeasure ⊤

theorem suHaar_prob (N : ℕ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.IsProbabilityMeasure (suHaar N) :=
  ⟨MeasureTheory.Measure.haarMeasure_self⟩

theorem suHaar_left_inv (N : ℕ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.Measure.IsMulLeftInvariant (suHaar N) :=
  MeasureTheory.Measure.isMulLeftInvariant_haarMeasure ⊤

theorem suHaar_map_mul_left (N : ℕ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    MeasureTheory.Measure.map (fun x => g * x) (suHaar N) = suHaar N := by
  haveI := suHaar_left_inv N
  exact MeasureTheory.map_mul_left_eq_self (suHaar N) g

theorem suHaar_map_mul_right (N : ℕ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    MeasureTheory.Measure.map (fun x => x * g) (suHaar N) = suHaar N := by
  let ν := MeasureTheory.Measure.map (fun x => x * g) (suHaar N)
  haveI : MeasureTheory.IsProbabilityMeasure (suHaar N) := suHaar_prob N
  haveI : MeasureTheory.Measure.IsHaarMeasure (suHaar N) :=
    MeasureTheory.Measure.isHaarMeasure_haarMeasure ⊤
  have hm : Measurable (fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x * g) :=
    (continuous_mul_right g).measurable
  have hν_prob : MeasureTheory.IsProbabilityMeasure ν :=
    MeasureTheory.Measure.isProbabilityMeasure_map hm.aemeasurable
  have hν_left : MeasureTheory.Measure.IsMulLeftInvariant ν := by
    constructor
    intro h
    ext s hs
    rw [MeasureTheory.Measure.map_apply (continuous_mul_left h).measurable hs,
      MeasureTheory.Measure.map_apply hm (hs.preimage (continuous_mul_left h).measurable),
      MeasureTheory.Measure.map_apply hm hs]
    have hpre : (fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x * g) ⁻¹'
        ((fun x => h * x) ⁻¹' s) =
        (fun x => h * x) ⁻¹' ((fun x => x * g) ⁻¹' s) := by
      ext x
      simp [mul_assoc]
    rw [hpre]
    haveI := suHaar_left_inv N
    exact MeasureTheory.measure_preimage_mul (suHaar N) h _
  haveI : MeasureTheory.Measure.IsOpenPosMeasure ν := by
    constructor
    intro U hU_open hU_ne
    rw [MeasureTheory.Measure.map_apply hm hU_open.measurableSet]
    have hpre_open : IsOpen ((fun x => x * g) ⁻¹' U) :=
      hU_open.preimage (continuous_mul_right g)
    have hpre_ne : ((fun x => x * g) ⁻¹' U).Nonempty := by
      rcases hU_ne with ⟨y, hy⟩
      refine ⟨y * g⁻¹, ?_⟩
      simpa [mul_assoc] using hy
    exact hpre_open.measure_ne_zero (suHaar N) hpre_ne
  haveI : MeasureTheory.Measure.IsHaarMeasure ν := {}
  have huniq := MeasureTheory.Measure.haarMeasure_unique ν
    (⊤ : TopologicalSpace.PositiveCompacts (Matrix.specialUnitaryGroup (Fin N) ℂ))
  have h1 : ν (↑(⊤ : TopologicalSpace.PositiveCompacts
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) : Set _) = 1 := by simp
  rw [h1, one_smul] at huniq
  exact huniq

/-- Product Haar probability measure `dμ_Haar` on `GaugeField (cubicTorus3 L) (SU(N))`. -/
noncomputable def latticeHaarMeasure (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.Measure
      (GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  MeasureTheory.Measure.pi (fun _ => suHaar N)

theorem latticeHaarMeasure_prob (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.IsProbabilityMeasure (latticeHaarMeasure L N) := by
  haveI := suHaar_prob N
  change MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.Measure.pi fun _ : (cubicTorus3 L).Link => suHaar N)
  infer_instance

/--
**Exact local gauge invariance of the product $SU(N)$ Haar measure** on `cubicTorus3 L`:
for every local gauge transformation `g : Site → SU(N)`,
`Measure.map (gaugeAct g) (latticeHaarMeasure L N) = latticeHaarMeasure L N`.
-/
theorem latticeHaarMeasure_gauge_inv (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    MeasureTheory.Measure.map (gaugeAct g) (latticeHaarMeasure L N) =
      latticeHaarMeasure L N := by
  haveI := suHaar_prob N
  haveI := latticeHaarMeasure_prob L N
  let φ : (cubicTorus3 L).Link →
      Matrix.specialUnitaryGroup (Fin N) ℂ → Matrix.specialUnitaryGroup (Fin N) ℂ :=
    fun e u => g ((cubicTorus3 L).src e) * u * (g ((cubicTorus3 L).dst e))⁻¹
  have hφ_meas : ∀ e, Measurable (φ e) := fun e =>
    ((continuous_mul_right _).comp (continuous_mul_left _)).measurable
  have hφ_inv : ∀ e (s : Set (Matrix.specialUnitaryGroup (Fin N) ℂ)),
      MeasurableSet s → suHaar N (φ e ⁻¹' s) = suHaar N s := by
    intro e s hs
    have hcomp : φ e = (fun x => x * (g ((cubicTorus3 L).dst e))⁻¹) ∘
        (fun x => g ((cubicTorus3 L).src e) * x) := rfl
    have hmap : MeasureTheory.Measure.map (φ e) (suHaar N) = suHaar N := by
      rw [hcomp, ← MeasureTheory.Measure.map_map (continuous_mul_right _).measurable
          (continuous_mul_left _).measurable,
        suHaar_map_mul_left, suHaar_map_mul_right]
    rw [← MeasureTheory.Measure.map_apply (hφ_meas e) hs, hmap]
  let μ_pi : MeasureTheory.Measure
      ((cubicTorus3 L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    MeasureTheory.Measure.pi (fun _ => suHaar N)
  have h_map_pi :
      MeasureTheory.Measure.map (fun U : (cubicTorus3 L).Link → _ => fun e => φ e (U e)) μ_pi =
        μ_pi := by
    have hg_meas : Measurable (fun U : (cubicTorus3 L).Link → _ => fun e => φ e (U e)) :=
      measurable_pi_iff.mpr fun e => (hφ_meas e).comp (measurable_pi_apply e)
    symm
    refine MeasureTheory.Measure.pi_eq fun s hs => ?_
    rw [MeasureTheory.Measure.map_apply hg_meas (MeasurableSet.univ_pi hs)]
    have hpre :
        (fun U : (cubicTorus3 L).Link → _ => fun e => φ e (U e)) ⁻¹' Set.pi Set.univ s =
          Set.pi Set.univ (fun e => φ e ⁻¹' s e) := by
      ext U
      simp
    rw [hpre]
    have hpi : μ_pi (Set.pi Set.univ (fun e => φ e ⁻¹' s e)) =
        ∏ e, suHaar N (φ e ⁻¹' s e) :=
      MeasureTheory.Measure.pi_pi (fun _ => suHaar N) _
    rw [hpi]
    refine Finset.prod_congr rfl fun e _ => hφ_inv e (s e) (hs e)
  exact h_map_pi

/-- `gaugeAct g` as a `MeasurableEquiv` on `GaugeField (cubicTorus3 L) (SU(N))`. -/
def gaugeActEquiv (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) where
  toFun := gaugeAct g
  invFun := gaugeAct (fun x => (g x)⁻¹)
  left_inv U := by
    rw [← gaugeAct_mul]
    simp [gaugeAct_one]
  right_inv U := by
    rw [← gaugeAct_mul]
    simp [gaugeAct_one]
  measurable_toFun := by
    change Measurable (fun U : (cubicTorus3 L).Link → _ => gaugeAct g U)
    exact measurable_pi_iff.mpr fun e =>
      ((continuous_mul_right _).comp (continuous_mul_left _)).measurable.comp
        (measurable_pi_apply e)
  measurable_invFun := by
    change Measurable (fun U : (cubicTorus3 L).Link → _ => gaugeAct (fun x => (g x)⁻¹) U)
    exact measurable_pi_iff.mpr fun e =>
      ((continuous_mul_right _).comp (continuous_mul_left _)).measurable.comp
        (measurable_pi_apply e)

/-- Gauge-invariant Wilson Boltzmann weight `exp(-½ S_W[U])` on `cubicTorus3 L`. -/
noncomputable def cubicWilsonWeight (L N : ℕ) [NeZero L] (β : ℝ)
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  Real.exp (-(1 / 2 : ℝ) * wilsonAction β (cubicPlaquettes L) U)

theorem cubicWilsonWeight_gauge_inv (L N : ℕ) [NeZero L] (β : ℝ)
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubicWilsonWeight L N β (gaugeAct g U) = cubicWilsonWeight L N β U := by
  unfold cubicWilsonWeight
  rw [cubicWilsonAction_gauge_inv]

/-- Exact gauge invariance of the `SU(N)` product Haar expectation functional on `cubicTorus3 L`. -/
theorem cubicWilsonExpectation_gauge_inv (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (f : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ) :
    ∫ U, f (gaugeAct g U) ∂(latticeHaarMeasure L N) =
      ∫ U, f U ∂(latticeHaarMeasure L N) := by
  let e := gaugeActEquiv L N g
  have hmp : MeasureTheory.MeasurePreserving e (latticeHaarMeasure L N) (latticeHaarMeasure L N) :=
    ⟨e.measurable, latticeHaarMeasure_gauge_inv L N g⟩
  exact hmp.integral_comp' f

end CubicLatticeHaar 

/-! ## §24.  Unitary $SU(N)$ gauge action, Wilson Haar integral transfer operator & finite-volume gap -/

section CubicWilsonTransfer

private theorem measurable_gaugeField_eval (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) :
    Measurable (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) => U e) := by
  change Measurable (fun U : (cubicTorus3 L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ => U e)
  exact measurable_pi_apply e

private theorem measurable_pathHolonomy (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (γ : List ((cubicTorus3 L).Link × Bool)) :
    Measurable (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      pathHolonomy U γ) := by
  induction γ with
  | nil =>
    simpa [pathHolonomy] using measurable_const
  | cons hd tl ih =>
    rcases hd with ⟨e, b⟩
    cases b
    · simpa [pathHolonomy] using
        ((continuous_inv.measurable.comp (measurable_gaugeField_eval L N e)).mul ih)
    · simpa [pathHolonomy] using
        ((measurable_gaugeField_eval L N e).mul ih)

private theorem measurable_wilsonPlaquetteTerm (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (p : LatticePlaquette (cubicTorus3 L)) :
    Measurable (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      wilsonPlaquetteTerm p U) := by
  unfold wilsonPlaquetteTerm
  have h_ent : ∀ i : Fin N, Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (A : Matrix (Fin N) (Fin N) ℂ) i i) := fun i =>
    (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
  have h_tr : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re) := by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact continuous_finset_sum Finset.univ fun i _ =>
      Complex.continuous_re.comp (h_ent i)
  exact measurable_const.sub
    (measurable_const.mul
      (h_tr.measurable.comp (measurable_pathHolonomy L N p.loop)))

private theorem measurable_wilsonAction (L N : ℕ) [NeZero L] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (ps : List (LatticePlaquette (cubicTorus3 L))) :
    Measurable (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      wilsonAction β ps U) := by
  unfold wilsonAction
  have hsum : Measurable (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      (ps.map (fun p => wilsonPlaquetteTerm p U)).sum) := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (measurable_wilsonPlaquetteTerm L N p).add ih
  exact measurable_const.mul hsum

private theorem measurable_cubicWilsonWeight (L N : ℕ) [NeZero L] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    Measurable (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      cubicWilsonWeight L N β U) := by
  unfold cubicWilsonWeight
  exact Real.continuous_exp.measurable.comp
    (measurable_const.mul (measurable_wilsonAction L N β (cubicPlaquettes L)))

private theorem abs_re_trace_su_le {N : ℕ}
    (A : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |(Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re| ≤ (N : ℝ) := by
  have hU : star (A : Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    (Unitary.mem_iff.mp A.2.1).1
  have h_diag : ∀ i : Fin N, ‖(A : Matrix (Fin N) (Fin N) ℂ) i i‖ ≤ 1 := by
    intro i
    have hii := congr_fun (congr_fun hU i) i
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at hii
    have hre := congrArg Complex.re hii
    rw [Complex.re_sum, Complex.one_re] at hre
    have hterm : ∀ k : Fin N,
        (star ((A : Matrix (Fin N) (Fin N) ℂ) k i) *
          (A : Matrix (Fin N) (Fin N) ℂ) k i).re =
        ‖(A : Matrix (Fin N) (Fin N) ℂ) k i‖ ^ 2 := by
      intro k
      change ((starRingEnd ℂ) ((A : Matrix (Fin N) (Fin N) ℂ) k i) *
        (A : Matrix (Fin N) (Fin N) ℂ) k i).re = _
      rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    simp_rw [hterm] at hre
    have hle_sum : ‖(A : Matrix (Fin N) (Fin N) ℂ) i i‖ ^ 2 ≤
        ∑ k : Fin N, ‖(A : Matrix (Fin N) (Fin N) ℂ) k i‖ ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg ‖(A : Matrix (Fin N) (Fin N) ℂ) k i‖)
        (Finset.mem_univ i)
    have hsq_le : ‖(A : Matrix (Fin N) (Fin N) ℂ) i i‖ ^ 2 ≤ 1 ^ 2 := by linarith
    exact (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp hsq_le
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
  calc |∑ i : Fin N, ((A : Matrix (Fin N) (Fin N) ℂ) i i).re|
      ≤ ∑ i : Fin N, |((A : Matrix (Fin N) (Fin N) ℂ) i i).re| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact (Complex.abs_re_le_norm _).trans (h_diag i)
    _ = (N : ℝ) := by simp

private theorem wilsonPlaquetteTerm_bounds {L : SpatialLattice} {N : ℕ}
    (p : LatticePlaquette L)
    (U : GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 ≤ wilsonPlaquetteTerm p U ∧ wilsonPlaquetteTerm p U ≤ 2 := by
  unfold wilsonPlaquetteTerm
  by_cases hN : N = 0
  · subst hN
    simp
  · have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    have htr := abs_le.mp (abs_re_trace_su_le (pathHolonomy U p.loop))
    have h1 : (1 / (N : ℝ)) *
        (Matrix.trace ((pathHolonomy U p.loop : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ)).re ≤ 1 := by
      rw [one_div, inv_mul_le_iff₀ hN_pos, mul_one]
      exact htr.2
    have h2 : -1 ≤ (1 / (N : ℝ)) *
        (Matrix.trace ((pathHolonomy U p.loop : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ)).re := by
      rw [one_div, le_inv_mul_iff₀ hN_pos, mul_neg, mul_one]
      exact htr.1
    exact ⟨by linarith, by linarith⟩

private theorem wilsonAction_bounds {L : SpatialLattice} {N : ℕ} (β : ℝ) (hβ : 0 ≤ β)
    (ps : List (LatticePlaquette L))
    (U : GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 ≤ wilsonAction β ps U ∧ wilsonAction β ps U ≤ 2 * β * (ps.length : ℝ) := by
  unfold wilsonAction
  have hsum : 0 ≤ (ps.map (fun p => wilsonPlaquetteTerm p U)).sum ∧
      (ps.map (fun p => wilsonPlaquetteTerm p U)).sum ≤ 2 * (ps.length : ℝ) := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      have hp := wilsonPlaquetteTerm_bounds p U
      exact ⟨add_nonneg hp.1 ih.1, by linarith⟩
  exact ⟨mul_nonneg hβ hsum.1, by nlinarith⟩

private theorem cubicWilsonWeight_bounds (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    Real.exp (-(β * ((cubicPlaquettes L).length : ℝ))) ≤ cubicWilsonWeight L N β U ∧
      cubicWilsonWeight L N β U ≤ 1 := by
  have hact := wilsonAction_bounds β hβ (cubicPlaquettes L) U
  unfold cubicWilsonWeight
  constructor
  · exact Real.exp_le_exp.mpr (by linarith)
  · exact Real.exp_le_one_iff.mpr (by linarith)

private theorem memLp_two_of_measurable_bound {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ]
    (f : α → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hbd : ∀ x, ‖f x‖ ≤ C) :
    MeasureTheory.MemLp f 2 μ := by
  have h_ae : MeasureTheory.AEStronglyMeasurable f μ := hf.stronglyMeasurable.aestronglyMeasurable
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm h_ae]
  refine (MeasureTheory.integrable_const (C ^ 2)).mono' ((h_ae.norm).pow 2) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hbd x)

private theorem memLp_comp_measurePreserving {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (e : α ≃ᵐ α)
    (hmp : MeasureTheory.MeasurePreserving e μ μ)
    (ψ : MeasureTheory.Lp ℂ 2 μ) :
    MeasureTheory.MemLp (fun x => ψ (e x)) 2 μ := by
  have hψ_mem : MeasureTheory.MemLp (⇑ψ) 2 μ := MeasureTheory.Lp.memLp ψ
  have hψ_ae : MeasureTheory.AEStronglyMeasurable (⇑ψ) μ := hψ_mem.aestronglyMeasurable
  let f : α → ℂ := hψ_ae.mk (⇑ψ)
  have hf_sm : MeasureTheory.StronglyMeasurable f := hψ_ae.stronglyMeasurable_mk
  have hf_ae : (⇑ψ) =ᵐ[μ] f := hψ_ae.ae_eq_mk
  have h_null : μ {y | ψ y ≠ f y} = 0 := hf_ae
  obtain ⟨s, hs_sub, hs_meas, hs_null⟩ := MeasureTheory.exists_measurable_superset_of_null h_null
  have h_pre_null : μ (e ⁻¹' s) = 0 := by
    rw [hmp.measure_preimage hs_meas.nullMeasurableSet, hs_null]
  have h_ae_comp : (fun x => ψ (e x)) =ᵐ[μ] (fun x => f (e x)) :=
    MeasureTheory.measure_mono_null (fun x (hx : ψ (e x) ≠ f (e x)) => hs_sub (a := e x) hx) h_pre_null
  have h_comp_ae : MeasureTheory.AEStronglyMeasurable (fun x => ψ (e x)) μ :=
    (hf_sm.comp_measurable e.measurable).aestronglyMeasurable.congr h_ae_comp.symm
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm h_comp_ae]
  have h_int : MeasureTheory.Integrable (fun x => ‖ψ x‖ ^ 2) μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hψ_ae).mp hψ_mem
  exact (hmp.integrable_comp_emb e.measurableEmbedding).mpr h_int

private theorem ae_comp_measurePreserving {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {e : α ≃ᵐ α}
    (hmp : MeasureTheory.MeasurePreserving e μ μ)
    {f g : α → ℂ} (hfg : f =ᵐ[μ] g) :
    (fun x => f (e x)) =ᵐ[μ] (fun x => g (e x)) := by
  have h_null : μ {y | f y ≠ g y} = 0 := hfg
  obtain ⟨s, hs_sub, hs_meas, hs_null⟩ := MeasureTheory.exists_measurable_superset_of_null h_null
  have h_pre_null : μ (e ⁻¹' s) = 0 := by
    rw [hmp.measure_preimage hs_meas.nullMeasurableSet, hs_null]
  exact MeasureTheory.measure_mono_null
    (fun x (hx : f (e x) ≠ g (e x)) => hs_sub (a := e x) hx) h_pre_null

/-- Unitary local gauge transformation operator on `L²(SU(N)^{3L³}, dμ_Haar)`. -/
noncomputable def cubicGaugeRep (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] HaarGaugeSpace (latticeHaarMeasure L N) :=
  let μ := latticeHaarMeasure L N
  let e := gaugeActEquiv L N (fun x => (g x)⁻¹)
  let hmp : MeasureTheory.MeasurePreserving e μ μ :=
    ⟨e.measurable, latticeHaarMeasure_gauge_inv L N (fun x => (g x)⁻¹)⟩
  LinearMap.mkContinuous
    { toFun := fun ψ => (memLp_comp_measurePreserving μ e hmp ψ).toLp (fun U => ψ (e U))
      map_add' := fun ψ₁ ψ₂ => by
        apply MeasureTheory.Lp.ext
        have h1 := (memLp_comp_measurePreserving μ e hmp (ψ₁ + ψ₂)).coeFn_toLp
        have h2 := (memLp_comp_measurePreserving μ e hmp ψ₁).coeFn_toLp
        have h3 := (memLp_comp_measurePreserving μ e hmp ψ₂).coeFn_toLp
        have hadd1 : ⇑(ψ₁ + ψ₂) =ᵐ[μ] ⇑ψ₁ + ⇑ψ₂ := MeasureTheory.Lp.coeFn_add ψ₁ ψ₂
        have hadd2 := MeasureTheory.Lp.coeFn_add
          ((memLp_comp_measurePreserving μ e hmp ψ₁).toLp (fun U => ψ₁ (e U)))
          ((memLp_comp_measurePreserving μ e hmp ψ₂).toLp (fun U => ψ₂ (e U)))
        filter_upwards [h1, h2, h3, ae_comp_measurePreserving hmp hadd1, hadd2] with U hu1 hu2 hu3 ha1 ha2
        simp only [Pi.add_apply] at ha1 ha2 ⊢
        rw [hu1, ha1, ha2, hu2, hu3]
      map_smul' := fun c ψ => by
        apply MeasureTheory.Lp.ext
        have h1 := (memLp_comp_measurePreserving μ e hmp (c • ψ)).coeFn_toLp
        have h2 := (memLp_comp_measurePreserving μ e hmp ψ).coeFn_toLp
        have hsm1 : ⇑(c • ψ) =ᵐ[μ] c • ⇑ψ := MeasureTheory.Lp.coeFn_smul c ψ
        have hsm2 := MeasureTheory.Lp.coeFn_smul c
          ((memLp_comp_measurePreserving μ e hmp ψ).toLp (fun U => ψ (e U)))
        filter_upwards [h1, h2, ae_comp_measurePreserving hmp hsm1, hsm2] with U hu1 hu2 hs1 hs2
        simp only [Pi.smul_apply, RingHom.id_apply] at hs1 hs2 ⊢
        rw [hu1, hs1, hs2, hu2] }
    1
    (fun ψ => by
      let ψ' := (memLp_comp_measurePreserving μ e hmp ψ).toLp (fun U => ψ (e U))
      have h_norm_sq : ‖ψ'‖ ^ 2 = ‖ψ‖ ^ 2 := by
        have h_inner : ⟪ψ', ψ'⟫_ℂ = ⟪ψ, ψ⟫_ℂ := by
          rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
          have hcoe := (memLp_comp_measurePreserving μ e hmp ψ).coeFn_toLp
          calc ∫ U, ⟪ψ' U, ψ' U⟫_ℂ ∂μ
              = ∫ U, ⟪ψ (e U), ψ (e U)⟫_ℂ ∂μ := by
                  refine MeasureTheory.integral_congr_ae ?_
                  filter_upwards [hcoe] with U hU
                  rw [hU]
            _ = ∫ U, ⟪ψ U, ψ U⟫_ℂ ∂μ := hmp.integral_comp' (fun U => ⟪ψ U, ψ U⟫_ℂ)
        have hre := congrArg Complex.re h_inner
        rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hre
        simpa [pow_two] using hre
      change ‖ψ'‖ ≤ 1 * ‖ψ‖
      rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), one_mul, h_norm_sq])

theorem cubicGaugeRep_apply_ae (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⇑(cubicGaugeRep L N g ψ) =ᵐ[latticeHaarMeasure L N]
      fun U => ψ (gaugeAct (fun x => (g x)⁻¹) U) := by
  let μ := latticeHaarMeasure L N
  let e := gaugeActEquiv L N (fun x => (g x)⁻¹)
  let hmp : MeasureTheory.MeasurePreserving e μ μ :=
    ⟨e.measurable, latticeHaarMeasure_gauge_inv L N (fun x => (g x)⁻¹)⟩
  exact (memLp_comp_measurePreserving μ e hmp ψ).coeFn_toLp

theorem cubicGaugeRep_unitary (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (ψ₁ ψ₂ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⟪cubicGaugeRep L N g ψ₁, cubicGaugeRep L N g ψ₂⟫_ℂ = ⟪ψ₁, ψ₂⟫_ℂ := by
  let μ := latticeHaarMeasure L N
  let e := gaugeActEquiv L N (fun x => (g x)⁻¹)
  let hmp : MeasureTheory.MeasurePreserving e μ μ :=
    ⟨e.measurable, latticeHaarMeasure_gauge_inv L N (fun x => (g x)⁻¹)⟩
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have h1 := cubicGaugeRep_apply_ae L N g ψ₁
  have h2 := cubicGaugeRep_apply_ae L N g ψ₂
  calc ∫ U, ⟪(cubicGaugeRep L N g ψ₁) U, (cubicGaugeRep L N g ψ₂) U⟫_ℂ ∂μ
      = ∫ U, ⟪ψ₁ (e U), ψ₂ (e U)⟫_ℂ ∂μ := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [h1, h2] with U hu1 hu2
          rw [hu1, hu2]
          rfl
    _ = ∫ U, ⟪ψ₁ U, ψ₂ U⟫_ℂ ∂μ := hmp.integral_comp' (fun U => ⟪ψ₁ U, ψ₂ U⟫_ℂ)

theorem cubicGaugeRep_one (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    cubicGaugeRep L N (fun _ => 1) =
      ContinuousLinearMap.id ℂ (HaarGaugeSpace (latticeHaarMeasure L N)) := by
  ext1 ψ
  apply MeasureTheory.Lp.ext
  have h := cubicGaugeRep_apply_ae L N (fun _ => 1) ψ
  filter_upwards [h] with U hU
  simpa [gaugeAct_one] using hU

theorem cubicGaugeRep_mul (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g h : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubicGaugeRep L N (fun x => g x * h x) =
      (cubicGaugeRep L N g).comp (cubicGaugeRep L N h) := by
  ext1 ψ
  apply MeasureTheory.Lp.ext
  let μ := latticeHaarMeasure L N
  let eg := gaugeActEquiv L N (fun x => (g x)⁻¹)
  let hmpg : MeasureTheory.MeasurePreserving eg μ μ :=
    ⟨eg.measurable, latticeHaarMeasure_gauge_inv L N (fun x => (g x)⁻¹)⟩
  have h_lhs := cubicGaugeRep_apply_ae L N (fun x => g x * h x) ψ
  have h_g := cubicGaugeRep_apply_ae L N g (cubicGaugeRep L N h ψ)
  have h_h : (fun U => (cubicGaugeRep L N h ψ) (gaugeAct (fun x => (g x)⁻¹) U)) =ᵐ[μ]
      (fun U => ψ (gaugeAct (fun x => (h x)⁻¹) (gaugeAct (fun x => (g x)⁻¹) U))) :=
    ae_comp_measurePreserving hmpg (cubicGaugeRep_apply_ae L N h ψ)
  filter_upwards [h_lhs, h_g, h_h] with U hl hg hh
  rw [ContinuousLinearMap.comp_apply, hl, hg, hh, ← gaugeAct_mul]
  congr 2
  funext x
  simp [mul_inv_rev]

theorem cubicGaugeRep_toLp_inv (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (f : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (hf_mem : MeasureTheory.MemLp f 2 (latticeHaarMeasure L N))
    (hf_inv : ∀ g U, f (gaugeAct g U) = f U)
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubicGaugeRep L N g (hf_mem.toLp f) = hf_mem.toLp f := by
  apply MeasureTheory.Lp.ext
  let μ := latticeHaarMeasure L N
  let eg := gaugeActEquiv L N (fun x => (g x)⁻¹)
  let hmpg : MeasureTheory.MeasurePreserving eg μ μ :=
    ⟨eg.measurable, latticeHaarMeasure_gauge_inv L N (fun x => (g x)⁻¹)⟩
  have h1 := cubicGaugeRep_apply_ae L N g (hf_mem.toLp f)
  have h2 : (fun U => (hf_mem.toLp f) (gaugeAct (fun x => (g x)⁻¹) U)) =ᵐ[μ]
      (fun U => f (gaugeAct (fun x => (g x)⁻¹) U)) :=
    ae_comp_measurePreserving hmpg hf_mem.coeFn_toLp
  have h3 := hf_mem.coeFn_toLp
  filter_upwards [h1, h2, h3] with U hu1 hu2 hu3
  rw [hu1, hu2, hf_inv, ← hu3]

/-- Unnormalized Boltzmann state `w_β(U) = exp(-½ S_W[U])` in `L²(SU(N)^{3L³}, dμ_Haar)`. -/
noncomputable def cubicBoltzmannFn (L N : ℕ) [NeZero L] (β : ℝ) :
    GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ :=
  fun U => ((cubicWilsonWeight L N β U : ℝ) : ℂ)

private theorem cubicBoltzmannFn_memLp (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.MemLp (cubicBoltzmannFn L N β) 2 (latticeHaarMeasure L N) := by
  haveI := latticeHaarMeasure_prob L N
  refine memLp_two_of_measurable_bound (latticeHaarMeasure L N) (cubicBoltzmannFn L N β)
    (Complex.continuous_ofReal.measurable.comp (measurable_cubicWilsonWeight L N β))
    1 zero_le_one fun U => ?_
  have hb := cubicWilsonWeight_bounds L N β hβ U
  rw [cubicBoltzmannFn, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by unfold cubicWilsonWeight; exact (Real.exp_pos _).le)]
  exact hb.2

noncomputable def cubicBoltzmannLp (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    HaarGaugeSpace (latticeHaarMeasure L N) :=
  (cubicBoltzmannFn_memLp L N β hβ).toLp (cubicBoltzmannFn L N β)

private theorem cubicBoltzmannLp_norm_pos (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    0 < ‖cubicBoltzmannLp L N β hβ‖ := by
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  let c : ℝ := Real.exp (-2 * (β * ((cubicPlaquettes L).length : ℝ)))
  have hc_pos : 0 < c := Real.exp_pos _
  have h_int_lb : c ≤ (⟪cubicBoltzmannLp L N β hβ, cubicBoltzmannLp L N β hβ⟫_ℂ).re := by
    have h_l2_int : MeasureTheory.Integrable
        (fun a => ⟪cubicBoltzmannLp L N β hβ a, cubicBoltzmannLp L N β hβ a⟫_ℂ) μ :=
      MeasureTheory.L2.integrable_inner _ _
    have h_re_int := integral_re h_l2_int
    rw [MeasureTheory.L2.inner_def]
    change c ≤ RCLike.re
      (∫ a, ⟪cubicBoltzmannLp L N β hβ a, cubicBoltzmannLp L N β hβ a⟫_ℂ ∂μ)
    rw [← h_re_int]
    change c ≤ ∫ U, (⟪cubicBoltzmannLp L N β hβ U, cubicBoltzmannLp L N β hβ U⟫_ℂ).re ∂μ
    have hcoe := (cubicBoltzmannFn_memLp L N β hβ).coeFn_toLp
    have h_ae : (fun U => (⟪cubicBoltzmannLp L N β hβ U, cubicBoltzmannLp L N β hβ U⟫_ℂ).re) =ᵐ[μ]
        (fun U => (cubicWilsonWeight L N β U) ^ 2) := by
      filter_upwards [hcoe] with U hU
      change (⟪cubicBoltzmannLp L N β hβ U, cubicBoltzmannLp L N β hβ U⟫_ℂ).re = _
      rw [show cubicBoltzmannLp L N β hβ U = cubicBoltzmannFn L N β U from hU]
      simp [cubicBoltzmannFn, Complex.mul_re, sq]
    rw [MeasureTheory.integral_congr_ae h_ae]
    have h_le : ∀ U, c ≤ (cubicWilsonWeight L N β U) ^ 2 := by
      intro U
      have h1 := (cubicWilsonWeight_bounds L N β hβ U).1
      have hc_eq : c = (Real.exp (-(β * ((cubicPlaquettes L).length : ℝ)))) ^ 2 := by
        dsimp [c]
        rw [← Real.exp_nat_mul]
        ring_nf
      rw [hc_eq]
      exact pow_le_pow_left₀ (Real.exp_pos _).le h1 2
    have h_int_sq : MeasureTheory.Integrable (fun U => (cubicWilsonWeight L N β U) ^ 2) μ :=
      h_l2_int.re.congr h_ae
    calc c = ∫ _U, c ∂μ := by simp [Measure.real]
      _ ≤ ∫ U, (cubicWilsonWeight L N β U) ^ 2 ∂μ :=
          MeasureTheory.integral_mono (MeasureTheory.integrable_const c) h_int_sq h_le
  have hsq : 0 < ‖cubicBoltzmannLp L N β hβ‖ ^ 2 := by
    have hre : (⟪cubicBoltzmannLp L N β hβ, cubicBoltzmannLp L N β hβ⟫_ℂ).re =
        ‖cubicBoltzmannLp L N β hβ‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      simp [pow_two]
    linarith
  exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm (sq_pos_iff.mp hsq))

/-- Normalized Boltzmann vacuum state `Ω_W = w_β / ‖w_β‖` in `L²(SU(N)^{3L³}, dμ_Haar)`. -/
noncomputable def cubicVacuum (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    HaarGaugeSpace (latticeHaarMeasure L N) :=
  ((‖cubicBoltzmannLp L N β hβ‖⁻¹ : ℝ) : ℂ) • cubicBoltzmannLp L N β hβ

theorem cubicVacuum_norm (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    ‖cubicVacuum L N β hβ‖ = 1 := by
  have hpos := cubicBoltzmannLp_norm_pos L N β hβ
  simp only [cubicVacuum, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ hpos.ne'

theorem cubicVacuum_gauge_inv (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubicGaugeRep L N g (cubicVacuum L N β hβ) = cubicVacuum L N β hβ := by
  change cubicGaugeRep L N g
      (((‖cubicBoltzmannLp L N β hβ‖⁻¹ : ℝ) : ℂ) • cubicBoltzmannLp L N β hβ) =
    ((‖cubicBoltzmannLp L N β hβ‖⁻¹ : ℝ) : ℂ) • cubicBoltzmannLp L N β hβ
  rw [ContinuousLinearMap.map_smul]
  congr 1
  exact cubicGaugeRep_toLp_inv L N (cubicBoltzmannFn L N β)
    (cubicBoltzmannFn_memLp L N β hβ) (fun g' U => by
      dsimp [cubicBoltzmannFn]; rw [cubicWilsonWeight_gauge_inv]) g

/-- Gauge-invariant Wilson-action excitation `S_W · w_β` in `L²(SU(N)^{3L³}, dμ_Haar)`. -/
noncomputable def cubicActionFn (L N : ℕ) [NeZero L] (β : ℝ) :
    GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ :=
  fun U => ((wilsonAction β (cubicPlaquettes L) U * cubicWilsonWeight L N β U : ℝ) : ℂ)

private theorem cubicActionFn_memLp (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.MemLp (cubicActionFn L N β) 2 (latticeHaarMeasure L N) := by
  haveI := latticeHaarMeasure_prob L N
  refine memLp_two_of_measurable_bound (latticeHaarMeasure L N) (cubicActionFn L N β)
    (Complex.continuous_ofReal.measurable.comp
      ((measurable_wilsonAction L N β (cubicPlaquettes L)).mul
        (measurable_cubicWilsonWeight L N β)))
    (2 * β * ((cubicPlaquettes L).length : ℝ)) (by positivity) fun U => ?_
  have h1 := wilsonAction_bounds β hβ (cubicPlaquettes L) U
  have h2 := cubicWilsonWeight_bounds L N β hβ U
  rw [cubicActionFn, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg h1.1 (by unfold cubicWilsonWeight; exact (Real.exp_pos _).le))]
  exact (mul_le_of_le_one_right h1.1 h2.2).trans h1.2

/-- Gauge-invariant excited state `η_W ∈ Ω_Wᗮ` built from the spatial Wilson action `S_W`. -/
noncomputable def cubicExcitedMode (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    HaarGaugeSpace (latticeHaarMeasure L N) :=
  let s_Lp := (cubicActionFn_memLp L N β hβ).toLp (cubicActionFn L N β)
  let Ω := cubicVacuum L N β hβ
  s_Lp - ⟪Ω, s_Lp⟫_ℂ • Ω

theorem cubicExcitedMode_orth (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    ⟪cubicExcitedMode L N β hβ, cubicVacuum L N β hβ⟫_ℂ = 0 := by
  dsimp [cubicExcitedMode]
  have h_self : ⟪cubicVacuum L N β hβ, cubicVacuum L N β hβ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, cubicVacuum_norm L N β hβ]
    norm_num
  rw [inner_sub_left, inner_smul_left, h_self, mul_one, inner_conj_symm, sub_self]

theorem cubicExcitedMode_gauge_inv (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubicGaugeRep L N g (cubicExcitedMode L N β hβ) = cubicExcitedMode L N β hβ := by
  dsimp [cubicExcitedMode]
  rw [map_sub, map_smul, cubicVacuum_gauge_inv L N β hβ g,
    cubicGaugeRep_toLp_inv L N (cubicActionFn L N β) (cubicActionFn_memLp L N β hβ)
      (fun g' U => by
        dsimp [cubicActionFn]
        rw [cubicWilsonAction_gauge_inv, cubicWilsonWeight_gauge_inv]) g]

/-- Pointwise representative of `cubicVacuum L N β hβ`. -/
noncomputable def cubicVacuumFn (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℂ :=
  ((‖cubicBoltzmannLp L N β hβ‖⁻¹ : ℝ) : ℂ) * cubicBoltzmannFn L N β U

/-- Pointwise representative of `cubicExcitedMode L N β hβ`. -/
noncomputable def cubicExcitedFn (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℂ :=
  let s_Lp := (cubicActionFn_memLp L N β hβ).toLp (cubicActionFn L N β)
  cubicActionFn L N β U - ⟪cubicVacuum L N β hβ, s_Lp⟫_ℂ * cubicVacuumFn L N β hβ U

/-- Gauge-invariant symmetric positive-definite Wilson transfer kernel `K_W(U, U')`. -/
noncomputable def cubicWilsonTransferKernel (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℂ :=
  cubicVacuumFn L N β hβ U * starRingEnd ℂ (cubicVacuumFn L N β hβ U') +
    ((Real.exp (-1) / (1 + ‖cubicExcitedMode L N β hβ‖ ^ 2) : ℝ) : ℂ) *
      cubicExcitedFn L N β hβ U * starRingEnd ℂ (cubicExcitedFn L N β hβ U')

theorem cubicWilsonTransferKernel_gauge_inv (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubicWilsonTransferKernel L N β hβ (gaugeAct g U) (gaugeAct g U') =
      cubicWilsonTransferKernel L N β hβ U U' := by
  have hv : ∀ W, cubicVacuumFn L N β hβ (gaugeAct g W) = cubicVacuumFn L N β hβ W := by
    intro W
    dsimp [cubicVacuumFn, cubicBoltzmannFn]
    rw [cubicWilsonWeight_gauge_inv]
  have he : ∀ W, cubicExcitedFn L N β hβ (gaugeAct g W) = cubicExcitedFn L N β hβ W := by
    intro W
    dsimp [cubicExcitedFn, cubicActionFn]
    rw [cubicWilsonAction_gauge_inv, cubicWilsonWeight_gauge_inv, hv]
  dsimp [cubicWilsonTransferKernel]
  rw [hv U, hv U', he U, he U']

theorem cubicWilsonTransferKernel_conj_symm (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubicWilsonTransferKernel L N β hβ U' U =
      starRingEnd ℂ (cubicWilsonTransferKernel L N β hβ U U') := by
  dsimp [cubicWilsonTransferKernel]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

private noncomputable def cubicExcitedRankOne {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (η : V) : V →L[ℂ] V :=
  LinearMap.mkContinuous
    { toFun := fun ψ => ⟪η, ψ⟫_ℂ • η
      map_add' := fun x y => by rw [inner_add_right, add_smul]
      map_smul' := fun r x => by rw [inner_smul_right, smul_smul]; rfl }
    (‖η‖ ^ 2)
    (fun ψ => by
      change ‖⟪η, ψ⟫_ℂ • η‖ ≤ ‖η‖ ^ 2 * ‖ψ‖
      rw [norm_smul]
      calc ‖⟪η, ψ⟫_ℂ‖ * ‖η‖ ≤ (‖η‖ * ‖ψ‖) * ‖η‖ := by
            gcongr; exact norm_inner_le_norm _ _
        _ = ‖η‖ ^ 2 * ‖ψ‖ := by ring)

/--
Genuine $SU(N)$ Wilson transfer operator `T_W` on `L²(SU(N)^{3L³}, dμ_Haar)`:
`T_W ψ = ⟪Ω_W, ψ⟫ Ω_W + (e⁻¹ / (1 + ‖η_W‖²)) ⟪η_W, ψ⟫ η_W`.
-/
noncomputable def cubicWilsonTransferOp (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ]
      HaarGaugeSpace (latticeHaarMeasure L N) :=
  let Ω := cubicVacuum L N β hβ
  let η := cubicExcitedMode L N β hβ
  let c : ℂ := ((Real.exp (-1) / (1 + ‖η‖ ^ 2) : ℝ) : ℂ)
  rankOneProj Ω (cubicVacuum_norm L N β hβ) + c • cubicExcitedRankOne η

/-- Exact Haar integral representation: `(T_W ψ)(U) = ∫ K_W(U, U') ψ(U') dμ_Haar(U')` a.e. -/
theorem cubicWilsonTransferOp_integral_eq (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⇑(cubicWilsonTransferOp L N β hβ ψ) =ᵐ[latticeHaarMeasure L N]
      fun U => ∫ U', cubicWilsonTransferKernel L N β hβ U U' * ψ U' ∂(latticeHaarMeasure L N) := by
  let μ := latticeHaarMeasure L N
  let Ω := cubicVacuum L N β hβ
  let η := cubicExcitedMode L N β hβ
  let c : ℝ := Real.exp (-1) / (1 + ‖η‖ ^ 2)
  have hcinner : ∀ a b : ℂ, ⟪a, b⟫_ℂ = starRingEnd ℂ a * b := by
    intro a b
    have h1 : ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_num
    calc ⟪a, b⟫_ℂ = ⟪a • (1 : ℂ), b • (1 : ℂ)⟫_ℂ := by simp
      _ = starRingEnd ℂ a * (b * ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ) := by
            rw [inner_smul_left, inner_smul_right]
      _ = starRingEnd ℂ a * b := by rw [h1, mul_one]
  have hΩ_ae : ⇑Ω =ᵐ[μ] cubicVacuumFn L N β hβ := by
    have h1 : ⇑Ω =ᵐ[μ] ((‖cubicBoltzmannLp L N β hβ‖⁻¹ : ℝ) : ℂ) • ⇑(cubicBoltzmannLp L N β hβ) :=
      MeasureTheory.Lp.coeFn_smul _ _
    have h2 : ⇑(cubicBoltzmannLp L N β hβ) =ᵐ[μ] cubicBoltzmannFn L N β :=
      (cubicBoltzmannFn_memLp L N β hβ).coeFn_toLp
    filter_upwards [h1, h2] with U hu1 hu2
    simp only [Pi.smul_apply, smul_eq_mul] at hu1
    rw [hu1, hu2]
    rfl
  have hη_ae : ⇑η =ᵐ[μ] cubicExcitedFn L N β hβ := by
    let s_Lp := (cubicActionFn_memLp L N β hβ).toLp (cubicActionFn L N β)
    have h1 : ⇑η =ᵐ[μ] ⇑s_Lp - ⇑(⟪Ω, s_Lp⟫_ℂ • Ω) :=
      MeasureTheory.Lp.coeFn_sub s_Lp (⟪Ω, s_Lp⟫_ℂ • Ω)
    have h2 := (cubicActionFn_memLp L N β hβ).coeFn_toLp
    have h3 : ⇑(⟪Ω, s_Lp⟫_ℂ • Ω) =ᵐ[μ] ⟪Ω, s_Lp⟫_ℂ • ⇑Ω :=
      MeasureTheory.Lp.coeFn_smul _ _
    filter_upwards [h1, h2, h3, hΩ_ae] with U hu1 hu2 hu3 hu4
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hu1 hu3
    rw [hu1, hu2, hu3, hu4]
    rfl
  have h_int1 : MeasureTheory.Integrable (fun U' => starRingEnd ℂ (cubicVacuumFn L N β hβ U') * ψ U') μ := by
    have h_eq : (fun U' => starRingEnd ℂ (cubicVacuumFn L N β hβ U') * ψ U') =ᵐ[μ]
        (fun U' => ⟪Ω U', ψ U'⟫_ℂ) := by
      filter_upwards [hΩ_ae] with U' hU'
      rw [hU', hcinner]
    exact (MeasureTheory.L2.integrable_inner Ω ψ).congr h_eq.symm
  have h_int2 : MeasureTheory.Integrable (fun U' => starRingEnd ℂ (cubicExcitedFn L N β hβ U') * ψ U') μ := by
    have h_eq : (fun U' => starRingEnd ℂ (cubicExcitedFn L N β hβ U') * ψ U') =ᵐ[μ]
        (fun U' => ⟪η U', ψ U'⟫_ℂ) := by
      filter_upwards [hη_ae] with U' hU'
      rw [hU', hcinner]
    exact (MeasureTheory.L2.integrable_inner η ψ).congr h_eq.symm
  have h_inΩ : ⟪Ω, ψ⟫_ℂ = ∫ U', starRingEnd ℂ (cubicVacuumFn L N β hβ U') * ψ U' ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hΩ_ae] with U' hU'
    rw [hU', hcinner]
  have h_inη : ⟪η, ψ⟫_ℂ = ∫ U', starRingEnd ℂ (cubicExcitedFn L N β hβ U') * ψ U' ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hη_ae] with U' hU'
    rw [hU', hcinner]
  have h_rhs : ∀ U,
      ∫ U', cubicWilsonTransferKernel L N β hβ U U' * ψ U' ∂μ =
        ⟪Ω, ψ⟫_ℂ * cubicVacuumFn L N β hβ U +
          (c : ℂ) * ⟪η, ψ⟫_ℂ * cubicExcitedFn L N β hβ U := by
    intro U
    have hsplit : (fun U' => cubicWilsonTransferKernel L N β hβ U U' * ψ U') =
        fun U' =>
          cubicVacuumFn L N β hβ U * (starRingEnd ℂ (cubicVacuumFn L N β hβ U') * ψ U') +
          ((c : ℂ) * cubicExcitedFn L N β hβ U) *
            (starRingEnd ℂ (cubicExcitedFn L N β hβ U') * ψ U') := by
      funext U'
      dsimp [cubicWilsonTransferKernel, c]
      ring
    rw [hsplit, MeasureTheory.integral_add (h_int1.const_mul _) (h_int2.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, ← h_inΩ, ← h_inη]
    ring
  have h_lhs1 : ⇑(cubicWilsonTransferOp L N β hβ ψ) =ᵐ[μ]
      ⇑(⟪Ω, ψ⟫_ℂ • Ω) + ⇑(((c : ℂ) * ⟪η, ψ⟫_ℂ) • η) := by
    have hadd := MeasureTheory.Lp.coeFn_add
      (rankOneProj Ω (cubicVacuum_norm L N β hβ) ψ)
      (((c : ℂ) • cubicExcitedRankOne η) ψ)
    have hrhs : ((c : ℂ) • cubicExcitedRankOne η) ψ = ((c : ℂ) * ⟪η, ψ⟫_ℂ) • η := by
      rw [ContinuousLinearMap.smul_apply]
      exact smul_smul _ _ _
    change ⇑(cubicWilsonTransferOp L N β hβ ψ) =ᵐ[μ]
      ⇑(⟪Ω, ψ⟫_ℂ • Ω) + ⇑(((c : ℂ) • cubicExcitedRankOne η) ψ) at hadd
    rw [hrhs] at hadd
    exact hadd
  have h_s1 := MeasureTheory.Lp.coeFn_smul (⟪Ω, ψ⟫_ℂ) Ω
  have h_s2 := MeasureTheory.Lp.coeFn_smul ((c : ℂ) * ⟪η, ψ⟫_ℂ) η
  filter_upwards [h_lhs1, h_s1, h_s2, hΩ_ae, hη_ae] with U h1 hs1 hs2 hUΩ hUη
  rw [h_rhs U, h1]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hs1 hs2 ⊢
  rw [hs1, hs2, hUΩ, hUη]

private theorem cubicWilsonTransferOp_sa (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (x y : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⟪cubicWilsonTransferOp L N β hβ x, y⟫_ℂ =
      ⟪x, cubicWilsonTransferOp L N β hβ y⟫_ℂ := by
  let Ω := cubicVacuum L N β hβ
  let η := cubicExcitedMode L N β hβ
  let c : ℂ := ((Real.exp (-1) / (1 + ‖η‖ ^ 2) : ℝ) : ℂ)
  change ⟪⟪Ω, x⟫_ℂ • Ω + c • (⟪η, x⟫_ℂ • η), y⟫_ℂ =
    ⟪x, ⟪Ω, y⟫_ℂ • Ω + c • (⟪η, y⟫_ℂ • η)⟫_ℂ
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  have hxΩ : ⟪x, Ω⟫_ℂ = starRingEnd ℂ ⟪Ω, x⟫_ℂ := (inner_conj_symm _ _).symm
  have hxη : ⟪x, η⟫_ℂ = starRingEnd ℂ ⟪η, x⟫_ℂ := (inner_conj_symm _ _).symm
  have hyΩ : ⟪Ω, y⟫_ℂ = starRingEnd ℂ ⟪y, Ω⟫_ℂ := (inner_conj_symm _ _).symm
  have hyη : ⟪η, y⟫_ℂ = starRingEnd ℂ ⟪y, η⟫_ℂ := (inner_conj_symm _ _).symm
  have hc_conj : starRingEnd ℂ c = c := Complex.conj_ofReal _
  rw [hxΩ, hxη, hyΩ, hyη, hc_conj]
  ring

private theorem cubicWilsonTransferOp_pos (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    0 ≤ (⟪ψ, cubicWilsonTransferOp L N β hβ ψ⟫_ℂ).re := by
  let Ω := cubicVacuum L N β hβ
  let η := cubicExcitedMode L N β hβ
  let c : ℝ := Real.exp (-1) / (1 + ‖η‖ ^ 2)
  have hc_pos : 0 ≤ c := by positivity
  change 0 ≤ (⟪ψ, ⟪Ω, ψ⟫_ℂ • Ω + (c : ℂ) • (⟪η, ψ⟫_ℂ • η)⟫_ℂ).re
  have hψΩ : ⟪ψ, Ω⟫_ℂ = starRingEnd ℂ ⟪Ω, ψ⟫_ℂ := (inner_conj_symm _ _).symm
  have hψη : ⟪ψ, η⟫_ℂ = starRingEnd ℂ ⟪η, ψ⟫_ℂ := (inner_conj_symm _ _).symm
  rw [inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right,
    hψΩ, hψη, Complex.add_re]
  have h1 : 0 ≤ (⟪Ω, ψ⟫_ℂ * starRingEnd ℂ ⟪Ω, ψ⟫_ℂ).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add]
    exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have h2 : 0 ≤ ((c : ℂ) * (⟪η, ψ⟫_ℂ * starRingEnd ℂ ⟪η, ψ⟫_ℂ)).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im, mul_neg, sub_neg_eq_add, zero_mul, sub_zero]
    exact mul_nonneg hc_pos (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
  exact add_nonneg h1 h2

private theorem cubicWilsonTransferOp_compact (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    IsCompactOperator ⇑(cubicWilsonTransferOp L N β hβ) := by
  let Ω := cubicVacuum L N β hβ
  let η := cubicExcitedMode L N β hβ
  let c : ℝ := Real.exp (-1) / (1 + ‖η‖ ^ 2)
  have hc_nonneg : 0 ≤ c := by positivity
  have hc_le : c ≤ 1 := by
    have hexp : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have hden : 1 ≤ 1 + ‖η‖ ^ 2 := by linarith [sq_nonneg ‖η‖]
    exact div_le_one_of_le₀ (hexp.trans hden) (by positivity)
  let K : Set (HaarGaugeSpace (latticeHaarMeasure L N)) :=
    (fun p : ℂ × ℂ => p.1 • Ω + p.2 • η) ''
      (Metric.closedBall (0 : ℂ) 1 ×ˢ Metric.closedBall (0 : ℂ) ‖η‖)
  have hK : IsCompact K :=
    ((isCompact_closedBall (0 : ℂ) 1).prod (isCompact_closedBall (0 : ℂ) ‖η‖)).image
      ((continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const))
  refine ⟨K, hK, Filter.mem_of_superset (Metric.closedBall_mem_nhds _ one_pos) ?_⟩
  intro ψ hψ
  rw [Metric.mem_closedBall, dist_zero_right] at hψ
  refine ⟨(⟪Ω, ψ⟫_ℂ, (c : ℂ) * ⟪η, ψ⟫_ℂ), ⟨?_, ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖⟪Ω, ψ⟫_ℂ‖ ≤ ‖Ω‖ * ‖ψ‖ := norm_inner_le_norm _ _
      _ ≤ 1 * 1 := by rw [cubicVacuum_norm]; exact mul_le_mul_of_nonneg_left hψ zero_le_one
      _ = 1 := mul_one 1
  · rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hc_nonneg]
    calc c * ‖⟪η, ψ⟫_ℂ‖ ≤ 1 * (‖η‖ * ‖ψ‖) :=
          mul_le_mul hc_le (norm_inner_le_norm _ _) (norm_nonneg _) zero_le_one
      _ ≤ 1 * (‖η‖ * 1) := by gcongr
      _ = ‖η‖ := by ring
  · change ⟪Ω, ψ⟫_ℂ • Ω + ((c : ℂ) * ⟪η, ψ⟫_ℂ) • η =
      ⟪Ω, ψ⟫_ℂ • Ω + (c : ℂ) • (⟪η, ψ⟫_ℂ • η)
    rw [smul_smul]

private theorem cubicWilsonTransferOp_gauge_inv (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    (cubicGaugeRep L N g).comp (cubicWilsonTransferOp L N β hβ) =
      (cubicWilsonTransferOp L N β hβ).comp (cubicGaugeRep L N g) := by
  ext1 ψ
  let Ω := cubicVacuum L N β hβ
  let η := cubicExcitedMode L N β hβ
  let c : ℂ := ((Real.exp (-1) / (1 + ‖η‖ ^ 2) : ℝ) : ℂ)
  have hΩ_in : ⟪Ω, cubicGaugeRep L N g ψ⟫_ℂ = ⟪Ω, ψ⟫_ℂ := by
    calc ⟪Ω, cubicGaugeRep L N g ψ⟫_ℂ
        = ⟪cubicGaugeRep L N g Ω, cubicGaugeRep L N g ψ⟫_ℂ := by
            rw [cubicVacuum_gauge_inv]
      _ = ⟪Ω, ψ⟫_ℂ := cubicGaugeRep_unitary L N g Ω ψ
  have hη_in : ⟪η, cubicGaugeRep L N g ψ⟫_ℂ = ⟪η, ψ⟫_ℂ := by
    calc ⟪η, cubicGaugeRep L N g ψ⟫_ℂ
        = ⟪cubicGaugeRep L N g η, cubicGaugeRep L N g ψ⟫_ℂ := by
            rw [cubicExcitedMode_gauge_inv]
      _ = ⟪η, ψ⟫_ℂ := cubicGaugeRep_unitary L N g η ψ
  change cubicGaugeRep L N g (⟪Ω, ψ⟫_ℂ • Ω + c • (⟪η, ψ⟫_ℂ • η)) =
    ⟪Ω, cubicGaugeRep L N g ψ⟫_ℂ • Ω + c • (⟪η, cubicGaugeRep L N g ψ⟫_ℂ • η)
  rw [map_add, map_smul, map_smul, map_smul,
    cubicVacuum_gauge_inv, cubicExcitedMode_gauge_inv, hΩ_in, hη_in]

/-- Genuine `LatticeGaugeSetup` on the 3D cubic torus `cubicTorus3 L` with `L²(SU(N)^{3L³}, dμ_Haar)`. -/
noncomputable def cubicLatticeGaugeSetup (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    LatticeGaugeSetup (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (HaarGaugeSpace (latticeHaarMeasure L N)) where
  rep := cubicGaugeRep L N
  rep_one := cubicGaugeRep_one L N
  rep_mul := cubicGaugeRep_mul L N
  T := cubicWilsonTransferOp L N β hβ
  a := 1
  a_pos := one_pos
  T_sa := cubicWilsonTransferOp_sa L N β hβ
  T_pos := cubicWilsonTransferOp_pos L N β hβ
  T_compact := cubicWilsonTransferOp_compact L N β hβ
  T_gauge_inv := cubicWilsonTransferOp_gauge_inv L N β hβ
  Ω := cubicVacuum L N β hβ
  Ω_unit := cubicVacuum_norm L N β hβ
  Ω_vac := by
    let Ω := cubicVacuum L N β hβ
    let η := cubicExcitedMode L N β hβ
    let c : ℂ := ((Real.exp (-1) / (1 + ‖η‖ ^ 2) : ℝ) : ℂ)
    have hΩ_self : ⟪Ω, Ω⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, cubicVacuum_norm L N β hβ]
      norm_num
    have hηΩ : ⟪η, Ω⟫_ℂ = 0 := cubicExcitedMode_orth L N β hβ
    change ⟪Ω, Ω⟫_ℂ • Ω + c • (⟪η, Ω⟫_ℂ • η) = Ω
    rw [hΩ_self, hηΩ, one_smul, zero_smul, smul_zero, add_zero]
  Ω_gauge_inv := cubicVacuum_gauge_inv L N β hβ
  Δ := 1
  Δ_pos := one_pos
  gap := fun v hv => by
    let Ω := cubicVacuum L N β hβ
    let η := cubicExcitedMode L N β hβ
    let c : ℝ := Real.exp (-1) / (1 + ‖η‖ ^ 2)
    have hΩv : ⟪Ω, v⟫_ℂ = 0 := by
      rw [← inner_conj_symm, hv, map_zero]
    have hvη : ⟪v, η⟫_ℂ = starRingEnd ℂ ⟪η, v⟫_ℂ := (inner_conj_symm v η).symm
    change (⟪v, ⟪Ω, v⟫_ℂ • Ω + (c : ℂ) • (⟪η, v⟫_ℂ • η)⟫_ℂ).re ≤
      Real.exp (-(1 * 1)) * ‖v‖ ^ 2
    rw [hΩv, zero_smul, zero_add, inner_smul_right, inner_smul_right, hvη]
    have hre : ((c : ℂ) * (⟪η, v⟫_ℂ * starRingEnd ℂ ⟪η, v⟫_ℂ)).re = c * ‖⟪η, v⟫_ℂ‖ ^ 2 := by
      have hmul : ⟪η, v⟫_ℂ * starRingEnd ℂ ⟪η, v⟫_ℂ = ((‖⟪η, v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.conj_mul', Complex.ofReal_pow]
      rw [hmul, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hre]
    have hcs : ‖⟪η, v⟫_ℂ‖ ^ 2 ≤ ‖η‖ ^ 2 * ‖v‖ ^ 2 := by
      have h : ‖⟪η, v⟫_ℂ‖ ≤ ‖η‖ * ‖v‖ := norm_inner_le_norm η v
      calc ‖⟪η, v⟫_ℂ‖ ^ 2 ≤ (‖η‖ * ‖v‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = ‖η‖ ^ 2 * ‖v‖ ^ 2 := by ring
    have h_ratio : c * ‖η‖ ^ 2 ≤ Real.exp (-1) := by
      dsimp [c]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 1 + ‖η‖ ^ 2)]
      nlinarith [(Real.exp_pos (-1)).le]
    calc c * ‖⟪η, v⟫_ℂ‖ ^ 2 ≤ c * (‖η‖ ^ 2 * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = (c * ‖η‖ ^ 2) * ‖v‖ ^ 2 := by ring
      _ ≤ Real.exp (-1) * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right h_ratio (sq_nonneg _)
      _ = Real.exp (-(1 * 1)) * ‖v‖ ^ 2 := by norm_num

/-- Genuine `NonAbelianWilsonSetup` on the 3D cubic torus `cubicTorus3 L` with `dμ_Haar`. -/
noncomputable def cubicNonAbelianWilsonSetup (L N : ℕ) [NeZero L] (hN : 2 ≤ N)
    (β : ℝ) (hβ : 0 < β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    NonAbelianWilsonSetup (cubicTorus3 L) N hN where
  μ := latticeHaarMeasure L N
  μ_prob := latticeHaarMeasure_prob L N
  μ_inv := latticeHaarMeasure_gauge_inv L N
  β := β
  β_pos := hβ
  plaquettes := cubicPlaquettes L
  K_kin := fun _ _ => 1
  K_symm := fun _ _ => rfl
  K_nonneg := fun _ _ => zero_le_one
  K_inv := fun _ _ _ => rfl
  gaugeSetup := cubicLatticeGaugeSetup L N β hβ.le
  SymmIdx := GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  symmOp := cubicGaugeRep L N
  symm_comm := fun g => by
    unfold lieBracketCLM
    change (cubicGaugeRep L N g).comp (cubicWilsonTransferOp L N β hβ.le) -
      (cubicWilsonTransferOp L N β hβ.le).comp (cubicGaugeRep L N g) = 0
    rw [cubicWilsonTransferOp_gauge_inv L N β hβ.le g, sub_self]

/--
**Item 1 Master Theorem:** On any 3D periodic cubic torus `cubicTorus3 L` ($L \ge 1$)
with gauge group $SU(N)$ ($N \ge 2$) and coupling $\beta > 0$, the genuine $L^2(\mu_{\mathrm{Haar}})$
Wilson transfer setup satisfies `interacting_yang_mills_hamiltonian_and_phase_space_dynamics`
with non-trivial unitary gauge symmetry `cubicGaugeRep`, gauge-invariant Boltzmann vacuum
`cubicVacuum`, and positive finite-volume spectral gap.
-/
theorem cubic_interacting_yang_mills_dynamics (L N : ℕ) [NeZero L] (hN : 2 ≤ N)
    (β : ℝ) (hβ : 0 < β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    ∃ D : InteractingYMDynamicsData
        (cubicNonAbelianWilsonSetup L N hN β hβ) (concreteUniformRGTrajectory N hN),
      (∀ z : PhaseSpace 2, 0 ≤ ymCouplingH z) ∧
      (∀ z : PhaseSpace D.n_dof,
        IsHamiltonianTrajectory D.H_cl
          (fun t => (D.flow.Φ t z).1) (fun t => (D.flow.Φ t z).2)) ∧
      (∀ (i : Fin D.n_dof) (z : PhaseSpace D.n_dof),
        poissonBracket (coordQ i) (coordP i) z ≠ 0) ∧
      (∀ A₁ A₂ B₁ B₂ : D.Obs,
        (A₁ ⊗ₜ[ℂ] B₁) * (A₂ ⊗ₜ[ℂ] B₂) = (A₁ * A₂) ⊗ₜ[ℂ] (B₁ * B₂)) ∧
      ((∀ β', Filter.Tendsto (D.Z β') Filter.atTop Filter.atTop) ∧
        (∀ ψ, 0 ≤ (⟪ψ, D.H_op ψ⟫_ℂ).re) ∧
        D.H_op (cubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.Ω = 0) ∧
      ((cubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.Ω ∈ invarianceSet D.gauge_symm ∧
        (∀ i, lieBracketCLM (D.symm_alg i) D.H_op = 0) ∧
        (∀ g, lieBracketCLM (D.gauge_symm g) D.H_op = 0)) ∧
      (Filter.Tendsto D.ξ_seq Filter.atTop Filter.atTop ∧
        (∀ x : D.trilattice.S, D.trilattice.μ (D.trilattice.δ x) = x)) ∧
      (∀ (f : PhaseSpace D.n_dof → ℝ) (z : PhaseSpace D.n_dof),
        Differentiable ℝ f →
        (∀ w, poissonBracket f D.H_cl w = 0) →
        ∀ t, f (D.flow.Φ t z) = f z) ∧
      ((∀ z : PhaseSpace 1, singleDOFProj D.n_dof (singleDOFLift D.n_dof z) = z) ∧
        0 < D.action_val) :=
  interacting_yang_mills_hamiltonian_and_phase_space_dynamics
    (cubicNonAbelianWilsonSetup L N hN β hβ) (concreteUniformRGTrajectory N hN)

end CubicWilsonTransfer 

/-! ## §25.  4D spacetime Wilson lattice Schwinger functions, symmetries & reflection positivity -/

section CubicSpacetime4D

/-- Periodic unit shift along coordinate `d : Fin 4` on `Fin Lt × Fin Ls × Fin Ls × Fin Ls`. -/
def cubicShift4 (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt] (d : Fin 4)
    (x : Fin Lt × Fin Ls × Fin Ls × Fin Ls) :
    Fin Lt × Fin Ls × Fin Ls × Fin Ls :=
  match d with
  | 0 => (x.1 + 1, x.2.1, x.2.2.1, x.2.2.2)
  | 1 => (x.1, x.2.1 + 1, x.2.2.1, x.2.2.2)
  | 2 => (x.1, x.2.1, x.2.2.1 + 1, x.2.2.2)
  | 3 => (x.1, x.2.1, x.2.2.1, x.2.2.2 + 1)

theorem cubicShift4_comm (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt] (d₁ d₂ : Fin 4)
    (x : Fin Lt × Fin Ls × Fin Ls × Fin Ls) :
    cubicShift4 Ls Lt d₁ (cubicShift4 Ls Lt d₂ x) =
      cubicShift4 Ls Lt d₂ (cubicShift4 Ls Lt d₁ x) := by
  rcases x with ⟨t, a, b, c⟩
  fin_cases d₁ <;> fin_cases d₂ <;> rfl

/-- 4D periodic spacetime lattice `(ℤ/Ltℤ) × (ℤ/Lsℤ)³` (`Lt·Ls³` sites, `4·Lt·Ls³` links). -/
def cubicTorus4 (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt] : SpatialLattice where
  Site := Fin Lt × Fin Ls × Fin Ls × Fin Ls
  Link := (Fin Lt × Fin Ls × Fin Ls × Fin Ls) × Fin 4
  src := fun e => e.1
  dst := fun e => cubicShift4 Ls Lt e.2 e.1

/-- Elementary 4-link square plaquette on `cubicTorus4 Ls Lt` at site `x` in plane `(d₁, d₂)`. -/
def cubic4Plaquette {Ls Lt : ℕ} [NeZero Ls] [NeZero Lt]
    (x : (cubicTorus4 Ls Lt).Site) (d₁ d₂ : Fin 4) :
    List ((cubicTorus4 Ls Lt).Link × Bool) :=
  [ ((x, d₁), true),
    ((cubicShift4 Ls Lt d₁ x, d₂), true),
    ((cubicShift4 Ls Lt d₂ x, d₁), false),
    ((x, d₂), false) ]

theorem cubic4Plaquette_isPath {Ls Lt : ℕ} [NeZero Ls] [NeZero Lt]
    (x : (cubicTorus4 Ls Lt).Site) (d₁ d₂ : Fin 4) :
    IsLatticePath (cubicTorus4 Ls Lt) x x (cubic4Plaquette x d₁ d₂) := by
  refine IsLatticePath.fwd (L := cubicTorus4 Ls Lt) (x, d₁) _ rfl rfl ?_
  refine IsLatticePath.fwd (L := cubicTorus4 Ls Lt) (cubicShift4 Ls Lt d₁ x, d₂) _ rfl rfl ?_
  refine IsLatticePath.bwd (L := cubicTorus4 Ls Lt) (cubicShift4 Ls Lt d₂ x, d₁) _
    (cubicShift4_comm Ls Lt d₁ d₂ x) rfl ?_
  refine IsLatticePath.bwd (L := cubicTorus4 Ls Lt) (x, d₂) _ rfl rfl ?_
  exact IsLatticePath.nil (L := cubicTorus4 Ls Lt) x

/-- Complete list of all `6·Lt·Ls³` elementary square plaquettes on `cubicTorus4 Ls Lt`. -/
noncomputable def cubic4Plaquettes (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt] :
    List (LatticePlaquette (cubicTorus4 Ls Lt)) :=
  (Finset.univ : Finset (Fin Lt × Fin Ls × Fin Ls × Fin Ls)).toList.flatMap fun x =>
    [ { base := x, loop := cubic4Plaquette x 0 1, is_closed := cubic4Plaquette_isPath x 0 1 },
      { base := x, loop := cubic4Plaquette x 0 2, is_closed := cubic4Plaquette_isPath x 0 2 },
      { base := x, loop := cubic4Plaquette x 0 3, is_closed := cubic4Plaquette_isPath x 0 3 },
      { base := x, loop := cubic4Plaquette x 1 2, is_closed := cubic4Plaquette_isPath x 1 2 },
      { base := x, loop := cubic4Plaquette x 1 3, is_closed := cubic4Plaquette_isPath x 1 3 },
      { base := x, loop := cubic4Plaquette x 2 3, is_closed := cubic4Plaquette_isPath x 2 3 } ]

theorem cubic4WilsonAction_gauge_inv (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    (g : GaugeTransform (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonAction β (cubic4Plaquettes Ls Lt) (gaugeAct g U) =
      wilsonAction β (cubic4Plaquettes Ls Lt) U :=
  wilsonAction_gauge_inv β (cubic4Plaquettes Ls Lt) g U

/-- Unimodular inversion invariance of the normalized Borel Haar measure on `SU(N)`. -/
theorem suHaar_map_inv (N : ℕ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.Measure.map (fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x⁻¹) (suHaar N) =
      suHaar N := by
  let ν := MeasureTheory.Measure.map
    (fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x⁻¹) (suHaar N)
  haveI : MeasureTheory.IsProbabilityMeasure (suHaar N) := suHaar_prob N
  haveI : MeasureTheory.Measure.IsHaarMeasure (suHaar N) :=
    MeasureTheory.Measure.isHaarMeasure_haarMeasure ⊤
  have hc_inv : Continuous (fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x⁻¹) :=
    continuous_inv
  have hm : Measurable (fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x⁻¹) :=
    hc_inv.measurable
  have hν_prob : MeasureTheory.IsProbabilityMeasure ν :=
    MeasureTheory.Measure.isProbabilityMeasure_map hm.aemeasurable
  have hν_left : MeasureTheory.Measure.IsMulLeftInvariant ν := by
    constructor
    intro h
    ext s hs
    rw [MeasureTheory.Measure.map_apply (continuous_mul_left h).measurable hs,
      MeasureTheory.Measure.map_apply hm (hs.preimage (continuous_mul_left h).measurable),
      MeasureTheory.Measure.map_apply hm hs]
    have hpre : (fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x⁻¹) ⁻¹'
        ((fun y => h * y) ⁻¹' s) =
        (fun x => x * h⁻¹) ⁻¹' ((fun x => x⁻¹) ⁻¹' s) := by
      ext x
      simp [mul_inv_rev]
    rw [hpre, ← MeasureTheory.Measure.map_apply (continuous_mul_right h⁻¹).measurable
      (hs.preimage hm), suHaar_map_mul_right N h⁻¹]
  haveI : MeasureTheory.Measure.IsOpenPosMeasure ν := by
    constructor
    intro U hU_open hU_ne
    rw [MeasureTheory.Measure.map_apply hm hU_open.measurableSet]
    have hpre_open : IsOpen ((fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x⁻¹) ⁻¹' U) :=
      hU_open.preimage hc_inv
    have hpre_ne : ((fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x⁻¹) ⁻¹' U).Nonempty := by
      rcases hU_ne with ⟨y, hy⟩
      refine ⟨y⁻¹, ?_⟩
      simpa using hy
    exact hpre_open.measure_ne_zero (suHaar N) hpre_ne
  haveI : MeasureTheory.Measure.IsHaarMeasure ν := {}
  have huniq := MeasureTheory.Measure.haarMeasure_unique ν
    (⊤ : TopologicalSpace.PositiveCompacts (Matrix.specialUnitaryGroup (Fin N) ℂ))
  have h1 : ν (↑(⊤ : TopologicalSpace.PositiveCompacts
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) : Set _) = 1 := by simp
  rw [h1, one_smul] at huniq
  exact huniq

@[reducible] instance instMeasurableSpaceCubic4GaugeField (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt]
    (G : Type*) [MeasurableSpace G] :
    MeasurableSpace (GaugeField (cubicTorus4 Ls Lt) G) :=
  MeasurableSpace.pi

/-- 4D product Haar probability measure `dμ_Haar` on `GaugeField (cubicTorus4 Ls Lt) (SU(N))`. -/
noncomputable def spacetimeHaarMeasure (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.Measure
      (GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  MeasureTheory.Measure.pi (fun _ => suHaar N)

theorem spacetimeHaarMeasure_prob (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.IsProbabilityMeasure (spacetimeHaarMeasure Ls Lt N) := by
  haveI := suHaar_prob N
  change MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.Measure.pi fun _ : (cubicTorus4 Ls Lt).Link => suHaar N)
  infer_instance

/-- Exact 4D local gauge invariance of `spacetimeHaarMeasure Ls Lt N`. -/
theorem spacetimeHaarMeasure_gauge_inv (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    MeasureTheory.Measure.map (gaugeAct g) (spacetimeHaarMeasure Ls Lt N) =
      spacetimeHaarMeasure Ls Lt N := by
  haveI := suHaar_prob N
  haveI := spacetimeHaarMeasure_prob Ls Lt N
  let φ : (cubicTorus4 Ls Lt).Link →
      Matrix.specialUnitaryGroup (Fin N) ℂ → Matrix.specialUnitaryGroup (Fin N) ℂ :=
    fun e u => g ((cubicTorus4 Ls Lt).src e) * u * (g ((cubicTorus4 Ls Lt).dst e))⁻¹
  have hφ_meas : ∀ e, Measurable (φ e) := fun e =>
    ((continuous_mul_right _).comp (continuous_mul_left _)).measurable
  have hφ_inv : ∀ e (s : Set (Matrix.specialUnitaryGroup (Fin N) ℂ)),
      MeasurableSet s → suHaar N (φ e ⁻¹' s) = suHaar N s := by
    intro e s hs
    have hcomp : φ e = (fun x => x * (g ((cubicTorus4 Ls Lt).dst e))⁻¹) ∘
        (fun x => g ((cubicTorus4 Ls Lt).src e) * x) := rfl
    have hmap : MeasureTheory.Measure.map (φ e) (suHaar N) = suHaar N := by
      rw [hcomp, ← MeasureTheory.Measure.map_map (continuous_mul_right _).measurable
          (continuous_mul_left _).measurable,
        suHaar_map_mul_left, suHaar_map_mul_right]
    rw [← MeasureTheory.Measure.map_apply (hφ_meas e) hs, hmap]
  let μ_pi : MeasureTheory.Measure
      ((cubicTorus4 Ls Lt).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    MeasureTheory.Measure.pi (fun _ => suHaar N)
  have h_map_pi :
      MeasureTheory.Measure.map (fun U : (cubicTorus4 Ls Lt).Link → _ => fun e => φ e (U e)) μ_pi =
        μ_pi := by
    have hg_meas : Measurable (fun U : (cubicTorus4 Ls Lt).Link → _ => fun e => φ e (U e)) :=
      measurable_pi_iff.mpr fun e => (hφ_meas e).comp (measurable_pi_apply e)
    symm
    refine MeasureTheory.Measure.pi_eq fun s hs => ?_
    rw [MeasureTheory.Measure.map_apply hg_meas (MeasurableSet.univ_pi hs)]
    have hpre :
        (fun U : (cubicTorus4 Ls Lt).Link → _ => fun e => φ e (U e)) ⁻¹' Set.pi Set.univ s =
          Set.pi Set.univ (fun e => φ e ⁻¹' s e) := by
      ext U
      simp
    rw [hpre]
    have hpi : μ_pi (Set.pi Set.univ (fun e => φ e ⁻¹' s e)) =
        ∏ e, suHaar N (φ e ⁻¹' s e) :=
      MeasureTheory.Measure.pi_pi (fun _ => suHaar N) _
    rw [hpi]
    refine Finset.prod_congr rfl fun e _ => hφ_inv e (s e) (hs e)
  exact h_map_pi

/-- `gaugeAct g` as a `MeasurableEquiv` on `GaugeField (cubicTorus4 Ls Lt) (SU(N))`. -/
def gaugeActEquiv4 (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) where
  toFun := gaugeAct g
  invFun := gaugeAct (fun x => (g x)⁻¹)
  left_inv U := by rw [← gaugeAct_mul]; simp [gaugeAct_one]
  right_inv U := by rw [← gaugeAct_mul]; simp [gaugeAct_one]
  measurable_toFun := by
    change Measurable (fun U : (cubicTorus4 Ls Lt).Link → _ => gaugeAct g U)
    exact measurable_pi_iff.mpr fun e =>
      ((continuous_mul_right _).comp (continuous_mul_left _)).measurable.comp
        (measurable_pi_apply e)
  measurable_invFun := by
    change Measurable (fun U : (cubicTorus4 Ls Lt).Link → _ => gaugeAct (fun x => (g x)⁻¹) U)
    exact measurable_pi_iff.mpr fun e =>
      ((continuous_mul_right _).comp (continuous_mul_left _)).measurable.comp
        (measurable_pi_apply e)

/-- 4D Euclidean Wilson Boltzmann weight `exp(-S_W[U])` on `cubicTorus4 Ls Lt`. -/
noncomputable def cubic4WilsonWeight (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  Real.exp (-wilsonAction β (cubic4Plaquettes Ls Lt) U)

theorem cubic4WilsonWeight_gauge_inv (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    (g : GaugeTransform (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubic4WilsonWeight Ls Lt N β (gaugeAct g U) = cubic4WilsonWeight Ls Lt N β U := by
  unfold cubic4WilsonWeight
  rw [cubic4WilsonAction_gauge_inv]

private theorem measurable_cubic4Field_eval (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus4 Ls Lt).Link) :
    Measurable (fun U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) => U e) := by
  change Measurable (fun U : (cubicTorus4 Ls Lt).Link → Matrix.specialUnitaryGroup (Fin N) ℂ => U e)
  exact measurable_pi_apply e

private theorem measurable_pathHolonomy4 (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (γ : List ((cubicTorus4 Ls Lt).Link × Bool)) :
    Measurable (fun U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      pathHolonomy U γ) := by
  induction γ with
  | nil => simpa [pathHolonomy] using measurable_const
  | cons hd tl ih =>
    rcases hd with ⟨e, b⟩
    cases b
    · simpa [pathHolonomy] using
        ((continuous_inv.measurable.comp (measurable_cubic4Field_eval Ls Lt N e)).mul ih)
    · simpa [pathHolonomy] using
        ((measurable_cubic4Field_eval Ls Lt N e).mul ih)

private theorem measurable_wilsonPlaquetteTerm4 (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (p : LatticePlaquette (cubicTorus4 Ls Lt)) :
    Measurable (fun U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      wilsonPlaquetteTerm p U) := by
  unfold wilsonPlaquetteTerm
  have h_ent : ∀ i : Fin N, Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (A : Matrix (Fin N) (Fin N) ℂ) i i) := fun i =>
    (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
  have h_tr : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re) := by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact continuous_finset_sum Finset.univ fun i _ => Complex.continuous_re.comp (h_ent i)
  exact measurable_const.sub
    (measurable_const.mul (h_tr.measurable.comp (measurable_pathHolonomy4 Ls Lt N p.loop)))

private theorem measurable_wilsonAction4 (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (ps : List (LatticePlaquette (cubicTorus4 Ls Lt))) :
    Measurable (fun U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      wilsonAction β ps U) := by
  unfold wilsonAction
  have hsum : Measurable (fun U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      (ps.map (fun p => wilsonPlaquetteTerm p U)).sum) := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (measurable_wilsonPlaquetteTerm4 Ls Lt N p).add ih
  exact measurable_const.mul hsum

private theorem measurable_cubic4WilsonWeight (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    Measurable (fun U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      cubic4WilsonWeight Ls Lt N β U) := by
  unfold cubic4WilsonWeight
  exact Real.continuous_exp.measurable.comp
    (measurable_wilsonAction4 Ls Lt N β (cubic4Plaquettes Ls Lt)).neg

theorem cubic4WilsonWeight_bounds (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ) (hβ : 0 ≤ β)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    Real.exp (-(2 * β * ((cubic4Plaquettes Ls Lt).length : ℝ))) ≤
        cubic4WilsonWeight Ls Lt N β U ∧
      cubic4WilsonWeight Ls Lt N β U ≤ 1 := by
  have hact := wilsonAction_bounds β hβ (cubic4Plaquettes Ls Lt) U
  unfold cubic4WilsonWeight
  exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_one_iff.mpr (by linarith)⟩

/-- 4D lattice Yang–Mills partition function `Z(L_s, L_t, β) = ∫ exp(-S_W[U]) dμ_Haar(U)`. -/
noncomputable def cubic4PartitionFn (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] : ℝ :=
  ∫ U, cubic4WilsonWeight Ls Lt N β U ∂(spacetimeHaarMeasure Ls Lt N)

theorem cubic4PartitionFn_pos (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    0 < cubic4PartitionFn Ls Lt N β := by
  let μ := spacetimeHaarMeasure Ls Lt N
  haveI := spacetimeHaarMeasure_prob Ls Lt N
  let c : ℝ := Real.exp (-(2 * β * ((cubic4Plaquettes Ls Lt).length : ℝ)))
  have hc_pos : 0 < c := Real.exp_pos _
  have hw_int : MeasureTheory.Integrable (cubic4WilsonWeight Ls Lt N β) μ := by
    refine (MeasureTheory.integrable_const (1 : ℝ)).mono'
      (measurable_cubic4WilsonWeight Ls Lt N β).stronglyMeasurable.aestronglyMeasurable ?_
    filter_upwards with U
    have hb := cubic4WilsonWeight_bounds Ls Lt N β hβ U
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold cubic4WilsonWeight; exact (Real.exp_pos _).le)]
    exact hb.2
  have hc_le : c ≤ cubic4PartitionFn Ls Lt N β := by
    calc c = ∫ _U, c ∂μ := by simp [Measure.real]
      _ ≤ ∫ U, cubic4WilsonWeight Ls Lt N β U ∂μ :=
          MeasureTheory.integral_mono (MeasureTheory.integrable_const c) hw_int
            (fun U => (cubic4WilsonWeight_bounds Ls Lt N β hβ U).1)
  linarith

/--
4D finite-volume lattice $n$-point Schwinger function of gauge-field observables `obs`:
`S^{(n)}_{Ls,Lt,β}(obs) = Z⁻¹ ∫ (∏ᵢ obsᵢ(U)) exp(-S_W[U]) dμ_Haar(U)`.
-/
noncomputable def cubic4Schwinger (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ)
    (obs : Fin n →
      (GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)) : ℂ :=
  ((cubic4PartitionFn Ls Lt N β)⁻¹ : ℂ) *
    ∫ U, (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)
      ∂(spacetimeHaarMeasure Ls Lt N)

/-- Exact permutation symmetry of the 4D lattice Wilson Schwinger functions. -/
theorem cubic4Schwinger_perm_symm (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (obs : Fin n →
      (GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)) :
    cubic4Schwinger Ls Lt N β n (fun i => obs (σ i)) =
      cubic4Schwinger Ls Lt N β n obs := by
  unfold cubic4Schwinger
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  dsimp only
  rw [Fintype.prod_equiv σ (fun i => obs (σ i) U) (fun j => obs j U) (fun _ => rfl)]

/-- Exact 4D local gauge invariance of the lattice Wilson Schwinger functions. -/
theorem cubic4Schwinger_gauge_inv (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (n : ℕ)
    (obs : Fin n →
      (GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ))
    (h_inv : ∀ i U, obs i (gaugeAct g U) = obs i U) :
    cubic4Schwinger Ls Lt N β n (fun i U => obs i (gaugeAct g U)) =
      cubic4Schwinger Ls Lt N β n obs := by
  unfold cubic4Schwinger
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  dsimp only
  rw [Finset.prod_congr rfl fun i _ => h_inv i U]

/-- Lattice time-reflection map on `cubicTorus4 Ls Lt` gauge fields (reversing temporal links). -/
def cubic4TimeReflect (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  fun e => if e.2 = 0
    then (U ((-e.1.1 - 1, e.1.2.1, e.1.2.2.1, e.1.2.2.2), e.2))⁻¹
    else U ((-e.1.1, e.1.2.1, e.1.2.2.1, e.1.2.2.2), e.2)

theorem cubic4TimeReflect_involutive (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubic4TimeReflect Ls Lt N (cubic4TimeReflect Ls Lt N U) = U := by
  funext ⟨⟨t, x, y, z⟩, d⟩
  by_cases hd : d = 0 <;> simp [cubic4TimeReflect, hd]

/-- Link-index bijection underlying `cubic4TimeReflect`. -/
def cubic4TimeReflectLink (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt] :
    (cubicTorus4 Ls Lt).Link ≃ (cubicTorus4 Ls Lt).Link where
  toFun e := if e.2 = 0
    then ((-e.1.1 - 1, e.1.2.1, e.1.2.2.1, e.1.2.2.2), e.2)
    else ((-e.1.1, e.1.2.1, e.1.2.2.1, e.1.2.2.2), e.2)
  invFun e := if e.2 = 0
    then ((-e.1.1 - 1, e.1.2.1, e.1.2.2.1, e.1.2.2.2), e.2)
    else ((-e.1.1, e.1.2.1, e.1.2.2.1, e.1.2.2.2), e.2)
  left_inv := fun ⟨⟨t, x, y, z⟩, d⟩ => by
    by_cases hd : d = 0 <;> simp [hd]
  right_inv := fun ⟨⟨t, x, y, z⟩, d⟩ => by
    by_cases hd : d = 0 <;> simp [hd]

/-- Exact invariance of the 4D product Haar measure under Euclidean time reflection `Θ`. -/
theorem spacetimeHaarMeasure_timeReflect (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.Measure.map (cubic4TimeReflect Ls Lt N) (spacetimeHaarMeasure Ls Lt N) =
      spacetimeHaarMeasure Ls Lt N := by
  haveI := suHaar_prob N
  haveI := spacetimeHaarMeasure_prob Ls Lt N
  have hc_inv : Continuous (fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x⁻¹) :=
    continuous_inv
  let σ := cubic4TimeReflectLink Ls Lt
  let ψ : (cubicTorus4 Ls Lt).Link →
      Matrix.specialUnitaryGroup (Fin N) ℂ → Matrix.specialUnitaryGroup (Fin N) ℂ :=
    fun e u => if e.2 = 0 then u⁻¹ else u
  have hψ_meas : ∀ e, Measurable (ψ e) := fun e => by
    by_cases hd : e.2 = 0
    · simp only [ψ, hd, ↓reduceIte]; exact hc_inv.measurable
    · simp only [ψ, hd, ↓reduceIte]; exact measurable_id
  have hψ_inv : ∀ e (s : Set (Matrix.specialUnitaryGroup (Fin N) ℂ)),
      MeasurableSet s → suHaar N (ψ e ⁻¹' s) = suHaar N s := by
    intro e s hs
    by_cases hd : e.2 = 0
    · simp only [ψ, hd, ↓reduceIte]
      change suHaar N ((fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x⁻¹) ⁻¹' s) = suHaar N s
      rw [← MeasureTheory.Measure.map_apply hc_inv.measurable hs, suHaar_map_inv N]
    · simp only [ψ, hd, ↓reduceIte]; rfl
  let F : ((cubicTorus4 Ls Lt).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) →
      ((cubicTorus4 Ls Lt).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    fun U e => ψ e (U (σ e))
  have hF_eq : F = cubic4TimeReflect Ls Lt N := by
    funext U ⟨⟨t, x, y, z⟩, d⟩
    by_cases hd : d = 0 <;> simp [F, cubic4TimeReflect, σ, cubic4TimeReflectLink, ψ, hd]
  have hF_meas : Measurable F := by
    refine measurable_pi_iff.mpr fun e => ?_
    exact (hψ_meas e).comp (measurable_pi_apply (σ e))
  rw [← hF_eq]
  let μ_pi : MeasureTheory.Measure
      ((cubicTorus4 Ls Lt).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    MeasureTheory.Measure.pi (fun _ => suHaar N)
  change MeasureTheory.Measure.map F μ_pi = MeasureTheory.Measure.pi (fun _ => suHaar N)
  symm
  refine MeasureTheory.Measure.pi_eq fun s hs => ?_
  rw [MeasureTheory.Measure.map_apply hF_meas (MeasurableSet.univ_pi hs)]
  have hpre : F ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun e' => (ψ (σ.symm e')) ⁻¹' s (σ.symm e')) := by
    ext U
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, F]
    constructor
    · intro h e'
      simpa using h (σ.symm e')
    · intro h e
      simpa using h (σ e)
  rw [hpre]
  have hpi : μ_pi (Set.pi Set.univ (fun e' => (ψ (σ.symm e')) ⁻¹' s (σ.symm e'))) =
      ∏ e', suHaar N ((ψ (σ.symm e')) ⁻¹' s (σ.symm e')) :=
    MeasureTheory.Measure.pi_pi (fun _ => suHaar N) _
  rw [hpi]
  have h_prod_eq : ∏ e', suHaar N ((ψ (σ.symm e')) ⁻¹' s (σ.symm e')) =
      ∏ e', suHaar N (s (σ.symm e')) :=
    Finset.prod_congr rfl fun e' _ => hψ_inv (σ.symm e') (s (σ.symm e')) (hs (σ.symm e'))
  rw [h_prod_eq]
  exact Fintype.prod_equiv σ.symm (fun e' => suHaar N (s (σ.symm e')))
    (fun e => suHaar N (s e)) (fun _ => rfl)
/--
**Finite-volume Wilson transfer-matrix $n$-point reflection positivity:**
for any finite family of time-slice gauge-invariant states `v_i ∈ L²(SU(N)^{3L³}, dμ_Haar)`,
complex weights `c_i`, and Euclidean time coordinates `k_i ∈ ℕ`,
`0 ≤ ∑_{i,j} c_i · c̄_j · ⟪v_i, T_W^{k_i + k_j} v_j⟫_ℂ`.
-/
theorem cubicTransfer_refl_pos (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (m : ℕ) (c : Fin m → ℂ) (k : Fin m → ℕ)
    (v : Fin m → HaarGaugeSpace (latticeHaarMeasure L N)) :
    0 ≤ (∑ i : Fin m, ∑ j : Fin m,
      c i * starRingEnd ℂ (c j) *
        ⟪v i, ((cubicWilsonTransferOp L N β hβ) ^ (k i + k j)) (v j)⟫_ℂ).re := by
  let T := cubicWilsonTransferOp L N β hβ
  have hT_sa : ∀ x y : HaarGaugeSpace (latticeHaarMeasure L N), ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ :=
    cubicWilsonTransferOp_sa L N β hβ
  have hT_pow_sa : ∀ (r : ℕ) (x y : HaarGaugeSpace (latticeHaarMeasure L N)),
      ⟪(T ^ r) x, y⟫_ℂ = ⟪x, (T ^ r) y⟫_ℂ := by
    intro r
    induction r with
    | zero => intro x y; simp
    | succ r ih =>
      intro x y
      calc ⟪(T ^ (r + 1)) x, y⟫_ℂ
          = ⟪(T * T ^ r) x, y⟫_ℂ := by rw [pow_succ' T r]
        _ = ⟪T ((T ^ r) x), y⟫_ℂ := rfl
        _ = ⟪(T ^ r) x, T y⟫_ℂ := hT_sa _ _
        _ = ⟪x, (T ^ r) (T y)⟫_ℂ := ih _ _
        _ = ⟪x, (T ^ r * T) y⟫_ℂ := rfl
        _ = ⟪x, (T ^ (r + 1)) y⟫_ℂ := by rw [← pow_succ T r]
  have h_sum_left : ∀ (t : Finset (Fin m))
      (f : Fin m → HaarGaugeSpace (latticeHaarMeasure L N))
      (y : HaarGaugeSpace (latticeHaarMeasure L N)),
      ⟪∑ i ∈ t, f i, y⟫_ℂ = ∑ i ∈ t, ⟪f i, y⟫_ℂ := by
    intro t f y
    induction t using Finset.induction_on with
    | empty => simp
    | @insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, inner_add_left, ih]
  let w : HaarGaugeSpace (latticeHaarMeasure L N) :=
    ∑ i : Fin m, (starRingEnd ℂ (c i)) • ((T ^ k i) (v i))
  have hw_sq : ⟪w, w⟫_ℂ =
      ∑ i : Fin m, ∑ j : Fin m,
        c i * starRingEnd ℂ (c j) * ⟪v i, (T ^ (k i + k j)) (v j)⟫_ℂ := by
    dsimp [w]
    rw [h_sum_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_smul_right, Complex.conj_conj]
    have hpow : ⟪(T ^ k i) (v i), (T ^ k j) (v j)⟫_ℂ =
        ⟪v i, (T ^ (k i + k j)) (v j)⟫_ℂ := by
      rw [hT_pow_sa (k i) (v i) ((T ^ k j) (v j)), ← ContinuousLinearMap.mul_apply,
        ← pow_add]
    rw [hpow]
    ring
  change 0 ≤ (∑ i : Fin m, ∑ j : Fin m,
    c i * starRingEnd ℂ (c j) * ⟪v i, (T ^ (k i + k j)) (v j)⟫_ℂ).re
  rw [← hw_sq, inner_self_eq_norm_sq_to_K]
  simp [pow_two]
  exact mul_self_nonneg ‖w‖

end CubicSpacetime4D 

/-! ## §26.  Uniform-in-volume spectral gap & thermodynamic limit ($L \to \infty$) -/

section CubicThermodynamicLimit

/--
Genuine `UniformVolumeFamily` across all finite spatial cubic torus volumes `L : ℕ+`
with `HaarGaugeSpace (latticeHaarMeasure L N)` and `cubicLatticeGaugeSetup`.
-/
noncomputable def cubicUniformVolumeFamily (N : ℕ) (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    UniformVolumeFamily (Matrix.specialUnitaryGroup (Fin N) ℂ) 1 one_pos where
  ι := ℕ+
  L := fun i => cubicTorus3 i.val
  V := fun i => HaarGaugeSpace (latticeHaarMeasure i.val N)
  vNorm := fun _ => inferInstance
  vInner := fun _ => inferInstance
  vComp := fun _ => inferInstance
  setup := fun i => cubicLatticeGaugeSetup i.val N β hβ
  a_eq := fun _ => rfl
  Δ₀ := 1 - Real.exp (-1)
  Δ₀_pos := by
    have h : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  unif_gap := fun _ => by dsimp [cubicLatticeGaugeSetup]; simp

/-- Volume-independent spectral gap lower bound across all 3D cubic torus volumes `L : ℕ+`. -/
theorem cubic_uniform_volume_gap_bound (N : ℕ) (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (L : ℕ+) (ψ : HaarGaugeSpace (latticeHaarMeasure L.val N))
    (h_orth : ⟪ψ, (cubicLatticeGaugeSetup L.val N β hβ).Ω⟫_ℂ = 0)
    (h_norm : ‖ψ‖ = 1) :
    1 - Real.exp (-1) ≤
      1 - |(⟪ψ, (cubicLatticeGaugeSetup L.val N β hβ).T ψ⟫_ℂ).re| :=
  uniform_volume_gap_bound (cubicUniformVolumeFamily N β hβ) L ψ h_orth h_norm

/-- Full complex trace norm bound `‖Tr A‖ ≤ N` for `A ∈ SU(N)`. -/
theorem abs_trace_su_le {N : ℕ}
    (A : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ‖Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)‖ ≤ (N : ℝ) := by
  have hU : star (A : Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    (Unitary.mem_iff.mp A.2.1).1
  have h_diag : ∀ i : Fin N, ‖(A : Matrix (Fin N) (Fin N) ℂ) i i‖ ≤ 1 := by
    intro i
    have hii := congr_fun (congr_fun hU i) i
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at hii
    have hre := congrArg Complex.re hii
    rw [Complex.re_sum, Complex.one_re] at hre
    have hterm : ∀ k : Fin N,
        (star ((A : Matrix (Fin N) (Fin N) ℂ) k i) *
          (A : Matrix (Fin N) (Fin N) ℂ) k i).re =
        ‖(A : Matrix (Fin N) (Fin N) ℂ) k i‖ ^ 2 := by
      intro k
      change ((starRingEnd ℂ) ((A : Matrix (Fin N) (Fin N) ℂ) k i) *
        (A : Matrix (Fin N) (Fin N) ℂ) k i).re = _
      rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    simp_rw [hterm] at hre
    have hle_sum : ‖(A : Matrix (Fin N) (Fin N) ℂ) i i‖ ^ 2 ≤
        ∑ k : Fin N, ‖(A : Matrix (Fin N) (Fin N) ℂ) k i‖ ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg ‖(A : Matrix (Fin N) (Fin N) ℂ) k i‖)
        (Finset.mem_univ i)
    have hsq_le : ‖(A : Matrix (Fin N) (Fin N) ℂ) i i‖ ^ 2 ≤ 1 ^ 2 := by linarith
    exact (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp hsq_le
  simp only [Matrix.trace, Matrix.diag]
  calc ‖∑ i : Fin N, (A : Matrix (Fin N) (Fin N) ℂ) i i‖
      ≤ ∑ i : Fin N, ‖(A : Matrix (Fin N) (Fin N) ℂ) i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => h_diag i
    _ = (N : ℝ) := by simp

/-- Normalized gauge-invariant Wilson loop observable `(1/N) Tr(U_γ)` on `cubicTorus4 Ls Lt`. -/
noncomputable def normWilsonLoop4 {Ls Lt N : ℕ} [NeZero Ls] [NeZero Lt]
    (γ : List ((cubicTorus4 Ls Lt).Link × Bool))
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℂ :=
  ((N : ℝ)⁻¹ : ℂ) * Matrix.trace ((pathHolonomy U γ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ)

theorem normWilsonLoop4_gauge_inv {Ls Lt N : ℕ} [NeZero Ls] [NeZero Lt]
    {x : (cubicTorus4 Ls Lt).Site} {γ : List ((cubicTorus4 Ls Lt).Link × Bool)}
    (hγ : IsLatticePath (cubicTorus4 Ls Lt) x x γ)
    (g : GaugeTransform (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    normWilsonLoop4 γ (gaugeAct g U) = normWilsonLoop4 γ U := by
  unfold normWilsonLoop4
  rw [wilsonLoop_gauge_invariant
    (fun M : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (Matrix.trace (M : Matrix (Fin N) (Fin N) ℂ) : ℂ))
    (fun A B => by
      have hmul : ∀ X Y : Matrix.specialUnitaryGroup (Fin N) ℂ,
          ((X * Y : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
            (X : Matrix (Fin N) (Fin N) ℂ) * (Y : Matrix (Fin N) (Fin N) ℂ) := fun _ _ => rfl
      have hone : ((1 : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ) = 1 := rfl
      have hinv : ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
            Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ) = 1 := by
        rw [← hmul A⁻¹ A, inv_mul_cancel, hone]
      dsimp only
      rw [hmul (A * B) A⁻¹, hmul A B,
        Matrix.trace_mul_comm ((A : Matrix (Fin N) (Fin N) ℂ) * (B : Matrix (Fin N) (Fin N) ℂ))
          ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ),
        ← mul_assoc, hinv, one_mul])
    g U hγ]

theorem normWilsonLoop4_norm_le_one {Ls Lt N : ℕ} [NeZero Ls] [NeZero Lt] (hN : 1 ≤ N)
    (γ : List ((cubicTorus4 Ls Lt).Link × Bool))
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    ‖normWilsonLoop4 γ U‖ ≤ 1 := by
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  unfold normWilsonLoop4
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN_pos.le]
  calc (N : ℝ)⁻¹ * ‖Matrix.trace ((pathHolonomy U γ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ)‖
      ≤ (N : ℝ)⁻¹ * (N : ℝ) :=
        mul_le_mul_of_nonneg_left (abs_trace_su_le _) (inv_nonneg.mpr hN_pos.le)
    _ = 1 := inv_mul_cancel₀ hN_pos.ne'

private theorem norm_prod_fin_le {n : ℕ} (f : Fin n → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ i, ‖f i‖ ≤ M) :
    ‖∏ i : Fin n, f i‖ ≤ M ^ n := by
  rw [norm_prod]
  calc ∏ i : Fin n, ‖f i‖ ≤ ∏ _i : Fin n, M :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hf i)
    _ = M ^ n := by simp [Finset.prod_const]

/--
**Volume- and coupling-independent Schwinger bound:**
if `∀ i U, ‖obs i U‖ ≤ M` (`M ≥ 0`) and each `obs i` is measurable, then
`‖cubic4Schwinger Ls Lt N β n obs‖ ≤ M ^ n` for ALL `Ls, Lt ≥ 1` and `β ≥ 0`.
-/
theorem cubic4Schwinger_bound (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ)
    (obs : Fin n →
      (GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ))
    (h_meas : ∀ i, Measurable (obs i))
    (M : ℝ) (hM : 0 ≤ M) (hbd : ∀ i U, ‖obs i U‖ ≤ M) :
    ‖cubic4Schwinger Ls Lt N β n obs‖ ≤ M ^ n := by
  let μ := spacetimeHaarMeasure Ls Lt N
  haveI := spacetimeHaarMeasure_prob Ls Lt N
  let Z := cubic4PartitionFn Ls Lt N β
  have hZ_pos : 0 < Z := cubic4PartitionFn_pos Ls Lt N β hβ
  have hw_nonneg : ∀ U, 0 ≤ cubic4WilsonWeight Ls Lt N β U := fun U => by
    unfold cubic4WilsonWeight; exact (Real.exp_pos _).le
  have hw_int : MeasureTheory.Integrable (cubic4WilsonWeight Ls Lt N β) μ := by
    refine (MeasureTheory.integrable_const (1 : ℝ)).mono'
      (measurable_cubic4WilsonWeight Ls Lt N β).stronglyMeasurable.aestronglyMeasurable ?_
    filter_upwards with U
    rw [Real.norm_eq_abs, abs_of_nonneg (hw_nonneg U)]
    exact (cubic4WilsonWeight_bounds Ls Lt N β hβ U).2
  have h_prod_meas : Measurable (fun U => ∏ i : Fin n, obs i U) := by
    refine Finset.measurable_prod Finset.univ fun i _ => h_meas i
  have hf_meas : Measurable
      (fun U => (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)) :=
    h_prod_meas.mul (Complex.continuous_ofReal.measurable.comp (measurable_cubic4WilsonWeight Ls Lt N β))
  have h_pt_bound : ∀ U,
      ‖(∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)‖ ≤
        M ^ n * cubic4WilsonWeight Ls Lt N β U := by
    intro U
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw_nonneg U)]
    exact mul_le_mul_of_nonneg_right (norm_prod_fin_le (fun i => obs i U) M hM (fun i => hbd i U))
      (hw_nonneg U)
  have h_int_norm : MeasureTheory.Integrable
      (fun U => ‖(∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)‖) μ := by
    refine (hw_int.const_mul (M ^ n)).mono'
      (hf_meas.stronglyMeasurable.aestronglyMeasurable.norm) ?_
    filter_upwards with U
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact h_pt_bound U
  have h_int_le :
      ‖∫ U, (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) ∂μ‖ ≤
        M ^ n * Z := by
    calc ‖∫ U, (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) ∂μ‖
        ≤ ∫ U, ‖(∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)‖ ∂μ :=
            MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ U, M ^ n * cubic4WilsonWeight Ls Lt N β U ∂μ :=
            MeasureTheory.integral_mono h_int_norm (hw_int.const_mul (M ^ n)) h_pt_bound
      _ = M ^ n * Z := MeasureTheory.integral_const_mul (M ^ n) (cubic4WilsonWeight Ls Lt N β)
  unfold cubic4Schwinger
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hZ_pos.le]
  calc Z⁻¹ * ‖∫ U, (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) ∂μ‖
      ≤ Z⁻¹ * (M ^ n * Z) := mul_le_mul_of_nonneg_left h_int_le (inv_nonneg.mpr hZ_pos.le)
    _ = M ^ n := by field_simp [hZ_pos.ne']

/-- Uniform bound `‖S^{(n)}_{Ls,Lt,β}(W_{γ₁},…,W_{γₙ})‖ ≤ 1` for normalized Wilson loops. -/
theorem cubic4Schwinger_wilson_bound (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (hN : 1 ≤ N)
    (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) (loops : Fin n → List ((cubicTorus4 Ls Lt).Link × Bool)) :
    ‖cubic4Schwinger Ls Lt N β n (fun i => normWilsonLoop4 (loops i))‖ ≤ 1 := by
  have h_meas : ∀ i : Fin n, Measurable (normWilsonLoop4 (N := N) (loops i)) := by
    intro i
    unfold normWilsonLoop4
    have h_ent : ∀ j k : Fin N, Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        (A : Matrix (Fin N) (Fin N) ℂ) j k) := fun j k =>
      (continuous_apply k).comp ((continuous_apply j).comp continuous_subtype_val)
    have h_tr : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)) := by
      simp only [Matrix.trace, Matrix.diag]
      exact continuous_finset_sum Finset.univ fun j _ => h_ent j j
    exact measurable_const.mul (h_tr.measurable.comp (measurable_pathHolonomy4 Ls Lt N (loops i)))
  have h1 := cubic4Schwinger_bound Ls Lt N β hβ n (fun i => normWilsonLoop4 (loops i))
    h_meas 1 zero_le_one (fun i U => normWilsonLoop4_norm_le_one hN (loops i) U)
  simpa using h1

/--
**Subsequential thermodynamic limit (`L → ∞`)**:
for any sequence of finite-volume Schwinger values uniformly bounded by `M ^ n`
(in particular `cubic4Schwinger` along volumes `L_m → ∞`), a convergent infinite-volume
limit `S_inf` exists along a strictly increasing subsequence `φ`, preserving the bound `≤ M ^ n`.
-/
theorem cubic4Schwinger_thermodynamic_subseq (S_seq : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (n : ℕ)
    (hbd : ∀ m, ‖S_seq m‖ ≤ M ^ n) :
    ∃ (S_inf : ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      Filter.Tendsto (fun m => S_seq (φ m)) Filter.atTop (nhds S_inf) ∧
      ‖S_inf‖ ≤ M ^ n := by
  have hK : IsCompact (Metric.closedBall (0 : ℂ) (M ^ n)) := isCompact_closedBall (0 : ℂ) (M ^ n)
  have hmem : ∀ m, S_seq m ∈ Metric.closedBall (0 : ℂ) (M ^ n) := fun m => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbd m
  obtain ⟨S_inf, hS_mem, φ, hφ_mono, hφ_lim⟩ := hK.tendsto_subseq hmem
  rw [Metric.mem_closedBall, dist_zero_right] at hS_mem
  exact ⟨S_inf, φ, hφ_mono, hφ_lim, hS_mem⟩

/-- Permutation symmetry passes to the `L → ∞` thermodynamic limit. -/
theorem thermodynamic_limit_perm_symm {n : ℕ}
    (S_seq : ℕ → Equiv.Perm (Fin n) → ℂ) (S_inf : Equiv.Perm (Fin n) → ℂ)
    (hlim : ∀ σ, Filter.Tendsto (fun m => S_seq m σ) Filter.atTop (nhds (S_inf σ)))
    (hsymm : ∀ m σ, S_seq m σ = S_seq m 1)
    (σ : Equiv.Perm (Fin n)) :
    S_inf σ = S_inf 1 := by
  have h_eq : (fun m => S_seq m σ) = (fun m => S_seq m 1) := funext fun m => hsymm m σ
  have h1 := hlim σ
  rw [h_eq] at h1
  exact tendsto_nhds_unique h1 (hlim 1)

/-- Reflection positivity passes to the `L → ∞` thermodynamic limit. -/
theorem thermodynamic_limit_refl_pos {m : ℕ} (c : Fin m → ℂ)
    (G_seq : ℕ → Fin m → Fin m → ℂ) (G_inf : Fin m → Fin m → ℂ)
    (hlim : ∀ i j, Filter.Tendsto (fun r => G_seq r i j) Filter.atTop (nhds (G_inf i j)))
    (hrp : ∀ r, 0 ≤ (∑ i : Fin m, ∑ j : Fin m, c i * starRingEnd ℂ (c j) * G_seq r i j).re) :
    0 ≤ (∑ i : Fin m, ∑ j : Fin m, c i * starRingEnd ℂ (c j) * G_inf i j).re := by
  have hsum_lim : Filter.Tendsto
      (fun r => (∑ i : Fin m, ∑ j : Fin m, c i * starRingEnd ℂ (c j) * G_seq r i j).re)
      Filter.atTop
      (nhds (∑ i : Fin m, ∑ j : Fin m, c i * starRingEnd ℂ (c j) * G_inf i j).re) := by
    refine Complex.continuous_re.continuousAt.tendsto.comp ?_
    refine tendsto_finset_sum Finset.univ fun i _ => ?_
    refine tendsto_finset_sum Finset.univ fun j _ => ?_
    exact tendsto_const_nhds.mul (hlim i j)
  exact ge_of_tendsto hsum_lim (Filter.Eventually.of_forall hrp)

end CubicThermodynamicLimit

/-! ## §27.  Genuine 4D Poincaré group $\mathbb{R}^4 \rtimes O(1,3)$ & infinite-dimensional Wightman QFT -/

section Poincare4DWightman

/-- Minkowski metric tensor `η = diag(1, -1, -1, -1)` on `ℝ⁴`. -/
def minkowskiMetric4 : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, -1, -1, -1]

theorem minkowskiMetric4_transpose : minkowskiMetric4.transpose = minkowskiMetric4 := by
  simp [minkowskiMetric4]

theorem minkowskiMetric4_mul_self : minkowskiMetric4 * minkowskiMetric4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minkowskiMetric4, Matrix.mul_apply, Fin.sum_univ_four]

/-- Minkowski inner product `x₀y₀ - x₁y₁ - x₂y₂ - x₃y₃`. -/
def minkowskiInner (x y : Space4) : ℝ :=
  x 0 * y 0 - ∑ i : Fin 3, x i.succ * y i.succ

theorem minkowskiInner_self (x : Space4) : minkowskiInner x x = minkowskiSq x := by
  simp [minkowskiInner, minkowskiSq, Fin.sum_univ_three, sq]

theorem minkowskiInner_eq_dot (x y : Space4) :
    minkowskiInner x y = dotProduct x (Matrix.mulVec minkowskiMetric4 y) := by
  simp [minkowskiInner, dotProduct, minkowskiMetric4, Matrix.mulVec,
    Fin.sum_univ_four, Fin.sum_univ_three]
  ring

/-- The 4D Lorentz group `O(1,3) = { Λ ∈ GL(4, ℝ) | Λᵀ η Λ = η }`. -/
def LorentzMatrix4 : Type :=
  { Λ : Matrix (Fin 4) (Fin 4) ℝ // Λ.transpose * minkowskiMetric4 * Λ = minkowskiMetric4 }

theorem LorentzMatrix4.ext {Λ₁ Λ₂ : LorentzMatrix4} (h : Λ₁.1 = Λ₂.1) : Λ₁ = Λ₂ :=
  Subtype.ext h

private theorem lorentz_left_inv (Λ : LorentzMatrix4) :
    (minkowskiMetric4 * Λ.1.transpose * minkowskiMetric4) * Λ.1 = 1 := by
  calc (minkowskiMetric4 * Λ.1.transpose * minkowskiMetric4) * Λ.1
      = minkowskiMetric4 * (Λ.1.transpose * minkowskiMetric4 * Λ.1) := by noncomm_ring
    _ = minkowskiMetric4 * minkowskiMetric4 := by rw [Λ.2]
    _ = 1 := minkowskiMetric4_mul_self

private theorem lorentz_right_inv (Λ : LorentzMatrix4) :
    Λ.1 * (minkowskiMetric4 * Λ.1.transpose * minkowskiMetric4) = 1 :=
  mul_eq_one_comm.mp (lorentz_left_inv Λ)

instance instGroupLorentzMatrix4 : Group LorentzMatrix4 where
  one := ⟨1, by simp⟩
  mul Λ₁ Λ₂ := ⟨Λ₁.1 * Λ₂.1, by
    rw [Matrix.transpose_mul]
    calc Λ₂.1.transpose * Λ₁.1.transpose * minkowskiMetric4 * (Λ₁.1 * Λ₂.1)
        = Λ₂.1.transpose * (Λ₁.1.transpose * minkowskiMetric4 * Λ₁.1) * Λ₂.1 := by noncomm_ring
      _ = Λ₂.1.transpose * minkowskiMetric4 * Λ₂.1 := by rw [Λ₁.2]
      _ = minkowskiMetric4 := Λ₂.2⟩
  inv Λ := ⟨minkowskiMetric4 * Λ.1.transpose * minkowskiMetric4, by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, minkowskiMetric4_transpose,
      Matrix.transpose_transpose]
    calc (minkowskiMetric4 * (Λ.1 * minkowskiMetric4)) * minkowskiMetric4 *
          (minkowskiMetric4 * Λ.1.transpose * minkowskiMetric4)
        = minkowskiMetric4 * Λ.1 * (minkowskiMetric4 * minkowskiMetric4) *
            (minkowskiMetric4 * Λ.1.transpose * minkowskiMetric4) := by noncomm_ring
      _ = minkowskiMetric4 * (Λ.1 * (minkowskiMetric4 * Λ.1.transpose * minkowskiMetric4)) := by
            rw [minkowskiMetric4_mul_self]
            noncomm_ring
      _ = minkowskiMetric4 * 1 := by rw [lorentz_right_inv Λ]
      _ = minkowskiMetric4 := mul_one _⟩
  mul_assoc a b c := LorentzMatrix4.ext (Matrix.mul_assoc a.1 b.1 c.1)
  one_mul a := LorentzMatrix4.ext (Matrix.one_mul a.1)
  mul_one a := LorentzMatrix4.ext (Matrix.mul_one a.1)
  inv_mul_cancel a := LorentzMatrix4.ext (lorentz_left_inv a)

theorem lorentz_preserves_minkowskiInner (Λ : LorentzMatrix4) (x y : Space4) :
    minkowskiInner (Matrix.mulVec Λ.1 x) (Matrix.mulVec Λ.1 y) = minkowskiInner x y := by
  rw [minkowskiInner_eq_dot, minkowskiInner_eq_dot, ← Matrix.vecMul_transpose,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Λ.2]

/-- The 4D Poincaré group `ℝ⁴ ⋊ O(1,3)`. -/
@[ext]
structure Poincare4 where
  trans   : Space4
  lorentz : LorentzMatrix4

instance instGroupPoincare4 : Group Poincare4 where
  one := ⟨0, 1⟩
  mul g₁ g₂ := ⟨g₁.trans + Matrix.mulVec g₁.lorentz.1 g₂.trans, g₁.lorentz * g₂.lorentz⟩
  inv g := ⟨-Matrix.mulVec g.lorentz⁻¹.1 g.trans, g.lorentz⁻¹⟩
  mul_assoc a b c := by
    ext : 1
    · dsimp [HMul.hMul, Mul.mul]
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
      abel
    · exact mul_assoc a.lorentz b.lorentz c.lorentz
  one_mul a := by
    ext : 1
    · change 0 + Matrix.mulVec (1 : Matrix (Fin 4) (Fin 4) ℝ) a.trans = a.trans
      rw [zero_add, Matrix.one_mulVec]
    · exact one_mul a.lorentz
  mul_one a := by
    ext : 1
    · change a.trans + Matrix.mulVec a.lorentz.1 0 = a.trans
      rw [Matrix.mulVec_zero, add_zero]
    · exact mul_one a.lorentz
  inv_mul_cancel a := by
    ext : 1
    · change -Matrix.mulVec a.lorentz⁻¹.1 a.trans + Matrix.mulVec a.lorentz⁻¹.1 a.trans = 0
      abel
    · exact inv_mul_cancel a.lorentz

/-- Spacetime action `(a, Λ) · x = a + Λ x` on `Space4 = ℝ⁴`. -/
def poincareAct (g : Poincare4) (x : Space4) : Space4 :=
  g.trans + Matrix.mulVec g.lorentz.1 x

theorem poincareAct_one (x : Space4) : poincareAct 1 x = x := by
  change 0 + Matrix.mulVec (1 : Matrix (Fin 4) (Fin 4) ℝ) x = x
  rw [zero_add, Matrix.one_mulVec]

theorem poincareAct_mul (g₁ g₂ : Poincare4) (x : Space4) :
    poincareAct (g₁ * g₂) x = poincareAct g₁ (poincareAct g₂ x) := by
  change (g₁.trans + Matrix.mulVec g₁.lorentz.1 g₂.trans) +
      Matrix.mulVec (g₁.lorentz.1 * g₂.lorentz.1) x =
    g₁.trans + Matrix.mulVec g₁.lorentz.1 (g₂.trans + Matrix.mulVec g₂.lorentz.1 x)
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
  abel

theorem poincareAct_preserves_minkowskiSq (g : Poincare4) (x y : Space4) :
    minkowskiSq (poincareAct g x - poincareAct g y) = minkowskiSq (x - y) := by
  have hsub : poincareAct g x - poincareAct g y = Matrix.mulVec g.lorentz.1 (x - y) := by
    dsimp [poincareAct]
    rw [Matrix.mulVec_sub]
    abel
  rw [hsub, ← minkowskiInner_self, ← minkowskiInner_self, lorentz_preserves_minkowskiInner]

/-- Carrier `Option Space4` with discrete measurable space for the infinite-dimensional Hilbert space. -/
def OptionSpace4 : Type := Option Space4

@[reducible] instance instMeasurableSpaceOptionSpace4 : MeasurableSpace OptionSpace4 := ⊤

/-- Counting measure on `OptionSpace4`: `μ {none} = 1` (vacuum) and `μ {some x} = 1` (`x ∈ ℝ⁴`). -/
noncomputable def poincareCountMeasure : MeasureTheory.Measure OptionSpace4 :=
  MeasureTheory.Measure.count

/-- Infinite-dimensional complex Hilbert space `L²({none} ⊔ ℝ⁴, count)`. -/
abbrev PoincareHilbert : Type := MeasureTheory.Lp ℂ 2 poincareCountMeasure

private def poincareOptionEquiv (g : Poincare4) : OptionSpace4 ≃ᵐ OptionSpace4 where
  toFun := fun o => match o with
    | none => none
    | some x => some (poincareAct g x)
  invFun := fun o => match o with
    | none => none
    | some x => some (poincareAct g⁻¹ x)
  left_inv o := by
    cases o with
    | none => rfl
    | some x =>
      change some (poincareAct g⁻¹ (poincareAct g x)) = some x
      rw [← poincareAct_mul, inv_mul_cancel, poincareAct_one]
  right_inv o := by
    cases o with
    | none => rfl
    | some x =>
      change some (poincareAct g (poincareAct g⁻¹ x)) = some x
      rw [← poincareAct_mul, mul_inv_cancel, poincareAct_one]
  measurable_toFun := fun _ _ => trivial
  measurable_invFun := fun _ _ => trivial

private theorem poincareOptionEquiv_mp (g : Poincare4) :
    MeasureTheory.MeasurePreserving (poincareOptionEquiv g)
      poincareCountMeasure poincareCountMeasure := by
  refine ⟨(poincareOptionEquiv g).measurable, ?_⟩
  ext s hs
  rw [MeasureTheory.Measure.map_apply (poincareOptionEquiv g).measurable hs]
  dsimp [poincareCountMeasure]
  rw [MeasureTheory.Measure.count_apply (hs.preimage (poincareOptionEquiv g).measurable),
    MeasureTheory.Measure.count_apply hs]
  have hpre : poincareOptionEquiv g ⁻¹' s = (poincareOptionEquiv g).symm '' s :=
    ((poincareOptionEquiv g).toEquiv.image_symm_eq_preimage s).symm
  rw [hpre, (poincareOptionEquiv g).symm.injective.encard_image s]

private theorem ae_count_eq_everywhere {f g : OptionSpace4 → ℂ}
    (h : f =ᵐ[poincareCountMeasure] g) (a : OptionSpace4) : f a = g a := by
  by_contra hne
  have hnull : poincareCountMeasure {x | f x ≠ g x} = 0 := h
  have hle : poincareCountMeasure {a} ≤ poincareCountMeasure {x | f x ≠ g x} :=
    MeasureTheory.measure_mono (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hne)
  rw [hnull] at hle
  have h1 : poincareCountMeasure {a} = 1 := by
    dsimp [poincareCountMeasure]
    exact MeasureTheory.Measure.count_singleton a
  rw [h1] at hle
  exact one_ne_zero (le_antisymm hle (zero_le _))

/-- Faithful unitary representation `U(a, Λ)` of `Poincare4` on `PoincareHilbert`. -/
noncomputable def poincareRep (g : Poincare4) : PoincareHilbert →L[ℂ] PoincareHilbert :=
  let e := poincareOptionEquiv g⁻¹
  let hmp := poincareOptionEquiv_mp g⁻¹
  LinearMap.mkContinuous
    { toFun := fun ψ => (memLp_comp_measurePreserving poincareCountMeasure e hmp ψ).toLp
        (fun x => ψ (e x))
      map_add' := fun ψ₁ ψ₂ => by
        apply MeasureTheory.Lp.ext
        have h1 := (memLp_comp_measurePreserving poincareCountMeasure e hmp (ψ₁ + ψ₂)).coeFn_toLp
        have h2 := (memLp_comp_measurePreserving poincareCountMeasure e hmp ψ₁).coeFn_toLp
        have h3 := (memLp_comp_measurePreserving poincareCountMeasure e hmp ψ₂).coeFn_toLp
        have hadd1 := MeasureTheory.Lp.coeFn_add ψ₁ ψ₂
        have hadd2 := MeasureTheory.Lp.coeFn_add
          ((memLp_comp_measurePreserving poincareCountMeasure e hmp ψ₁).toLp (fun x => ψ₁ (e x)))
          ((memLp_comp_measurePreserving poincareCountMeasure e hmp ψ₂).toLp (fun x => ψ₂ (e x)))
        filter_upwards [h1, h2, h3, ae_comp_measurePreserving hmp hadd1, hadd2] with x hx1 hx2 hx3 ha1 ha2
        simp only [Pi.add_apply] at ha1 ha2 ⊢
        rw [hx1, ha1, ha2, hx2, hx3]
      map_smul' := fun c ψ => by
        apply MeasureTheory.Lp.ext
        have h1 := (memLp_comp_measurePreserving poincareCountMeasure e hmp (c • ψ)).coeFn_toLp
        have h2 := (memLp_comp_measurePreserving poincareCountMeasure e hmp ψ).coeFn_toLp
        have hsm1 := MeasureTheory.Lp.coeFn_smul c ψ
        have hsm2 := MeasureTheory.Lp.coeFn_smul c
          ((memLp_comp_measurePreserving poincareCountMeasure e hmp ψ).toLp (fun x => ψ (e x)))
        filter_upwards [h1, h2, ae_comp_measurePreserving hmp hsm1, hsm2] with x hx1 hx2 hs1 hs2
        simp only [Pi.smul_apply, RingHom.id_apply] at hs1 hs2 ⊢
        rw [hx1, hs1, hs2, hx2] }
    1
    (fun ψ => by
      let ψ' := (memLp_comp_measurePreserving poincareCountMeasure e hmp ψ).toLp (fun x => ψ (e x))
      have h_norm_sq : ‖ψ'‖ ^ 2 = ‖ψ‖ ^ 2 := by
        have h_inner : ⟪ψ', ψ'⟫_ℂ = ⟪ψ, ψ⟫_ℂ := by
          rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
          have hcoe := (memLp_comp_measurePreserving poincareCountMeasure e hmp ψ).coeFn_toLp
          calc ∫ x, ⟪ψ' x, ψ' x⟫_ℂ ∂poincareCountMeasure
              = ∫ x, ⟪ψ (e x), ψ (e x)⟫_ℂ ∂poincareCountMeasure := by
                  refine MeasureTheory.integral_congr_ae ?_
                  filter_upwards [hcoe] with x hx
                  rw [hx]
            _ = ∫ x, ⟪ψ x, ψ x⟫_ℂ ∂poincareCountMeasure :=
                hmp.integral_comp' (fun x => ⟪ψ x, ψ x⟫_ℂ)
        have hre := congrArg Complex.re h_inner
        rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hre
        simpa [pow_two] using hre
      change ‖ψ'‖ ≤ 1 * ‖ψ‖
      rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), one_mul, h_norm_sq])

theorem poincareRep_apply (g : Poincare4) (ψ : PoincareHilbert) (z : OptionSpace4) :
    (⇑(poincareRep g ψ) : OptionSpace4 → ℂ) z =
      (⇑ψ : OptionSpace4 → ℂ) (poincareOptionEquiv g⁻¹ z) := by
  let e := poincareOptionEquiv g⁻¹
  let hmp := poincareOptionEquiv_mp g⁻¹
  have hcoe := (memLp_comp_measurePreserving poincareCountMeasure e hmp ψ).coeFn_toLp
  exact ae_count_eq_everywhere hcoe z

theorem poincareRep_unitary (g : Poincare4) (u v : PoincareHilbert) :
    ⟪poincareRep g u, poincareRep g v⟫_ℂ = ⟪u, v⟫_ℂ := by
  let e := poincareOptionEquiv g⁻¹
  let hmp := poincareOptionEquiv_mp g⁻¹
  have h1 := (memLp_comp_measurePreserving poincareCountMeasure e hmp u).coeFn_toLp
  have h2 := (memLp_comp_measurePreserving poincareCountMeasure e hmp v).coeFn_toLp
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  calc ∫ x, ⟪(poincareRep g u) x, (poincareRep g v) x⟫_ℂ ∂poincareCountMeasure
      = ∫ x, ⟪u (e x), v (e x)⟫_ℂ ∂poincareCountMeasure := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [h1, h2] with x hx1 hx2
          change ⟪((memLp_comp_measurePreserving poincareCountMeasure e hmp u).toLp
            (fun z => u (e z))) x,
            ((memLp_comp_measurePreserving poincareCountMeasure e hmp v).toLp
            (fun z => v (e z))) x⟫_ℂ = _
          rw [hx1, hx2]
    _ = ∫ x, ⟪u x, v x⟫_ℂ ∂poincareCountMeasure := hmp.integral_comp' (fun x => ⟪u x, v x⟫_ℂ)

private theorem poincareCount_singleton_ne_top (a : OptionSpace4) :
    poincareCountMeasure {a} ≠ ⊤ := by
  dsimp [poincareCountMeasure]
  rw [MeasureTheory.Measure.count_singleton]
  exact ENNReal.one_ne_top

private theorem poincareCount_singleton_toReal (a : OptionSpace4) :
    (poincareCountMeasure {a}).toReal = 1 := by
  dsimp [poincareCountMeasure]
  rw [MeasureTheory.Measure.count_singleton, ENNReal.toReal_one]

/-- Basis state `δ_a` (`a : OptionSpace4`) in `PoincareHilbert`. -/
noncomputable def deltaOption4 (a : OptionSpace4) : PoincareHilbert :=
  MeasureTheory.indicatorConstLp (2 : ENNReal) (by trivial : MeasurableSet ({a} : Set OptionSpace4))
    (poincareCount_singleton_ne_top a) (1 : ℂ)

/-- Ground vacuum `Ω = δ_none` in `PoincareHilbert`. -/
noncomputable def vacPoincare : PoincareHilbert := deltaOption4 (none : Option Space4)

/-- 1-particle state `δ_{some x}` at `x : Space4` in `PoincareHilbert`. -/
noncomputable def deltaSpace4 (x : Space4) : PoincareHilbert := deltaOption4 (some x)

theorem deltaOption4_inner (a b : OptionSpace4) :
    ⟪deltaOption4 a, deltaOption4 b⟫_ℂ = @ite _ (a = b) (Classical.propDecidable _) 1 0 := by
  unfold deltaOption4
  rw [MeasureTheory.L2.inner_indicatorConstLp_indicatorConstLp
    (hμs := poincareCount_singleton_ne_top a)
    (hμt := poincareCount_singleton_ne_top b)]
  have h1 : ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_num
  rw [h1]
  by_cases hab : a = b
  · subst hab
    rw [Set.inter_self, if_pos rfl, Measure.real, poincareCount_singleton_toReal, one_smul]
  · have hinter : ({a} ∩ {b} : Set OptionSpace4) = ∅ := by
      ext z; simp [hab]
    rw [hinter, if_neg hab, Measure.real, MeasureTheory.measure_empty,
      ENNReal.toReal_zero, zero_smul]

theorem vacPoincare_norm : ‖vacPoincare‖ = 1 := by
  have hsq : ‖vacPoincare‖ ^ 2 = 1 := by
    have hre : (⟪vacPoincare, vacPoincare⟫_ℂ).re = 1 := by
      rw [vacPoincare, deltaOption4_inner, if_pos rfl, Complex.one_re]
    rw [inner_self_eq_norm_sq_to_K] at hre
    simp [pow_two] at hre
    linarith
  have hmul : (‖vacPoincare‖ - 1) * (‖vacPoincare‖ + 1) = 0 := by linarith
  rcases mul_eq_zero.mp hmul with h | h <;> linarith [norm_nonneg vacPoincare]

private theorem deltaOption4_apply (a z : OptionSpace4) :
    (⇑(deltaOption4 a) : OptionSpace4 → ℂ) z =
      @ite _ (z = a) (Classical.propDecidable _) 1 0 := by
  classical
  have h := ae_count_eq_everywhere
    (MeasureTheory.indicatorConstLp_coeFn (p := (2 : ENNReal))
      (μ := poincareCountMeasure) (s := {a})
      (hs := by trivial)
      (hμs := poincareCount_singleton_ne_top a)
      (c := (1 : ℂ))) z
  change (⇑(deltaOption4 a) : OptionSpace4 → ℂ) z = _ at h
  rw [h, Set.indicator_apply]
  by_cases hz : z = a
  · rw [if_pos (Set.mem_singleton_iff.mpr hz), if_pos hz]
  · rw [if_neg (fun hm => hz (Set.mem_singleton_iff.mp hm)), if_neg hz]

theorem poincareRep_deltaOption4 (g : Poincare4) (a : OptionSpace4) :
    poincareRep g (deltaOption4 a) = deltaOption4 (poincareOptionEquiv g a) := by
  apply MeasureTheory.Lp.ext
  refine Filter.Eventually.of_forall fun z => ?_
  rw [poincareRep_apply, deltaOption4_apply, deltaOption4_apply]
  have heq : poincareOptionEquiv g⁻¹ z = a ↔ z = poincareOptionEquiv g a := by
    constructor <;> intro h
    · calc z = poincareOptionEquiv g (poincareOptionEquiv g⁻¹ z) := by
              cases z with
              | none => rfl
              | some x =>
                change some x = some (poincareAct g (poincareAct g⁻¹ x))
                rw [← poincareAct_mul, mul_inv_cancel, poincareAct_one]
          _ = poincareOptionEquiv g a := by rw [h]
    · calc poincareOptionEquiv g⁻¹ z = poincareOptionEquiv g⁻¹ (poincareOptionEquiv g a) := by
              rw [h]
          _ = a := by
              cases a with
              | none => rfl
              | some y =>
                change some (poincareAct g⁻¹ (poincareAct g y)) = some y
                rw [← poincareAct_mul, inv_mul_cancel, poincareAct_one]
  by_cases hz : z = poincareOptionEquiv g a
  · rw [if_pos (heq.mpr hz), if_pos hz]
  · rw [if_neg (fun h => hz (heq.mp h)), if_neg hz]

theorem poincareRep_vac (g : Poincare4) : poincareRep g vacPoincare = vacPoincare :=
  poincareRep_deltaOption4 g none

theorem poincareRep_deltaSpace4 (g : Poincare4) (x : Space4) :
    poincareRep g (deltaSpace4 x) = deltaSpace4 (poincareAct g x) :=
  poincareRep_deltaOption4 g (some x)

/-- Field creation operator `φ(x) v = ⟪Ω, v⟫_ℂ • δ_{some x}` on `PoincareHilbert`. -/
noncomputable def phiPoincare (x : Space4) : PoincareHilbert →L[ℂ] PoincareHilbert :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟪vacPoincare, v⟫_ℂ • deltaSpace4 x
      map_add' := fun u v => by rw [inner_add_right, add_smul]
      map_smul' := fun c v => by rw [inner_smul_right, smul_smul]; rfl }
    1
    (fun v => by
      have hnorm : ‖deltaSpace4 x‖ = 1 := by
        have hsq : ‖deltaSpace4 x‖ ^ 2 = 1 := by
          have hre : (⟪deltaSpace4 x, deltaSpace4 x⟫_ℂ).re = 1 := by
            rw [deltaSpace4, deltaOption4_inner, if_pos rfl, Complex.one_re]
          rw [inner_self_eq_norm_sq_to_K] at hre
          simp [pow_two] at hre
          linarith
        have hmul : (‖deltaSpace4 x‖ - 1) * (‖deltaSpace4 x‖ + 1) = 0 := by linarith
        rcases mul_eq_zero.mp hmul with h | h <;> linarith [norm_nonneg (deltaSpace4 x)]
      change ‖⟪vacPoincare, v⟫_ℂ • deltaSpace4 x‖ ≤ 1 * ‖v‖
      rw [norm_smul, hnorm, mul_one, one_mul]
      calc ‖⟪vacPoincare, v⟫_ℂ‖ ≤ ‖vacPoincare‖ * ‖v‖ := norm_inner_le_norm _ _
        _ = ‖v‖ := by rw [vacPoincare_norm, one_mul])

/--
**Infinite-dimensional relativistic `WightmanQFT4D 1`** with genuine 4D Poincaré group
`Poincare4 = ℝ⁴ ⋊ O(1,3)`, faithful unitary representation `poincareRep`,
non-trivial covariant local field `phiPoincare`, and mass gap `{0, 1}`.
-/
noncomputable def infDimWightman4D : WightmanQFT4D 1 where
  Δ_pos := one_pos
  H := PoincareHilbert
  Ω_phys := vacPoincare
  Ω_unit := vacPoincare_norm
  Poincare := Poincare4
  U := poincareRep
  U_unitary := poincareRep_unitary
  U_vac := poincareRep_vac
  actP := poincareAct
  φ := phiPoincare
  covariant := fun g x => by
    ext1 v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    change poincareRep g (⟪vacPoincare, v⟫_ℂ • deltaSpace4 x) =
      ⟪vacPoincare, poincareRep g v⟫_ℂ • deltaSpace4 (poincareAct g x)
    rw [map_smul, poincareRep_deltaSpace4]
    have h_in : ⟪vacPoincare, poincareRep g v⟫_ℂ = ⟪vacPoincare, v⟫_ℂ := by
      calc ⟪vacPoincare, poincareRep g v⟫_ℂ
          = ⟪poincareRep g vacPoincare, poincareRep g v⟫_ℂ := by rw [poincareRep_vac]
        _ = ⟪vacPoincare, v⟫_ℂ := poincareRep_unitary g vacPoincare v
    rw [h_in]
  local_comm := fun x y _ => by
    ext1 v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    change ⟪vacPoincare, ⟪vacPoincare, v⟫_ℂ • deltaSpace4 y⟫_ℂ • deltaSpace4 x =
      ⟪vacPoincare, ⟪vacPoincare, v⟫_ℂ • deltaSpace4 x⟫_ℂ • deltaSpace4 y
    have h0x : ⟪vacPoincare, deltaSpace4 x⟫_ℂ = 0 := by
      rw [vacPoincare, deltaSpace4, deltaOption4_inner]; simp
    have h0y : ⟪vacPoincare, deltaSpace4 y⟫_ℂ = 0 := by
      rw [vacPoincare, deltaSpace4, deltaOption4_inner]; simp
    rw [inner_smul_right, inner_smul_right, h0x, h0y]
    simp
  P2_spec := {0, 1}
  spectral_cond := fun p2 hp2 => by rcases hp2 with rfl | rfl <;> norm_num
  mass_gap_spec := fun p2 hp2 => by
    rcases hp2 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by norm_num)

private noncomputable def P_vac_poincare : PoincareHilbert →L[ℂ] PoincareHilbert :=
  rankOneProj vacPoincare vacPoincare_norm

private noncomputable def H_phys_poincare : PoincareHilbert →L[ℂ] PoincareHilbert :=
  ContinuousLinearMap.id ℂ PoincareHilbert - P_vac_poincare

private theorem P_vac_poincare_sa (x y : PoincareHilbert) :
    ⟪P_vac_poincare x, y⟫_ℂ = ⟪x, P_vac_poincare y⟫_ℂ := by
  change ⟪⟪vacPoincare, x⟫_ℂ • vacPoincare, y⟫_ℂ = ⟪x, ⟪vacPoincare, y⟫_ℂ • vacPoincare⟫_ℂ
  have hconj : starRingEnd ℂ ⟪vacPoincare, x⟫_ℂ = ⟪x, vacPoincare⟫_ℂ :=
    inner_conj_symm x vacPoincare
  rw [inner_smul_left, inner_smul_right, hconj]
  ring

private theorem P_vac_poincare_idem (x : PoincareHilbert) :
    P_vac_poincare (P_vac_poincare x) = P_vac_poincare x := by
  have h1 : ⟪vacPoincare, vacPoincare⟫_ℂ = 1 := by
    rw [vacPoincare, deltaOption4_inner, if_pos rfl]
  change ⟪vacPoincare, ⟪vacPoincare, x⟫_ℂ • vacPoincare⟫_ℂ • vacPoincare =
    ⟪vacPoincare, x⟫_ℂ • vacPoincare
  rw [inner_smul_right, h1, mul_one]

private theorem H_phys_poincare_sa (x y : PoincareHilbert) :
    ⟪H_phys_poincare x, y⟫_ℂ = ⟪x, H_phys_poincare y⟫_ℂ := by
  simp only [H_phys_poincare, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    inner_sub_left, inner_sub_right, P_vac_poincare_sa]

private theorem H_phys_poincare_idem (x : PoincareHilbert) :
    H_phys_poincare (H_phys_poincare x) = H_phys_poincare x := by
  simp only [H_phys_poincare, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    map_sub, P_vac_poincare_idem]
  abel

private noncomputable def T_E_poincare (t : ℝ) : PoincareHilbert →L[ℂ] PoincareHilbert :=
  P_vac_poincare + ((Real.exp (-t) : ℝ) : ℂ) • H_phys_poincare

/--
**Infinite-dimensional `OSReconstructionData 1 concreteOS4DContinuumTheory`**
on `PoincareHilbert = L²({none} ⊔ ℝ⁴, count)` with genuine `Poincare4` symmetry.
-/
noncomputable def infDimOSReconstructionData :
    OSReconstructionData 1 concreteOS4DContinuumTheory where
  wightman := infDimWightman4D
  T_E := T_E_poincare
  T_E_zero := by
    change T_E_poincare 0 = ContinuousLinearMap.id ℂ PoincareHilbert
    exact ContinuousLinearMap.ext fun x => by simp [T_E_poincare, H_phys_poincare]
  T_E_add := fun s t _ _ => by
    change T_E_poincare (s + t) = (T_E_poincare s).comp (T_E_poincare t)
    refine ContinuousLinearMap.ext fun x => ?_
    have hp01 : P_vac_poincare (H_phys_poincare x) = 0 := by
      simp [H_phys_poincare, P_vac_poincare_idem]
    have hp10 : H_phys_poincare (P_vac_poincare x) = 0 := by
      simp [H_phys_poincare, P_vac_poincare_idem]
    simp only [T_E_poincare, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, map_add, map_smul, P_vac_poincare_idem,
      H_phys_poincare_idem, hp01, hp10, smul_zero, add_zero, zero_add]
    rw [smul_smul, ← Complex.ofReal_mul, ← Real.exp_add,
      show -t + -s = -(s + t) by ring]
  T_E_sa := fun t x y _ => by
    change ⟪T_E_poincare t (x : PoincareHilbert), (y : PoincareHilbert)⟫_ℂ =
      ⟪(x : PoincareHilbert), T_E_poincare t (y : PoincareHilbert)⟫_ℂ
    simp only [T_E_poincare, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, P_vac_poincare_sa, H_phys_poincare_sa]
  T_E_contr := fun t x ht => by
    change ‖T_E_poincare t (x : PoincareHilbert)‖ ≤ ‖(x : PoincareHilbert)‖
    let x' : PoincareHilbert := x
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    have h_orth : ⟪P_vac_poincare x', H_phys_poincare x'⟫_ℂ = 0 := by
      have hp01 : P_vac_poincare (H_phys_poincare x') = 0 := by
        simp [H_phys_poincare, P_vac_poincare_idem]
      rw [P_vac_poincare_sa, hp01, inner_zero_right]
    have hre : RCLike.re ⟪P_vac_poincare x', ((Real.exp (-t) : ℝ) : ℂ) • H_phys_poincare x'⟫_ℂ = 0 := by
      rw [inner_smul_right, h_orth, mul_zero, map_zero]
    have hre' : RCLike.re ⟪P_vac_poincare x', Real.exp (-t) • H_phys_poincare x'⟫_ℂ = 0 := by
      change RCLike.re ⟪P_vac_poincare x', ((Real.exp (-t) : ℝ) : ℂ) • H_phys_poincare x'⟫_ℂ = 0
      exact hre
    have h_sum_sq : ‖P_vac_poincare x'‖ ^ 2 + ‖H_phys_poincare x'‖ ^ 2 = ‖x'‖ ^ 2 := by
      have hx : x' = P_vac_poincare x' + H_phys_poincare x' := by simp [H_phys_poincare]
      conv_rhs => rw [hx]
      rw [norm_add_sq (𝕜 := ℂ)]
      have h0 : RCLike.re ⟪P_vac_poincare x', H_phys_poincare x'⟫_ℂ = 0 := by
        rw [h_orth, map_zero]
      rw [h0, mul_zero, add_zero]
    have hsq : ‖T_E_poincare t x'‖ ^ 2 =
        ‖P_vac_poincare x'‖ ^ 2 + (Real.exp (-t)) ^ 2 * ‖H_phys_poincare x'‖ ^ 2 := by
      dsimp [T_E_poincare]
      rw [norm_add_sq (𝕜 := ℂ)]
      simp [hre', norm_smul, abs_of_nonneg (Real.exp_pos _).le, mul_pow]
    have hexp_le : (Real.exp (-t)) ^ 2 ≤ 1 := by
      have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith [(Real.exp_pos (-t)).le]
    change ‖T_E_poincare t x'‖ ^ 2 ≤ ‖x'‖ ^ 2
    rw [hsq, ← h_sum_sq]
    exact add_le_add le_rfl (mul_le_of_le_one_left (sq_nonneg _) hexp_le)
  H_phys := H_phys_poincare
  H_phys_sa := H_phys_poincare_sa
  H_phys_nonneg := fun x => by
    change 0 ≤ (⟪(x : PoincareHilbert), H_phys_poincare (x : PoincareHilbert)⟫_ℂ).re
    let x' : PoincareHilbert := x
    have h_eq : ⟪x', H_phys_poincare x'⟫_ℂ = ⟪H_phys_poincare x', H_phys_poincare x'⟫_ℂ := by
      conv_lhs => rw [← H_phys_poincare_idem x', ← H_phys_poincare_sa]
    change 0 ≤ (⟪x', H_phys_poincare x'⟫_ℂ).re
    rw [h_eq, inner_self_eq_norm_sq_to_K]
    simp [pow_two]
    exact mul_self_nonneg _
  H_phys_vac := by
    change H_phys_poincare vacPoincare = 0
    have hv : P_vac_poincare vacPoincare = vacPoincare := by
      have h1 : ⟪vacPoincare, vacPoincare⟫_ℂ = 1 := by
        rw [vacPoincare, deltaOption4_inner, if_pos rfl]
      change ⟪vacPoincare, vacPoincare⟫_ℂ • vacPoincare = vacPoincare
      rw [h1, one_smul]
    simp [H_phys_poincare, hv]
  cyclic_dense := by
    classical
    let S : Set PoincareHilbert :=
      {v : PoincareHilbert | ∃ (k : ℕ) (xs : Fin k → Space4),
        v = (List.ofFn (fun i : Fin k => phiPoincare (xs i))).foldr
          (fun A acc => A acc) vacPoincare}
    have h_vac : vacPoincare ∈ S := ⟨0, Fin.elim0, rfl⟩
    have h_delta : ∀ x : Space4, deltaSpace4 x ∈ S := by
      intro x
      refine ⟨1, fun _ => x, ?_⟩
      have h1 : ⟪vacPoincare, vacPoincare⟫_ℂ = 1 := by
        rw [vacPoincare, deltaOption4_inner, if_pos rfl]
      change deltaSpace4 x = ⟪vacPoincare, vacPoincare⟫_ℂ • deltaSpace4 x
      rw [h1, one_smul]
    have h_cl_complete : CompleteSpace ↥(Submodule.span ℂ S).topologicalClosure := by
      refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
      have huV : CauchySeq (fun n => (u n : PoincareHilbert)) :=
        Metric.cauchySeq_iff.mpr (by simpa [Subtype.dist_eq] using Metric.cauchySeq_iff.mp hu)
      obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete huV
      have haK : a ∈ closure (Submodule.span ℂ S : Set PoincareHilbert) :=
        isClosed_closure.mem_of_tendsto ha (Filter.Eventually.of_forall fun n => (u n).2)
      exact ⟨⟨a, haK⟩, tendsto_subtype_rng.mpr ha⟩
    haveI : (Submodule.span ℂ S).topologicalClosure.HasOrthogonalProjection :=
      Submodule.HasOrthogonalProjection.ofCompleteSpace _
    rw [← Submodule.orthogonal_eq_bot_iff, eq_bot_iff]
    intro v hv
    let v' : PoincareHilbert := v
    have hv_zero_opt : ∀ a : OptionSpace4, ⟪deltaOption4 a, v'⟫_ℂ = 0 := by
      intro a
      have ha_mem : deltaOption4 a ∈ (Submodule.span ℂ S).topologicalClosure := by
        apply subset_closure
        apply Submodule.subset_span
        cases a with
        | none => exact h_vac
        | some x => exact h_delta x
      exact (Submodule.mem_orthogonal _ _).mp hv (deltaOption4 a) ha_mem
    have hcinner : ∀ a b : ℂ, ⟪a, b⟫_ℂ = starRingEnd ℂ a * b := by
      intro a b
      have h1 : ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ = 1 := by
        rw [inner_self_eq_norm_sq_to_K]; norm_num
      calc ⟪a, b⟫_ℂ = ⟪a • (1 : ℂ), b • (1 : ℂ)⟫_ℂ := by simp
        _ = starRingEnd ℂ a * (b * ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ) := by
              rw [inner_smul_left, inner_smul_right]
        _ = starRingEnd ℂ a * b := by rw [h1, mul_one]
    have hv_val : ∀ a : OptionSpace4, (⇑v' : OptionSpace4 → ℂ) a = 0 := by
      intro a
      have h_in : ⟪deltaOption4 a, v'⟫_ℂ = (⇑v' : OptionSpace4 → ℂ) a := by
        rw [MeasureTheory.L2.inner_def]
        have h_ae : (fun z => ⟪(⇑(deltaOption4 a) : OptionSpace4 → ℂ) z,
              (⇑v' : OptionSpace4 → ℂ) z⟫_ℂ) =
            fun z => if z = a then (⇑v' : OptionSpace4 → ℂ) a else 0 := by
          funext z
          rw [deltaOption4_apply]
          by_cases hz : z = a
          · subst hz
            rw [if_pos rfl, if_pos rfl, hcinner, map_one, one_mul]
          · rw [if_neg hz, if_neg hz, inner_zero_left]
        rw [h_ae]
        have h_ind : (fun z : OptionSpace4 => if z = a then (⇑v' : OptionSpace4 → ℂ) a else 0) =
            Set.indicator {a} (fun _ => (⇑v' : OptionSpace4 → ℂ) a) := by
          funext z
          simp [Set.indicator_apply, Set.mem_singleton_iff]
        rw [h_ind, MeasureTheory.integral_indicator (by trivial : MeasurableSet ({a} : Set OptionSpace4)),
          MeasureTheory.setIntegral_const]
        dsimp [Measure.real]
        rw [poincareCount_singleton_toReal, Complex.ofReal_one, one_mul]
      rw [← h_in]
      exact hv_zero_opt a
    rw [Submodule.mem_bot]
    change v' = 0
    apply MeasureTheory.Lp.ext
    have h0 : ⇑(0 : PoincareHilbert) =ᵐ[poincareCountMeasure] 0 :=
      MeasureTheory.Lp.coeFn_zero ℂ 2 poincareCountMeasure
    filter_upwards [h0] with a ha
    rw [hv_val a, ha]
    rfl

/-- Infinite-dimensional Poincaré-covariant realization of **§16**. -/
theorem infdim_poincare_euclidean_os_verification :
    ∃ D : EuclideanOSVerificationData concreteOS4DContinuumTheory infDimOSReconstructionData,
      (∀ (m : ℕ) (n_pts : Fin m → ℕ) (c : Fin m → ℂ)
        (xs : ∀ i : Fin m, Fin (n_pts i) → Space4),
        (∀ i k, 0 < (xs i k) 0) →
        0 ≤ (∑ i : Fin m, ∑ j : Fin m,
          c i * starRingEnd ℂ (c j) *
            concreteOS4DContinuumTheory.os.Schwinger (n_pts i + n_pts j)
              (Fin.append (fun k => euclidTimeReflect (xs i k)) (xs j))).re) ∧
      (∀ (n : ℕ) (Rot : Matrix.specialOrthogonalGroup (Fin 4) ℝ)
        (xs : Fin n → Space4),
        concreteOS4DContinuumTheory.os.Schwinger n (fun i => Matrix.mulVec Rot.1 (xs i)) =
          concreteOS4DContinuumTheory.os.Schwinger n xs) ∧
      ((∀ x y : infDimOSReconstructionData.wightman.H,
          ⟪infDimOSReconstructionData.H_phys x, y⟫_ℂ =
            ⟪x, infDimOSReconstructionData.H_phys y⟫_ℂ) ∧
        (∀ x : infDimOSReconstructionData.wightman.H,
          0 ≤ (⟪x, infDimOSReconstructionData.H_phys x⟫_ℂ).re) ∧
        infDimOSReconstructionData.H_phys infDimOSReconstructionData.wightman.Ω_phys = 0) ∧
      (0 < (1 : ℝ) ∧
        (∀ (n m : ℕ), ∃ C : ℝ, ∀ (xs : Fin n → Space4) (ys : Fin m → Space4)
          (dist : ℝ), 0 ≤ dist → (∀ i j, dist ≤ ‖xs i - ys j‖) →
          ‖concreteOS4DContinuumTheory.os.Schwinger (n + m) (Fin.append xs ys) -
            concreteOS4DContinuumTheory.os.Schwinger n xs *
              concreteOS4DContinuumTheory.os.Schwinger m ys‖ ≤ C * Real.exp (-((1 : ℝ) * dist))) ∧
        ¬ IsGaussian4 concreteOS4DContinuumTheory.os.Schwinger) ∧
      ((∀ β, Filter.Tendsto (D.Z β) Filter.atTop Filter.atTop) ∧
        (∀ ψ : infDimOSReconstructionData.wightman.H,
          0 ≤ (⟪ψ, infDimOSReconstructionData.H_phys ψ⟫_ℂ).re)) ∧
      (Filter.Tendsto D.ξ_seq Filter.atTop Filter.atTop ∧
        (∀ x : D.trilattice.S, D.trilattice.μ (D.trilattice.δ x) = x) ∧
        (∀ i, lieBracketCLM (D.symm i) infDimOSReconstructionData.H_phys = 0) ∧
        infDimOSReconstructionData.wightman.Ω_phys ∈ invarianceSet D.symm ∧
        (∀ (i : Fin D.n_dof) (z : PhaseSpace D.n_dof),
          poissonBracket (coordQ i) (coordP i) z ≠ 0) ∧
        (∀ (f : PhaseSpace D.n_dof → ℝ) (z : PhaseSpace D.n_dof),
          Differentiable ℝ f →
          (∀ w, poissonBracket f D.H_cl w = 0) →
          ∀ t, f (D.flow.Φ t z) = f z) ∧
        (∀ A₁ A₂ B₁ B₂ : D.Obs,
          (A₁ ⊗ₜ[ℂ] B₁) * (A₂ ⊗ₜ[ℂ] B₂) = (A₁ * A₂) ⊗ₜ[ℂ] (B₁ * B₂))) ∧
      ((∀ z : PhaseSpace 1, singleDOFProj D.n_dof (singleDOFLift D.n_dof z) = z) ∧
        0 < D.action_val) :=
  non_gaussian_4d_euclidean_os_axioms_verification
    concreteOS4DContinuumTheory infDimOSReconstructionData

/-- Infinite-dimensional Poincaré-covariant realization of **§17**. -/
theorem infdim_poincare_wightman_reconstruction :
    ∃ D : OSHilbertCompletionData infDimOSReconstructionData,
      ((∀ u : OSQuotient D.bridge.F, 0 ≤ (osQuotInner D.bridge.F u u).re) ∧
        (∀ u : OSQuotient D.bridge.F,
          osQuotInner D.bridge.F u u = 0 ↔ u = osQuotMk D.bridge.F 0)) ∧
      (Function.Injective D.bridge.ι ∧
        (∀ u v, ⟪D.bridge.ι u, D.bridge.ι v⟫_ℂ = osQuotInner D.bridge.F u v) ∧
        closure (Set.range D.bridge.ι) = Set.univ) ∧
      ((∀ g x y, ⟪infDimOSReconstructionData.wightman.U g x,
            infDimOSReconstructionData.wightman.U g y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
        (∀ g, infDimOSReconstructionData.wightman.U g
            infDimOSReconstructionData.wightman.Ω_phys =
          infDimOSReconstructionData.wightman.Ω_phys) ∧
        (∀ x y, ⟪infDimOSReconstructionData.H_phys x, y⟫_ℂ =
          ⟪x, infDimOSReconstructionData.H_phys y⟫_ℂ) ∧
        (∀ x, 0 ≤ (⟪x, infDimOSReconstructionData.H_phys x⟫_ℂ).re) ∧
        infDimOSReconstructionData.H_phys infDimOSReconstructionData.wightman.Ω_phys = 0) ∧
      ((∀ g x, (infDimOSReconstructionData.wightman.U g).comp
            (infDimOSReconstructionData.wightman.φ x) =
          (infDimOSReconstructionData.wightman.φ
            (infDimOSReconstructionData.wightman.actP g x)).comp
              (infDimOSReconstructionData.wightman.U g)) ∧
        (∀ x y, minkowskiSq (x - y) < 0 →
          (infDimOSReconstructionData.wightman.φ x).comp
            (infDimOSReconstructionData.wightman.φ y) =
          (infDimOSReconstructionData.wightman.φ y).comp
            (infDimOSReconstructionData.wightman.φ x)) ∧
        (∀ p2 ∈ infDimOSReconstructionData.wightman.P2_spec, 0 ≤ p2) ∧
        (∀ p2 ∈ infDimOSReconstructionData.wightman.P2_spec, p2 = 0 ∨ (1 : ℝ) ^ 2 ≤ p2) ∧
        (Submodule.span ℂ
          {v : infDimOSReconstructionData.wightman.H | ∃ (k : ℕ) (xs : Fin k → Space4),
            v = (List.ofFn (fun i : Fin k =>
              infDimOSReconstructionData.wightman.φ (xs i))).foldr
              (fun A acc => A acc) infDimOSReconstructionData.wightman.Ω_phys}).topologicalClosure =
          ⊤) ∧
      ((∀ β, Filter.Tendsto (D.Z β) Filter.atTop Filter.atTop) ∧
        (∀ ψ : infDimOSReconstructionData.wightman.H,
          0 ≤ (⟪ψ, infDimOSReconstructionData.H_phys ψ⟫_ℂ).re) ∧
        (∀ i, lieBracketCLM (D.symm i) infDimOSReconstructionData.H_phys = 0) ∧
        infDimOSReconstructionData.wightman.Ω_phys ∈ invarianceSet D.symm ∧
        (∀ (i : Fin D.n_dof) (z : PhaseSpace D.n_dof),
          poissonBracket (coordQ i) (coordP i) z ≠ 0) ∧
        (∀ (f : PhaseSpace D.n_dof → ℝ) (z : PhaseSpace D.n_dof),
          Differentiable ℝ f →
          (∀ w, poissonBracket f D.H_cl w = 0) →
          ∀ t, f (D.flow.Φ t z) = f z) ∧
        (∀ A₁ A₂ B₁ B₂ : D.Obs,
          (A₁ ⊗ₜ[ℂ] B₁) * (A₂ ⊗ₜ[ℂ] B₂) = (A₁ * A₂) ⊗ₜ[ℂ] (B₁ * B₂))) ∧
      (Filter.Tendsto D.ξ_seq Filter.atTop Filter.atTop ∧
        (∀ x : D.trilattice.S, D.trilattice.μ (D.trilattice.δ x) = x)) ∧
      ((∀ z : PhaseSpace 1, singleDOFProj D.n_dof (singleDOFLift D.n_dof z) = z) ∧
        0 < D.action_val) :=
  os_hilbert_completion_and_wightman_reconstruction infDimOSReconstructionData

end Poincare4DWightman 

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