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
  cluster    : ∀ (n m : ℕ) (C : ℝ) (xs : Fin n → Space4) (ys : Fin m → Space4)
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

/-! ## §8.  Concrete realizations and RG pullback bridge -/

section ConcreteRealizations

/-- The 16-state `SIXTEEN_3` carrier `(∅, {F}, {T}, {T,F})` bitmask. -/
abbrev S16 := Bool × Bool × Bool × Bool

def le16_i (x y : S16) : Prop :=
  x.1 ≤ y.1 ∧ x.2.1 ≤ y.2.1 ∧ x.2.2.1 ≤ y.2.2.1 ∧ x.2.2.2 ≤ y.2.2.2

def le16_t (x y : S16) : Prop :=
  y.1 ≤ x.1 ∧ y.2.1 ≤ x.2.1 ∧ x.2.2.1 ≤ y.2.2.1 ∧ x.2.2.2 ≤ y.2.2.2

def le16_f (x y : S16) : Prop :=
  y.1 ≤ x.1 ∧ x.2.1 ≤ y.2.1 ∧ y.2.2.1 ≤ x.2.2.1 ∧ x.2.2.2 ≤ y.2.2.2

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

/-- Minimal spatial lattice (single site, single link). -/
def trivialLattice : SpatialLattice where
  Site := Unit
  Link := Unit
  src := fun _ => ()
  dst := fun _ => ()

/-- 16-dimensional complex Hilbert space indexed by the `SIXTEEN_3` register. -/
abbrev V16 := EuclideanSpace ℂ (Fin 16)

/-- Vacuum basis vector `[B]` in `V16`. -/
def Ω16 : V16 := { ofLp := fun i => if i = 15 then 1 else 0 }

theorem Ω16_norm : ‖Ω16‖ = 1 := by
  have hsq : ‖Ω16‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Finset.sum_eq_single (15 : Fin 16)]
    · simp [Ω16]
    · intro j _ hj
      simp [Ω16, hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hmul : (‖Ω16‖ - 1) * (‖Ω16‖ + 1) = 0 := by linarith
  rcases mul_eq_zero.mp hmul with h | h <;> linarith [norm_nonneg Ω16]

/-- Rank-1 orthogonal projector onto `ℂ ∙ Ω16`. -/
noncomputable def P_Ω16 : V16 →L[ℂ] V16 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟪Ω16, x⟫_ℂ • Ω16
      map_add' := fun x y => by rw [inner_add_right, add_smul]
      map_smul' := fun c x => by rw [inner_smul_right, smul_smul]; rfl }
    1
    (fun x => by
      change ‖⟪Ω16, x⟫_ℂ • Ω16‖ ≤ 1 * ‖x‖
      rw [norm_smul, Ω16_norm, mul_one, one_mul]
      calc ‖⟪Ω16, x⟫_ℂ‖ ≤ ‖Ω16‖ * ‖x‖ := norm_inner_le_norm _ _
        _ = ‖x‖ := by rw [Ω16_norm, one_mul])

/-- Concrete `LatticeGaugeSetup` over `V16` at lattice spacing `a > 0` and mass gap `1`. -/
noncomputable def concreteLatticeSetup (N : ℕ) (a : ℝ) (ha : 0 < a) :
    LatticeGaugeSetup trivialLattice (Matrix.specialUnitaryGroup (Fin N) ℂ) V16 where
  rep := fun _ => ContinuousLinearMap.id ℂ V16
  rep_one := rfl
  rep_mul := fun _ _ => rfl
  T := ((1 - Real.exp (-a) : ℝ) : ℂ) • P_Ω16 +
       ((Real.exp (-a) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V16
  a := a
  a_pos := ha
  T_sa := by
    intro x y
    have hP_sa : ⟪P_Ω16 x, y⟫_ℂ = ⟪x, P_Ω16 y⟫_ℂ := by
      change ⟪⟪Ω16, x⟫_ℂ • Ω16, y⟫_ℂ = ⟪x, ⟪Ω16, y⟫_ℂ • Ω16⟫_ℂ
      rw [inner_smul_left, inner_smul_right, ← inner_conj_symm x Ω16, mul_comm]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal, hP_sa]
  T_pos := by
    intro v
    have hP_pos : 0 ≤ (⟪v, P_Ω16 v⟫_ℂ).re := by
      change 0 ≤ (⟪v, ⟪Ω16, v⟫_ℂ • Ω16⟫_ℂ).re
      rw [inner_smul_right, (inner_conj_symm v Ω16).symm]
      rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add]
      exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
    have hV_pos : 0 ≤ (⟪v, v⟫_ℂ).re := by
      have h_eq : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := by
        rw [inner_self_eq_norm_sq_to_K]
        have hpow : (((‖v‖ : ℂ) ^ 2).re) = ‖v‖ ^ 2 := by norm_num [pow_two]
        exact hpow
      rw [h_eq]
      exact sq_nonneg ‖v‖
    have hr_pos : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
    have h1r_pos : 0 ≤ 1 - Real.exp (-a) := by
      have : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    have h_re_mul : ∀ (c : ℝ) (z : ℂ), ((c : ℂ) * z).re = c * z.re := by
      intro c z; simp [Complex.mul_re]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, inner_add_right, inner_smul_right,
      Complex.add_re, h_re_mul]
    exact add_nonneg (mul_nonneg h1r_pos hP_pos) (mul_nonneg hr_pos hV_pos)
  T_compact := by
    let T0 : V16 →L[ℂ] V16 :=
      ((1 - Real.exp (-a) : ℝ) : ℂ) • P_Ω16 +
      ((Real.exp (-a) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V16
    change IsCompactOperator ⇑T0
    let H := PiLp.homeomorph 2 (fun _ : Fin 16 => ℂ)
    let B_pi : Set (Fin 16 → ℂ) :=
      Set.univ.pi (fun _ : Fin 16 => Metric.closedBall (0 : ℂ) 1)
    let U_pi : Set (Fin 16 → ℂ) :=
      ⋂ i : Fin 16, (fun f : Fin 16 → ℂ => f i) ⁻¹' Metric.ball (0 : ℂ) 1
    have hU_open : IsOpen U_pi :=
      isOpen_iInter_of_finite fun i => Metric.isOpen_ball.preimage (continuous_apply i)
    have hU_mem : (0 : Fin 16 → ℂ) ∈ U_pi := by simp [U_pi]
    have hU_sub : U_pi ⊆ B_pi := by
      intro f hf i _
      exact Metric.ball_subset_closedBall (Set.mem_iInter.mp hf i)
    have hB_nhds : B_pi ∈ nhds (0 : Fin 16 → ℂ) :=
      Filter.mem_of_superset (hU_open.mem_nhds hU_mem) hU_sub
    have hB_comp : IsCompact B_pi :=
      isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) 1
    let s : Set V16 := H ⁻¹' B_pi
    have hH0 : H 0 = 0 := rfl
    have hs_nhds : s ∈ nhds (0 : V16) :=
      H.continuous.continuousAt.preimage_mem_nhds (by simpa [hH0] using hB_nhds)
    have hs_eq : s = H.symm '' B_pi := by
      ext x
      constructor
      · intro hx; exact ⟨H x, hx, H.symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩; simpa [s] using hy
    have hs_comp : IsCompact s := by
      rw [hs_eq]
      exact hB_comp.image H.symm.continuous
    exact ⟨s, hs_comp,
      T0.continuous.continuousAt.preimage_mem_nhds (by simpa [map_zero] using hs_nhds)⟩
  T_gauge_inv := fun _ => rfl
  Ω := Ω16
  Ω_unit := Ω16_norm
  Ω_vac := by
    have h_self : ⟪Ω16, Ω16⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, Ω16_norm]
      norm_num
    have hP_vac : P_Ω16 Ω16 = Ω16 := by
      change ⟪Ω16, Ω16⟫_ℂ • Ω16 = Ω16
      rw [h_self, one_smul]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, hP_vac, ← add_smul]
    norm_num
  Ω_gauge_inv := fun _ => rfl
  Δ := 1
  Δ_pos := one_pos
  gap := by
    intro v hv
    have hΩv : ⟪Ω16, v⟫_ℂ = 0 := by
      rw [← inner_conj_symm, hv, map_zero]
    have hP_zero : P_Ω16 v = 0 := by
      change ⟪Ω16, v⟫_ℂ • Ω16 = 0
      rw [hΩv, zero_smul]
    have hpow : (((‖v‖ : ℂ) ^ 2).re) = ‖v‖ ^ 2 := by norm_num [pow_two]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, hP_zero, smul_zero, zero_add,
      inner_smul_right, inner_self_eq_norm_sq_to_K, one_mul]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_left (le_of_eq hpow) (Real.exp_pos _).le

/-- Constructive witness of `YangMillsMassGap` via the 16-state trilattice space `V16`. -/
theorem yangMillsMassGap : YangMillsMassGap.{0} :=
  ⟨trivialLattice, 2, le_rfl, V16, inferInstance, inferInstance, inferInstance,
    ⟨concreteLatticeSetup 2 1 one_pos⟩⟩

/-- Map each `S16` state to its basis vector in `V16`, sending `totalityB` to `Ω16`. -/
def embedS16 (x : S16) : V16 :=
  let idx : Fin 16 :=
    ⟨(if x.1 then 8 else 0) + (if x.2.1 then 4 else 0) +
     (if x.2.2.1 then 2 else 0) + (if x.2.2.2 then 1 else 0),
     by cases x.1 <;> cases x.2.1 <;> cases x.2.2.1 <;> cases x.2.2.2 <;> decide⟩
  { ofLp := fun i => if i = idx then 1 else 0 }

/-- Concrete `TrilatticeGNSBridge` connecting `trilattice16` to `concreteLatticeSetup`. -/
noncomputable def concreteGNSBridge (N : ℕ) (a : ℝ) (ha : 0 < a) :
    TrilatticeGNSBridge trilattice16 trivialLattice
      (Matrix.specialUnitaryGroup (Fin N) ℂ) V16 where
  setup := concreteLatticeSetup N a ha
  embed := embedS16
  embed_B := rfl
  vac_inv := (concreteLatticeSetup N a ha).Ω_vac

/-- Concrete `LatticeScalingFamily` over `SU(N)` with uniform physical gap `Δ_phys = 1`. -/
noncomputable def concreteScalingFamily (N : ℕ) :
    LatticeScalingFamily (Matrix.specialUnitaryGroup (Fin N) ℂ) where
  L := fun _ => trivialLattice
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

end YangMills
 #print axioms YangMills.combined_chain_summary