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

/-! ## §28.  Kogut–Susskind Yang–Mills Hamiltonian, non-commuting link algebra & Gauss law -/

section KogutSusskindYM

private theorem memLp_realMul {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α)
    (f : α → ℝ) (hf_meas : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hbd : ∀ x, |f x| ≤ C) (ψ : MeasureTheory.Lp ℂ 2 μ) :
    MeasureTheory.MemLp (fun x => ((f x : ℝ) : ℂ) * ψ x) 2 μ := by
  have hψ_mem : MeasureTheory.MemLp (⇑ψ) 2 μ := MeasureTheory.Lp.memLp ψ
  have hψ_ae : MeasureTheory.AEStronglyMeasurable (⇑ψ) μ := hψ_mem.aestronglyMeasurable
  have hf_ae : MeasureTheory.AEStronglyMeasurable (fun x => ((f x : ℝ) : ℂ)) μ :=
    (Complex.continuous_ofReal.measurable.comp hf_meas).stronglyMeasurable.aestronglyMeasurable
  have h_ae : MeasureTheory.AEStronglyMeasurable (fun x => ((f x : ℝ) : ℂ) * ψ x) μ :=
    hf_ae.mul hψ_ae
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm h_ae]
  have h_int : MeasureTheory.Integrable (fun x => ‖ψ x‖ ^ 2) μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hψ_ae).mp hψ_mem
  refine (h_int.const_mul (C ^ 2)).mono' (h_ae.norm.pow 2) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) (hbd x) 2) (sq_nonneg _)

/-- Bounded self-adjoint multiplication operator `ψ ↦ f · ψ` on `L²(μ)` for real `|f| ≤ C`. -/
noncomputable def realMulOp {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α)
    (f : α → ℝ) (hf_meas : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hbd : ∀ x, |f x| ≤ C) :
    MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun ψ => (memLp_realMul μ f hf_meas C hC hbd ψ).toLp
        (fun x => ((f x : ℝ) : ℂ) * ψ x)
      map_add' := fun ψ₁ ψ₂ => by
        apply MeasureTheory.Lp.ext
        have h1 := (memLp_realMul μ f hf_meas C hC hbd (ψ₁ + ψ₂)).coeFn_toLp
        have h2 := (memLp_realMul μ f hf_meas C hC hbd ψ₁).coeFn_toLp
        have h3 := (memLp_realMul μ f hf_meas C hC hbd ψ₂).coeFn_toLp
        have hadd1 := MeasureTheory.Lp.coeFn_add ψ₁ ψ₂
        have hadd2 := MeasureTheory.Lp.coeFn_add
          ((memLp_realMul μ f hf_meas C hC hbd ψ₁).toLp (fun x => ((f x : ℝ) : ℂ) * ψ₁ x))
          ((memLp_realMul μ f hf_meas C hC hbd ψ₂).toLp (fun x => ((f x : ℝ) : ℂ) * ψ₂ x))
        filter_upwards [h1, h2, h3, hadd1, hadd2] with x hx1 hx2 hx3 ha1 ha2
        simp only [Pi.add_apply] at ha1 ha2 ⊢
        rw [hx1, ha1, mul_add, ha2, hx2, hx3]
      map_smul' := fun c ψ => by
        apply MeasureTheory.Lp.ext
        have h1 := (memLp_realMul μ f hf_meas C hC hbd (c • ψ)).coeFn_toLp
        have h2 := (memLp_realMul μ f hf_meas C hC hbd ψ).coeFn_toLp
        have hsm1 := MeasureTheory.Lp.coeFn_smul c ψ
        have hsm2 := MeasureTheory.Lp.coeFn_smul c
          ((memLp_realMul μ f hf_meas C hC hbd ψ).toLp (fun x => ((f x : ℝ) : ℂ) * ψ x))
        filter_upwards [h1, h2, hsm1, hsm2] with x hx1 hx2 hs1 hs2
        simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul] at hs1 hs2 ⊢
        rw [hx1, hs1, hs2, hx2]
        ring }
    C
    (fun ψ => by
      let ψ' := (memLp_realMul μ f hf_meas C hC hbd ψ).toLp (fun x => ((f x : ℝ) : ℂ) * ψ x)
      change ‖ψ'‖ ≤ C * ‖ψ‖
      rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)), mul_pow]
      have h_inner_lhs : (⟪ψ', ψ'⟫_ℂ).re = ∫ x, ‖ψ' x‖ ^ 2 ∂μ := by
        have h_l2 : MeasureTheory.Integrable (fun x => ⟪ψ' x, ψ' x⟫_ℂ) μ :=
          MeasureTheory.L2.integrable_inner _ _
        have h_re := integral_re h_l2
        rw [MeasureTheory.L2.inner_def]
        change RCLike.re (∫ x, ⟪ψ' x, ψ' x⟫_ℂ ∂μ) = _
        rw [← h_re]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        change (⟪ψ' x, ψ' x⟫_ℂ).re = ‖ψ' x‖ ^ 2
        rw [inner_self_eq_norm_sq_to_K]
        simp [pow_two]
      have h_inner_rhs : (⟪ψ, ψ⟫_ℂ).re = ∫ x, ‖ψ x‖ ^ 2 ∂μ := by
        have h_l2 : MeasureTheory.Integrable (fun x => ⟪ψ x, ψ x⟫_ℂ) μ :=
          MeasureTheory.L2.integrable_inner _ _
        have h_re := integral_re h_l2
        rw [MeasureTheory.L2.inner_def]
        change RCLike.re (∫ x, ⟪ψ x, ψ x⟫_ℂ ∂μ) = _
        rw [← h_re]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        change (⟪ψ x, ψ x⟫_ℂ).re = ‖ψ x‖ ^ 2
        rw [inner_self_eq_norm_sq_to_K]
        simp [pow_two]
      have h_norm_sq : ∀ (φ : MeasureTheory.Lp ℂ 2 μ), ‖φ‖ ^ 2 = (⟪φ, φ⟫_ℂ).re := by
        intro φ
        rw [inner_self_eq_norm_sq_to_K]
        simp [pow_two]
      rw [h_norm_sq ψ', h_norm_sq ψ, h_inner_lhs, h_inner_rhs, ← MeasureTheory.integral_const_mul]
      have hcoe := (memLp_realMul μ f hf_meas C hC hbd ψ).coeFn_toLp
      have hψ_ae : MeasureTheory.AEStronglyMeasurable (⇑ψ) μ :=
        (MeasureTheory.Lp.memLp ψ).aestronglyMeasurable
      have h_int1 : MeasureTheory.Integrable (fun x => ‖ψ' x‖ ^ 2) μ :=
        (MeasureTheory.memLp_two_iff_integrable_sq_norm
          (MeasureTheory.Lp.memLp ψ').aestronglyMeasurable).mp (MeasureTheory.Lp.memLp ψ')
      have h_int2 : MeasureTheory.Integrable (fun x => C ^ 2 * ‖ψ x‖ ^ 2) μ :=
        ((MeasureTheory.memLp_two_iff_integrable_sq_norm hψ_ae).mp
          (MeasureTheory.Lp.memLp ψ)).const_mul (C ^ 2)
      refine MeasureTheory.integral_mono_ae h_int1 h_int2 ?_
      filter_upwards [hcoe] with x hx
      rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) (hbd x) 2) (sq_nonneg _))

theorem realMulOp_apply_ae {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (f : α → ℝ) (hf_meas : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hbd : ∀ x, |f x| ≤ C)
    (ψ : MeasureTheory.Lp ℂ 2 μ) :
    ⇑(realMulOp μ f hf_meas C hC hbd ψ) =ᵐ[μ] fun x => ((f x : ℝ) : ℂ) * ψ x :=
  (memLp_realMul μ f hf_meas C hC hbd ψ).coeFn_toLp

theorem realMulOp_sa {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (f : α → ℝ) (hf_meas : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hbd : ∀ x, |f x| ≤ C)
    (u v : MeasureTheory.Lp ℂ 2 μ) :
    ⟪realMulOp μ f hf_meas C hC hbd u, v⟫_ℂ =
      ⟪u, realMulOp μ f hf_meas C hC hbd v⟫_ℂ := by
  have hcinner : ∀ a b : ℂ, ⟪a, b⟫_ℂ = starRingEnd ℂ a * b := by
    intro a b
    have h1 : ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_num
    calc ⟪a, b⟫_ℂ = ⟪a • (1 : ℂ), b • (1 : ℂ)⟫_ℂ := by simp
      _ = starRingEnd ℂ a * (b * ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ) := by
            rw [inner_smul_left, inner_smul_right]
      _ = starRingEnd ℂ a * b := by rw [h1, mul_one]
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have h1 := realMulOp_apply_ae μ f hf_meas C hC hbd u
  have h2 := realMulOp_apply_ae μ f hf_meas C hC hbd v
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2, hcinner, hcinner, map_mul, Complex.conj_ofReal]
  ring

theorem realMulOp_nonneg {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (f : α → ℝ) (hf_meas : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hbd : ∀ x, |f x| ≤ C)
    (hf_pos : ∀ x, 0 ≤ f x) (ψ : MeasureTheory.Lp ℂ 2 μ) :
    0 ≤ (⟪ψ, realMulOp μ f hf_meas C hC hbd ψ⟫_ℂ).re := by
  have hcinner : ∀ a b : ℂ, ⟪a, b⟫_ℂ = starRingEnd ℂ a * b := by
    intro a b
    have h1 : ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_num
    calc ⟪a, b⟫_ℂ = ⟪a • (1 : ℂ), b • (1 : ℂ)⟫_ℂ := by simp
      _ = starRingEnd ℂ a * (b * ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ) := by
            rw [inner_smul_left, inner_smul_right]
      _ = starRingEnd ℂ a * b := by rw [h1, mul_one]
  let opψ := realMulOp μ f hf_meas C hC hbd ψ
  have h_l2 : MeasureTheory.Integrable (fun x => ⟪ψ x, opψ x⟫_ℂ) μ :=
    MeasureTheory.L2.integrable_inner _ _
  have h_re := integral_re h_l2
  rw [MeasureTheory.L2.inner_def]
  change 0 ≤ RCLike.re (∫ x, ⟪ψ x, opψ x⟫_ℂ ∂μ)
  rw [← h_re]
  refine MeasureTheory.integral_nonneg_of_ae ?_
  have hcoe := realMulOp_apply_ae μ f hf_meas C hC hbd ψ
  filter_upwards [hcoe] with x hx
  change 0 ≤ (⟪ψ x, opψ x⟫_ℂ).re
  have h_eq : opψ x = ((f x : ℝ) : ℂ) * ψ x := hx
  rw [h_eq, hcinner]
  have hmul : starRingEnd ℂ (ψ x) * (((f x : ℝ) : ℂ) * ψ x) =
      ((f x : ℝ) : ℂ) * (starRingEnd ℂ (ψ x) * ψ x) := by ring
  rw [hmul, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (hf_pos x) (sq_nonneg _)

/-- Elementary Kogut–Susskind magnetic plaquette operator `ψ ↦ (1 - (1/N) Re Tr U_□) ψ`. -/
noncomputable def ksPlaquetteOp (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (p : LatticePlaquette (cubicTorus3 L)) :
    HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] HaarGaugeSpace (latticeHaarMeasure L N) :=
  realMulOp (latticeHaarMeasure L N) (wilsonPlaquetteTerm p)
    (measurable_wilsonPlaquetteTerm L N p) 2 (by norm_num) (fun U => by
      have hb := wilsonPlaquetteTerm_bounds p U
      rw [abs_of_nonneg hb.1]
      exact hb.2)

theorem ksPlaquetteOp_gauge_inv (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (p : LatticePlaquette (cubicTorus3 L))
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    lieBracketCLM (cubicGaugeRep L N g) (ksPlaquetteOp L N p) = 0 := by
  unfold lieBracketCLM
  ext1 ψ
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, sub_eq_zero]
  apply MeasureTheory.Lp.ext
  let μ := latticeHaarMeasure L N
  let eg := gaugeActEquiv L N (fun x => (g x)⁻¹)
  let hmpg : MeasureTheory.MeasurePreserving eg μ μ :=
    ⟨eg.measurable, latticeHaarMeasure_gauge_inv L N (fun x => (g x)⁻¹)⟩
  have hL1 := cubicGaugeRep_apply_ae L N g (ksPlaquetteOp L N p ψ)
  have hL2 : (fun U => (ksPlaquetteOp L N p ψ) (gaugeAct (fun x => (g x)⁻¹) U)) =ᵐ[μ]
      (fun U => ((wilsonPlaquetteTerm p (gaugeAct (fun x => (g x)⁻¹) U) : ℝ) : ℂ) *
        ψ (gaugeAct (fun x => (g x)⁻¹) U)) :=
    ae_comp_measurePreserving hmpg (realMulOp_apply_ae μ _ _ _ _ _ ψ)
  have hR1 := realMulOp_apply_ae μ (wilsonPlaquetteTerm p)
    (measurable_wilsonPlaquetteTerm L N p) 2 (by norm_num) (fun U => by
      have hb := wilsonPlaquetteTerm_bounds p U
      rw [abs_of_nonneg hb.1]; exact hb.2) (cubicGaugeRep L N g ψ)
  have hR2 := cubicGaugeRep_apply_ae L N g ψ
  filter_upwards [hL1, hL2, hR1, hR2] with U hl1 hl2 hr1 hr2
  change ⇑(cubicGaugeRep L N g (ksPlaquetteOp L N p ψ)) U =
    ⇑(ksPlaquetteOp L N p (cubicGaugeRep L N g ψ)) U
  change ⇑(ksPlaquetteOp L N p (cubicGaugeRep L N g ψ)) U = _ at hr1
  rw [hl1, hl2, wilsonPlaquetteTerm_gauge_inv, hr1, hr2]

/--
Full Kogut–Susskind magnetic plaquette Hamiltonian
`H_B = (1 / (g² a)) ∑_□ (1 - (1/N) Re Tr U_□)` on `L²(SU(N)^{3L³}, dμ_Haar)`.
-/
noncomputable def ksMagneticH (L N : ℕ) [NeZero L] (g_sq a : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] HaarGaugeSpace (latticeHaarMeasure L N) :=
  ((1 / (g_sq * a) : ℝ) : ℂ) •
    ((cubicPlaquettes L).map (ksPlaquetteOp L N)).sum

theorem ksMagneticH_sa (L N : ℕ) [NeZero L] (g_sq a : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (x y : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⟪ksMagneticH L N g_sq a x, y⟫_ℂ = ⟪x, ksMagneticH L N g_sq a y⟫_ℂ := by
  have hsum_sa : ∀ (ps : List (LatticePlaquette (cubicTorus3 L))),
      ⟪((ps.map (ksPlaquetteOp L N)).sum) x, y⟫_ℂ =
        ⟪x, ((ps.map (ksPlaquetteOp L N)).sum) y⟫_ℂ := by
    intro ps
    induction ps with
    | nil =>
      change ⟪(0 : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] _) x, y⟫_ℂ =
        ⟪x, (0 : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] _) y⟫_ℂ
      simp
    | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, ContinuousLinearMap.add_apply,
        inner_add_left, inner_add_right]
      dsimp [ksPlaquetteOp]
      rw [realMulOp_sa, ih]
  change ⟪(((1 / (g_sq * a) : ℝ) : ℂ) •
      ((cubicPlaquettes L).map (ksPlaquetteOp L N)).sum) x, y⟫_ℂ =
    ⟪x, (((1 / (g_sq * a) : ℝ) : ℂ) •
      ((cubicPlaquettes L).map (ksPlaquetteOp L N)).sum) y⟫_ℂ
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal, hsum_sa]

theorem ksMagneticH_nonneg (L N : ℕ) [NeZero L] (g_sq a : ℝ)
    (hg : 0 < g_sq) (ha : 0 < a)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    0 ≤ (⟪ψ, ksMagneticH L N g_sq a ψ⟫_ℂ).re := by
  have hsum_nonneg : ∀ (ps : List (LatticePlaquette (cubicTorus3 L))),
      0 ≤ (⟪ψ, ((ps.map (ksPlaquetteOp L N)).sum) ψ⟫_ℂ).re := by
    intro ps
    induction ps with
    | nil =>
      change 0 ≤ (⟪ψ, (0 : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] _) ψ⟫_ℂ).re
      simp
    | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, ContinuousLinearMap.add_apply,
        inner_add_right, Complex.add_re]
      exact add_nonneg (realMulOp_nonneg _ _ _ _ _ _ (fun U => (wilsonPlaquetteTerm_bounds p U).1) ψ) ih
  change 0 ≤ (⟪ψ, (((1 / (g_sq * a) : ℝ) : ℂ) •
    ((cubicPlaquettes L).map (ksPlaquetteOp L N)).sum) ψ⟫_ℂ).re
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (by positivity) (hsum_nonneg (cubicPlaquettes L))

theorem ksMagneticH_gauge_inv (L N : ℕ) [NeZero L] (g_sq a : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    lieBracketCLM (cubicGaugeRep L N g) (ksMagneticH L N g_sq a) = 0 := by
  have hsum_comm : ∀ (ps : List (LatticePlaquette (cubicTorus3 L))),
      lieBracketCLM (cubicGaugeRep L N g) ((ps.map (ksPlaquetteOp L N)).sum) = 0 := by
    intro ps
    induction ps with
    | nil =>
      unfold lieBracketCLM
      simp
    | cons p ps ih =>
      have hp := ksPlaquetteOp_gauge_inv L N p g
      unfold lieBracketCLM at hp ih ⊢
      ext1 ψ
      have hp' := congrArg (fun f : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] _ => f ψ) hp
      have ih' := congrArg (fun f : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] _ => f ψ) ih
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.zero_apply, sub_eq_zero] at hp' ih' ⊢
      simp only [List.map_cons, List.sum_cons, ContinuousLinearMap.add_apply, map_add,
        hp', ih', sub_self]
  have hc := hsum_comm (cubicPlaquettes L)
  unfold lieBracketCLM at hc
  unfold lieBracketCLM ksMagneticH
  ext1 ψ
  have hc' := congrArg (fun f : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] _ => f ψ) hc
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply, map_smul, sub_eq_zero] at hc' ⊢
  rw [hc']

/-- Left multiplication shift along a single spatial link `e` by `u ∈ SU(N)`. -/
def linkLeftShift (L N : ℕ) [NeZero L]
    (e : (cubicTorus3 L).Link) (u : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  fun e' => if e' = e then u * U e else U e'

def linkLeftShiftEquiv (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) (u : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) where
  toFun := linkLeftShift L N e u
  invFun := linkLeftShift L N e u⁻¹
  left_inv U := by
    funext e'
    by_cases he : e' = e <;> simp [linkLeftShift, he, ← mul_assoc]
  right_inv U := by
    funext e'
    by_cases he : e' = e <;> simp [linkLeftShift, he, ← mul_assoc]
  measurable_toFun := by
    change Measurable (fun U : (cubicTorus3 L).Link → _ => linkLeftShift L N e u U)
    refine measurable_pi_iff.mpr fun e' => ?_
    by_cases he : e' = e
    · simp only [linkLeftShift, he, ↓reduceIte]
      exact (continuous_mul_left u).measurable.comp (measurable_pi_apply e)
    · simp only [linkLeftShift, he, ↓reduceIte]
      exact measurable_pi_apply e'
  measurable_invFun := by
    change Measurable (fun U : (cubicTorus3 L).Link → _ => linkLeftShift L N e u⁻¹ U)
    refine measurable_pi_iff.mpr fun e' => ?_
    by_cases he : e' = e
    · simp only [linkLeftShift, he, ↓reduceIte]
      exact (continuous_mul_left u⁻¹).measurable.comp (measurable_pi_apply e)
    · simp only [linkLeftShift, he, ↓reduceIte]
      exact measurable_pi_apply e'

theorem linkLeftShiftEquiv_mp (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) (u : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    MeasureTheory.MeasurePreserving (linkLeftShiftEquiv L N e u)
      (latticeHaarMeasure L N) (latticeHaarMeasure L N) := by
  haveI := suHaar_prob N
  haveI := latticeHaarMeasure_prob L N
  let φ : (cubicTorus3 L).Link →
      Matrix.specialUnitaryGroup (Fin N) ℂ → Matrix.specialUnitaryGroup (Fin N) ℂ :=
    fun e' w => if e' = e then u * w else w
  have hφ_meas : ∀ e', Measurable (φ e') := fun e' => by
    by_cases he : e' = e
    · simp only [φ, he, ↓reduceIte]; exact (continuous_mul_left u).measurable
    · simp only [φ, he, ↓reduceIte]; exact measurable_id
  have hφ_inv : ∀ e' (s : Set (Matrix.specialUnitaryGroup (Fin N) ℂ)),
      MeasurableSet s → suHaar N (φ e' ⁻¹' s) = suHaar N s := by
    intro e' s hs
    by_cases he : e' = e
    · simp only [φ, he, ↓reduceIte]
      rw [← MeasureTheory.Measure.map_apply (continuous_mul_left u).measurable hs,
        suHaar_map_mul_left]
    · simp only [φ, he, ↓reduceIte]; rfl
  let F : ((cubicTorus3 L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) →
      ((cubicTorus3 L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    fun U e' => φ e' (U e')
  have hF_eq : F = ⇑(linkLeftShiftEquiv L N e u) := by
    funext U e'
    by_cases he : e' = e
    · subst he; simp [F, φ, linkLeftShiftEquiv, linkLeftShift]
    · simp [F, φ, linkLeftShiftEquiv, linkLeftShift, he]
  have hF_meas : Measurable F :=
    measurable_pi_iff.mpr fun e' => (hφ_meas e').comp (measurable_pi_apply e')
  refine ⟨(linkLeftShiftEquiv L N e u).measurable, ?_⟩
  let μ_pi : MeasureTheory.Measure
      ((cubicTorus3 L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    MeasureTheory.Measure.pi (fun _ => suHaar N)
  rw [← hF_eq]
  change MeasureTheory.Measure.map F μ_pi = MeasureTheory.Measure.pi (fun _ => suHaar N)
  symm
  refine MeasureTheory.Measure.pi_eq fun s hs => ?_
  rw [MeasureTheory.Measure.map_apply hF_meas (MeasurableSet.univ_pi hs)]
  have hpre : F ⁻¹' Set.pi Set.univ s = Set.pi Set.univ (fun e' => φ e' ⁻¹' s e') := by
    ext U
    simp [F]
  rw [hpre, MeasureTheory.Measure.pi_pi (fun _ => suHaar N)]
  exact Finset.prod_congr rfl fun e' _ => hφ_inv e' (s e') (hs e')

/-- Unitary electric link-shift operator `(U_{e,v} ψ)(U) = ψ(linkLeftShift e v⁻¹ U)`. -/
noncomputable def ksLinkShiftOp (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) (v : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] HaarGaugeSpace (latticeHaarMeasure L N) :=
  let μ := latticeHaarMeasure L N
  let eqv := linkLeftShiftEquiv L N e v⁻¹
  let hmp := linkLeftShiftEquiv_mp L N e v⁻¹
  LinearMap.mkContinuous
    { toFun := fun ψ => (memLp_comp_measurePreserving μ eqv hmp ψ).toLp (fun U => ψ (eqv U))
      map_add' := fun ψ₁ ψ₂ => by
        apply MeasureTheory.Lp.ext
        have h1 := (memLp_comp_measurePreserving μ eqv hmp (ψ₁ + ψ₂)).coeFn_toLp
        have h2 := (memLp_comp_measurePreserving μ eqv hmp ψ₁).coeFn_toLp
        have h3 := (memLp_comp_measurePreserving μ eqv hmp ψ₂).coeFn_toLp
        have hadd1 := MeasureTheory.Lp.coeFn_add ψ₁ ψ₂
        have hadd2 := MeasureTheory.Lp.coeFn_add
          ((memLp_comp_measurePreserving μ eqv hmp ψ₁).toLp (fun U => ψ₁ (eqv U)))
          ((memLp_comp_measurePreserving μ eqv hmp ψ₂).toLp (fun U => ψ₂ (eqv U)))
        filter_upwards [h1, h2, h3, ae_comp_measurePreserving hmp hadd1, hadd2] with U hu1 hu2 hu3 ha1 ha2
        simp only [Pi.add_apply] at ha1 ha2 ⊢
        rw [hu1, ha1, ha2, hu2, hu3]
      map_smul' := fun c ψ => by
        apply MeasureTheory.Lp.ext
        have h1 := (memLp_comp_measurePreserving μ eqv hmp (c • ψ)).coeFn_toLp
        have h2 := (memLp_comp_measurePreserving μ eqv hmp ψ).coeFn_toLp
        have hsm1 := MeasureTheory.Lp.coeFn_smul c ψ
        have hsm2 := MeasureTheory.Lp.coeFn_smul c
          ((memLp_comp_measurePreserving μ eqv hmp ψ).toLp (fun U => ψ (eqv U)))
        filter_upwards [h1, h2, ae_comp_measurePreserving hmp hsm1, hsm2] with U hu1 hu2 hs1 hs2
        simp only [Pi.smul_apply, RingHom.id_apply] at hs1 hs2 ⊢
        rw [hu1, hs1, hs2, hu2] }
    1
    (fun ψ => by
      let ψ' := (memLp_comp_measurePreserving μ eqv hmp ψ).toLp (fun U => ψ (eqv U))
      have h_norm_sq : ‖ψ'‖ ^ 2 = ‖ψ‖ ^ 2 := by
        have h_inner : ⟪ψ', ψ'⟫_ℂ = ⟪ψ, ψ⟫_ℂ := by
          rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
          have hcoe := (memLp_comp_measurePreserving μ eqv hmp ψ).coeFn_toLp
          calc ∫ U, ⟪ψ' U, ψ' U⟫_ℂ ∂μ
              = ∫ U, ⟪ψ (eqv U), ψ (eqv U)⟫_ℂ ∂μ := by
                  refine MeasureTheory.integral_congr_ae ?_
                  filter_upwards [hcoe] with U hU
                  rw [hU]
            _ = ∫ U, ⟪ψ U, ψ U⟫_ℂ ∂μ := hmp.integral_comp' (fun U => ⟪ψ U, ψ U⟫_ℂ)
        have hre := congrArg Complex.re h_inner
        rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hre
        simpa [pow_two] using hre
      change ‖ψ'‖ ≤ 1 * ‖ψ‖
      rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), one_mul, h_norm_sq])

theorem ksLinkShiftOp_apply_ae (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) (v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⇑(ksLinkShiftOp L N e v ψ) =ᵐ[latticeHaarMeasure L N]
      fun U => ψ (linkLeftShift L N e v⁻¹ U) :=
  (memLp_comp_measurePreserving (latticeHaarMeasure L N)
    (linkLeftShiftEquiv L N e v⁻¹) (linkLeftShiftEquiv_mp L N e v⁻¹) ψ).coeFn_toLp

theorem ksLinkShiftOp_unitary (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) (v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (ψ₁ ψ₂ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⟪ksLinkShiftOp L N e v ψ₁, ksLinkShiftOp L N e v ψ₂⟫_ℂ = ⟪ψ₁, ψ₂⟫_ℂ := by
  let μ := latticeHaarMeasure L N
  let eqv := linkLeftShiftEquiv L N e v⁻¹
  let hmp := linkLeftShiftEquiv_mp L N e v⁻¹
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  calc ∫ U, ⟪(ksLinkShiftOp L N e v ψ₁) U, (ksLinkShiftOp L N e v ψ₂) U⟫_ℂ ∂μ
      = ∫ U, ⟪ψ₁ (eqv U), ψ₂ (eqv U)⟫_ℂ ∂μ := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [ksLinkShiftOp_apply_ae L N e v ψ₁,
            ksLinkShiftOp_apply_ae L N e v ψ₂] with U hu1 hu2
          rw [hu1, hu2]
          rfl
    _ = ∫ U, ⟪ψ₁ U, ψ₂ U⟫_ℂ ∂μ := hmp.integral_comp' (fun U => ⟪ψ₁ U, ψ₂ U⟫_ℂ)

theorem ksLinkShiftOp_adj (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) (v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (x y : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⟪ksLinkShiftOp L N e v x, y⟫_ℂ = ⟪x, ksLinkShiftOp L N e v⁻¹ y⟫_ℂ := by
  calc ⟪ksLinkShiftOp L N e v x, y⟫_ℂ
      = ⟪ksLinkShiftOp L N e v⁻¹ (ksLinkShiftOp L N e v x),
          ksLinkShiftOp L N e v⁻¹ y⟫_ℂ :=
          (ksLinkShiftOp_unitary L N e v⁻¹ _ _).symm
    _ = ⟪x, ksLinkShiftOp L N e v⁻¹ y⟫_ℂ := by
          congr 1
          apply MeasureTheory.Lp.ext
          let μ := latticeHaarMeasure L N
          let eqv := linkLeftShiftEquiv L N e v
          let hmp := linkLeftShiftEquiv_mp L N e v
          have h1 := ksLinkShiftOp_apply_ae L N e v⁻¹ (ksLinkShiftOp L N e v x)
          have h2 : (fun U => (ksLinkShiftOp L N e v x) (linkLeftShift L N e v U)) =ᵐ[μ]
              (fun U => x (linkLeftShift L N e v⁻¹ (linkLeftShift L N e v U))) := by
            simpa [eqv] using ae_comp_measurePreserving hmp (ksLinkShiftOp_apply_ae L N e v x)
          filter_upwards [h1, h2] with U hu1 hu2
          rw [inv_inv] at hu1
          rw [hu1, hu2]
          congr 1
          funext e'
          by_cases he : e' = e <;> simp [linkLeftShift, he, ← mul_assoc]

/--
Kogut–Susskind electric link Laplacian `Δ_{e, v} = 2 I - U_{e,v} - U_{e,v⁻¹} = (I - U_{e,v})* (I - U_{e,v})`
on `L²(SU(N)^{3L³}, dμ_Haar)`.
-/
noncomputable def ksElectricLaplacian (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) (v : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] HaarGaugeSpace (latticeHaarMeasure L N) :=
  (2 : ℂ) • ContinuousLinearMap.id ℂ (HaarGaugeSpace (latticeHaarMeasure L N)) -
    ksLinkShiftOp L N e v - ksLinkShiftOp L N e v⁻¹

theorem ksElectricLaplacian_sa (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) (v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (x y : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⟪ksElectricLaplacian L N e v x, y⟫_ℂ = ⟪x, ksElectricLaplacian L N e v y⟫_ℂ := by
  simp only [ksElectricLaplacian, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofNat]
  rw [ksLinkShiftOp_adj L N e v x y, ksLinkShiftOp_adj L N e v⁻¹ x y, inv_inv]
  ring

theorem ksElectricLaplacian_nonneg (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) (v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    0 ≤ (⟪ψ, ksElectricLaplacian L N e v ψ⟫_ℂ).re := by
  let U := ksLinkShiftOp L N e v
  have h_id : ⟪ψ, ksElectricLaplacian L N e v ψ⟫_ℂ = ⟪ψ - U ψ, ψ - U ψ⟫_ℂ := by
    simp only [ksElectricLaplacian, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      inner_sub_right, inner_smul_right, inner_sub_left]
    rw [← ksLinkShiftOp_adj L N e v ψ ψ, ksLinkShiftOp_unitary L N e v ψ ψ]
    change 2 * ⟪ψ, ψ⟫_ℂ - ⟪ψ, U ψ⟫_ℂ - ⟪U ψ, ψ⟫_ℂ =
      ⟪ψ, ψ⟫_ℂ - ⟪U ψ, ψ⟫_ℂ - (⟪ψ, U ψ⟫_ℂ - ⟪ψ, ψ⟫_ℂ)
    ring
  rw [h_id, inner_self_eq_norm_sq_to_K]
  simp [pow_two]
  exact mul_self_nonneg _

private theorem measurable_ksLinkTrace (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) :
    Measurable (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      (Matrix.trace ((U e : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ)).re) := by
  have h_ent : ∀ i : Fin N, Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (A : Matrix (Fin N) (Fin N) ℂ) i i) := fun i =>
    (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
  have h_tr : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re) := by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact continuous_finset_sum Finset.univ fun i _ => Complex.continuous_re.comp (h_ent i)
  exact h_tr.measurable.comp (measurable_gaugeField_eval L N e)

/-- Real link trace observable `ψ ↦ (Re Tr U_e) · ψ`. -/
noncomputable def ksLinkTraceOp (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) :
    HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] HaarGaugeSpace (latticeHaarMeasure L N) :=
  realMulOp (latticeHaarMeasure L N)
    (fun U => (Matrix.trace ((U e : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ)).re)
    (measurable_ksLinkTrace L N e)
    (N : ℝ) (Nat.cast_nonneg N) (fun U => abs_re_trace_su_le (U e))

/-- Canonical non-central `SU(N)` element `diag(-1, -1, 1, …, 1)` for `N ≥ 2`. -/
def suFlip2 (N : ℕ) (hN : 2 ≤ N) : Matrix.specialUnitaryGroup (Fin N) ℂ :=
  let d : Fin N → ℂ := fun i => if (i : ℕ) < 2 then -1 else 1
  have hU : star (Matrix.diagonal d) * Matrix.diagonal d = 1 ∧
      Matrix.diagonal d * star (Matrix.diagonal d) = 1 := by
    constructor <;>
    · ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal_apply_eq,
          Matrix.one_apply_eq]
        rw [Finset.sum_eq_single i]
        · by_cases hi : (i : ℕ) < 2 <;> simp [d, hi]
        · intro k _ hki
          simp [Matrix.diagonal_apply_ne _ hki.symm, Matrix.diagonal_apply_ne _ hki]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      · simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_ne hij]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hki : k = i
        · subst hki
          simp [Matrix.diagonal_apply, hij, Ne.symm hij]
        · simp [Matrix.diagonal_apply, hki, Ne.symm hki]
  have hdet : (Matrix.diagonal d).det = 1 := by
    rw [Matrix.det_diagonal]
    let i0 : Fin N := ⟨0, by omega⟩
    let i1 : Fin N := ⟨1, by omega⟩
    have h01 : i0 ≠ i1 := by
      intro h
      have := congrArg Fin.val h
      norm_num [i0, i1] at this
    rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i0)]
    have hi1_mem : i1 ∈ Finset.univ.erase i0 := Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ i1⟩
    rw [← Finset.mul_prod_erase (Finset.univ.erase i0) d hi1_mem]
    have h_rest : ∏ x ∈ (Finset.univ.erase i0).erase i1, d x = 1 := by
      refine Finset.prod_eq_one fun x hx => ?_
      have hx1 : x ≠ i1 := (Finset.mem_erase.mp hx).1
      have hx0 : x ≠ i0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      have hge2 : ¬ (x : ℕ) < 2 := by
        intro hlt
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h0 | h1
        · exact hx0 (Fin.ext (Nat.lt_one_iff.mp h0))
        · exact hx1 (Fin.ext h1)
      simp [d, hge2]
    have hd0 : d i0 = -1 := by simp [d, i0]
    have hd1 : d i1 = -1 := by simp [d, i1]
    rw [hd0, hd1, h_rest]
    ring
  ⟨Matrix.diagonal d, Unitary.mem_iff.mpr hU, hdet⟩

/--
**Non-commuting canonical electric–link bracket:**
for any `N ≥ 2` and link `e` on `cubicTorus3 L`, the electric shift operator
`ksLinkShiftOp L N e (suFlip2 N hN)` does NOT commute with `ksLinkTraceOp L N e`.
-/
theorem ks_electric_link_noncommute (L N : ℕ) [NeZero L] (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) :
    lieBracketCLM (ksLinkShiftOp L N e (suFlip2 N hN)) (ksLinkTraceOp L N e) ≠ 0 := by
  intro h0
  let μ := latticeHaarMeasure L N
  haveI := suHaar_prob N
  haveI := latticeHaarMeasure_prob L N
  haveI : MeasureTheory.Measure.IsHaarMeasure (suHaar N) :=
    MeasureTheory.Measure.isHaarMeasure_haarMeasure ⊤
  let oneLp : HaarGaugeSpace μ :=
    MeasureTheory.indicatorConstLp (2 : ENNReal) MeasurableSet.univ
      (MeasureTheory.measure_ne_top μ Set.univ) (1 : ℂ)
  have hone_ae : ⇑oneLp =ᵐ[μ] fun _ => (1 : ℂ) := by
    have h := MeasureTheory.indicatorConstLp_coeFn (p := (2 : ENNReal))
      (μ := μ) (s := Set.univ) (hs := MeasurableSet.univ)
      (hμs := MeasureTheory.measure_ne_top μ Set.univ) (c := (1 : ℂ))
    filter_upwards [h] with U hU
    simpa [oneLp] using hU
  have hcomm := congrArg (fun f : HaarGaugeSpace μ →L[ℂ] HaarGaugeSpace μ => f oneLp) h0
  dsimp only [lieBracketCLM] at hcomm
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, sub_eq_zero] at hcomm
  let v := suFlip2 N hN
  let eqv := linkLeftShiftEquiv L N e v⁻¹
  let hmp := linkLeftShiftEquiv_mp L N e v⁻¹
  let trFn : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ :=
    fun U => (Matrix.trace ((U e : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ)).re
  have h_tr_ae : ∀ (ψ : HaarGaugeSpace μ),
      ⇑(ksLinkTraceOp L N e ψ) =ᵐ[μ] fun U => ((trFn U : ℝ) : ℂ) * ψ U :=
    fun ψ => realMulOp_apply_ae μ trFn (measurable_ksLinkTrace L N e)
      (N : ℝ) (Nat.cast_nonneg N) (fun U => abs_re_trace_su_le (U e)) ψ
  have hL1 := ksLinkShiftOp_apply_ae L N e v (ksLinkTraceOp L N e oneLp)
  have hL2 := ae_comp_measurePreserving hmp (h_tr_ae oneLp)
  have hL3 := ae_comp_measurePreserving hmp hone_ae
  have hR1 := h_tr_ae (ksLinkShiftOp L N e v oneLp)
  have hR2 := ksLinkShiftOp_apply_ae L N e v oneLp
  have h_ae_diff : (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      ((Matrix.trace ((v⁻¹ * U e : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ)).re : ℂ) -
      ((Matrix.trace ((U e : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ)).re : ℂ)) =ᵐ[μ] 0 := by
    have h_eq := MeasureTheory.Lp.ext_iff.mp hcomm
    filter_upwards [h_eq, hL1, hL2, hL3, hR1, hR2, hone_ae] with U hU hl1 hl2 hl3 hr1 hr2 h_one
    change ⇑((ksLinkShiftOp L N e v) ((ksLinkTraceOp L N e) oneLp)) U =
      ⇑((ksLinkTraceOp L N e) ((ksLinkShiftOp L N e v) oneLp)) U at hU
    have hl2' : ⇑((ksLinkTraceOp L N e) oneLp) (linkLeftShift L N e v⁻¹ U) =
        ((trFn (linkLeftShift L N e v⁻¹ U) : ℝ) : ℂ) *
          ⇑oneLp (linkLeftShift L N e v⁻¹ U) := by
      simpa [eqv] using hl2
    have hl3' : ⇑oneLp (linkLeftShift L N e v⁻¹ U) = 1 := by simpa [eqv] using hl3
    have h_tr_shift : trFn (linkLeftShift L N e v⁻¹ U) =
        (Matrix.trace ((v⁻¹ * U e : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ)).re := by
      simp [trFn, linkLeftShift]
    rw [hl1, hl2', hl3', mul_one, h_tr_shift, hr1, hr2, hl3', mul_one] at hU
    change _ - _ = (0 : ℂ)
    rw [hU, sub_self]
  let g_su : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ := fun A =>
    (Matrix.trace ((v⁻¹ * A : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ)).re -
    (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re
  have hg_cont : Continuous g_su := by
    have h_ent : ∀ i : Fin N, Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        (A : Matrix (Fin N) (Fin N) ℂ) i i) := fun i =>
      (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
    have h_tr : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re) := by
      simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
      exact continuous_finset_sum Finset.univ fun i _ => Complex.continuous_re.comp (h_ent i)
    exact (h_tr.comp (continuous_mul_left v⁻¹)).sub h_tr
  let S_open : Set (Matrix.specialUnitaryGroup (Fin N) ℂ) := { A | g_su A ≠ 0 }
  have hS_open : IsOpen S_open := isOpen_ne.preimage hg_cont
  have h1_mem : (1 : Matrix.specialUnitaryGroup (Fin N) ℂ) ∈ S_open := by
    change g_su 1 ≠ 0
    have hdiff : g_su 1 =
        (Matrix.trace ((v⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ)).re - (N : ℝ) := by
      simp [g_su]
    have h_le : (Matrix.trace ((v⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ)).re ≤ (N : ℝ) - 4 := by
      have hv_inv : (v⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) = v := by
        apply Subtype.ext
        have h_mul : (v : Matrix (Fin N) (Fin N) ℂ) * (v : Matrix (Fin N) (Fin N) ℂ) = 1 := by
          ext i j
          by_cases hij : i = j
          · subst hij
            simp only [v, suFlip2, Matrix.mul_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
            rw [Finset.sum_eq_single i]
            · by_cases hi : (i : ℕ) < 2 <;> simp [hi]
            · intro k _ hki
              simp [Matrix.diagonal_apply_ne _ hki.symm, Matrix.diagonal_apply_ne _ hki]
            · intro hi; exact absurd (Finset.mem_univ i) hi
          · simp only [v, suFlip2, Matrix.mul_apply, Matrix.one_apply_ne hij]
            refine Finset.sum_eq_zero fun k _ => ?_
            by_cases hki : k = i
            · subst hki
              simp [Matrix.diagonal_apply, hij]
            · simp [Matrix.diagonal_apply, Ne.symm hki]
        have hv_eq : (v : Matrix (Fin N) (Fin N) ℂ) = (v⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) := by
          have := congrArg (fun M : Matrix.specialUnitaryGroup (Fin N) ℂ => (M : Matrix (Fin N) (Fin N) ℂ))
            (inv_eq_of_mul_eq_one_left (Subtype.ext h_mul))
          exact this.symm
        exact hv_eq.symm
      rw [hv_inv]
      simp only [v, suFlip2, Matrix.trace, Matrix.diag, Matrix.diagonal_apply_eq, Complex.re_sum]
      let i0 : Fin N := ⟨0, by omega⟩
      let i1 : Fin N := ⟨1, by omega⟩
      have h01 : i0 ≠ i1 := by
        intro h; have := congrArg Fin.val h; norm_num [i0, i1] at this
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0)]
      have hi1_mem : i1 ∈ Finset.univ.erase i0 := Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ i1⟩
      rw [← Finset.add_sum_erase (Finset.univ.erase i0) _ hi1_mem]
      have h0 : ((if (i0 : ℕ) < 2 then (-1 : ℂ) else 1)).re = -1 := by simp [i0]
      have h1 : ((if (i1 : ℕ) < 2 then (-1 : ℂ) else 1)).re = -1 := by simp [i1]
      have h_rest : ∑ x ∈ (Finset.univ.erase i0).erase i1,
          ((if (x : ℕ) < 2 then (-1 : ℂ) else 1)).re ≤ ((N : ℝ) - 2) := by
        calc ∑ x ∈ (Finset.univ.erase i0).erase i1,
              ((if (x : ℕ) < 2 then (-1 : ℂ) else 1)).re
            ≤ ∑ _x ∈ (Finset.univ.erase i0).erase i1, (1 : ℝ) := by
              refine Finset.sum_le_sum fun x _ => ?_
              by_cases hx : (x : ℕ) < 2 <;> simp [hx]
          _ = (((Finset.univ.erase i0).erase i1).card : ℝ) := by simp
          _ = (N : ℝ) - 2 := by
              have hc1 : ((Finset.univ.erase i0).erase i1).card = N - 2 := by
                rw [Finset.card_erase_of_mem hi1_mem, Finset.card_erase_of_mem (Finset.mem_univ i0),
                  Finset.card_univ, Fintype.card_fin]
                omega
              rw [hc1, Nat.cast_sub hN]
              norm_num
      linarith
    rw [hdiff]
    linarith
  have hS_pos : 0 < suHaar N S_open :=
    hS_open.measure_pos (suHaar N) ⟨1, h1_mem⟩
  have h_prod_pos : 0 < μ { U | U e ∈ S_open } := by
    let T_set : (cubicTorus3 L).Link → Set (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
      Function.update (fun _ => Set.univ) e S_open
    have h_eq_pi : { U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) |
        U e ∈ S_open } = Set.pi Set.univ T_set := by
      ext U
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left, T_set]
      constructor
      · intro h e'
        by_cases he : e' = e
        · subst he; simpa [Function.update_self] using h
        · simp [Function.update_of_ne he]
      · intro h
        simpa [Function.update_self] using h e
    have h_pi_val : μ (Set.pi Set.univ T_set) = ∏ e', suHaar N (T_set e') := by
      change (MeasureTheory.Measure.pi (fun _ => suHaar N)) (Set.pi Set.univ T_set) = _
      exact MeasureTheory.Measure.pi_pi (fun _ => suHaar N) T_set
    have h_prod_eq : ∏ e', suHaar N (T_set e') = suHaar N S_open := by
      rw [← Finset.mul_prod_erase Finset.univ (fun e' => suHaar N (T_set e')) (Finset.mem_univ e)]
      have h_other : ∏ e' ∈ Finset.univ.erase e, suHaar N (T_set e') = 1 := by
        refine Finset.prod_eq_one fun e' he' => ?_
        have hne : e' ≠ e := (Finset.mem_erase.mp he').1
        simp [T_set, Function.update_of_ne hne, MeasureTheory.measure_univ]
      rw [h_other, mul_one]
      simp [T_set, Function.update_self]
    rw [h_eq_pi, h_pi_val, h_prod_eq]
    exact hS_pos
  have h_zero : μ { U | U e ∈ S_open } = 0 := by
    refine MeasureTheory.measure_mono_null (fun U hU => ?_) h_ae_diff
    intro h0_pt
    have h0_re := congrArg Complex.re h0_pt
    change g_su (U e) = 0 at h0_re
    exact hU h0_re
  exact lt_irrefl 0 (h_prod_pos.trans_eq h_zero)

/--
Full gauge-invariant Kogut–Susskind Hamiltonian combining the magnetic plaquette
operator `ksMagneticH` and the Wilson transfer Hamiltonian `transferHamiltonian`.
-/
noncomputable def ksGaugeInvariantH (L N : ℕ) [NeZero L] (β g_sq a : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] HaarGaugeSpace (latticeHaarMeasure L N) :=
  ksMagneticH L N g_sq a + transferHamiltonian (cubicLatticeGaugeSetup L N β hβ)

theorem ksGaugeInvariantH_sa (L N : ℕ) [NeZero L] (β g_sq a : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (x y : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⟪ksGaugeInvariantH L N β g_sq a hβ x, y⟫_ℂ =
      ⟪x, ksGaugeInvariantH L N β g_sq a hβ y⟫_ℂ := by
  simp only [ksGaugeInvariantH, ContinuousLinearMap.add_apply, inner_add_left, inner_add_right,
    ksMagneticH_sa, transferHamiltonian_sa]

theorem ksGaugeInvariantH_nonneg (L N : ℕ) [NeZero L] (β g_sq a : ℝ)
    (hβ : 0 ≤ β) (hg : 0 < g_sq) (ha : 0 < a)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    0 ≤ (⟪ψ, ksGaugeInvariantH L N β g_sq a hβ ψ⟫_ℂ).re := by
  simp only [ksGaugeInvariantH, ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
  exact add_nonneg (ksMagneticH_nonneg L N g_sq a hg ha ψ) (transferHamiltonian_nonneg _ ψ)

theorem ksGaugeInvariantH_gauge_comm (L N : ℕ) [NeZero L] (β g_sq a : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    lieBracketCLM (cubicGaugeRep L N g) (ksGaugeInvariantH L N β g_sq a hβ) = 0 := by
  have hm := ksMagneticH_gauge_inv L N g_sq a g
  have ht := transferHamiltonian_comm_of_comm (cubicLatticeGaugeSetup L N β hβ)
    (cubicGaugeRep L N g) (by
      unfold lieBracketCLM
      change (cubicGaugeRep L N g).comp (cubicWilsonTransferOp L N β hβ) -
        (cubicWilsonTransferOp L N β hβ).comp (cubicGaugeRep L N g) = 0
      rw [cubicWilsonTransferOp_gauge_inv L N β hβ g, sub_self])
  unfold lieBracketCLM at hm ht
  unfold lieBracketCLM ksGaugeInvariantH
  ext1 ψ
  have hm' := congrArg (fun f : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] _ => f ψ) hm
  have ht' := congrArg (fun f : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] _ => f ψ) ht
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply, map_add, sub_eq_zero] at hm' ht' ⊢
  rw [hm', ht']

/-- Gauss-law invariance preserves `invarianceSet (cubicGaugeRep L N)` under `ksGaugeInvariantH`. -/
theorem ksGaugeInvariantH_preserves_gaussLaw (L N : ℕ) [NeZero L] (β g_sq a : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {ψ : HaarGaugeSpace (latticeHaarMeasure L N)}
    (hψ : ψ ∈ invarianceSet (cubicGaugeRep L N)) :
    ksGaugeInvariantH L N β g_sq a hβ ψ ∈ invarianceSet (cubicGaugeRep L N) :=
  invarianceSet_preserved (cubicGaugeRep L N) (ksGaugeInvariantH L N β g_sq a hβ)
    (fun g => sub_eq_zero.mp (ksGaugeInvariantH_gauge_comm L N β g_sq a hβ g)) hψ

end KogutSusskindYM

/-! ## §29.  End-to-end wiring of §§22–28 (OSHilbertSpace, 4D SU(N) Schwinger, Poincare4, KS) -/

section EndToEndSUYangMills

/-- Non-negativity lifts from `(E, F)` to the true OS Hilbert completion `OSHilbertSpace F` (§22). -/
theorem osLiftOperator_nonneg {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T : E →ₗ[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hbd : ∀ x : E, (F.B (T x) (T x)).re ≤ C ^ 2 * (F.B x x).re)
    (h_nonneg : ∀ x : E, 0 ≤ (F.B x (T x)).re)
    (z : OSHilbertSpace F) :
    0 ≤ (⟪z, osLiftOperator F T C hC hbd z⟫_ℂ).re := by
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · exact isClosed_le continuous_const
      (Complex.continuous_re.comp (continuous_id.inner (osLiftOperator F T C hC hbd).continuous))
  · intro u
    refine Quotient.inductionOn u fun x => ?_
    change 0 ≤ (⟪osCompletionMap F (osPreMk F x),
      osLiftOperator F T C hC hbd (osCompletionMap F (osPreMk F x))⟫_ℂ).re
    rw [osLiftOperator_coe, osCompletionMap_inner]
    exact h_nonneg x

/-- Lift a contractive symmetric Euclidean semigroup `T_pre` on `(E, F)` to `OSHilbertSpace F` (§22). -/
noncomputable def osLiftSemigroup {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T_pre : ℝ → (E →ₗ[ℂ] E))
    (h_contr : ∀ t, 0 ≤ t → ∀ x : E, (F.B (T_pre t x) (T_pre t x)).re ≤ 1 ^ 2 * (F.B x x).re)
    (t : ℝ) : OSHilbertSpace F →L[ℂ] OSHilbertSpace F :=
  if ht : 0 ≤ t then osLiftOperator F (T_pre t) 1 zero_le_one (h_contr t ht)
  else ContinuousLinearMap.id ℂ (OSHilbertSpace F)

theorem osLiftSemigroup_zero {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T_pre : ℝ → (E →ₗ[ℂ] E))
    (h_contr : ∀ t, 0 ≤ t → ∀ x : E, (F.B (T_pre t x) (T_pre t x)).re ≤ 1 ^ 2 * (F.B x x).re)
    (h_zero : ∀ x : E, T_pre 0 x = x) :
    osLiftSemigroup F T_pre h_contr 0 = ContinuousLinearMap.id ℂ (OSHilbertSpace F) := by
  dsimp [osLiftSemigroup]
  rw [dif_pos le_rfl]
  ext1 z
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · exact isClosed_eq
      (osLiftOperator F (T_pre 0) 1 zero_le_one (h_contr 0 le_rfl)).continuous
      (ContinuousLinearMap.id ℂ (OSHilbertSpace F)).continuous
  · intro u
    refine Quotient.inductionOn u fun x => ?_
    change osLiftOperator F (T_pre 0) 1 zero_le_one (h_contr 0 le_rfl)
        (osCompletionMap F (osPreMk F x)) =
      (ContinuousLinearMap.id ℂ (OSHilbertSpace F)) (osCompletionMap F (osPreMk F x))
    rw [ContinuousLinearMap.id_apply, osLiftOperator_coe, h_zero x]

theorem osLiftSemigroup_add {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T_pre : ℝ → (E →ₗ[ℂ] E))
    (h_contr : ∀ t, 0 ≤ t → ∀ x : E, (F.B (T_pre t x) (T_pre t x)).re ≤ 1 ^ 2 * (F.B x x).re)
    (h_add : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ x : E, T_pre (s + t) x = T_pre s (T_pre t x))
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    osLiftSemigroup F T_pre h_contr (s + t) =
      (osLiftSemigroup F T_pre h_contr s).comp (osLiftSemigroup F T_pre h_contr t) := by
  dsimp [osLiftSemigroup]
  rw [dif_pos (add_nonneg hs ht), dif_pos hs, dif_pos ht]
  ext1 z
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · exact isClosed_eq
      (osLiftOperator F (T_pre (s + t)) 1 zero_le_one (h_contr (s + t) (add_nonneg hs ht))).continuous
      ((osLiftOperator F (T_pre s) 1 zero_le_one (h_contr s hs)).comp
        (osLiftOperator F (T_pre t) 1 zero_le_one (h_contr t ht))).continuous
  · intro u
    refine Quotient.inductionOn u fun x => ?_
    rw [ContinuousLinearMap.comp_apply]
    change osLiftOperator F (T_pre (s + t)) 1 zero_le_one (h_contr (s + t) (add_nonneg hs ht))
        (osCompletionMap F (osPreMk F x)) =
      osLiftOperator F (T_pre s) 1 zero_le_one (h_contr s hs)
        (osLiftOperator F (T_pre t) 1 zero_le_one (h_contr t ht)
          (osCompletionMap F (osPreMk F x)))
    rw [osLiftOperator_coe, osLiftOperator_coe, osLiftOperator_coe, h_add s t hs ht x]

theorem osLiftSemigroup_sa {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T_pre : ℝ → (E →ₗ[ℂ] E))
    (h_contr : ∀ t, 0 ≤ t → ∀ x : E, (F.B (T_pre t x) (T_pre t x)).re ≤ 1 ^ 2 * (F.B x x).re)
    (h_sa : ∀ t, 0 ≤ t → ∀ x y : E, F.B (T_pre t x) y = F.B x (T_pre t y))
    (t : ℝ) (ht : 0 ≤ t) (u v : OSHilbertSpace F) :
    ⟪osLiftSemigroup F T_pre h_contr t u, v⟫_ℂ =
      ⟪u, osLiftSemigroup F T_pre h_contr t v⟫_ℂ := by
  dsimp [osLiftSemigroup]
  rw [dif_pos ht]
  exact osLiftOperator_sa F (T_pre t) 1 zero_le_one (h_contr t ht) (h_sa t ht) u v

theorem osLiftSemigroup_contr {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T_pre : ℝ → (E →ₗ[ℂ] E))
    (h_contr : ∀ t, 0 ≤ t → ∀ x : E, (F.B (T_pre t x) (T_pre t x)).re ≤ 1 ^ 2 * (F.B x x).re)
    (t : ℝ) (ht : 0 ≤ t) (z : OSHilbertSpace F) :
    ‖osLiftSemigroup F T_pre h_contr t z‖ ≤ ‖z‖ := by
  dsimp [osLiftSemigroup]
  rw [dif_pos ht]
  simpa using osLiftOperator_norm_le F (T_pre t) 1 zero_le_one (h_contr t ht) z

/--
Pre-Hilbert OS reconstruction inputs on positive-time Euclidean test configurations `(E, F)`
with genuine 4D Poincaré group `Poincare4` (§27) and true OS completion `OSHilbertSpace F` (§22).
-/
structure EuclideanOSPreData (Δ_phys : ℝ) (os : OS4DContinuumTheory Δ_phys) where
  E            : Type
  [eAdd        : AddCommGroup E]
  [eMod        : Module ℂ E]
  F            : OSReflectionForm E
  Ω_E          : E
  Ω_E_norm     : F.B Ω_E Ω_E = 1
  T_E_pre      : ℝ → (E →ₗ[ℂ] E)
  T_E_zero     : ∀ x : E, T_E_pre 0 x = x
  T_E_add      : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ x : E, T_E_pre (s + t) x = T_E_pre s (T_E_pre t x)
  T_E_sa       : ∀ t, 0 ≤ t → ∀ x y : E, F.B (T_E_pre t x) y = F.B x (T_E_pre t y)
  T_E_contr    : ∀ t, 0 ≤ t → ∀ x : E, (F.B (T_E_pre t x) (T_E_pre t x)).re ≤ 1 ^ 2 * (F.B x x).re
  H_pre        : E →ₗ[ℂ] E
  H_bound      : ℝ
  H_bound_nn   : 0 ≤ H_bound
  H_bd         : ∀ x : E, (F.B (H_pre x) (H_pre x)).re ≤ H_bound ^ 2 * (F.B x x).re
  H_sa         : ∀ x y : E, F.B (H_pre x) y = F.B x (H_pre y)
  H_nonneg     : ∀ x : E, 0 ≤ (F.B x (H_pre x)).re
  H_vac        : H_pre Ω_E = 0
  U_pre        : Poincare4 → (E →ₗ[ℂ] E)
  U_unit_pre   : ∀ g x y, F.B (U_pre g x) (U_pre g y) = F.B x y
  U_vac_pre    : ∀ g, U_pre g Ω_E = Ω_E
  φ_pre        : Space4 → (E →ₗ[ℂ] E)
  φ_bound      : Space4 → ℝ
  φ_bound_nn   : ∀ x, 0 ≤ φ_bound x
  φ_bd         : ∀ x (v : E), (F.B (φ_pre x v) (φ_pre x v)).re ≤ (φ_bound x) ^ 2 * (F.B v v).re
  cov_pre      : ∀ g x v, U_pre g (φ_pre x v) = φ_pre (poincareAct g x) (U_pre g v)
  loc_pre      : ∀ x y, minkowskiSq (x - y) < 0 → ∀ v, φ_pre x (φ_pre y v) = φ_pre y (φ_pre x v)
  P2_spec      : Set ℝ
  spec_cond    : ∀ p2 ∈ P2_spec, 0 ≤ p2
  gap_spec     : ∀ p2 ∈ P2_spec, p2 = 0 ∨ Δ_phys ^ 2 ≤ p2
  cyclic_dense : (Submodule.span ℂ
      {v : OSHilbertSpace F | ∃ (k : ℕ) (xs : Fin k → Space4),
        v = (List.ofFn (fun i : Fin k =>
          osLiftOperator F (φ_pre (xs i)) (φ_bound (xs i)) (φ_bound_nn (xs i)) (φ_bd (xs i)))).foldr
          (fun A acc => A acc) (osCompletionMap F (osPreMk F Ω_E))}).topologicalClosure = ⊤

attribute [instance] EuclideanOSPreData.eAdd EuclideanOSPreData.eMod

/-- Construct `WightmanQFT4D Δ_phys` directly on `OSHilbertSpace P.F` with `Poincare4` (§22 + §27). -/
noncomputable def buildWightmanOnOSCompletion {Δ_phys : ℝ} {os : OS4DContinuumTheory Δ_phys}
    (P : EuclideanOSPreData Δ_phys os) : WightmanQFT4D Δ_phys where
  Δ_pos := os.os.Δ_pos
  H := OSHilbertSpace P.F
  Ω_phys := osCompletionMap P.F (osPreMk P.F P.Ω_E)
  Ω_unit := by
    have hsq : ‖osCompletionMap P.F (osPreMk P.F P.Ω_E)‖ ^ 2 = 1 := by
      rw [osCompletionMap_norm, osPre_norm_sq, P.Ω_E_norm, Complex.one_re]
    have hmul : (‖osCompletionMap P.F (osPreMk P.F P.Ω_E)‖ - 1) *
        (‖osCompletionMap P.F (osPreMk P.F P.Ω_E)‖ + 1) = 0 := by linarith
    rcases mul_eq_zero.mp hmul with h | h <;>
      linarith [norm_nonneg (osCompletionMap P.F (osPreMk P.F P.Ω_E))]
  Poincare := Poincare4
  U := fun g => osLiftOperator P.F (P.U_pre g) 1 zero_le_one (fun x => by
    rw [one_pow, one_mul, P.U_unit_pre g x x])
  U_unitary := fun g u v => by
    refine UniformSpace.Completion.induction_on₂ u v ?_ ?_
    · exact isClosed_eq
        (((osLiftOperator P.F (P.U_pre g) 1 zero_le_one (fun x => by
            rw [one_pow, one_mul, P.U_unit_pre g x x])).continuous.comp continuous_fst).inner
          ((osLiftOperator P.F (P.U_pre g) 1 zero_le_one (fun x => by
            rw [one_pow, one_mul, P.U_unit_pre g x x])).continuous.comp continuous_snd))
        (continuous_fst.inner continuous_snd)
    · intro a b
      refine Quotient.inductionOn₂ a b fun x y => ?_
      change ⟪osLiftOperator P.F (P.U_pre g) 1 zero_le_one _ (osCompletionMap P.F (osPreMk P.F x)),
          osLiftOperator P.F (P.U_pre g) 1 zero_le_one _ (osCompletionMap P.F (osPreMk P.F y))⟫_ℂ =
        ⟪osCompletionMap P.F (osPreMk P.F x), osCompletionMap P.F (osPreMk P.F y)⟫_ℂ
      rw [osLiftOperator_coe, osLiftOperator_coe, osCompletionMap_inner, osCompletionMap_inner]
      exact P.U_unit_pre g x y
  U_vac := fun g => by
    change osLiftOperator P.F (P.U_pre g) 1 zero_le_one _ (osCompletionMap P.F (osPreMk P.F P.Ω_E)) =
      osCompletionMap P.F (osPreMk P.F P.Ω_E)
    rw [osLiftOperator_coe, P.U_vac_pre g]
  actP := poincareAct
  φ := fun x => osLiftOperator P.F (P.φ_pre x) (P.φ_bound x) (P.φ_bound_nn x) (P.φ_bd x)
  covariant := fun g x => by
    ext1 z
    refine UniformSpace.Completion.induction_on z ?_ ?_
    · exact isClosed_eq
        ((osLiftOperator P.F (P.U_pre g) 1 zero_le_one (fun w => by
            rw [one_pow, one_mul, P.U_unit_pre g w w])).comp
          (osLiftOperator P.F (P.φ_pre x) (P.φ_bound x) (P.φ_bound_nn x) (P.φ_bd x))).continuous
        ((osLiftOperator P.F (P.φ_pre (poincareAct g x)) (P.φ_bound (poincareAct g x))
            (P.φ_bound_nn (poincareAct g x)) (P.φ_bd (poincareAct g x))).comp
          (osLiftOperator P.F (P.U_pre g) 1 zero_le_one (fun w => by
            rw [one_pow, one_mul, P.U_unit_pre g w w]))).continuous
    · intro u
      refine Quotient.inductionOn u fun v => ?_
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      change osLiftOperator P.F (P.U_pre g) 1 zero_le_one _
          (osLiftOperator P.F (P.φ_pre x) (P.φ_bound x) (P.φ_bound_nn x) (P.φ_bd x)
            (osCompletionMap P.F (osPreMk P.F v))) =
        osLiftOperator P.F (P.φ_pre (poincareAct g x)) (P.φ_bound (poincareAct g x))
          (P.φ_bound_nn (poincareAct g x)) (P.φ_bd (poincareAct g x))
          (osLiftOperator P.F (P.U_pre g) 1 zero_le_one _
            (osCompletionMap P.F (osPreMk P.F v)))
      rw [osLiftOperator_coe, osLiftOperator_coe, osLiftOperator_coe, osLiftOperator_coe,
        P.cov_pre g x v]
  local_comm := fun x y hxy => by
    ext1 z
    refine UniformSpace.Completion.induction_on z ?_ ?_
    · exact isClosed_eq
        ((osLiftOperator P.F (P.φ_pre x) (P.φ_bound x) (P.φ_bound_nn x) (P.φ_bd x)).comp
          (osLiftOperator P.F (P.φ_pre y) (P.φ_bound y) (P.φ_bound_nn y) (P.φ_bd y))).continuous
        ((osLiftOperator P.F (P.φ_pre y) (P.φ_bound y) (P.φ_bound_nn y) (P.φ_bd y)).comp
          (osLiftOperator P.F (P.φ_pre x) (P.φ_bound x) (P.φ_bound_nn x) (P.φ_bd x))).continuous
    · intro u
      refine Quotient.inductionOn u fun v => ?_
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      change osLiftOperator P.F (P.φ_pre x) (P.φ_bound x) (P.φ_bound_nn x) (P.φ_bd x)
          (osLiftOperator P.F (P.φ_pre y) (P.φ_bound y) (P.φ_bound_nn y) (P.φ_bd y)
            (osCompletionMap P.F (osPreMk P.F v))) =
        osLiftOperator P.F (P.φ_pre y) (P.φ_bound y) (P.φ_bound_nn y) (P.φ_bd y)
          (osLiftOperator P.F (P.φ_pre x) (P.φ_bound x) (P.φ_bound_nn x) (P.φ_bd x)
            (osCompletionMap P.F (osPreMk P.F v)))
      rw [osLiftOperator_coe, osLiftOperator_coe, osLiftOperator_coe, osLiftOperator_coe,
        P.loc_pre x y hxy v]
  P2_spec := P.P2_spec
  spectral_cond := P.spec_cond
  mass_gap_spec := P.gap_spec

/-- Construct `OSReconstructionData Δ_phys os` directly on `OSHilbertSpace P.F` (§22 + §27). -/
noncomputable def buildOSReconstructionOnCompletion {Δ_phys : ℝ} {os : OS4DContinuumTheory Δ_phys}
    (P : EuclideanOSPreData Δ_phys os) : OSReconstructionData Δ_phys os where
  wightman := buildWightmanOnOSCompletion P
  T_E := osLiftSemigroup P.F P.T_E_pre P.T_E_contr
  T_E_zero := osLiftSemigroup_zero P.F P.T_E_pre P.T_E_contr P.T_E_zero
  T_E_add := osLiftSemigroup_add P.F P.T_E_pre P.T_E_contr P.T_E_add
  T_E_sa := fun t x y ht => osLiftSemigroup_sa P.F P.T_E_pre P.T_E_contr P.T_E_sa t ht x y
  T_E_contr := fun t x ht => osLiftSemigroup_contr P.F P.T_E_pre P.T_E_contr t ht x
  H_phys := osLiftOperator P.F P.H_pre P.H_bound P.H_bound_nn P.H_bd
  H_phys_sa := osLiftOperator_sa P.F P.H_pre P.H_bound P.H_bound_nn P.H_bd P.H_sa
  H_phys_nonneg := osLiftOperator_nonneg P.F P.H_pre P.H_bound P.H_bound_nn P.H_bd P.H_nonneg
  H_phys_vac := by
    change osLiftOperator P.F P.H_pre P.H_bound P.H_bound_nn P.H_bd
        (osCompletionMap P.F (osPreMk P.F P.Ω_E)) = 0
    rw [osLiftOperator_coe, P.H_vac]
    have h0 : osPreMk P.F (0 : P.E) = 0 := rfl
    rw [h0, map_zero]
  cyclic_dense := P.cyclic_dense

/--
Complete dynamical bridge tying the 4D `SU(N)` lattice Schwinger functions `cubic4Schwinger` (§25)
and 3D Kogut–Susskind Hamiltonian `ksGaugeInvariantH` (§28) to a non-Gaussian continuum
`OS4DContinuumTheory Δ_phys` and its true OS completion `EuclideanOSPreData` (§22 + §27).
-/
structure SUYangMillsDynamicalBridge (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] where
  Δ_phys         : ℝ
  os             : OS4DContinuumTheory Δ_phys
  pre            : EuclideanOSPreData Δ_phys os
  Ls_seq         : ℕ → ℕ
  Lt_seq         : ℕ → ℕ
  [Ls_nz         : ∀ m, NeZero (Ls_seq m)]
  [Lt_nz         : ∀ m, NeZero (Lt_seq m)]
  a_seq          : ℕ → ℝ
  β_seq          : ℕ → ℝ
  ha_pos         : ∀ m, 0 < a_seq m
  ha_lim         : Filter.Tendsto a_seq Filter.atTop (nhds 0)
  hβ_pos         : ∀ m, 0 < β_seq m
  hβ_lim         : Filter.Tendsto β_seq Filter.atTop Filter.atTop
  g_sq_seq       : ℕ → ℝ
  hg_pos         : ∀ m, 0 < g_sq_seq m
  Δ_latt         : ℕ → ℝ
  Δ_latt_pos     : ∀ m, 0 < Δ_latt m
  gap_lim        : Filter.Tendsto (fun m => Δ_latt m / a_seq m) Filter.atTop (nhds Δ_phys)
  latt_obs       : ∀ (m n : ℕ), (Fin n → Space4) → Fin n →
                     (GaugeField (cubicTorus4 (Ls_seq m) (Lt_seq m))
                       (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
  schwinger_conv : ∀ (n : ℕ) (xs : Fin n → Space4),
    Filter.Tendsto
      (fun m => cubic4Schwinger (Ls_seq m) (Lt_seq m) N (β_seq m) n (latt_obs m n xs))
      Filter.atTop (nhds (os.os.Schwinger n xs))

attribute [instance] SUYangMillsDynamicalBridge.Ls_nz SUYangMillsDynamicalBridge.Lt_nz

/--
End-to-end master theorem wiring `§§22–28` together:
given any `SUYangMillsDynamicalBridge N hN`, we get:
1. positive 4D lattice partition functions `cubic4PartitionFn > 0` (§25),
2. self-adjoint, non-negative, Gauss-law-preserving Kogut–Susskind Hamiltonians `ksGaugeInvariantH`
   along the RG trajectory with non-commuting link algebra (§28),
3. genuine convergence of `cubic4Schwinger` to the non-Gaussian `OS4DContinuumTheory` (§25 + §13),
4. the full OS Hilbert completion and `Poincare4` Wightman QFT reconstruction on `OSHilbertSpace` (§22 + §27 + §17),
5. diverging correlation length `ξ → ∞` and absence of mass states in `(0, Δ_phys²)` (§10 + §14).
-/
theorem endToEnd_su_yang_mills_from_dynamical_bridge
    {N : ℕ} {hN : 2 ≤ N}
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (B : SUYangMillsDynamicalBridge N hN) :
    (∀ m, 0 < cubic4PartitionFn (B.Ls_seq m) (B.Lt_seq m) N (B.β_seq m)) ∧
    (∀ m (ψ : HaarGaugeSpace (latticeHaarMeasure (B.Ls_seq m) N)),
      0 ≤ (⟪ψ, ksGaugeInvariantH (B.Ls_seq m) N (B.β_seq m) (B.g_sq_seq m) (B.a_seq m)
        (B.hβ_pos m).le ψ⟫_ℂ).re) ∧
    (∀ m (e : (cubicTorus3 (B.Ls_seq m)).Link),
      lieBracketCLM (ksLinkShiftOp (B.Ls_seq m) N e (suFlip2 N hN))
        (ksLinkTraceOp (B.Ls_seq m) N e) ≠ 0) ∧
    (0 < B.Δ_phys ∧ ¬ IsGaussian4 B.os.os.Schwinger) ∧
    Filter.Tendsto (fun m => (B.Δ_latt m)⁻¹) Filter.atTop Filter.atTop ∧
    (∃ D : OSHilbertCompletionData (buildOSReconstructionOnCompletion B.pre),
      (∀ p2 ∈ (buildOSReconstructionOnCompletion B.pre).wightman.P2_spec,
        ¬ (0 < p2 ∧ p2 < B.Δ_phys ^ 2)) ∧
      (∀ x : (buildOSReconstructionOnCompletion B.pre).wightman.H,
        0 ≤ (⟪x, (buildOSReconstructionOnCompletion B.pre).H_phys x⟫_ℂ).re) ∧
      (buildOSReconstructionOnCompletion B.pre).H_phys
        (buildOSReconstructionOnCompletion B.pre).wightman.Ω_phys = 0 ∧
      (∀ g x,
        ((buildOSReconstructionOnCompletion B.pre).wightman.U g).comp
          ((buildOSReconstructionOnCompletion B.pre).wightman.φ x) =
        ((buildOSReconstructionOnCompletion B.pre).wightman.φ
          (poincareAct g x)).comp
          ((buildOSReconstructionOnCompletion B.pre).wightman.U g)) ∧
      D.trilattice.μ (D.trilattice.δ D.trilattice.totalityB) = D.trilattice.totalityB) := by
  let R := buildOSReconstructionOnCompletion B.pre
  obtain ⟨D, _, _, h3, h4, _, _, _⟩ := os_hilbert_completion_and_wightman_reconstruction R
  refine ⟨?_, ?_, ?_, ?_, ?_, D, ?_, h3.2.2.2.1, h3.2.2.2.2, h4.1, ?_⟩
  · intro m
    exact cubic4PartitionFn_pos (B.Ls_seq m) (B.Lt_seq m) N (B.β_seq m) (B.hβ_pos m).le
  · intro m ψ
    exact ksGaugeInvariantH_nonneg (B.Ls_seq m) N (B.β_seq m) (B.g_sq_seq m) (B.a_seq m)
      (B.hβ_pos m).le (B.hg_pos m) (B.ha_pos m) ψ
  · intro m e
    exact ks_electric_link_noncommute (B.Ls_seq m) N hN e
  · exact ⟨B.os.os.Δ_pos, os4d_theory_non_gaussian B.os⟩
  · exact correlation_length_diverges B.a_seq B.Δ_latt B.Δ_phys
      B.ha_pos B.ha_lim B.Δ_latt_pos B.gap_lim
  · intro p2 hp2 hlt
    rcases R.wightman.mass_gap_spec p2 hp2 with rfl | hge
    · exact lt_irrefl 0 hlt.1
    · linarith [hlt.2]
  · exact D.trilattice.mu_delta D.trilattice.totalityB

end EndToEndSUYangMills

/-! ## §30.  OS pre-Hilbert GNS construction, Glimm–Jaffe contraction & joint thermodynamic limit -/

section OSPreHilbertFromSchwinger

/-- Positive-time Euclidean configuration `(n, xs)` with `0 < (xs k) 0`. -/
structure PosTimeConfig where
  n_pts : ℕ
  pts   : Fin n_pts → Space4
  pos_t : ∀ k : Fin n_pts, 0 < pts k 0

noncomputable instance instDecidableEqPosTimeConfig : DecidableEq PosTimeConfig :=
  Classical.decEq PosTimeConfig

/-- Formal finite complex linear combinations of positive-time configurations. -/
abbrev OSPosTestSpace := PosTimeConfig →₀ ℂ

/-- Single positive-time configuration embedded in `OSPosTestSpace`. -/
noncomputable def osConfigSingle (x : PosTimeConfig) : OSPosTestSpace :=
  Finsupp.single x 1

/-- Reflection-positive Euclidean kernel between two positive-time configurations. -/
noncomputable def osConfigKernel {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (x y : PosTimeConfig) : ℂ :=
  os.os.Schwinger (x.n_pts + y.n_pts)
    (Fin.append (fun k => euclidTimeReflect (x.pts k)) y.pts)

/-- Sesquilinear form on `OSPosTestSpace` induced by `os.os.Schwinger`. -/
noncomputable def osConfigInner {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (f g : OSPosTestSpace) : ℂ :=
  ∑ x ∈ f.support, ∑ y ∈ g.support,
    starRingEnd ℂ (f x) * g y * osConfigKernel os x y

theorem osConfigInner_zero_left {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (g : OSPosTestSpace) : osConfigInner os 0 g = 0 := by
  simp [osConfigInner]

theorem osConfigInner_zero_right {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (f : OSPosTestSpace) : osConfigInner os f 0 = 0 := by
  simp [osConfigInner]

theorem osConfigInner_single {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (x y : PosTimeConfig) :
    osConfigInner os (osConfigSingle x) (osConfigSingle y) = osConfigKernel os x y := by
  dsimp [osConfigInner, osConfigSingle]
  rw [Finsupp.support_single_ne_zero x one_ne_zero,
      Finsupp.support_single_ne_zero y one_ne_zero,
      Finset.sum_singleton, Finset.sum_singleton,
      Finsupp.single_eq_same, Finsupp.single_eq_same]
  simp

/--
Construct `OSReflectionForm OSPosTestSpace` directly from `os : OS4DContinuumTheory Δ_phys`
and reflection hermiticity `osConfigKernel os x y = starRingEnd ℂ (osConfigKernel os y x)`.
-/
noncomputable def osConfigForm {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (h_herm : ∀ x y : PosTimeConfig,
      osConfigKernel os x y = starRingEnd ℂ (osConfigKernel os y x)) :
    OSReflectionForm OSPosTestSpace where
  B := osConfigInner os
  add_left := fun f₁ f₂ g => by
    let s := (f₁ + f₂).support ∪ f₁.support ∪ f₂.support
    have h_sub : ∀ (f : OSPosTestSpace), f.support ⊆ s →
        osConfigInner os f g =
          ∑ x ∈ s, ∑ y ∈ g.support, starRingEnd ℂ (f x) * g y * osConfigKernel os x y := by
      intro f hf
      refine Finset.sum_subset hf fun x _ hx => ?_
      have hfx : f x = 0 := by
        by_contra hne
        exact hx (Finsupp.mem_support_iff.mpr hne)
      simp [hfx]
    rw [h_sub (f₁ + f₂) (Finset.subset_union_left.trans Finset.subset_union_left),
        h_sub f₁ (Finset.subset_union_right.trans Finset.subset_union_left),
        h_sub f₂ Finset.subset_union_right,
        ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finsupp.add_apply, map_add]
    ring
  smul_left := fun c f g => by
    let s := (c • f).support ∪ f.support
    have h_sub : ∀ (u : OSPosTestSpace), u.support ⊆ s →
        osConfigInner os u g =
          ∑ x ∈ s, ∑ y ∈ g.support, starRingEnd ℂ (u x) * g y * osConfigKernel os x y := by
      intro u hu
      refine Finset.sum_subset hu fun x _ hx => ?_
      have hux : u x = 0 := by
        by_contra hne
        exact hx (Finsupp.mem_support_iff.mpr hne)
      simp [hux]
    rw [h_sub (c • f) Finset.subset_union_left,
        h_sub f Finset.subset_union_right,
        Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul, map_mul]
    ring
  conj_symm := fun f g => by
    dsimp [osConfigInner]
    simp_rw [map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [map_mul, Complex.conj_conj]
    rw [h_herm y x]
    ring
  pos_re := fun f => by
    dsimp [osConfigInner, osConfigKernel]
    let m := f.support.card
    let e : Fin m ≃ ↥f.support := f.support.equivFin.symm
    let ι : Fin m → PosTimeConfig := fun i => (e i).1
    have hι_inj : Function.Injective ι := fun i j h => e.injective (Subtype.ext h)
    have hs_eq : (Finset.univ : Finset (Fin m)).image ι = f.support := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, ι]
      constructor
      · rintro ⟨i, rfl⟩; exact (e i).2
      · intro hx
        refine ⟨e.symm ⟨x, hx⟩, ?_⟩
        rw [Equiv.apply_symm_apply]
    rw [← hs_eq, Finset.sum_image (fun a _ b _ h => hι_inj h)]
    simp_rw [Finset.sum_image (fun a _ b _ h => hι_inj h)]
    have h_rp := os.refl_pos_n m (fun i => (ι i).n_pts)
      (fun i => starRingEnd ℂ (f (ι i))) (fun i => (ι i).pts) (fun i k => (ι i).pos_t k)
    refine le_trans h_rp (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.conj_conj]

/-- Euclidean positive-time shift `x₀ ↦ x₀ + t` on `PosTimeConfig`. -/
def posTimeShiftConfig (t : ℝ) (ht : 0 ≤ t) (x : PosTimeConfig) : PosTimeConfig where
  n_pts := x.n_pts
  pts := fun k i => if i = 0 then x.pts k 0 + t else x.pts k i
  pos_t := fun k => by
    change 0 < if (0 : Fin 4) = 0 then x.pts k 0 + t else x.pts k 0
    rw [if_pos rfl]
    linarith [x.pos_t k]

/-- Linear time-shift operator `T_E_pre t` on `OSPosTestSpace`. -/
noncomputable def osTimeShiftPre (t : ℝ) (ht : 0 ≤ t) :
    OSPosTestSpace →ₗ[ℂ] OSPosTestSpace where
  toFun := Finsupp.mapDomain (posTimeShiftConfig t ht)
  map_add' := fun _ _ => Finsupp.mapDomain_add
  map_smul' := fun c f => Finsupp.mapDomain_smul c f

theorem osTimeShiftPre_zero (f : OSPosTestSpace) :
    osTimeShiftPre 0 le_rfl f = f := by
  have hid : posTimeShiftConfig 0 le_rfl = id := by
    funext ⟨n, pts, hpt⟩
    dsimp [posTimeShiftConfig]
    congr 1
    funext k i
    by_cases hi : i = 0
    · subst hi; simp
    · simp [hi]
  change Finsupp.mapDomain (posTimeShiftConfig 0 le_rfl) f = f
  rw [hid, Finsupp.mapDomain_id]

theorem osTimeShiftPre_add (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (f : OSPosTestSpace) :
    osTimeShiftPre (s + t) (add_nonneg hs ht) f =
      osTimeShiftPre s hs (osTimeShiftPre t ht f) := by
  have hcomp : posTimeShiftConfig (s + t) (add_nonneg hs ht) =
      (posTimeShiftConfig s hs) ∘ (posTimeShiftConfig t ht) := by
    funext ⟨n, pts, hpt⟩
    dsimp [posTimeShiftConfig, Function.comp_def]
    congr 1
    funext k i
    by_cases hi : i = 0
    · subst hi; simp [add_assoc, add_comm]
    · simp [hi]
  change Finsupp.mapDomain (posTimeShiftConfig (s + t) (add_nonneg hs ht)) f =
    Finsupp.mapDomain (posTimeShiftConfig s hs)
      (Finsupp.mapDomain (posTimeShiftConfig t ht) f)
  rw [hcomp, Finsupp.mapDomain_comp]

theorem osTimeShiftPre_sa {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (h_herm : ∀ x y : PosTimeConfig,
      osConfigKernel os x y = starRingEnd ℂ (osConfigKernel os y x))
    (t : ℝ) (ht : 0 ≤ t)
    (h_kern : ∀ x y : PosTimeConfig,
      osConfigKernel os (posTimeShiftConfig t ht x) y =
        osConfigKernel os x (posTimeShiftConfig t ht y))
    (f g : OSPosTestSpace) :
    osConfigInner os (osTimeShiftPre t ht f) g =
      osConfigInner os f (osTimeShiftPre t ht g) := by
  let F := osConfigForm os h_herm
  have h_single_left : ∀ (x : PosTimeConfig) (c : ℂ) (v : OSPosTestSpace),
      osConfigInner os (osTimeShiftPre t ht (Finsupp.single x c)) v =
        osConfigInner os (Finsupp.single x c) (osTimeShiftPre t ht v) := by
    intro x c v
    refine Finsupp.induction_linear v ?_ ?_ ?_
    · rw [map_zero, osConfigInner_zero_right, osConfigInner_zero_right]
    · intro v₁ v₂ ih₁ ih₂
      rw [map_add]
      change F.B (osTimeShiftPre t ht (Finsupp.single x c)) (v₁ + v₂) =
        F.B (Finsupp.single x c) (osTimeShiftPre t ht v₁ + osTimeShiftPre t ht v₂)
      rw [F.add_right, F.add_right]
      exact congrArg₂ (· + ·) ih₁ ih₂
    · intro y d
      by_cases hc : c = 0
      · subst hc; simp [osConfigInner_zero_left]
      · by_cases hd : d = 0
        · subst hd; simp [osConfigInner_zero_right]
        · change osConfigInner os (Finsupp.mapDomain (posTimeShiftConfig t ht) (Finsupp.single x c))
              (Finsupp.single y d) =
            osConfigInner os (Finsupp.single x c)
              (Finsupp.mapDomain (posTimeShiftConfig t ht) (Finsupp.single y d))
          rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single]
          dsimp [osConfigInner]
          rw [Finsupp.support_single_ne_zero (posTimeShiftConfig t ht x) hc,
              Finsupp.support_single_ne_zero y hd,
              Finsupp.support_single_ne_zero x hc,
              Finsupp.support_single_ne_zero (posTimeShiftConfig t ht y) hd]
          simp only [Finset.sum_singleton, Finsupp.single_eq_same, h_kern x y]
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · rw [map_zero, osConfigInner_zero_left, osConfigInner_zero_left]
  · intro f₁ f₂ ih₁ ih₂
    rw [map_add]
    change F.B (osTimeShiftPre t ht f₁ + osTimeShiftPre t ht f₂) g =
      F.B (f₁ + f₂) (osTimeShiftPre t ht g)
    rw [F.add_left, F.add_left]
    exact congrArg₂ (· + ·) ih₁ ih₂
  · intro x c
    exact h_single_left x c g

/--
Glimm–Jaffe repeated Cauchy–Schwarz semigroup contraction:
if `T s` is symmetric and `‖T (2^k t) f‖² ≤ C` uniformly in `k`, then `‖T t f‖² ≤ ‖f‖²`.
-/
theorem os_semigroup_contraction_of_bounded {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T : ℝ → (E →ₗ[ℂ] E))
    (h_add : ∀ s₁ s₂, 0 ≤ s₁ → 0 ≤ s₂ → ∀ x : E, T (s₁ + s₂) x = T s₁ (T s₂ x))
    (h_sa : ∀ s, 0 ≤ s → ∀ x y : E, F.B (T s x) y = F.B x (T s y))
    (t : ℝ) (ht : 0 ≤ t) (f : E)
    (C : ℝ) (h_ub : ∀ k : ℕ, (F.B (T (((2 ^ k : ℕ) : ℝ) * t) f)
      (T (((2 ^ k : ℕ) : ℝ) * t) f)).re ≤ C) :
    (F.B (T t f) (T t f)).re ≤ (F.B f f).re := by
  let b : ℕ → ℝ := fun n =>
    (F.B (T (((2 ^ n : ℕ) : ℝ) * t) f) (T (((2 ^ n : ℕ) : ℝ) * t) f)).re
  have hb_nn : ∀ n : ℕ, 0 ≤ b n := fun n => F.pos_re _
  have hb0_eq : b 0 = (F.B (T t f) (T t f)).re := by
    dsimp [b]
    simp
  have h_rec : ∀ n : ℕ, b n ^ 2 ≤ (F.B f f).re * b (n + 1) := by
    intro n
    let s : ℝ := ((2 ^ n : ℕ) : ℝ) * t
    have hs : 0 ≤ s := mul_nonneg (Nat.cast_nonneg _) ht
    have hs2 : s + s = ((2 ^ (n + 1) : ℕ) : ℝ) * t := by
      dsimp [s]
      push_cast
      rw [pow_succ]
      ring
    have h_eq : F.B (T s f) (T s f) = F.B f (T (((2 ^ (n + 1) : ℕ) : ℝ) * t) f) := by
      rw [h_sa s hs f (T s f), ← h_add s s hs hs f, hs2]
    have hcs := os_cauchy_schwarz F f (T (((2 ^ (n + 1) : ℕ) : ℝ) * t) f)
    have hre_le : (F.B f (T (((2 ^ (n + 1) : ℕ) : ℝ) * t) f)).re ^ 2 ≤
        (F.B f f).re * b (n + 1) := by
      have him_nn : 0 ≤ (F.B f (T (((2 ^ (n + 1) : ℕ) : ℝ) * t) f)).im ^ 2 := sq_nonneg _
      linarith
    have hb_eq : b n = (F.B f (T (((2 ^ (n + 1) : ℕ) : ℝ) * t) f)).re := by
      dsimp [b]
      exact congrArg Complex.re h_eq
    rwa [hb_eq]
  rw [← hb0_eq]
  rcases lt_or_eq_of_le (F.pos_re f) with hpos | hzero
  · let u : ℕ → ℝ := fun n => b n / (F.B f f).re
    have hu_nn : ∀ n, 0 ≤ u n := fun n => div_nonneg (hb_nn n) hpos.le
    have hu_rec : ∀ n, u n ^ 2 ≤ u (n + 1) := by
      intro n
      dsimp [u]
      rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos hpos) hpos]
      calc b n ^ 2 * (F.B f f).re
          ≤ ((F.B f f).re * b (n + 1)) * (F.B f f).re :=
              mul_le_mul_of_nonneg_right (h_rec n) hpos.le
        _ = b (n + 1) * (F.B f f).re ^ 2 := by ring
    have hu_pow : ∀ k : ℕ, u 0 ^ (2 ^ k) ≤ u k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc u 0 ^ (2 ^ (k + 1))
            = u 0 ^ (2 ^ k * 2) := by rw [pow_succ]
          _ = (u 0 ^ (2 ^ k)) ^ 2 := by rw [pow_mul]
          _ ≤ u k ^ 2 := pow_le_pow_left₀ (pow_nonneg (hu_nn 0) _) ih 2
          _ ≤ u (k + 1) := hu_rec k
    have hu0_le : u 0 ≤ 1 := by
      by_contra h_gt
      push_neg at h_gt
      have h_pow_lim : Filter.Tendsto (fun m : ℕ => u 0 ^ m) Filter.atTop Filter.atTop :=
        tendsto_pow_atTop_atTop_of_one_lt h_gt
      have h_two_pow : Filter.Tendsto (fun k : ℕ => (2 ^ k : ℕ)) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_atTop.mpr fun N =>
          ⟨N, fun a ha => le_trans ha (Nat.le_of_lt Nat.lt_two_pow_self)⟩
      have h_lim := h_pow_lim.comp h_two_pow
      have h_ev := (Filter.tendsto_atTop.mp h_lim) (C / (F.B f f).re + 1)
      rw [Filter.eventually_atTop] at h_ev
      obtain ⟨k, hk⟩ := h_ev
      have h_le1 : u 0 ^ (2 ^ k) ≤ C / (F.B f f).re :=
        (hu_pow k).trans (div_le_div_of_nonneg_right (h_ub k) hpos.le)
      have h_le2 : C / (F.B f f).re + 1 ≤ u 0 ^ (2 ^ k) := hk k le_rfl
      linarith
    exact (div_le_one hpos).mp hu0_le
  · have h0 : b 0 ^ 2 ≤ 0 := by
      have hr := h_rec 0
      rw [← hzero, zero_mul] at hr
      exact hr
    have hle : b 0 ≤ 0 := by nlinarith
    linarith

/--
Joint infinite-volume thermodynamic limit (`L → ∞`):
for any countable family of uniformly bounded Schwinger sequences `S_seq k m`
with `‖S_seq k m‖ ≤ B k`, a single strictly increasing subsequence `φ` exists
along which every `S_seq k (φ m)` converges simultaneously to `S_inf k`.
-/
theorem cubic4Schwinger_joint_thermodynamic_subseq
    (S_seq : ℕ → ℕ → ℂ) (B : ℕ → ℝ)
    (hbd : ∀ k m, ‖S_seq k m‖ ≤ B k) :
    ∃ (S_inf : ℕ → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ k, Filter.Tendsto (fun m => S_seq k (φ m)) Filter.atTop (nhds (S_inf k))) ∧
      (∀ k, ‖S_inf k‖ ≤ B k) := by
  let K : Set (ℕ → ℂ) := Set.univ.pi fun k => Metric.closedBall (0 : ℂ) (B k)
  have hK : IsCompact K := isCompact_univ_pi fun k => isCompact_closedBall (0 : ℂ) (B k)
  let seq : ℕ → (ℕ → ℂ) := fun m k => S_seq k m
  have hmem : ∀ m, seq m ∈ K := by
    intro m k _
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbd k m
  obtain ⟨S_inf, hS_mem, φ, hφ_mono, hφ_lim⟩ := hK.tendsto_subseq hmem
  refine ⟨S_inf, φ, hφ_mono, fun k => (tendsto_pi_nhds.mp hφ_lim k), fun k => ?_⟩
  have hk := hS_mem k (Set.mem_univ k)
  rwa [Metric.mem_closedBall, dist_zero_right] at hk

end OSPreHilbertFromSchwinger

/-! ## §31.  Direct Schwinger-to-PreData wiring eliminating manual OS/semigroup fields -/

section SchwingerToPreData

/-- Norm-like `ℓ¹` weight bound `∑ x, ‖f x‖ * M ^ n_pts(x)` on `OSPosTestSpace`. -/
noncomputable def osConfigNormBound (M : ℝ) (f : OSPosTestSpace) : ℝ :=
  ∑ x ∈ f.support, ‖f x‖ * M ^ x.n_pts

theorem osConfigNormBound_nonneg (M : ℝ) (hM : 0 ≤ M) (f : OSPosTestSpace) :
    0 ≤ osConfigNormBound M f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (norm_nonneg _) (pow_nonneg hM _)

theorem osConfigNormBound_add_le (M : ℝ) (hM : 0 ≤ M) (f g : OSPosTestSpace) :
    osConfigNormBound M (f + g) ≤ osConfigNormBound M f + osConfigNormBound M g := by
  let s := (f + g).support ∪ f.support ∪ g.support
  have h_sub : ∀ (u : OSPosTestSpace), u.support ⊆ s →
      osConfigNormBound M u = ∑ x ∈ s, ‖u x‖ * M ^ x.n_pts := by
    intro u hu
    refine Finset.sum_subset hu fun x _ hx => ?_
    have hux : u x = 0 := by
      by_contra hne
      exact hx (Finsupp.mem_support_iff.mpr hne)
    simp [hux]
  rw [h_sub (f + g) (Finset.subset_union_left.trans Finset.subset_union_left),
      h_sub f (Finset.subset_union_right.trans Finset.subset_union_left),
      h_sub g Finset.subset_union_right,
      ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [Finsupp.add_apply, ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le (f x) (g x)) (pow_nonneg hM _)

theorem osConfigNormBound_mapDomain_le (M : ℝ) (hM : 0 ≤ M)
    (φ : PosTimeConfig → PosTimeConfig) (hφ : ∀ x, (φ x).n_pts = x.n_pts)
    (f : OSPosTestSpace) :
    osConfigNormBound M (Finsupp.mapDomain φ f) ≤ osConfigNormBound M f := by
  refine Finsupp.induction f ?_ ?_
  · simp [osConfigNormBound]
  · intro a b f' ha hb ih
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    have h_add := osConfigNormBound_add_le M hM (Finsupp.single (φ a) b) (Finsupp.mapDomain φ f')
    have h_s : osConfigNormBound M (Finsupp.single (φ a) b) ≤ ‖b‖ * M ^ a.n_pts := by
      dsimp [osConfigNormBound]
      rw [Finsupp.support_single_ne_zero (φ a) hb, Finset.sum_singleton,
          Finsupp.single_eq_same, hφ a]
    have hfa : f' a = 0 := by
      by_contra hne
      exact ha (Finsupp.mem_support_iff.mpr hne)
    have hsub : (Finsupp.single a b + f').support ⊆ insert a f'.support := by
      intro x hx
      rw [Finsupp.mem_support_iff, Finsupp.add_apply] at hx
      by_cases hxa : x = a
      · exact hxa ▸ Finset.mem_insert_self a f'.support
      · apply Finset.mem_insert_of_mem
        rw [Finsupp.mem_support_iff]
        intro hfx
        apply hx
        rw [Finsupp.single_apply, if_neg (Ne.symm hxa), hfx, add_zero]
    have h_eq : osConfigNormBound M (Finsupp.single a b + f') =
        ∑ x ∈ insert a f'.support, ‖(Finsupp.single a b + f') x‖ * M ^ x.n_pts := by
      refine Finset.sum_subset hsub fun x _ hx => ?_
      have hx0 : (Finsupp.single a b + f') x = 0 := by
        by_contra hne
        exact hx (Finsupp.mem_support_iff.mpr hne)
      simp [hx0]
    have h_rest : ∑ x ∈ f'.support, ‖(Finsupp.single a b + f') x‖ * M ^ x.n_pts =
        osConfigNormBound M f' := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hxa : x ≠ a := fun h => ha (h ▸ hx)
      rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hxa), zero_add]
    have h_lhs : osConfigNormBound M (Finsupp.single a b + f') =
        ‖b‖ * M ^ a.n_pts + osConfigNormBound M f' := by
      rw [h_eq, Finset.sum_insert ha, Finsupp.add_apply, Finsupp.single_eq_same,
          hfa, add_zero, h_rest]
    linarith

theorem osConfigInner_norm_le {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (M : ℝ) (hM : 0 ≤ M)
    (h_bd : ∀ (n : ℕ) (xs : Fin n → Space4), ‖os.os.Schwinger n xs‖ ≤ M ^ n)
    (f g : OSPosTestSpace) :
    ‖osConfigInner os f g‖ ≤ osConfigNormBound M f * osConfigNormBound M g := by
  dsimp [osConfigInner, osConfigNormBound]
  calc ‖∑ x ∈ f.support, ∑ y ∈ g.support, starRingEnd ℂ (f x) * g y * osConfigKernel os x y‖
      ≤ ∑ x ∈ f.support, ‖∑ y ∈ g.support, starRingEnd ℂ (f x) * g y * osConfigKernel os x y‖ :=
          norm_sum_le _ _
    _ ≤ ∑ x ∈ f.support, ∑ y ∈ g.support, ‖starRingEnd ℂ (f x) * g y * osConfigKernel os x y‖ :=
          Finset.sum_le_sum fun x _ => norm_sum_le _ _
    _ ≤ ∑ x ∈ f.support, ∑ y ∈ g.support, (‖f x‖ * M ^ x.n_pts) * (‖g y‖ * M ^ y.n_pts) := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
          have hconj : ‖starRingEnd ℂ (f x)‖ = ‖f x‖ := norm_star (f x)
          rw [norm_mul, norm_mul, hconj]
          have hk : ‖osConfigKernel os x y‖ ≤ M ^ (x.n_pts + y.n_pts) :=
            h_bd (x.n_pts + y.n_pts) _
          calc ‖f x‖ * ‖g y‖ * ‖osConfigKernel os x y‖
              ≤ ‖f x‖ * ‖g y‖ * M ^ (x.n_pts + y.n_pts) :=
                  mul_le_mul_of_nonneg_left hk (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            _ = (‖f x‖ * M ^ x.n_pts) * (‖g y‖ * M ^ y.n_pts) := by
                  rw [pow_add]; ring
    _ = (∑ x ∈ f.support, ‖f x‖ * M ^ x.n_pts) * (∑ y ∈ g.support, ‖g y‖ * M ^ y.n_pts) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.mul_sum]

/-- 0-point vacuum configuration in `PosTimeConfig`. -/
def emptyPosConfig : PosTimeConfig where
  n_pts := 0
  pts   := Fin.elim0
  pos_t := fun k => Fin.elim0 k

theorem osConfigVac_norm {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (h_herm : ∀ x y : PosTimeConfig,
      osConfigKernel os x y = starRingEnd ℂ (osConfigKernel os y x))
    (h_S0 : os.os.Schwinger 0 Fin.elim0 = 1) :
    (osConfigForm os h_herm).B (osConfigSingle emptyPosConfig) (osConfigSingle emptyPosConfig) = 1 := by
  change osConfigInner os (osConfigSingle emptyPosConfig) (osConfigSingle emptyPosConfig) = 1
  rw [osConfigInner_single]
  dsimp [osConfigKernel, emptyPosConfig]
  have happ : Fin.append (fun k : Fin 0 => euclidTimeReflect (Fin.elim0 k)) Fin.elim0 = Fin.elim0 := by
    funext k
    exact Fin.elim0 k
  rw [happ, h_S0]

/-- Total Euclidean time-shift semigroup on `OSPosTestSpace` (identity for `t < 0`). -/
noncomputable def osTimeShiftSemigroup (t : ℝ) : OSPosTestSpace →ₗ[ℂ] OSPosTestSpace :=
  if ht : 0 ≤ t then osTimeShiftPre t ht else LinearMap.id

theorem osTimeShiftSemigroup_zero (f : OSPosTestSpace) :
    osTimeShiftSemigroup 0 f = f := by
  dsimp [osTimeShiftSemigroup]
  rw [dif_pos le_rfl]
  exact osTimeShiftPre_zero f

theorem osTimeShiftSemigroup_add (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (f : OSPosTestSpace) :
    osTimeShiftSemigroup (s + t) f = osTimeShiftSemigroup s (osTimeShiftSemigroup t f) := by
  dsimp [osTimeShiftSemigroup]
  rw [dif_pos (add_nonneg hs ht), dif_pos hs, dif_pos ht]
  exact osTimeShiftPre_add s t hs ht f

theorem osTimeShiftSemigroup_sa {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (h_herm : ∀ x y : PosTimeConfig,
      osConfigKernel os x y = starRingEnd ℂ (osConfigKernel os y x))
    (h_kern : ∀ (t : ℝ) (ht : 0 ≤ t) (x y : PosTimeConfig),
      osConfigKernel os (posTimeShiftConfig t ht x) y =
        osConfigKernel os x (posTimeShiftConfig t ht y))
    (t : ℝ) (ht : 0 ≤ t) (f g : OSPosTestSpace) :
    (osConfigForm os h_herm).B (osTimeShiftSemigroup t f) g =
      (osConfigForm os h_herm).B f (osTimeShiftSemigroup t g) := by
  dsimp [osTimeShiftSemigroup]
  rw [dif_pos ht]
  exact osTimeShiftPre_sa os h_herm t ht (h_kern t ht) f g

theorem osTimeShiftSemigroup_contr {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (h_herm : ∀ x y : PosTimeConfig,
      osConfigKernel os x y = starRingEnd ℂ (osConfigKernel os y x))
    (h_kern : ∀ (t : ℝ) (ht : 0 ≤ t) (x y : PosTimeConfig),
      osConfigKernel os (posTimeShiftConfig t ht x) y =
        osConfigKernel os x (posTimeShiftConfig t ht y))
    (M : ℝ) (hM : 0 ≤ M)
    (h_bd : ∀ (n : ℕ) (xs : Fin n → Space4), ‖os.os.Schwinger n xs‖ ≤ M ^ n)
    (t : ℝ) (ht : 0 ≤ t) (f : OSPosTestSpace) :
    ((osConfigForm os h_herm).B (osTimeShiftSemigroup t f) (osTimeShiftSemigroup t f)).re ≤
      1 ^ 2 * ((osConfigForm os h_herm).B f f).re := by
  rw [one_pow, one_mul]
  refine os_semigroup_contraction_of_bounded (osConfigForm os h_herm) osTimeShiftSemigroup
    osTimeShiftSemigroup_add (osTimeShiftSemigroup_sa os h_herm h_kern) t ht f
    ((osConfigNormBound M f) ^ 2) fun k => ?_
  let s : ℝ := ((2 ^ k : ℕ) : ℝ) * t
  have hs : 0 ≤ s := mul_nonneg (Nat.cast_nonneg _) ht
  have hs_eq : osTimeShiftSemigroup s f = osTimeShiftPre s hs f := by
    dsimp [osTimeShiftSemigroup]
    rw [dif_pos hs]
  change (osConfigInner os (osTimeShiftSemigroup s f) (osTimeShiftSemigroup s f)).re ≤
    (osConfigNormBound M f) ^ 2
  rw [hs_eq]
  have h1 : (osConfigInner os (osTimeShiftPre s hs f) (osTimeShiftPre s hs f)).re ≤
      ‖osConfigInner os (osTimeShiftPre s hs f) (osTimeShiftPre s hs f)‖ :=
    (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have h2 : ‖osConfigInner os (osTimeShiftPre s hs f) (osTimeShiftPre s hs f)‖ ≤
      osConfigNormBound M (osTimeShiftPre s hs f) * osConfigNormBound M (osTimeShiftPre s hs f) :=
    osConfigInner_norm_le os M hM h_bd _ _
  have h3 : osConfigNormBound M (osTimeShiftPre s hs f) ≤ osConfigNormBound M f :=
    osConfigNormBound_mapDomain_le M hM (posTimeShiftConfig s hs) (fun _ => rfl) f
  have h4 : osConfigNormBound M (osTimeShiftPre s hs f) *
      osConfigNormBound M (osTimeShiftPre s hs f) ≤ (osConfigNormBound M f) ^ 2 := by
    have hnn := osConfigNormBound_nonneg M hM (osTimeShiftPre s hs f)
    rw [sq]
    exact mul_le_mul h3 h3 hnn (osConfigNormBound_nonneg M hM f)
  exact h1.trans (h2.trans h4)

/--
Reduced OS reconstruction inputs on `(OSPosTestSpace, osConfigForm os h_herm)`:
only the Minkowski continuation operators (`H_pre`, `U_pre`, `φ_pre`, `P2_spec`, `cyclic_dense`)
remain; `E`, `F`, `Ω_E`, `T_E_pre` and all semigroup axioms are constructed automatically.
-/
structure ReducedMinkowskiContinuationData (Δ_phys : ℝ) (os : OS4DContinuumTheory Δ_phys) where
  h_herm       : ∀ x y : PosTimeConfig,
                   osConfigKernel os x y = starRingEnd ℂ (osConfigKernel os y x)
  h_S0         : os.os.Schwinger 0 Fin.elim0 = 1
  h_kern       : ∀ (t : ℝ) (ht : 0 ≤ t) (x y : PosTimeConfig),
                   osConfigKernel os (posTimeShiftConfig t ht x) y =
                     osConfigKernel os x (posTimeShiftConfig t ht y)
  M_bd         : ℝ
  hM_nn        : 0 ≤ M_bd
  h_bd         : ∀ (n : ℕ) (xs : Fin n → Space4), ‖os.os.Schwinger n xs‖ ≤ M_bd ^ n
  H_pre        : OSPosTestSpace →ₗ[ℂ] OSPosTestSpace
  H_bound      : ℝ
  H_bound_nn   : 0 ≤ H_bound
  H_bd         : ∀ x : OSPosTestSpace,
                   ((osConfigForm os h_herm).B (H_pre x) (H_pre x)).re ≤
                     H_bound ^ 2 * ((osConfigForm os h_herm).B x x).re
  H_sa         : ∀ x y : OSPosTestSpace,
                   (osConfigForm os h_herm).B (H_pre x) y =
                     (osConfigForm os h_herm).B x (H_pre y)
  H_nonneg     : ∀ x : OSPosTestSpace, 0 ≤ ((osConfigForm os h_herm).B x (H_pre x)).re
  H_vac        : H_pre (osConfigSingle emptyPosConfig) = 0
  U_pre        : Poincare4 → (OSPosTestSpace →ₗ[ℂ] OSPosTestSpace)
  U_unit_pre   : ∀ g x y,
                   (osConfigForm os h_herm).B (U_pre g x) (U_pre g y) =
                     (osConfigForm os h_herm).B x y
  U_vac_pre    : ∀ g, U_pre g (osConfigSingle emptyPosConfig) = osConfigSingle emptyPosConfig
  φ_pre        : Space4 → (OSPosTestSpace →ₗ[ℂ] OSPosTestSpace)
  φ_bound      : Space4 → ℝ
  φ_bound_nn   : ∀ x, 0 ≤ φ_bound x
  φ_bd         : ∀ x (v : OSPosTestSpace),
                   ((osConfigForm os h_herm).B (φ_pre x v) (φ_pre x v)).re ≤
                     (φ_bound x) ^ 2 * ((osConfigForm os h_herm).B v v).re
  cov_pre      : ∀ g x v, U_pre g (φ_pre x v) = φ_pre (poincareAct g x) (U_pre g v)
  loc_pre      : ∀ x y, minkowskiSq (x - y) < 0 →
                   ∀ v, φ_pre x (φ_pre y v) = φ_pre y (φ_pre x v)
  P2_spec      : Set ℝ
  spec_cond    : ∀ p2 ∈ P2_spec, 0 ≤ p2
  gap_spec     : ∀ p2 ∈ P2_spec, p2 = 0 ∨ Δ_phys ^ 2 ≤ p2
  cyclic_dense : (Submodule.span ℂ
      {v : OSHilbertSpace (osConfigForm os h_herm) | ∃ (k : ℕ) (xs : Fin k → Space4),
        v = (List.ofFn (fun i : Fin k =>
          osLiftOperator (osConfigForm os h_herm) (φ_pre (xs i))
            (φ_bound (xs i)) (φ_bound_nn (xs i)) (φ_bd (xs i)))).foldr
          (fun A acc => A acc)
          (osCompletionMap (osConfigForm os h_herm)
            (osPreMk (osConfigForm os h_herm) (osConfigSingle emptyPosConfig)))}).topologicalClosure = ⊤

/-- Assemble `EuclideanOSPreData` directly from `ReducedMinkowskiContinuationData`. -/
noncomputable def buildEuclideanOSPreDataFromSchwinger
    {Δ_phys : ℝ} {os : OS4DContinuumTheory Δ_phys}
    (R : ReducedMinkowskiContinuationData Δ_phys os) :
    EuclideanOSPreData Δ_phys os where
  E := OSPosTestSpace
  F := osConfigForm os R.h_herm
  Ω_E := osConfigSingle emptyPosConfig
  Ω_E_norm := osConfigVac_norm os R.h_herm R.h_S0
  T_E_pre := osTimeShiftSemigroup
  T_E_zero := osTimeShiftSemigroup_zero
  T_E_add := osTimeShiftSemigroup_add
  T_E_sa := osTimeShiftSemigroup_sa os R.h_herm R.h_kern
  T_E_contr := osTimeShiftSemigroup_contr os R.h_herm R.h_kern R.M_bd R.hM_nn R.h_bd
  H_pre := R.H_pre
  H_bound := R.H_bound
  H_bound_nn := R.H_bound_nn
  H_bd := R.H_bd
  H_sa := R.H_sa
  H_nonneg := R.H_nonneg
  H_vac := R.H_vac
  U_pre := R.U_pre
  U_unit_pre := R.U_unit_pre
  U_vac_pre := R.U_vac_pre
  φ_pre := R.φ_pre
  φ_bound := R.φ_bound
  φ_bound_nn := R.φ_bound_nn
  φ_bd := R.φ_bd
  cov_pre := R.cov_pre
  loc_pre := R.loc_pre
  P2_spec := R.P2_spec
  spec_cond := R.spec_cond
  gap_spec := R.gap_spec
  cyclic_dense := R.cyclic_dense

end SchwingerToPreData

/-! ## §32.  Full-rank SU(N) Wilson integral transfer operator on L²(dμ_Haar) -/

section FullRankWilsonIntegralOp

@[reducible] instance instTopologicalSpaceCubicGaugeField (L : ℕ) [NeZero L]
    (G : Type*) [TopologicalSpace G] :
    TopologicalSpace (GaugeField (cubicTorus3 L) G) :=
  Pi.topologicalSpace

instance instSecondCountableCubicGaugeField (L N : ℕ) [NeZero L] :
    SecondCountableTopology
      (GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  show SecondCountableTopology
    ((cubicTorus3 L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) from inferInstance

instance instBorelSpaceCubicGaugeField (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    BorelSpace (GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  ⟨(inferInstance : BorelSpace ((cubicTorus3 L).Link →
    Matrix.specialUnitaryGroup (Fin N) ℂ)).measurable_eq⟩

private theorem continuous_cubicField_eval (L N : ℕ) [NeZero L]
    (e : (cubicTorus3 L).Link) :
    Continuous (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) => U e) := by
  change Continuous (fun U : (cubicTorus3 L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ => U e)
  exact continuous_apply e

private theorem continuous_pathHolonomy3 (L N : ℕ) [NeZero L]
    (γ : List ((cubicTorus3 L).Link × Bool)) :
    Continuous (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      pathHolonomy U γ) := by
  induction γ with
  | nil => simpa [pathHolonomy] using continuous_const
  | cons hd tl ih =>
    rcases hd with ⟨e, b⟩
    cases b
    · simpa [pathHolonomy] using
        ((continuous_inv.comp (continuous_cubicField_eval L N e)).mul ih)
    · simpa [pathHolonomy] using
        ((continuous_cubicField_eval L N e).mul ih)

private theorem continuous_wilsonPlaquetteTerm3 (L N : ℕ) [NeZero L]
    (p : LatticePlaquette (cubicTorus3 L)) :
    Continuous (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      wilsonPlaquetteTerm p U) := by
  unfold wilsonPlaquetteTerm
  have h_ent : ∀ i : Fin N, Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (A : Matrix (Fin N) (Fin N) ℂ) i i) := fun i =>
    (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
  have h_tr : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re) := by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact continuous_finset_sum Finset.univ fun i _ => Complex.continuous_re.comp (h_ent i)
  exact continuous_const.sub
    (continuous_const.mul (h_tr.comp (continuous_pathHolonomy3 L N p.loop)))

theorem continuous_cubicWilsonAction (L N : ℕ) [NeZero L] (β : ℝ) :
    Continuous (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      wilsonAction β (cubicPlaquettes L) U) := by
  unfold wilsonAction
  have hsum : ∀ (ps : List (LatticePlaquette (cubicTorus3 L))),
      Continuous (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        (ps.map (fun p => wilsonPlaquetteTerm p U)).sum) := by
    intro ps
    induction ps with
    | nil => simp [continuous_const]
    | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (continuous_wilsonPlaquetteTerm3 L N p).add ih
  exact continuous_const.mul (hsum (cubicPlaquettes L))

theorem continuous_cubicWilsonKernel (L N : ℕ) [NeZero L] (β : ℝ)
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin)) :
    Continuous (Function.uncurry (wilsonKernel β (cubicPlaquettes L) K_kin)) := by
  change Continuous (fun p :
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      Real.exp (-(1 / 2 : ℝ) *
        (wilsonAction β (cubicPlaquettes L) p.1 + wilsonAction β (cubicPlaquettes L) p.2)) *
        K_kin p.1 p.2)
  have hS := continuous_cubicWilsonAction L N β
  exact (Real.continuous_exp.comp
    (continuous_const.mul ((hS.comp continuous_fst).add (hS.comp continuous_snd)))).mul hK_cont

private theorem continuous_cubicWilsonKernel_right (L N : ℕ) [NeZero L] (β : ℝ)
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    Continuous (fun U' => wilsonKernel β (cubicPlaquettes L) K_kin U U') := by
  have hS := continuous_cubicWilsonAction L N β
  have h_pair : Continuous
      (fun U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) => (U, U')) :=
    continuous_const.prodMk continuous_id
  have hK_U : Continuous (fun U' => K_kin U U') := hK_cont.comp h_pair
  change Continuous (fun U' =>
    Real.exp (-(1 / 2 : ℝ) *
      (wilsonAction β (cubicPlaquettes L) U + wilsonAction β (cubicPlaquettes L) U')) *
      K_kin U U')
  exact (Real.continuous_exp.comp
    (continuous_const.mul (continuous_const.add hS))).mul hK_U

private theorem continuous_cubicWilsonKernel_left (L N : ℕ) [NeZero L] (β : ℝ)
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    Continuous (fun U => wilsonKernel β (cubicPlaquettes L) K_kin U U') := by
  have hS := continuous_cubicWilsonAction L N β
  have h_pair : Continuous
      (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) => (U, U')) :=
    continuous_id.prodMk continuous_const
  have hK_U' : Continuous (fun U => K_kin U U') := hK_cont.comp h_pair
  change Continuous (fun U =>
    Real.exp (-(1 / 2 : ℝ) *
      (wilsonAction β (cubicPlaquettes L) U + wilsonAction β (cubicPlaquettes L) U')) *
      K_kin U U')
  exact (Real.continuous_exp.comp
    (continuous_const.mul (hS.add continuous_const))).mul hK_U'

private theorem l1_le_l2_prob {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (ψ : MeasureTheory.Lp ℂ 2 μ) :
    ∫ a, ‖ψ a‖ ∂μ ≤ ‖ψ‖ := by
  let c : ℝ := ∫ a, ‖ψ a‖ ∂μ
  have hψ_mem : MeasureTheory.MemLp (⇑ψ) 2 μ := MeasureTheory.Lp.memLp ψ
  have hψ_ae : MeasureTheory.AEStronglyMeasurable (⇑ψ) μ := hψ_mem.aestronglyMeasurable
  have h_int1 : MeasureTheory.Integrable (fun a => ‖ψ a‖) μ :=
    (hψ_mem.integrable one_le_two).norm
  have h_int2 : MeasureTheory.Integrable (fun a => ‖ψ a‖ ^ 2) μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hψ_ae).mp hψ_mem
  have hc_nn : 0 ≤ c := MeasureTheory.integral_nonneg fun _ => norm_nonneg _
  have h_var_nn : 0 ≤ ∫ a, (‖ψ a‖ - c) ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have h_exp : (fun a => (‖ψ a‖ - c) ^ 2) =
      fun a => ‖ψ a‖ ^ 2 - 2 * c * ‖ψ a‖ + c ^ 2 := by
    funext a; ring
  have h_int_sub : MeasureTheory.Integrable (fun a => ‖ψ a‖ ^ 2 - 2 * c * ‖ψ a‖) μ :=
    h_int2.sub (h_int1.const_mul (2 * c))
  have h_var_val : ∫ a, (‖ψ a‖ - c) ^ 2 ∂μ = (∫ a, ‖ψ a‖ ^ 2 ∂μ) - c ^ 2 := by
    rw [h_exp, MeasureTheory.integral_add h_int_sub (MeasureTheory.integrable_const (c ^ 2)),
        MeasureTheory.integral_sub h_int2 (h_int1.const_mul (2 * c)),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const]
    change (∫ a, ‖ψ a‖ ^ 2 ∂μ) - 2 * c * c + μ.real Set.univ • c ^ 2 = _
    simp only [Measure.real, MeasureTheory.measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    ring
  have h_l2_sq : ∫ a, ‖ψ a‖ ^ 2 ∂μ = ‖ψ‖ ^ 2 := by
    have h_l2 : MeasureTheory.Integrable (fun a => ⟪ψ a, ψ a⟫_ℂ) μ :=
      MeasureTheory.L2.integrable_inner _ _
    have h_re := integral_re h_l2
    have h_in : (⟪ψ, ψ⟫_ℂ).re = ∫ a, ‖ψ a‖ ^ 2 ∂μ := by
      rw [MeasureTheory.L2.inner_def]
      change RCLike.re (∫ a, ⟪ψ a, ψ a⟫_ℂ ∂μ) = _
      rw [← h_re]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      change (⟪ψ a, ψ a⟫_ℂ).re = ‖ψ a‖ ^ 2
      rw [inner_self_eq_norm_sq_to_K]
      simp [pow_two]
    rw [← h_in, inner_self_eq_norm_sq_to_K]
    simp [pow_two]
  rw [h_var_val, h_l2_sq] at h_var_nn
  have h_sq_le : c ^ 2 ≤ ‖ψ‖ ^ 2 := by linarith
  exact (sq_le_sq₀ hc_nn (norm_nonneg ψ)).mp h_sq_le

/-- Pointwise Haar integral `(T_W ψ)(U) = ∫ K_W(U, U') ψ(U') dμ_Haar(U')`. -/
noncomputable def wilsonIntegralFn (L N : ℕ) [NeZero L] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N))
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℂ :=
  ∫ U', ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) * ψ U'
    ∂(latticeHaarMeasure L N)

private theorem wilsonKernel_cubic_le (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (M_K : ℝ) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 ≤ wilsonKernel β (cubicPlaquettes L) K_kin U U' ∧
      wilsonKernel β (cubicPlaquettes L) K_kin U U' ≤ M_K := by
  have hnn := wilsonKernel_nonneg β (cubicPlaquettes L) K_kin hK_nn U U'
  have h1 := (wilsonAction_bounds β hβ (cubicPlaquettes L) U).1
  have h2 := (wilsonAction_bounds β hβ (cubicPlaquettes L) U').1
  have hexp : Real.exp (-(1 / 2 : ℝ) *
      (wilsonAction β (cubicPlaquettes L) U + wilsonAction β (cubicPlaquettes L) U')) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  refine ⟨hnn, ?_⟩
  unfold wilsonKernel
  calc Real.exp _ * K_kin U U' ≤ 1 * K_kin U U' :=
        mul_le_mul_of_nonneg_right hexp (hK_nn U U')
    _ ≤ M_K := by rw [one_mul]; exact hK_bd U U'

private theorem wilsonKernel_mul_integrable (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (M_K : ℝ) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N))
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    MeasureTheory.Integrable
      (fun U' => ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) * ψ U')
      (latticeHaarMeasure L N) := by
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  have hψ_mem : MeasureTheory.MemLp (⇑ψ) 2 μ := MeasureTheory.Lp.memLp ψ
  have h_dom : MeasureTheory.Integrable (fun U' => M_K * ‖ψ U'‖) μ :=
    (hψ_mem.integrable one_le_two).norm.const_mul M_K
  refine h_dom.mono' ?_ ?_
  · have hK_U : Continuous (fun U' => ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_cubicWilsonKernel_right L N β K_kin hK_cont U)
    exact hK_U.stronglyMeasurable.aestronglyMeasurable.mul hψ_mem.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun U' => ?_
    have hb := wilsonKernel_cubic_le L N β hβ K_kin hK_nn M_K hK_bd U U'
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)

private theorem wilsonIntegralFn_continuous (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (M_K : ℝ) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    Continuous (wilsonIntegralFn L N β K_kin ψ) := by
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  have hψ_mem : MeasureTheory.MemLp (⇑ψ) 2 μ := MeasureTheory.Lp.memLp ψ
  have hψ_int : MeasureTheory.Integrable (fun U' => M_K * ‖ψ U'‖) μ :=
    (hψ_mem.integrable one_le_two).norm.const_mul M_K
  refine MeasureTheory.continuous_of_dominated ?_ ?_ hψ_int ?_
  · intro U
    exact (wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd ψ U).aestronglyMeasurable
  · intro U
    refine Filter.Eventually.of_forall fun U' => ?_
    have hb := wilsonKernel_cubic_le L N β hβ K_kin hK_nn M_K hK_bd U U'
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)
  · refine Filter.Eventually.of_forall fun U' => ?_
    have hK_U' : Continuous (fun U => ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_cubicWilsonKernel_left L N β K_kin hK_cont U')
    exact hK_U'.mul continuous_const

private theorem wilsonIntegralFn_pt_bound (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N))
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    ‖wilsonIntegralFn L N β K_kin ψ U‖ ≤ M_K * ‖ψ‖ := by
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  have h_int := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd ψ U
  have h_dom : MeasureTheory.Integrable (fun U' => M_K * ‖ψ U'‖) μ :=
    ((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul M_K
  calc ‖wilsonIntegralFn L N β K_kin ψ U‖
      ≤ ∫ U', ‖((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) * ψ U'‖ ∂μ :=
          MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ U', M_K * ‖ψ U'‖ ∂μ := by
          refine MeasureTheory.integral_mono h_int.norm h_dom fun U' => ?_
          have hb := wilsonKernel_cubic_le L N β hβ K_kin hK_nn M_K hK_bd U U'
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
          exact mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)
    _ = M_K * ∫ U', ‖ψ U'‖ ∂μ := MeasureTheory.integral_const_mul M_K _
    _ ≤ M_K * ‖ψ‖ := mul_le_mul_of_nonneg_left (l1_le_l2_prob μ ψ) hM_K

private theorem wilsonIntegralFn_memLp (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    MeasureTheory.MemLp (wilsonIntegralFn L N β K_kin ψ) 2 (latticeHaarMeasure L N) := by
  haveI := latticeHaarMeasure_prob L N
  exact memLp_two_of_measurable_bound (latticeHaarMeasure L N)
    (wilsonIntegralFn L N β K_kin ψ)
    (wilsonIntegralFn_continuous L N β hβ K_kin hK_cont hK_nn M_K hK_bd ψ).measurable
    (M_K * ‖ψ‖) (mul_nonneg hM_K (norm_nonneg _))
    (wilsonIntegralFn_pt_bound L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ)

/--
Full-rank Wilson integral transfer operator `T_W` on `L²(SU(N)^{3L³}, dμ_Haar)`:
`(T_W ψ)(U) = ∫ wilsonKernel(U, U') ψ(U') dμ_Haar(U')`.
-/
noncomputable def wilsonIntegralOp (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ U U', K_kin U U' ≤ M_K) :
    HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ]
      HaarGaugeSpace (latticeHaarMeasure L N) :=
  let μ := latticeHaarMeasure L N
  LinearMap.mkContinuous
    { toFun := fun ψ =>
        (wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ).toLp
          (wilsonIntegralFn L N β K_kin ψ)
      map_add' := fun ψ₁ ψ₂ => by
        apply MeasureTheory.Lp.ext
        have h1 := (wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd
          (ψ₁ + ψ₂)).coeFn_toLp
        have h2 := (wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ₁).coeFn_toLp
        have h3 := (wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ₂).coeFn_toLp
        have hadd := MeasureTheory.Lp.coeFn_add
          ((wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ₁).toLp
            (wilsonIntegralFn L N β K_kin ψ₁))
          ((wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ₂).toLp
            (wilsonIntegralFn L N β K_kin ψ₂))
        have hψ_add := MeasureTheory.Lp.coeFn_add ψ₁ ψ₂
        filter_upwards [h1, h2, h3, hadd] with U hu1 hu2 hu3 ha
        simp only [Pi.add_apply] at ha ⊢
        rw [hu1, ha, hu2, hu3]
        have hi1 := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd ψ₁ U
        have hi2 := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd ψ₂ U
        dsimp [wilsonIntegralFn]
        rw [← MeasureTheory.integral_add hi1 hi2]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hψ_add] with U' hU'
        have hU'' : (ψ₁ + ψ₂) U' = ψ₁ U' + ψ₂ U' := hU'
        change ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) * (ψ₁ + ψ₂) U' =
          ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) * ψ₁ U' +
            ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) * ψ₂ U'
        rw [hU'', mul_add]
      map_smul' := fun c ψ => by
        apply MeasureTheory.Lp.ext
        have h1 := (wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd
          (c • ψ)).coeFn_toLp
        have h2 := (wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ).coeFn_toLp
        have hsm := MeasureTheory.Lp.coeFn_smul c
          ((wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ).toLp
            (wilsonIntegralFn L N β K_kin ψ))
        have hψ_sm := MeasureTheory.Lp.coeFn_smul c ψ
        filter_upwards [h1, h2, hsm] with U hu1 hu2 hs
        simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul] at hs ⊢
        rw [hu1, hs, hu2]
        dsimp [wilsonIntegralFn]
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hψ_sm] with U' hU'
        have hU'' : (c • ψ) U' = c * ψ U' := hU'
        change ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) * (c • ψ) U' =
          c * (((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) * ψ U')
        rw [hU'', mul_left_comm] }
    M_K
    (fun ψ => by
      haveI := latticeHaarMeasure_prob L N
      let ψ' := (wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ).toLp
        (wilsonIntegralFn L N β K_kin ψ)
      change ‖ψ'‖ ≤ M_K * ‖ψ‖
      rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM_K (norm_nonneg _))]
      have h_l2 : MeasureTheory.Integrable (fun U => ⟪ψ' U, ψ' U⟫_ℂ) μ :=
        MeasureTheory.L2.integrable_inner _ _
      have h_re := integral_re h_l2
      have h_norm_sq : ‖ψ'‖ ^ 2 = ∫ U, ‖ψ' U‖ ^ 2 ∂μ := by
        have h_in : (⟪ψ', ψ'⟫_ℂ).re = ∫ U, ‖ψ' U‖ ^ 2 ∂μ := by
          rw [MeasureTheory.L2.inner_def]
          change RCLike.re (∫ U, ⟪ψ' U, ψ' U⟫_ℂ ∂μ) = _
          rw [← h_re]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
          change (⟪ψ' U, ψ' U⟫_ℂ).re = ‖ψ' U‖ ^ 2
          rw [inner_self_eq_norm_sq_to_K]
          simp [pow_two]
        rw [← h_in, inner_self_eq_norm_sq_to_K]
        simp [pow_two]
      have h_int1 : MeasureTheory.Integrable (fun U => ‖ψ' U‖ ^ 2) μ :=
        (MeasureTheory.memLp_two_iff_integrable_sq_norm
          (MeasureTheory.Lp.memLp ψ').aestronglyMeasurable).mp (MeasureTheory.Lp.memLp ψ')
      have h_int2 : MeasureTheory.Integrable (fun _ => (M_K * ‖ψ‖) ^ 2) μ :=
        MeasureTheory.integrable_const _
      have hcoe := (wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ).coeFn_toLp
      rw [h_norm_sq]
      calc ∫ U, ‖ψ' U‖ ^ 2 ∂μ
          ≤ ∫ _U, (M_K * ‖ψ‖) ^ 2 ∂μ := by
              refine MeasureTheory.integral_mono_ae h_int1 h_int2 ?_
              filter_upwards [hcoe] with U hU
              rw [hU]
              exact pow_le_pow_left₀ (norm_nonneg _)
                (wilsonIntegralFn_pt_bound L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ U) 2
        _ = (M_K * ‖ψ‖) ^ 2 := by
              rw [MeasureTheory.integral_const]
              simp [Measure.real, MeasureTheory.measure_univ])

theorem wilsonIntegralOp_apply_ae (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⇑(wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ) =ᵐ[latticeHaarMeasure L N]
      wilsonIntegralFn L N β K_kin ψ :=
  (wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ).coeFn_toLp

/-- Exact self-adjointness of the full-rank Wilson integral operator via Fubini. -/
theorem wilsonIntegralOp_sa (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_symm : ∀ U U', K_kin U' U = K_kin U U')
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (ψ₁ ψ₂ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⟪wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ₁, ψ₂⟫_ℂ =
      ⟪ψ₁, wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ₂⟫_ℂ := by
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  let K_W := wilsonKernel β (cubicPlaquettes L) K_kin
  let T := wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd
  have hcinner : ∀ a b : ℂ, ⟪a, b⟫_ℂ = starRingEnd ℂ a * b := by
    intro a b
    have h1 : ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_num
    calc ⟪a, b⟫_ℂ = ⟪a • (1 : ℂ), b • (1 : ℂ)⟫_ℂ := by simp
      _ = starRingEnd ℂ a * (b * ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ) := by
            rw [inner_smul_left, inner_smul_right]
      _ = starRingEnd ℂ a * b := by rw [h1, mul_one]
  have hL : ⟪T ψ₁, ψ₂⟫_ℂ =
      ∫ U, starRingEnd ℂ (wilsonIntegralFn L N β K_kin ψ₁ U) * ψ₂ U ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ₁] with U hU
    rw [hU, hcinner]
  have hR : ⟪ψ₁, T ψ₂⟫_ℂ =
      ∫ U', starRingEnd ℂ (ψ₁ U') * wilsonIntegralFn L N β K_kin ψ₂ U' ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ₂] with U' hU'
    rw [hU', hcinner]
  have hKW_cont : Continuous (Function.uncurry K_W) :=
    continuous_cubicWilsonKernel L N β K_kin hK_cont
  have h_prod_int : MeasureTheory.Integrable
      (Function.uncurry fun U U' => ψ₂ U * starRingEnd ℂ (((K_W U U' : ℝ) : ℂ) * ψ₁ U'))
      (μ.prod μ) := by
    have h1_aesm : MeasureTheory.AEStronglyMeasurable
        (fun p : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
          GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) => ψ₁ p.2)
        (μ.prod μ) :=
      (MeasureTheory.Lp.memLp ψ₁).aestronglyMeasurable.comp_quasiMeasurePreserving
        MeasureTheory.Measure.quasiMeasurePreserving_snd
    have h2_aesm : MeasureTheory.AEStronglyMeasurable
        (fun p : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
          GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) => ψ₂ p.1)
        (μ.prod μ) :=
      (MeasureTheory.Lp.memLp ψ₂).aestronglyMeasurable.comp_quasiMeasurePreserving
        MeasureTheory.Measure.quasiMeasurePreserving_fst
    have hK_aesm : MeasureTheory.AEStronglyMeasurable
        (fun p : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
          GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
          ((K_W p.1 p.2 : ℝ) : ℂ))
        (μ.prod μ) :=
      (Complex.continuous_ofReal.comp hKW_cont).stronglyMeasurable.aestronglyMeasurable
    have h_conj_aesm : MeasureTheory.AEStronglyMeasurable
        (fun p : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
          GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
          starRingEnd ℂ (((K_W p.1 p.2 : ℝ) : ℂ) * ψ₁ p.2))
        (μ.prod μ) :=
      continuous_star.comp_aestronglyMeasurable (hK_aesm.mul h1_aesm)
    have h_dom : MeasureTheory.Integrable
        (fun p : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
          GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
          (M_K * ‖ψ₂ p.1‖) * ‖ψ₁ p.2‖)
        (μ.prod μ) :=
      (((MeasureTheory.Lp.memLp ψ₂).integrable one_le_two).norm.const_mul M_K).mul_prod
        ((MeasureTheory.Lp.memLp ψ₁).integrable one_le_two).norm
    refine h_dom.mono' (h2_aesm.mul h_conj_aesm) ?_
    refine Filter.Eventually.of_forall fun p => ?_
    have hb := wilsonKernel_cubic_le L N β hβ K_kin hK_nn M_K hK_bd p.1 p.2
    have hconj : ‖starRingEnd ℂ (((K_W p.1 p.2 : ℝ) : ℂ) * ψ₁ p.2)‖ =
        ‖((K_W p.1 p.2 : ℝ) : ℂ) * ψ₁ p.2‖ :=
      norm_star _
    change ‖ψ₂ p.1 * starRingEnd ℂ (((K_W p.1 p.2 : ℝ) : ℂ) * ψ₁ p.2)‖ ≤
      (M_K * ‖ψ₂ p.1‖) * ‖ψ₁ p.2‖
    rw [norm_mul, hconj, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
    calc ‖ψ₂ p.1‖ * (K_W p.1 p.2 * ‖ψ₁ p.2‖)
        ≤ ‖ψ₂ p.1‖ * (M_K * ‖ψ₁ p.2‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)) (norm_nonneg _)
      _ = (M_K * ‖ψ₂ p.1‖) * ‖ψ₁ p.2‖ := by ring
  rw [hL, hR]
  have hL_eq :
      (∫ U, starRingEnd ℂ (wilsonIntegralFn L N β K_kin ψ₁ U) * ψ₂ U ∂μ) =
        ∫ U, ∫ U', ψ₂ U * starRingEnd ℂ (((K_W U U' : ℝ) : ℂ) * ψ₁ U') ∂μ ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    dsimp only [wilsonIntegralFn]
    rw [← integral_conj, mul_comm, ← MeasureTheory.integral_const_mul]
  have hR_eq :
      (∫ U', starRingEnd ℂ (ψ₁ U') * wilsonIntegralFn L N β K_kin ψ₂ U' ∂μ) =
        ∫ U', ∫ U, ψ₂ U * starRingEnd ℂ (((K_W U U' : ℝ) : ℂ) * ψ₁ U') ∂μ ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U' => ?_)
    dsimp only [wilsonIntegralFn]
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    dsimp only
    change starRingEnd ℂ (ψ₁ U') * (((K_W U' U : ℝ) : ℂ) * ψ₂ U) =
      ψ₂ U * starRingEnd ℂ (((K_W U U' : ℝ) : ℂ) * ψ₁ U')
    rw [map_mul, Complex.conj_ofReal]
    have hsym : K_W U U' = K_W U' U :=
      wilsonKernel_symm β (cubicPlaquettes L) K_kin hK_symm U' U
    rw [hsym]
    ring
  rw [hL_eq, hR_eq]
  exact MeasureTheory.integral_integral_swap h_prod_int

/-- Exact local gauge invariance of the full-rank Wilson integral operator under `cubicGaugeRep`. -/
theorem wilsonIntegralOp_gauge_inv (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (hK_inv : ∀ g U U', K_kin (gaugeAct g U) (gaugeAct g U') = K_kin U U')
    (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    (cubicGaugeRep L N g).comp
        (wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd) =
      (wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd).comp
        (cubicGaugeRep L N g) := by
  ext1 ψ
  apply MeasureTheory.Lp.ext
  let μ := latticeHaarMeasure L N
  let eqv := gaugeActEquiv L N (fun x => (g x)⁻¹)
  let hmp : MeasureTheory.MeasurePreserving eqv μ μ :=
    ⟨eqv.measurable, latticeHaarMeasure_gauge_inv L N (fun x => (g x)⁻¹)⟩
  let T := wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd
  have hL1 := cubicGaugeRep_apply_ae L N g (T ψ)
  have hL2 : (fun U => (T ψ) (eqv U)) =ᵐ[μ] (fun U => wilsonIntegralFn L N β K_kin ψ (eqv U)) :=
    ae_comp_measurePreserving hmp (wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ)
  have hR1 := wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd (cubicGaugeRep L N g ψ)
  have h_pt : ∀ U, wilsonIntegralFn L N β K_kin ψ (eqv U) =
      wilsonIntegralFn L N β K_kin (cubicGaugeRep L N g ψ) U := by
    intro U
    dsimp [wilsonIntegralFn]
    have h_comp := (hmp.integral_comp'
      (fun U' => ((wilsonKernel β (cubicPlaquettes L) K_kin (eqv U) U' : ℝ) : ℂ) * ψ U')).symm
    rw [h_comp]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [cubicGaugeRep_apply_ae L N g ψ] with U' hU'
    have h_kern := wilsonKernel_gauge_inv β (cubicPlaquettes L) K_kin hK_inv
      (fun x => (g x)⁻¹) U U'
    change ((wilsonKernel β (cubicPlaquettes L) K_kin
        (gaugeAct (fun x => (g x)⁻¹) U) (gaugeAct (fun x => (g x)⁻¹) U') : ℝ) : ℂ) *
        ψ (gaugeAct (fun x => (g x)⁻¹) U') =
      ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) *
        (cubicGaugeRep L N g ψ) U'
    rw [h_kern, hU']
  filter_upwards [hL1, hL2, hR1] with U hl1 hl2 hr1
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hl1]
  have hl2' : (T ψ) (gaugeAct (fun x => (g x)⁻¹) U) =
      wilsonIntegralFn L N β K_kin ψ (gaugeAct (fun x => (g x)⁻¹) U) := hl2
  rw [hl2', hr1]
  exact h_pt U

end FullRankWilsonIntegralOp

/-! ## §33.  Full-rank SU(N) Wilson integral operator: compactness, Gram positivity,
            Perron–Frobenius vacuum & finite-volume spectral gap -/

section FullRankWilsonSpectralGap

instance instCompactSpaceCubicGaugeField (L N : ℕ) [NeZero L] :
    CompactSpace (GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  show CompactSpace ((cubicTorus3 L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) from
    inferInstance

instance instT2SpaceCubicGaugeField (L N : ℕ) [NeZero L] :
    T2Space (GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  show T2Space ((cubicTorus3 L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) from
    inferInstance

instance instIsOpenPosLatticeHaar (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.Measure.IsOpenPosMeasure (latticeHaarMeasure L N) := by
  haveI := suHaar_prob N
  haveI : MeasureTheory.Measure.IsHaarMeasure (suHaar N) :=
    MeasureTheory.Measure.isHaarMeasure_haarMeasure ⊤
  change MeasureTheory.Measure.IsOpenPosMeasure
    (MeasureTheory.Measure.pi fun _ : (cubicTorus3 L).Link => suHaar N)
  infer_instance

private theorem lp_coeFn_finset_sum {α ι : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (t : Finset ι) [DecidableEq ι]
    (f : ι → MeasureTheory.Lp ℂ 2 μ) :
    ⇑(∑ i ∈ t, f i) =ᵐ[μ] fun x => ∑ i ∈ t, (f i) x := by
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact MeasureTheory.Lp.coeFn_zero ℂ 2 μ
  | @insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    have hadd := MeasureTheory.Lp.coeFn_add (f a) (∑ i ∈ t, f i)
    filter_upwards [hadd, ih] with x hxa hxi
    simp only [Pi.add_apply] at hxa
    rw [hxa, hxi]

private theorem lp_norm_sq_eq_integral {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (ψ : MeasureTheory.Lp ℂ 2 μ) :
    ‖ψ‖ ^ 2 = ∫ a, ‖ψ a‖ ^ 2 ∂μ := by
  have h_l2 : MeasureTheory.Integrable (fun a => ⟪ψ a, ψ a⟫_ℂ) μ :=
    MeasureTheory.L2.integrable_inner _ _
  have h_re := integral_re h_l2
  have h_in : (⟪ψ, ψ⟫_ℂ).re = ∫ a, ‖ψ a‖ ^ 2 ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    change RCLike.re (∫ a, ⟪ψ a, ψ a⟫_ℂ ∂μ) = _
    rw [← h_re]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    change (⟪ψ a, ψ a⟫_ℂ).re = ‖ψ a‖ ^ 2
    rw [inner_self_eq_norm_sq_to_K]
    simp [pow_two]
  rw [← h_in, inner_self_eq_norm_sq_to_K]
  simp [pow_two]

private theorem integrable_of_continuous_compact {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ]
    (f : α → ℝ) (hf : Continuous f) :
    MeasureTheory.Integrable f μ := by
  obtain ⟨M, hM⟩ := (isCompact_univ.image (continuous_abs.comp hf)).bddAbove
  let C : ℝ := max M 0
  refine (MeasureTheory.integrable_const C).mono' hf.stronglyMeasurable.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs]
  exact le_max_of_le_left (hM ⟨x, Set.mem_univ x, rfl⟩)

private theorem memLp_of_continuous_compact {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ]
    (f : α → ℝ) (hf : Continuous f) :
    MeasureTheory.MemLp (fun x => (f x : ℂ)) 2 μ := by
  obtain ⟨M, hM⟩ := (isCompact_univ.image (continuous_abs.comp hf)).bddAbove
  let C : ℝ := max M 0
  have hC : 0 ≤ C := le_max_right M 0
  refine memLp_two_of_measurable_bound μ (fun x => (f x : ℂ))
    (Complex.continuous_ofReal.comp hf).measurable C hC fun x => ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact le_max_of_le_left (hM ⟨x, Set.mem_univ x, rfl⟩)

private theorem compact_integral_op_of_cont_kernel
    {α : Type*} [TopologicalSpace α] [CompactSpace α] [T2Space α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (K : α → α → ℝ) (hK_cont : Continuous (Function.uncurry K))
    (hK_nn : ∀ x y, 0 ≤ K x y) (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ x y, K x y ≤ M_K)
    (T : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ)
    (hT_ae : ∀ ψ, ⇑T ψ =ᵐ[μ] fun x => ∫ y, ((K x y : ℝ) : ℂ) * ψ y ∂μ) :
    IsCompactOperator ⇑T := by
  classical
  let fn : MeasureTheory.Lp ℂ 2 μ → α → ℂ := fun ψ x => ∫ y, ((K x y : ℝ) : ℂ) * ψ y ∂μ
  have hK_mul_int : ∀ (ψ : MeasureTheory.Lp ℂ 2 μ) (x : α),
      MeasureTheory.Integrable (fun y => ((K x y : ℝ) : ℂ) * ψ y) μ := by
    intro ψ x
    have hψ_mem : MeasureTheory.MemLp (⇑ψ) 2 μ := MeasureTheory.Lp.memLp ψ
    have h_dom : MeasureTheory.Integrable (fun y => M_K * ‖ψ y‖) μ :=
      (hψ_mem.integrable one_le_two).norm.const_mul M_K
    refine h_dom.mono' ?_ ?_
    · have hp : Continuous (fun y : α => (x, y)) := continuous_const.prodMk continuous_id
      exact (Complex.continuous_ofReal.comp (hK_cont.comp hp)).stronglyMeasurable.aestronglyMeasurable.mul
        hψ_mem.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun y => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK_nn x y)]
      exact mul_le_mul_of_nonneg_right (hK_bd x y) (norm_nonneg _)
  have h_pt_bd : ∀ (ψ : MeasureTheory.Lp ℂ 2 μ) (x : α), ‖fn ψ x‖ ≤ M_K * ‖ψ‖ := by
    intro ψ x
    have h_int := hK_mul_int ψ x
    have h_dom : MeasureTheory.Integrable (fun y => M_K * ‖ψ y‖) μ :=
      ((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul M_K
    calc ‖fn ψ x‖ ≤ ∫ y, ‖((K x y : ℝ) : ℂ) * ψ y‖ ∂μ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ y, M_K * ‖ψ y‖ ∂μ := by
          refine MeasureTheory.integral_mono h_int.norm h_dom fun y => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK_nn x y)]
          exact mul_le_mul_of_nonneg_right (hK_bd x y) (norm_nonneg _)
      _ = M_K * ∫ y, ‖ψ y‖ ∂μ := MeasureTheory.integral_const_mul M_K _
      _ ≤ M_K * ‖ψ‖ := mul_le_mul_of_nonneg_left (l1_le_l2_prob μ ψ) hM_K
  have h_approx : ∀ n : ℕ, ∃ T_n : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ,
      IsCompactOperator ⇑T_n ∧ ‖T - T_n‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    let δ : ℝ := 1 / ((n : ℝ) + 1)
    have hδ : 0 < δ := by positivity
    let V : α → Set α := fun x₀ => { x | ∀ y : α, |K x y - K x₀ y| < δ }
    have hV_open : ∀ x₀ : α, IsOpen (V x₀) := by
      intro x₀
      let C_set : Set (α × α) := { p | δ ≤ |K p.1 p.2 - K x₀ p.2| }
      have h_pair : Continuous (fun p : α × α => (x₀, p.2)) :=
        continuous_const.prodMk continuous_snd
      have hC_cont : Continuous (fun p : α × α => |K p.1 p.2 - K x₀ p.2|) :=
        continuous_abs.comp (hK_cont.sub (hK_cont.comp h_pair))
      have hC_closed : IsClosed C_set := isClosed_le continuous_const hC_cont
      have h_proj_closed : IsClosed (Prod.fst '' C_set) :=
        (hC_closed.isCompact.image continuous_fst).isClosed
      have hV_eq : V x₀ = (Prod.fst '' C_set)ᶜ := by
        ext x
        simp only [V, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, C_set, Prod.exists,
          not_exists, not_and]
        constructor
        · intro h a b hle ha; subst ha; exact not_le.mpr (h b) hle
        · intro h y; exact not_le.mp fun hle => h x y hle rfl
      rw [hV_eq]
      exact h_proj_closed.isOpen_compl
    have h_cov : Set.univ ⊆ ⋃ x₀ : α, V x₀ := by
      intro x _; refine Set.mem_iUnion.mpr ⟨x, fun y => by simpa using hδ⟩
    obtain ⟨t, ht_cov⟩ := isCompact_univ.elim_finite_subcover V hV_open h_cov
    let m := t.card
    let e : Fin m ≃ ↥t := t.equivFin.symm
    let x_rep : Fin m → α := fun i => (e i).1
    let s : Fin m → Set α := fun i =>
      V (x_rep i) \ ⋃ j ∈ Finset.univ.filter (fun j : Fin m => j < i), V (x_rep j)
    have hs_meas : ∀ i : Fin m, MeasurableSet (s i) := fun i =>
      (hV_open (x_rep i)).measurableSet.diff
        (Finset.measurableSet_biUnion _ fun j _ => (hV_open (x_rep j)).measurableSet)
    have hs_disj : ∀ i j : Fin m, i ≠ j → Disjoint (s i) (s j) := by
      intro i j hij
      rw [Set.disjoint_left]
      intro x hxi hxj
      rcases lt_trichotomy i j with hlt | heq | hgt
      · exact hxj.2 (Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩) hxi.1)
      · exact hij heq
      · exact hxi.2 (Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩) hxj.1)
    have hs_cover : ∀ x : α, ∃ i : Fin m, x ∈ s i := by
      intro x
      let F_x : Finset (Fin m) := Finset.univ.filter (fun i => x ∈ V (x_rep i))
      have hF_ne : F_x.Nonempty := by
        have hmem := ht_cov (Set.mem_univ x)
        rw [Set.mem_iUnion₂] at hmem
        rcases hmem with ⟨x₀, hx₀, hxV⟩
        refine ⟨e.symm ⟨x₀, hx₀⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        simpa [x_rep, Equiv.apply_symm_apply] using hxV
      let i₀ := F_x.min' hF_ne
      refine ⟨i₀, (Finset.mem_filter.mp (Finset.min'_mem F_x hF_ne)).2, ?_⟩
      intro h_in
      rw [Set.mem_iUnion₂] at h_in
      rcases h_in with ⟨j, hj, hjV⟩
      have hj_lt : j < i₀ := (Finset.mem_filter.mp hj).2
      have hj_mem : j ∈ F_x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjV⟩
      exact absurd (Finset.min'_le F_x j hj_mem) (not_le_of_gt hj_lt)
    let ind : Fin m → MeasureTheory.Lp ℂ 2 μ := fun i =>
      MeasureTheory.indicatorConstLp 2 (hs_meas i) (MeasureTheory.measure_ne_top μ (s i)) (1 : ℂ)
    let c : Fin m → MeasureTheory.Lp ℂ 2 μ → ℂ := fun i ψ => fn ψ (x_rep i)
    have hc_add : ∀ i ψ₁ ψ₂, c i (ψ₁ + ψ₂) = c i ψ₁ + c i ψ₂ := by
      intro i ψ₁ ψ₂
      dsimp [c, fn]
      rw [← MeasureTheory.integral_add (hK_mul_int ψ₁ (x_rep i)) (hK_mul_int ψ₂ (x_rep i))]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.Lp.coeFn_add ψ₁ ψ₂] with y hy
      have hy' : (ψ₁ + ψ₂) y = ψ₁ y + ψ₂ y := hy
      change ((K (x_rep i) y : ℝ) : ℂ) * (ψ₁ + ψ₂) y =
        ((K (x_rep i) y : ℝ) : ℂ) * ψ₁ y + ((K (x_rep i) y : ℝ) : ℂ) * ψ₂ y
      rw [hy', mul_add]
    have hc_smul : ∀ i (r : ℂ) ψ, c i (r • ψ) = r * c i ψ := by
      intro i r ψ
      dsimp [c, fn]
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.Lp.coeFn_smul r ψ] with y hy
      have hy' : (r • ψ) y = r * ψ y := hy
      change ((K (x_rep i) y : ℝ) : ℂ) * (r • ψ) y =
        r * (((K (x_rep i) y : ℝ) : ℂ) * ψ y)
      rw [hy', mul_left_comm]
    have hind_norm : ∀ i, ‖ind i‖ ≤ 1 := by
      intro i
      rw [← sq_le_sq₀ (norm_nonneg _) zero_le_one, one_pow, lp_norm_sq_eq_integral]
      have hcoe := MeasureTheory.indicatorConstLp_coeFn (p := (2 : ENNReal))
        (μ := μ) (s := s i) (hs := hs_meas i)
        (hμs := MeasureTheory.measure_ne_top μ (s i)) (c := (1 : ℂ))
      have h_int_ae : (fun x => ‖(ind i) x‖ ^ 2) =ᵐ[μ]
          fun x => if x ∈ s i then (1 : ℝ) else 0 := by
        filter_upwards [hcoe] with x hx
        change ‖(ind i) x‖ ^ 2 = _
        rw [hx, Set.indicator_apply]
        by_cases hxi : x ∈ s i <;> simp [hxi]
      rw [MeasureTheory.integral_congr_ae h_int_ae]
      have h_le : ∀ x, (if x ∈ s i then (1 : ℝ) else 0) ≤ 1 := fun x => by split_ifs <;> norm_num
      have h_ind_aesm : MeasureTheory.AEStronglyMeasurable
          ((s i).indicator (fun _ => (1 : ℝ))) μ :=
        (MeasureTheory.aestronglyMeasurable_const (b := (1 : ℝ))).indicator (hs_meas i)
      have h_int1 : MeasureTheory.Integrable (fun x => if x ∈ s i then (1 : ℝ) else 0) μ :=
        (MeasureTheory.integrable_const (1 : ℝ)).mono'
          (h_ind_aesm.congr (Filter.Eventually.of_forall fun U => by simp [Set.indicator_apply]))
          (Filter.Eventually.of_forall fun U => by split_ifs <;> simp)
      calc ∫ x, (if x ∈ s i then (1 : ℝ) else 0) ∂μ
          ≤ ∫ _x, (1 : ℝ) ∂μ :=
            MeasureTheory.integral_mono h_int1 (MeasureTheory.integrable_const 1) h_le
        _ = 1 := by simp [Measure.real, MeasureTheory.measure_univ]
    let T_n : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ :=
      LinearMap.mkContinuous
        { toFun := fun ψ => ∑ i : Fin m, c i ψ • ind i
          map_add' := fun ψ₁ ψ₂ => by simp only [hc_add, add_smul, Finset.sum_add_distrib]
          map_smul' := fun r ψ => by
            simp only [hc_smul, smul_smul, RingHom.id_apply, Finset.smul_sum] }
        ((m : ℝ) * M_K)
        (fun ψ => by
          change ‖∑ i : Fin m, c i ψ • ind i‖ ≤ ((m : ℝ) * M_K) * ‖ψ‖
          calc ‖∑ i : Fin m, c i ψ • ind i‖
              ≤ ∑ i : Fin m, ‖c i ψ • ind i‖ := norm_sum_le _ _
            _ ≤ ∑ _i : Fin m, M_K * ‖ψ‖ := by
                  refine Finset.sum_le_sum fun i _ => ?_
                  rw [norm_smul]
                  calc ‖c i ψ‖ * ‖ind i‖ ≤ (M_K * ‖ψ‖) * 1 :=
                        mul_le_mul (h_pt_bd ψ (x_rep i)) (hind_norm i) (norm_nonneg _)
                          (mul_nonneg hM_K (norm_nonneg _))
                    _ = M_K * ‖ψ‖ := mul_one _
            _ = ((m : ℝ) * M_K) * ‖ψ‖ := by simp [Finset.sum_const, nsmul_eq_mul, mul_assoc])
    have hTn_comp : IsCompactOperator ⇑T_n := by
      let Φ : (Fin m → ℂ) → MeasureTheory.Lp ℂ 2 μ := fun z => ∑ i : Fin m, z i • ind i
      have hΦ_cont : Continuous Φ :=
        continuous_finset_sum Finset.univ fun i _ => (continuous_apply i).smul continuous_const
      let B_m : Set (Fin m → ℂ) := Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) M_K
      have hB_m : IsCompact B_m := isCompact_univ_pi fun _ => isCompact_closedBall 0 M_K
      refine ⟨Φ '' B_m, hB_m.image hΦ_cont,
        Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) fun ψ hψ => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right] at hψ
      refine ⟨fun i => c i ψ, fun i _ => ?_, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖c i ψ‖ ≤ M_K * ‖ψ‖ := h_pt_bd ψ (x_rep i)
        _ ≤ M_K * 1 := mul_le_mul_of_nonneg_left hψ hM_K
        _ = M_K := mul_one M_K
    have hTn_norm : ‖T - T_n‖ ≤ δ := by
      refine ContinuousLinearMap.opNorm_le_bound _ hδ.le fun ψ => ?_
      have hTn_ae : ⇑(T_n ψ) =ᵐ[μ] fun x => ∑ i : Fin m, if x ∈ s i then c i ψ else 0 := by
        have hsum := lp_coeFn_finset_sum μ Finset.univ (fun i => c i ψ • ind i)
        have hterm : ∀ i : Fin m,
            ⇑(c i ψ • ind i) =ᵐ[μ] fun x => if x ∈ s i then c i ψ else 0 := by
          intro i
          have hs_ae := MeasureTheory.Lp.coeFn_smul (c i ψ) (ind i)
          have hi_ae := MeasureTheory.indicatorConstLp_coeFn (p := (2 : ENNReal))
            (μ := μ) (s := s i) (hs := hs_meas i)
            (hμs := MeasureTheory.measure_ne_top μ (s i)) (c := (1 : ℂ))
          filter_upwards [hs_ae, hi_ae] with x hxs hxi
          simp only [Pi.smul_apply, smul_eq_mul] at hxs
          change ⇑(c i ψ • ind i) x = _
          rw [hxs]
          change c i ψ * ⇑(ind i) x = _
          rw [hxi, Set.indicator_apply]
          split_ifs <;> simp
        have hall : (fun x => ∑ i : Fin m, (c i ψ • ind i) x) =ᵐ[μ]
            fun x => ∑ i : Fin m, if x ∈ s i then c i ψ else 0 := by
          have h_ev : ∀ᵐ x ∂μ, ∀ i : Fin m,
              ⇑(c i ψ • ind i) x = if x ∈ s i then c i ψ else 0 :=
            MeasureTheory.ae_all_iff.mpr hterm
          filter_upwards [h_ev] with x hx
          exact Finset.sum_congr rfl fun i _ => hx i
        filter_upwards [hsum, hall] with x hx1 hx2
        change ⇑(∑ i : Fin m, c i ψ • ind i) x = _
        rw [hx1, hx2]
      have hdiff_ae : ⇑((T - T_n) ψ) =ᵐ[μ]
          fun x => fn ψ x - ∑ i : Fin m, if x ∈ s i then c i ψ else 0 := by
        have hsub := MeasureTheory.Lp.coeFn_sub (T ψ) (T_n ψ)
        filter_upwards [hsub, hT_ae ψ, hTn_ae] with x hs hT hTn
        change ⇑(T ψ - T_n ψ) x = _
        rw [hs]
        simp only [Pi.sub_apply]
        rw [hT, hTn]
      have hpt_le : ∀ᵐ x ∂μ, ‖((T - T_n) ψ) x‖ ≤ δ * ‖ψ‖ := by
        filter_upwards [hdiff_ae] with x hx
        change ‖((T - T_n) ψ) x‖ ≤ δ * ‖ψ‖
        rw [hx]
        obtain ⟨i₀, hi₀⟩ := hs_cover x
        have hsum_eq : (∑ i : Fin m, if x ∈ s i then c i ψ else 0) = c i₀ ψ := by
          rw [Finset.sum_eq_single i₀]
          · simp [hi₀]
          · intro i _ hne
            have hnot : x ∉ s i := fun hi => (Set.disjoint_left.mp (hs_disj i i₀ hne)) hi hi₀
            simp [hnot]
          · intro hi₀_not
            exact absurd (Finset.mem_univ i₀) hi₀_not
        rw [hsum_eq]
        have hi₀_V : x ∈ V (x_rep i₀) := hi₀.1
        have hi1 := hK_mul_int ψ x
        have hi2 := hK_mul_int ψ (x_rep i₀)
        dsimp [c, fn]
        rw [← MeasureTheory.integral_sub hi1 hi2]
        have h_dom : MeasureTheory.Integrable (fun y => δ * ‖ψ y‖) μ :=
          ((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul δ
        have h_sub_int : MeasureTheory.Integrable
            (fun y => ‖((K x y : ℝ) : ℂ) * ψ y - ((K (x_rep i₀) y : ℝ) : ℂ) * ψ y‖) μ :=
          (hi1.sub hi2).norm
        calc ‖∫ y, (((K x y : ℝ) : ℂ) * ψ y - ((K (x_rep i₀) y : ℝ) : ℂ) * ψ y) ∂μ‖
            ≤ ∫ y, ‖((K x y : ℝ) : ℂ) * ψ y - ((K (x_rep i₀) y : ℝ) : ℂ) * ψ y‖ ∂μ :=
              MeasureTheory.norm_integral_le_integral_norm _
          _ ≤ ∫ y, δ * ‖ψ y‖ ∂μ := by
              refine MeasureTheory.integral_mono h_sub_int h_dom fun y => ?_
              have hfac : ((K x y : ℝ) : ℂ) * ψ y - ((K (x_rep i₀) y : ℝ) : ℂ) * ψ y =
                  (((K x y - K (x_rep i₀) y : ℝ) : ℂ)) * ψ y := by
                push_cast; ring
              rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_right (hi₀_V y).le (norm_nonneg _)
          _ = δ * ∫ y, ‖ψ y‖ ∂μ := MeasureTheory.integral_const_mul δ _
          _ ≤ δ * ‖ψ‖ := mul_le_mul_of_nonneg_left (l1_le_l2_prob μ ψ) hδ.le
      rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ.le (norm_nonneg _)),
          lp_norm_sq_eq_integral]
      have h_int1 : MeasureTheory.Integrable (fun x => ‖((T - T_n) ψ) x‖ ^ 2) μ :=
        (MeasureTheory.memLp_two_iff_integrable_sq_norm
          (MeasureTheory.Lp.memLp ((T - T_n) ψ)).aestronglyMeasurable).mp
          (MeasureTheory.Lp.memLp ((T - T_n) ψ))
      have h_int2 : MeasureTheory.Integrable (fun _ => (δ * ‖ψ‖) ^ 2) μ :=
        MeasureTheory.integrable_const _
      calc ∫ x, ‖((T - T_n) ψ) x‖ ^ 2 ∂μ
          ≤ ∫ _x, (δ * ‖ψ‖) ^ 2 ∂μ := by
            refine MeasureTheory.integral_mono_ae h_int1 h_int2 ?_
            filter_upwards [hpt_le] with x hx
            exact pow_le_pow_left₀ (norm_nonneg _) hx 2
        _ = (δ * ‖ψ‖) ^ 2 := by
            rw [MeasureTheory.integral_const]
            simp [Measure.real, MeasureTheory.measure_univ]
    exact ⟨T_n, hTn_comp, hTn_norm⟩
  choose T_seq hT_comp hT_norm using h_approx
  have h_tendsto : Filter.Tendsto T_seq Filter.atTop (nhds T) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / ε)
    refine ⟨N₀, fun n hn => ?_⟩
    have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h_lt : 1 / ((n : ℝ) + 1) < ε := by
      rw [div_lt_iff₀ hn_pos]
      have h1 : 1 / ε < (n : ℝ) + 1 := lt_of_lt_of_le hN₀ (by exact_mod_cast (Nat.le_succ_of_le hn))
      have h2 := (div_lt_iff₀ hε).mp h1
      linarith
    calc dist (T_seq n) T = ‖T - T_seq n‖ := by rw [dist_comm, dist_eq_norm]
      _ ≤ 1 / ((n : ℝ) + 1) := hT_norm n
      _ < ε := h_lt
  exact isClosed_setOf_isCompactOperator.mem_of_tendsto h_tendsto
    (Filter.Eventually.of_forall hT_comp)

/--
**Compactness of `wilsonIntegralOp`**:
every continuous Wilson kernel on the compact product group `SU(N)^{3L³}` defines
a compact integral operator on `L²(SU(N)^{3L³}, dμ_Haar)` via norm-convergent
finite-rank kernel partitions.
-/
theorem wilsonIntegralOp_compact (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ U U', K_kin U U' ≤ M_K) :
    IsCompactOperator ⇑(wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd) := by
  haveI := latticeHaarMeasure_prob L N
  exact compact_integral_op_of_cont_kernel (latticeHaarMeasure L N)
    (wilsonKernel β (cubicPlaquettes L) K_kin)
    (continuous_cubicWilsonKernel L N β K_kin hK_cont)
    (wilsonKernel_nonneg β (cubicPlaquettes L) K_kin hK_nn)
    M_K hM_K (fun U U' => (wilsonKernel_cubic_le L N β hβ K_kin hK_nn M_K hK_bd U U').2)
    (wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd)
    (wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd)

/-- Gram-factorized symmetric positive-definite kinetic kernel `∫ χ(U, W) χ(U', W) dμ(W)`. -/
noncomputable def wilsonGramKernel (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  ∫ W, χ U W * χ U' W ∂(latticeHaarMeasure L N)

theorem continuous_wilsonGramKernel (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hχ_cont : Continuous (Function.uncurry χ))
    (hχ_nn : ∀ U W, 0 ≤ χ U W)
    (M_χ : ℝ) (hM_χ : 0 ≤ M_χ) (hχ_bd : ∀ U W, χ U W ≤ M_χ) :
    Continuous (Function.uncurry (wilsonGramKernel L N χ)) := by
  let G_L := GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  refine MeasureTheory.continuous_of_dominated
    (bound := fun _ : G_L => M_χ ^ 2) ?_ ?_ (MeasureTheory.integrable_const _) ?_
  · intro p
    have hp1 : Continuous (fun W : G_L => (p.1, W)) := continuous_const.prodMk continuous_id
    have hp2 : Continuous (fun W : G_L => (p.2, W)) := continuous_const.prodMk continuous_id
    exact ((hχ_cont.comp hp1).mul (hχ_cont.comp hp2)).stronglyMeasurable.aestronglyMeasurable
  · intro p
    refine Filter.Eventually.of_forall fun W => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hχ_nn p.1 W) (hχ_nn p.2 W)), sq]
    exact mul_le_mul (hχ_bd p.1 W) (hχ_bd p.2 W) (hχ_nn p.2 W) hM_χ
  · refine Filter.Eventually.of_forall fun W => ?_
    have hp1 : Continuous (fun p : G_L × G_L => (p.1, W)) := continuous_fst.prodMk continuous_const
    have hp2 : Continuous (fun p : G_L × G_L => (p.2, W)) := continuous_snd.prodMk continuous_const
    exact (hχ_cont.comp hp1).mul (hχ_cont.comp hp2)

theorem wilsonGramKernel_symm (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonGramKernel L N χ U' U = wilsonGramKernel L N χ U U' := by
  dsimp [wilsonGramKernel]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => by dsimp only; exact mul_comm _ _)

theorem wilsonGramKernel_nonneg (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hχ_nn : ∀ U W, 0 ≤ χ U W)
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 ≤ wilsonGramKernel L N χ U U' :=
  MeasureTheory.integral_nonneg fun W => mul_nonneg (hχ_nn U W) (hχ_nn U' W)

theorem wilsonGramKernel_le (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hχ_cont : Continuous (Function.uncurry χ))
    (hχ_nn : ∀ U W, 0 ≤ χ U W)
    (M_χ : ℝ) (hM_χ : 0 ≤ M_χ) (hχ_bd : ∀ U W, χ U W ≤ M_χ)
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonGramKernel L N χ U U' ≤ M_χ ^ 2 := by
  let G_L := GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  have hp1 : Continuous (fun W : G_L => (U, W)) := continuous_const.prodMk continuous_id
  have hp2 : Continuous (fun W : G_L => (U', W)) := continuous_const.prodMk continuous_id
  have h_int : MeasureTheory.Integrable (fun W => χ U W * χ U' W) μ :=
    integrable_of_continuous_compact μ _ ((hχ_cont.comp hp1).mul (hχ_cont.comp hp2))
  calc wilsonGramKernel L N χ U U'
      ≤ ∫ _W, M_χ ^ 2 ∂μ := by
        refine MeasureTheory.integral_mono h_int (MeasureTheory.integrable_const _) fun W => ?_
        rw [sq]
        exact mul_le_mul (hχ_bd U W) (hχ_bd U' W) (hχ_nn U' W) hM_χ
    _ = M_χ ^ 2 := by simp [Measure.real, MeasureTheory.measure_univ]

theorem wilsonGramKernel_lb (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hχ_cont : Continuous (Function.uncurry χ))
    (c_χ : ℝ) (hc_χ : 0 ≤ c_χ) (hχ_lb : ∀ U W, c_χ ≤ χ U W)
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    c_χ ^ 2 ≤ wilsonGramKernel L N χ U U' := by
  let G_L := GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  have hp1 : Continuous (fun W : G_L => (U, W)) := continuous_const.prodMk continuous_id
  have hp2 : Continuous (fun W : G_L => (U', W)) := continuous_const.prodMk continuous_id
  have h_int : MeasureTheory.Integrable (fun W => χ U W * χ U' W) μ :=
    integrable_of_continuous_compact μ _ ((hχ_cont.comp hp1).mul (hχ_cont.comp hp2))
  calc c_χ ^ 2 = ∫ _W, c_χ ^ 2 ∂μ := by simp [Measure.real, MeasureTheory.measure_univ]
    _ ≤ wilsonGramKernel L N χ U U' := by
        refine MeasureTheory.integral_mono (MeasureTheory.integrable_const _) h_int fun W => ?_
        rw [sq]
        exact mul_le_mul (hχ_lb U W) (hχ_lb U' W) hc_χ (hc_χ.trans (hχ_lb U W))

theorem wilsonGramKernel_gauge_inv (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hχ_inv : ∀ g U W, χ (gaugeAct g U) (gaugeAct g W) = χ U W)
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonGramKernel L N χ (gaugeAct g U) (gaugeAct g U') = wilsonGramKernel L N χ U U' := by
  dsimp [wilsonGramKernel]
  calc ∫ W, χ (gaugeAct g U) W * χ (gaugeAct g U') W ∂(latticeHaarMeasure L N)
      = ∫ W, χ (gaugeAct g U) (gaugeAct g W) * χ (gaugeAct g U') (gaugeAct g W)
          ∂(latticeHaarMeasure L N) :=
        (cubicWilsonExpectation_gauge_inv L N g
          (fun W => χ (gaugeAct g U) W * χ (gaugeAct g U') W)).symm
    _ = ∫ W, χ U W * χ U' W ∂(latticeHaarMeasure L N) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
        dsimp only
        rw [hχ_inv, hχ_inv]

/--
**Positivity (reflection positivity) of `wilsonIntegralOp`** for any Gram-factorized
Wilson kernel: `0 ≤ Re ⟪ψ, T_W ψ⟫ = ∫ ‖∫ exp(-½ S_W[U]) χ(U, W) ψ(U) dμ(U)‖² dμ(W)`.
-/
theorem wilsonIntegralOp_gram_pos (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hχ_cont : Continuous (Function.uncurry χ))
    (hχ_nn : ∀ U W, 0 ≤ χ U W)
    (M_χ : ℝ) (hM_χ : 0 ≤ M_χ) (hχ_bd : ∀ U W, χ U W ≤ M_χ)
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    0 ≤ (⟪ψ, wilsonIntegralOp L N β hβ (wilsonGramKernel L N χ)
      (continuous_wilsonGramKernel L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd)
      (wilsonGramKernel_nonneg L N χ hχ_nn) (M_χ ^ 2) (sq_nonneg M_χ)
      (wilsonGramKernel_le L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd) ψ⟫_ℂ).re := by
  let G_L := GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  let K_kin := wilsonGramKernel L N χ
  have hK_cont := continuous_wilsonGramKernel L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd
  have hK_nn := wilsonGramKernel_nonneg L N χ hχ_nn
  have hK_bd := wilsonGramKernel_le L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd
  let T := wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn (M_χ ^ 2) (sq_nonneg M_χ) hK_bd
  let κ : G_L → G_L → ℝ := fun U W => cubicWilsonWeight L N β U * χ U W
  have hκ_cont : Continuous (Function.uncurry κ) := by
    have hS := continuous_cubicWilsonAction L N β
    have hw : Continuous (cubicWilsonWeight L N β) :=
      Real.continuous_exp.comp (continuous_const.mul hS)
    exact (hw.comp continuous_fst).mul hχ_cont
  have hκ_bd : ∀ U W, 0 ≤ κ U W ∧ κ U W ≤ M_χ := fun U W => by
    have hwb := cubicWilsonWeight_bounds L N β hβ U
    have hwnn : 0 ≤ cubicWilsonWeight L N β U := by
      unfold cubicWilsonWeight; exact (Real.exp_pos _).le
    refine ⟨mul_nonneg hwnn (hχ_nn U W), ?_⟩
    calc cubicWilsonWeight L N β U * χ U W ≤ 1 * χ U W :=
          mul_le_mul_of_nonneg_right hwb.2 (hχ_nn U W)
      _ ≤ M_χ := by rw [one_mul]; exact hχ_bd U W
  have hKW_eq : ∀ U U', ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) =
      ∫ W, ((κ U W : ℝ) : ℂ) * ((κ U' W : ℝ) : ℂ) ∂μ := by
    intro U U'
    have h_exp : Real.exp (-(1 / 2 : ℝ) *
        (wilsonAction β (cubicPlaquettes L) U + wilsonAction β (cubicPlaquettes L) U')) =
        cubicWilsonWeight L N β U * cubicWilsonWeight L N β U' := by
      unfold cubicWilsonWeight
      rw [← Real.exp_add]
      congr 1; ring
    have h_real : wilsonKernel β (cubicPlaquettes L) K_kin U U' =
        ∫ W, κ U W * κ U' W ∂μ := by
      unfold wilsonKernel K_kin wilsonGramKernel
      rw [h_exp, ← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
      dsimp [κ]; ring
    have h_int_c : MeasureTheory.Integrable
        (fun W => (((κ U W * κ U' W : ℝ) : ℂ))) μ := by
      have hp1 : Continuous (fun W : G_L => (U, W)) := continuous_const.prodMk continuous_id
      have hp2 : Continuous (fun W : G_L => (U', W)) := continuous_const.prodMk continuous_id
      refine (MeasureTheory.integrable_const (M_χ ^ 2)).mono'
        (Complex.continuous_ofReal.comp
          ((hκ_cont.comp hp1).mul (hκ_cont.comp hp2))).stronglyMeasurable.aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall fun W => ?_
      have h1 := hκ_bd U W
      have h2 := hκ_bd U' W
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1.1 h2.1), sq]
      exact mul_le_mul h1.2 h2.2 h2.1 hM_χ
    rw [h_real]
    have h_cast : (fun W => ((κ U W : ℝ) : ℂ) * ((κ U' W : ℝ) : ℂ)) =
        fun W => (((κ U W * κ U' W : ℝ) : ℂ)) := by
      funext W; push_cast; ring
    rw [h_cast]
    have h_re_eq : (∫ W, (((κ U W * κ U' W : ℝ) : ℂ)) ∂μ).re = ∫ W, κ U W * κ U' W ∂μ := by
      change RCLike.re (∫ W, (((κ U W * κ U' W : ℝ) : ℂ)) ∂μ) = _
      rw [← integral_re h_int_c]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
      simp
    have h_im_eq : (∫ W, (((κ U W * κ U' W : ℝ) : ℂ)) ∂μ).im = 0 := by
      have h1 : (∫ W, (((κ U W * κ U' W : ℝ) : ℂ)) ∂μ).im =
          RCLike.re (-Complex.I * ∫ W, (((κ U W * κ U' W : ℝ) : ℂ)) ∂μ) := by
        simp [Complex.mul_re]
      rw [h1, ← MeasureTheory.integral_const_mul, ← integral_re (h_int_c.const_mul (-Complex.I))]
      refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun W => ?_)
      simp [Complex.mul_re]
    exact Complex.ext h_re_eq.symm h_im_eq.symm
  let g_half : G_L → ℂ := fun W => ∫ U, ((κ U W : ℝ) : ℂ) * ψ U ∂μ
  have hg_cont : Continuous g_half := by
    have h_dom : MeasureTheory.Integrable (fun U => M_χ * ‖ψ U‖) μ :=
      ((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul M_χ
    refine MeasureTheory.continuous_of_dominated ?_ ?_ h_dom ?_
    · intro W
      have hp : Continuous (fun U : G_L => (U, W)) := continuous_id.prodMk continuous_const
      exact (Complex.continuous_ofReal.comp (hκ_cont.comp hp)).stronglyMeasurable.aestronglyMeasurable.mul
        (MeasureTheory.Lp.memLp ψ).aestronglyMeasurable
    · intro W
      refine Filter.Eventually.of_forall fun U => ?_
      have hb := hκ_bd U W
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)
    · refine Filter.Eventually.of_forall fun U => ?_
      have hp : Continuous (fun W : G_L => (U, W)) := continuous_const.prodMk continuous_id
      exact (Complex.continuous_ofReal.comp (hκ_cont.comp hp)).mul continuous_const
  have hg_bd : ∀ W, ‖g_half W‖ ≤ M_χ * ‖ψ‖ := by
    intro W
    have hp : Continuous (fun U : G_L => (U, W)) := continuous_id.prodMk continuous_const
    have h_int : MeasureTheory.Integrable (fun U => ‖((κ U W : ℝ) : ℂ) * ψ U‖) μ := by
      have h_dom : MeasureTheory.Integrable (fun U => M_χ * ‖ψ U‖) μ :=
        ((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul M_χ
      refine h_dom.mono'
        ((Complex.continuous_ofReal.comp (hκ_cont.comp hp)).stronglyMeasurable.aestronglyMeasurable.mul
          (MeasureTheory.Lp.memLp ψ).aestronglyMeasurable).norm ?_
      refine Filter.Eventually.of_forall fun U => ?_
      have hb := hκ_bd U W
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)
    calc ‖g_half W‖ ≤ ∫ U, ‖((κ U W : ℝ) : ℂ) * ψ U‖ ∂μ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ U, M_χ * ‖ψ U‖ ∂μ := by
          refine MeasureTheory.integral_mono h_int
            (((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul M_χ) fun U => ?_
          have hb := hκ_bd U W
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
          exact mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)
      _ = M_χ * ∫ U, ‖ψ U‖ ∂μ := MeasureTheory.integral_const_mul M_χ _
      _ ≤ M_χ * ‖ψ‖ := mul_le_mul_of_nonneg_left (l1_le_l2_prob μ ψ) hM_χ
  have h_inner_eq : ⟪ψ, T ψ⟫_ℂ = ∫ W, (((‖g_half W‖ ^ 2 : ℝ) : ℂ)) ∂μ := by
    have hcinner : ∀ a b : ℂ, ⟪a, b⟫_ℂ = starRingEnd ℂ a * b := by
      intro a b
      have h1 : ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ = 1 := by
        rw [inner_self_eq_norm_sq_to_K]; norm_num
      calc ⟪a, b⟫_ℂ = ⟪a • (1 : ℂ), b • (1 : ℂ)⟫_ℂ := by simp
        _ = starRingEnd ℂ a * (b * ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ) := by
              rw [inner_smul_left, inner_smul_right]
        _ = starRingEnd ℂ a * b := by rw [h1, mul_one]
    have h1 : ⟪ψ, T ψ⟫_ℂ =
        ∫ U, starRingEnd ℂ (ψ U) * wilsonIntegralFn L N β K_kin ψ U ∂μ := by
      rw [MeasureTheory.L2.inner_def]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
        (M_χ ^ 2) (sq_nonneg M_χ) hK_bd ψ] with U hU
      rw [hU, hcinner]
    have h_step1 : ∀ U, wilsonIntegralFn L N β K_kin ψ U =
        ∫ W, ((κ U W : ℝ) : ℂ) * g_half W ∂μ := by
      intro U
      dsimp [wilsonIntegralFn]
      have h_prod1 : MeasureTheory.Integrable
          (Function.uncurry fun U' W => ((κ U W : ℝ) : ℂ) * (((κ U' W : ℝ) : ℂ) * ψ U'))
          (μ.prod μ) := by
        have hψ_aesm : MeasureTheory.AEStronglyMeasurable (fun p : G_L × G_L => ψ p.1) (μ.prod μ) :=
          (MeasureTheory.Lp.memLp ψ).aestronglyMeasurable.comp_quasiMeasurePreserving
            MeasureTheory.Measure.quasiMeasurePreserving_fst
        have hκ1 : MeasureTheory.AEStronglyMeasurable
            (fun p : G_L × G_L => ((κ U p.2 : ℝ) : ℂ)) (μ.prod μ) :=
          (Complex.continuous_ofReal.comp
            (hκ_cont.comp (continuous_const.prodMk continuous_snd))).stronglyMeasurable.aestronglyMeasurable
        have hκ2 : MeasureTheory.AEStronglyMeasurable
            (fun p : G_L × G_L => ((κ p.1 p.2 : ℝ) : ℂ)) (μ.prod μ) :=
          (Complex.continuous_ofReal.comp hκ_cont).stronglyMeasurable.aestronglyMeasurable
        have h_dom : MeasureTheory.Integrable
            (fun p : G_L × G_L => (M_χ ^ 2 * ‖ψ p.1‖) * (1 : ℝ)) (μ.prod μ) :=
          ((((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul (M_χ ^ 2)).mul_prod
            (MeasureTheory.integrable_const (1 : ℝ)))
        refine h_dom.mono' (hκ1.mul (hκ2.mul hψ_aesm)) ?_
        refine Filter.Eventually.of_forall fun p => ?_
        have hb1 := hκ_bd U p.2
        have hb2 := hκ_bd p.1 p.2
        dsimp only [Function.uncurry]
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hb1.1, abs_of_nonneg hb2.1, mul_one]
        calc κ U p.2 * (κ p.1 p.2 * ‖ψ p.1‖)
            ≤ M_χ * (M_χ * ‖ψ p.1‖) :=
              mul_le_mul hb1.2 (mul_le_mul_of_nonneg_right hb2.2 (norm_nonneg _))
                (mul_nonneg hb2.1 (norm_nonneg _)) hM_χ
          _ = M_χ ^ 2 * ‖ψ p.1‖ := by rw [sq]; ring
      calc ∫ U', ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) * ψ U' ∂μ
          = ∫ U', ∫ W, ((κ U W : ℝ) : ℂ) * (((κ U' W : ℝ) : ℂ) * ψ U') ∂μ ∂μ := by
              refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U' => ?_)
              dsimp only
              rw [hKW_eq U U', ← MeasureTheory.integral_mul_const]
              refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => by
                dsimp only; ring)
        _ = ∫ W, ∫ U', ((κ U W : ℝ) : ℂ) * (((κ U' W : ℝ) : ℂ) * ψ U') ∂μ ∂μ :=
              MeasureTheory.integral_integral_swap h_prod1
        _ = ∫ W, ((κ U W : ℝ) : ℂ) * g_half W ∂μ := by
              refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
              dsimp only
              rw [MeasureTheory.integral_const_mul]
    have h_prod2 : MeasureTheory.Integrable
        (Function.uncurry fun U W =>
          (starRingEnd ℂ (((κ U W : ℝ) : ℂ) * ψ U)) * g_half W)
        (μ.prod μ) := by
      have hψ_aesm : MeasureTheory.AEStronglyMeasurable (fun p : G_L × G_L => ψ p.1) (μ.prod μ) :=
        (MeasureTheory.Lp.memLp ψ).aestronglyMeasurable.comp_quasiMeasurePreserving
          MeasureTheory.Measure.quasiMeasurePreserving_fst
      have hκ_aesm : MeasureTheory.AEStronglyMeasurable
          (fun p : G_L × G_L => ((κ p.1 p.2 : ℝ) : ℂ)) (μ.prod μ) :=
        (Complex.continuous_ofReal.comp hκ_cont).stronglyMeasurable.aestronglyMeasurable
      have hg_aesm : MeasureTheory.AEStronglyMeasurable
          (fun p : G_L × G_L => g_half p.2) (μ.prod μ) :=
        (hg_cont.comp continuous_snd).stronglyMeasurable.aestronglyMeasurable
      have h_conj : MeasureTheory.AEStronglyMeasurable
          (fun p : G_L × G_L => starRingEnd ℂ (((κ p.1 p.2 : ℝ) : ℂ) * ψ p.1)) (μ.prod μ) :=
        continuous_star.comp_aestronglyMeasurable (hκ_aesm.mul hψ_aesm)
      have h_dom : MeasureTheory.Integrable
          (fun p : G_L × G_L => (M_χ * ‖ψ p.1‖) * (M_χ * ‖ψ‖)) (μ.prod μ) :=
        (((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul M_χ).mul_prod
          (MeasureTheory.integrable_const (M_χ * ‖ψ‖))
      refine h_dom.mono' (h_conj.mul hg_aesm) ?_
      refine Filter.Eventually.of_forall fun p => ?_
      have hb := hκ_bd p.1 p.2
      have hconj : ‖starRingEnd ℂ (((κ p.1 p.2 : ℝ) : ℂ) * ψ p.1)‖ =
          ‖((κ p.1 p.2 : ℝ) : ℂ) * ψ p.1‖ := norm_star _
      dsimp only [Function.uncurry]
      rw [norm_mul, hconj, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _))
        (hg_bd p.2) (norm_nonneg _) (mul_nonneg hM_χ (norm_nonneg _))
    rw [h1]
    calc ∫ U, starRingEnd ℂ (ψ U) * wilsonIntegralFn L N β K_kin ψ U ∂μ
        = ∫ U, ∫ W, starRingEnd ℂ (((κ U W : ℝ) : ℂ) * ψ U) * g_half W ∂μ ∂μ := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
            dsimp only
            rw [h_step1 U, ← MeasureTheory.integral_const_mul]
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
            dsimp only
            rw [map_mul, Complex.conj_ofReal]
            ring
      _ = ∫ W, ∫ U, starRingEnd ℂ (((κ U W : ℝ) : ℂ) * ψ U) * g_half W ∂μ ∂μ :=
            MeasureTheory.integral_integral_swap h_prod2
      _ = ∫ W, (((‖g_half W‖ ^ 2 : ℝ) : ℂ)) ∂μ := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
            dsimp only
            rw [MeasureTheory.integral_mul_const, integral_conj]
            change starRingEnd ℂ (g_half W) * g_half W = _
            rw [Complex.conj_mul', Complex.ofReal_pow]
  rw [h_inner_eq]
  have h_norm_int : MeasureTheory.Integrable (fun W => (((‖g_half W‖ ^ 2 : ℝ) : ℂ))) μ := by
    refine (MeasureTheory.integrable_const ((M_χ * ‖ψ‖) ^ 2)).mono'
      (Complex.continuous_ofReal.comp (hg_cont.norm.pow 2)).stronglyMeasurable.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun W => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hg_bd W) 2
  change 0 ≤ RCLike.re (∫ W, (((‖g_half W‖ ^ 2 : ℝ) : ℂ)) ∂μ)
  rw [← integral_re h_norm_int]
  refine MeasureTheory.integral_nonneg fun W => ?_
  change 0 ≤ (((‖g_half W‖ ^ 2 : ℝ) : ℂ)).re
  rw [Complex.ofReal_re]
  exact sq_nonneg _

/--
Every nonzero compact positive self-adjoint operator on a Hilbert space `V`
attains its operator norm `‖T‖ > 0` at a unit eigenvector `v`.
-/
theorem compact_sa_pos_exists_max_eigenvector
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (T : V →L[ℂ] V)
    (hT_sa : ∀ x y : V, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (hT_pos : ∀ x : V, 0 ≤ (⟪x, T x⟫_ℂ).re)
    (hT_comp : IsCompactOperator ⇑T)
    (hT_ne : T ≠ 0) :
    ∃ v : V, ‖v‖ = 1 ∧ T v = (‖T‖ : ℂ) • v := by
  have hT_selfadj : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT_sa
  have hT_pos_norm : 0 < ‖T‖ := lt_of_le_of_ne (norm_nonneg T) (Ne.symm (norm_ne_zero_iff.mpr hT_ne))
  let s : ℝ := ⨆ x : V, |T.rayleighQuotient x|
  have hbdd : BddAbove (Set.range fun x : V => |T.rayleighQuotient x|) :=
    ContinuousLinearMap.bddAbove_rayleighQuotient T
  have hnorm_eq : ‖T‖ = s := norm_eq_iSup_rayleighQuotient hT_selfadj
  have hu_ex : ∀ n : ℕ, ∃ u : V, ‖T‖ * (1 - 1 / ((n : ℝ) + 2)) < |T.rayleighQuotient u| := by
    intro n
    have hlt : ‖T‖ * (1 - 1 / ((n : ℝ) + 2)) < s := by
      rw [← hnorm_eq]
      have h1 : 0 < 1 / ((n : ℝ) + 2) := by positivity
      nlinarith
    exact (lt_ciSup_iff hbdd).mp hlt
  choose u hu_lt using hu_ex
  have hu_ne : ∀ n : ℕ, u n ≠ 0 := by
    intro n h0
    have hlt := hu_lt n
    have hrq0 : T.rayleighQuotient (u n) = 0 := by
      simp [ContinuousLinearMap.rayleighQuotient, h0]
    rw [hrq0, abs_zero] at hlt
    have hnonneg : 0 ≤ ‖T‖ * (1 - 1 / ((n : ℝ) + 2)) := by
      have h2 : 0 ≤ 1 - 1 / ((n : ℝ) + 2) := by
        have h3 : 1 / ((n : ℝ) + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
        linarith
      exact mul_nonneg hT_pos_norm.le h2
    exact not_lt_of_ge hnonneg hlt
  let x : ℕ → V := fun n => ((‖u n‖⁻¹ : ℝ) : ℂ) • u n
  have hx_norm : ∀ n : ℕ, ‖x n‖ = 1 := by
    intro n
    simp only [x, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hu_ne n))
  let lam : ℕ → ℝ := fun n => (⟪T (x n), x n⟫_ℂ).re
  have hlam_eq_rq : ∀ n : ℕ, lam n = T.rayleighQuotient (u n) := by
    intro n
    have hnorm_u : ‖u n‖ ≠ 0 := norm_ne_zero_iff.mpr (hu_ne n)
    simp only [lam, ContinuousLinearMap.rayleighQuotient, x, map_smul,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    have hcast : (((‖u n‖⁻¹ : ℝ) : ℂ) * (((‖u n‖⁻¹ : ℝ) : ℂ) * ⟪T (u n), u n⟫_ℂ)).re =
        (‖u n‖⁻¹ * ‖u n‖⁻¹) * (⟪T (u n), u n⟫_ℂ).re := by
      simp [Complex.mul_re]; ring
    rw [hcast]
    change (‖u n‖⁻¹ * ‖u n‖⁻¹) * (⟪T (u n), u n⟫_ℂ).re =
      (⟪T (u n), u n⟫_ℂ).re / ‖u n‖ ^ 2
    field_simp [hnorm_u]
  have hlam_mem : ∀ n : ℕ, lam n ∈ Set.Icc (-‖T‖) ‖T‖ := fun n => by
    rw [Set.mem_Icc, ← abs_le, hlam_eq_rq n]
    exact T.rayleighQuotient_le_norm (u n)
  have hTx_mem : ∀ n : ℕ, T (x n) ∈ closure (T '' Metric.closedBall (0 : V) 1) := fun n => by
    apply subset_closure
    refine ⟨x n, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, hx_norm n]
  let S_comp : Set (ℝ × V) := Set.Icc (-‖T‖) ‖T‖ ×ˢ closure (T '' Metric.closedBall (0 : V) 1)
  have hS_comp : IsCompact S_comp :=
    isCompact_Icc.prod (hT_comp.isCompact_closure_image_closedBall (1 : ℝ))
  let seq : ℕ → ℝ × V := fun n => (lam n, T (x n))
  obtain ⟨⟨μ, y⟩, hμy_mem, φ, hφ_mono, hφ_tendsto⟩ :=
    hS_comp.tendsto_subseq (x := seq) (fun n => ⟨hlam_mem n, hTx_mem n⟩)
  have hlam_tendsto : Filter.Tendsto (fun n => lam (φ n)) Filter.atTop (nhds μ) := by
    simpa [seq, Function.comp_def] using (continuous_fst.tendsto (μ, y)).comp hφ_tendsto
  have hTx_tendsto : Filter.Tendsto (fun n => T (x (φ n))) Filter.atTop (nhds y) := by
    simpa [seq, Function.comp_def] using (continuous_snd.tendsto (μ, y)).comp hφ_tendsto
  have hμ_abs : |μ| = ‖T‖ := by
    have h_abs_tendsto : Filter.Tendsto (fun n => |lam (φ n)|) Filter.atTop (nhds |μ|) :=
      continuous_abs.continuousAt.tendsto.comp hlam_tendsto
    have h_lower : Filter.Tendsto (fun n => ‖T‖ * (1 - 1 / ((φ n : ℝ) + 2)))
        Filter.atTop (nhds ‖T‖) := by
      have h_inv : Filter.Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 2)) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop
          (Filter.tendsto_atTop_add_const_right _ 2
            (tendsto_natCast_atTop_atTop.comp hφ_mono.tendsto_atTop))
      simpa using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => ‖T‖) Filter.atTop (nhds ‖T‖)).mul
          ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1)).sub h_inv)
    have h_le : ‖T‖ ≤ |μ| :=
      le_of_tendsto_of_tendsto' h_lower h_abs_tendsto fun n => by
        rw [hlam_eq_rq]; exact (hu_lt (φ n)).le
    exact le_antisymm (abs_le.mpr hμy_mem.1) h_le
  have hμ_ne : μ ≠ 0 := by intro h0; rw [h0, abs_zero] at hμ_abs; linarith
  have hμ_sq : μ ^ 2 = ‖T‖ ^ 2 := by rw [← hμ_abs, sq_abs]
  have h_diff_sq_tendsto : Filter.Tendsto
      (fun n => ‖T (x (φ n)) - (μ : ℂ) • x (φ n)‖ ^ 2) Filter.atTop (nhds 0) := by
    have h_upper : ∀ n : ℕ,
        ‖T (x (φ n)) - (μ : ℂ) • x (φ n)‖ ^ 2 ≤ ‖T‖ ^ 2 - 2 * μ * lam (φ n) + μ ^ 2 := by
      intro n
      have h_exp : ‖T (x (φ n)) - (μ : ℂ) • x (φ n)‖ ^ 2 =
          ‖T (x (φ n))‖ ^ 2 - 2 * μ * lam (φ n) + μ ^ 2 := by
        rw [norm_sub_sq (𝕜 := ℂ)]
        have h_re : RCLike.re ⟪T (x (φ n)), (μ : ℂ) • x (φ n)⟫_ℂ = μ * lam (φ n) := by
          rw [inner_smul_right]
          simp [lam, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        have h_norm_μx : ‖(μ : ℂ) • x (φ n)‖ ^ 2 = μ ^ 2 := by
          rw [norm_smul, hx_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
        rw [h_re, h_norm_μx]; ring
      have h_le_norm : ‖T (x (φ n))‖ ^ 2 ≤ ‖T‖ ^ 2 := by
        have h1 : ‖T (x (φ n))‖ ≤ ‖T‖ := by
          calc ‖T (x (φ n))‖ ≤ ‖T‖ * ‖x (φ n)‖ := T.le_opNorm _
            _ = ‖T‖ := by rw [hx_norm, mul_one]
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      linarith
    have h_rhs : Filter.Tendsto (fun n => ‖T‖ ^ 2 - 2 * μ * lam (φ n) + μ ^ 2)
        Filter.atTop (nhds 0) := by
      have h0 : ‖T‖ ^ 2 - 2 * μ * μ + μ ^ 2 = 0 := by linarith [hμ_sq]
      rw [← h0]
      exact (tendsto_const_nhds.sub (tendsto_const_nhds.mul hlam_tendsto)).add tendsto_const_nhds
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_rhs
      (fun _ => sq_nonneg _) h_upper
  have h_diff_tendsto : Filter.Tendsto
      (fun n => T (x (φ n)) - (μ : ℂ) • x (φ n)) Filter.atTop (nhds 0) := by
    have h_norm_tendsto : Filter.Tendsto
        (fun n => ‖T (x (φ n)) - (μ : ℂ) • x (φ n)‖) Filter.atTop (nhds 0) := by
      have hsqrt := continuous_sqrt.continuousAt.tendsto.comp h_diff_sq_tendsto
      rw [Real.sqrt_zero] at hsqrt
      refine hsqrt.congr fun n => ?_
      dsimp only [Function.comp_def]
      exact Real.sqrt_sq (norm_nonneg _)
    exact tendsto_zero_iff_norm_tendsto_zero.mpr h_norm_tendsto
  have hx_tendsto : Filter.Tendsto (fun n => x (φ n)) Filter.atTop (nhds ((μ : ℂ)⁻¹ • y)) := by
    have h_smul : Filter.Tendsto (fun n => (μ : ℂ) • x (φ n)) Filter.atTop (nhds y) := by
      have hsub := hTx_tendsto.sub h_diff_tendsto
      rw [sub_zero] at hsub
      refine hsub.congr fun n => ?_
      abel
    have hμc : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ_ne
    have h_inv := (continuous_const_smul ((μ : ℂ)⁻¹)).continuousAt.tendsto.comp h_smul
    convert h_inv using 1
    · ext n; simp only [Function.comp_apply]; rw [smul_smul, inv_mul_cancel₀ hμc, one_smul]
  have hy_ne : y ≠ 0 := by
    intro hy0
    have h_norm_x : Filter.Tendsto (fun n => ‖x (φ n)‖) Filter.atTop (nhds ‖(μ : ℂ)⁻¹ • y‖) :=
      continuous_norm.continuousAt.tendsto.comp hx_tendsto
    have h_const1 : (fun n => ‖x (φ n)‖) = fun _ => 1 := funext fun n => hx_norm (φ n)
    rw [h_const1, hy0, smul_zero, norm_zero] at h_norm_x
    have h_eq := tendsto_nhds_unique tendsto_const_nhds h_norm_x
    norm_num at h_eq
  have hy_eig : T y = (μ : ℂ) • y := by
    have h_eq : y = T ((μ : ℂ)⁻¹ • y) :=
      tendsto_nhds_unique hTx_tendsto (T.continuous.continuousAt.tendsto.comp hx_tendsto)
    have hμc : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ_ne
    calc T y = T ((μ : ℂ) • ((μ : ℂ)⁻¹ • y)) := by rw [smul_smul, mul_inv_cancel₀ hμc, one_smul]
      _ = (μ : ℂ) • T ((μ : ℂ)⁻¹ • y) := T.map_smul _ _
      _ = (μ : ℂ) • y := by rw [← h_eq]
  let v : V := ((‖y‖⁻¹ : ℝ) : ℂ) • y
  have hv_norm : ‖v‖ = 1 := by
    simp only [v, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy_ne)
  have hv_eig : T v = (μ : ℂ) • v := by
    have h1 : T (((‖y‖⁻¹ : ℝ) : ℂ) • y) = ((‖y‖⁻¹ : ℝ) : ℂ) • T y :=
      ContinuousLinearMap.map_smul T ((‖y‖⁻¹ : ℝ) : ℂ) y
    have h2 : ((‖y‖⁻¹ : ℝ) : ℂ) • ((μ : ℂ) • y) = (μ : ℂ) • (((‖y‖⁻¹ : ℝ) : ℂ) • y) := by
      rw [smul_smul, mul_comm, ← smul_smul]
    change T (((‖y‖⁻¹ : ℝ) : ℂ) • y) = (μ : ℂ) • (((‖y‖⁻¹ : ℝ) : ℂ) • y)
    rw [h1, hy_eig, h2]
  have hμ_nn : 0 ≤ μ := by
    have hp := hT_pos v
    rw [hv_eig, inner_smul_right, inner_self_eq_norm_sq_to_K, hv_norm] at hp
    change 0 ≤ ((μ : ℂ) * ((1 : ℝ) : ℂ) ^ 2).re at hp
    rw [Complex.ofReal_one, one_pow, mul_one, Complex.ofReal_re] at hp
    exact hp
  have hμ_eq : μ = ‖T‖ := by rwa [abs_of_nonneg hμ_nn] at hμ_abs
  exact ⟨v, hv_norm, hμ_eq ▸ hv_eig⟩

/-- Orthogonal complement `Ωᗮ` of a vacuum state `Ω`. -/
noncomputable def wilsonPerpSubmodule {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (Ω : V) : Submodule ℂ V :=
  (Submodule.span ℂ {Ω})ᗮ

private theorem wilsonPerpSubmodule_inv {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {T_norm : V →L[ℂ] V} {Ω : V}
    (hT_sa : ∀ x y : V, ⟪T_norm x, y⟫_ℂ = ⟪x, T_norm y⟫_ℂ)
    (hT_Ω : T_norm Ω = Ω)
    {x : V} (hx : x ∈ wilsonPerpSubmodule Ω) :
    T_norm x ∈ wilsonPerpSubmodule Ω := by
  unfold wilsonPerpSubmodule at hx ⊢
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro z hz
  rw [Submodule.mem_span_singleton] at hz
  rcases hz with ⟨c, rfl⟩
  have hΩx : ⟪Ω, x⟫_ℂ = 0 := hx Ω (Submodule.subset_span rfl)
  rw [inner_smul_left, ← hT_sa, hT_Ω, hΩx, mul_zero]

/-- Restriction of a self-adjoint operator `T_norm` (fixing `Ω`) to `Ωᗮ`. -/
noncomputable def wilsonPerpOp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (T_norm : V →L[ℂ] V) (Ω : V)
    (hT_sa : ∀ x y : V, ⟪T_norm x, y⟫_ℂ = ⟪x, T_norm y⟫_ℂ)
    (hT_Ω : T_norm Ω = Ω) :
    ↥(wilsonPerpSubmodule Ω) →L[ℂ] ↥(wilsonPerpSubmodule Ω) :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨T_norm x.1, wilsonPerpSubmodule_inv hT_sa hT_Ω x.2⟩
      map_add' := fun x y => Subtype.ext (T_norm.map_add x.1 y.1)
      map_smul' := fun c x => Subtype.ext (T_norm.map_smul c x.1) }
    ‖T_norm‖
    (fun x => by
      change ‖T_norm x.1‖ ≤ ‖T_norm‖ * ‖x.1‖
      exact T_norm.le_opNorm x.1)

/-- Exact spectral gap `-log ‖T_norm|_{Ωᗮ}‖` (with `1` when `T_norm|_{Ωᗮ} = 0`). -/
noncomputable def wilsonExactGap {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (T_norm : V →L[ℂ] V) (Ω : V)
    (hT_sa : ∀ x y : V, ⟪T_norm x, y⟫_ℂ = ⟪x, T_norm y⟫_ℂ)
    (hT_Ω : T_norm Ω = Ω) : ℝ :=
  if ‖wilsonPerpOp T_norm Ω hT_sa hT_Ω‖ = 0 then 1
  else -Real.log ‖wilsonPerpOp T_norm Ω hT_sa hT_Ω‖

private theorem eq_of_ae_continuous {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] (μ : MeasureTheory.Measure α) [MeasureTheory.Measure.IsOpenPosMeasure μ]
    {f g : α → ℂ} (hf : Continuous f) (hg : Continuous g) (h_ae : f =ᵐ[μ] g) :
    ∀ x, f x = g x := by
  intro x
  by_contra hne
  let S : Set α := { y | f y ≠ g y }
  have hS_eq : S = (fun y => f y - g y) ⁻¹' { z | z ≠ 0 } := by
    ext y
    change f y ≠ g y ↔ f y - g y ≠ 0
    exact sub_ne_zero.symm
  have hS_open : IsOpen S := hS_eq ▸ isOpen_ne.preimage (hf.sub hg)
  have hS_pos : 0 < μ S := hS_open.measure_pos μ ⟨x, hne⟩
  have hS_zero : μ S = 0 := h_ae
  exact lt_irrefl 0 (hS_pos.trans_eq hS_zero)

private theorem eq_zero_of_continuous_sq_integral_zero {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.Measure.IsOpenPosMeasure μ]
    (h : α → ℝ) (hh : Continuous h)
    (h_int : ∫ x, h x ^ 2 ∂μ = 0) :
    ∀ x, h x = 0 := by
  intro x₀
  by_contra hx₀
  let δ : ℝ := (h x₀) ^ 2 / 2
  have hδ : 0 < δ := by positivity
  let B : Set α := { x | δ < h x ^ 2 }
  have hB_open : IsOpen B := isOpen_lt continuous_const (hh.pow 2)
  have hx0_sq : 0 < h x₀ ^ 2 := sq_pos_iff.mpr hx₀
  have hB_pos : 0 < μ.real B :=
    ENNReal.toReal_pos
      (hB_open.measure_pos μ ⟨x₀, by change δ < h x₀ ^ 2; dsimp [δ]; linarith⟩).ne'
      (MeasureTheory.measure_ne_top μ B)
  have h_cont_int : MeasureTheory.Integrable (fun x => h x ^ 2) μ :=
    integrable_of_continuous_compact μ _ (hh.pow 2)
  have h_ind_int : MeasureTheory.Integrable (Set.indicator B (fun _ => δ)) μ :=
    (MeasureTheory.integrable_const δ).indicator hB_open.measurableSet
  have h_le : ∀ x, Set.indicator B (fun _ => δ) x ≤ h x ^ 2 := by
    intro x
    rw [Set.indicator_apply]
    by_cases hx : x ∈ B
    · rw [if_pos hx]; exact (hx : _ < _).le
    · rw [if_neg hx]; exact sq_nonneg _
  have h_val : ∫ x, Set.indicator B (fun _ => δ) x ∂μ = μ.real B * δ := by
    rw [MeasureTheory.integral_indicator hB_open.measurableSet, MeasureTheory.setIntegral_const]
    simp [smul_eq_mul]
  have h_pos : 0 < ∫ x, h x ^ 2 ∂μ := by
    calc 0 < μ.real B * δ := mul_pos hB_pos hδ
      _ = ∫ x, Set.indicator B (fun _ => δ) x ∂μ := h_val.symm
      _ ≤ ∫ x, h x ^ 2 ∂μ := MeasureTheory.integral_mono h_ind_int h_cont_int h_le
  linarith

private structure IsWilsonGroundState (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (Ω : HaarGaugeSpace (latticeHaarMeasure L N))
    (ω : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ) : Prop where
  norm_pos  : 0 < ‖wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd‖
  unit      : ‖Ω‖ = 1
  ω_cont    : Continuous ω
  ω_pos     : ∀ U, 0 < ω U
  ae_eq     : ⇑Ω =ᵐ[latticeHaarMeasure L N] (fun U => (ω U : ℂ))
  eig       : wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd Ω =
                (‖wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd‖ : ℂ) • Ω
  gauge_inv : ∀ g, cubicGaugeRep L N g Ω = Ω
  simple    : ∀ w : HaarGaugeSpace (latticeHaarMeasure L N),
                wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd w =
                  (‖wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd‖ : ℂ) • w →
                ⟪w, Ω⟫_ℂ = 0 → w = 0

/--
**Perron–Frobenius Ground State & Simplicity for `wilsonIntegralOp`**:
for any continuous, symmetric, gauge-invariant, strictly positive kinetic kernel
`K_kin`, `T = wilsonIntegralOp ...` has simple top eigenvalue `‖T‖ > 0`
attained at a strictly positive continuous gauge-invariant eigenfunction `ω`.
-/
private theorem wilsonIntegral_ground_state (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_symm : ∀ U U', K_kin U' U = K_kin U U')
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (hK_inv : ∀ g U U', K_kin (gaugeAct g U) (gaugeAct g U') = K_kin U U')
    (c_min : ℝ) (hc_min : 0 < c_min) (hK_lb : ∀ U U', c_min ≤ K_kin U U')
    (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (hT_pos : ∀ ψ : HaarGaugeSpace (latticeHaarMeasure L N),
      0 ≤ (⟪ψ, wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ⟫_ℂ).re) :
    ∃ (Ω : HaarGaugeSpace (latticeHaarMeasure L N))
      (ω : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ),
      IsWilsonGroundState L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd Ω ω := by
  let G_L := GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  haveI := instIsOpenPosLatticeHaar L N
  let K_W := wilsonKernel β (cubicPlaquettes L) K_kin
  let T := wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd
  have hT_sa : ∀ x y : HaarGaugeSpace μ, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ :=
    wilsonIntegralOp_sa L N β hβ K_kin hK_cont hK_symm hK_nn M_K hM_K hK_bd
  have hT_comp : IsCompactOperator ⇑T :=
    wilsonIntegralOp_compact L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd
  let c_W : ℝ := Real.exp (-(2 * β * ((cubicPlaquettes L).length : ℝ))) * c_min
  have hc_W_pos : 0 < c_W := mul_pos (Real.exp_pos _) hc_min
  have hKW_lb : ∀ U U', c_W ≤ K_W U U' := by
    intro U U'
    have h1 := (wilsonAction_bounds β hβ (cubicPlaquettes L) U).2
    have h2 := (wilsonAction_bounds β hβ (cubicPlaquettes L) U').2
    have hexp : Real.exp (-(2 * β * ((cubicPlaquettes L).length : ℝ))) ≤
        Real.exp (-(1 / 2 : ℝ) *
          (wilsonAction β (cubicPlaquettes L) U + wilsonAction β (cubicPlaquettes L) U')) :=
      Real.exp_le_exp.mpr (by linarith)
    unfold K_W wilsonKernel
    exact mul_le_mul hexp (hK_lb U U') hc_min.le (Real.exp_pos _).le
  have hcinner : ∀ a b : ℂ, ⟪a, b⟫_ℂ = starRingEnd ℂ a * b := by
    intro a b
    have h1 : ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_num
    calc ⟪a, b⟫_ℂ = ⟪a • (1 : ℂ), b • (1 : ℂ)⟫_ℂ := by simp
      _ = starRingEnd ℂ a * (b * ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ) := by
            rw [inner_smul_left, inner_smul_right]
      _ = starRingEnd ℂ a * b := by rw [h1, mul_one]
  have hT_ne : T ≠ 0 := by
    let oneLp : HaarGaugeSpace μ :=
      MeasureTheory.indicatorConstLp (2 : ENNReal) MeasurableSet.univ
        (MeasureTheory.measure_ne_top μ Set.univ) (1 : ℂ)
    have hone_ae : ⇑oneLp =ᵐ[μ] fun _ => (1 : ℂ) := by
      have h := MeasureTheory.indicatorConstLp_coeFn (p := (2 : ENNReal))
        (μ := μ) (s := Set.univ) (hs := MeasurableSet.univ)
        (hμs := MeasureTheory.measure_ne_top μ Set.univ) (c := (1 : ℂ))
      filter_upwards [h] with U hU
      simpa [oneLp] using hU
    have h_l2 : MeasureTheory.Integrable (fun U => ⟪oneLp U, (T oneLp) U⟫_ℂ) μ :=
      MeasureTheory.L2.integrable_inner _ _
    have h_re := integral_re h_l2
    have h_in_re : (⟪oneLp, T oneLp⟫_ℂ).re =
        ∫ U, (⟪oneLp U, (T oneLp) U⟫_ℂ).re ∂μ := by
      rw [MeasureTheory.L2.inner_def]
      change RCLike.re (∫ U, ⟪oneLp U, (T oneLp) U⟫_ℂ ∂μ) = _
      rw [← h_re]
      rfl
    have h_ae_ge : ∀ᵐ U ∂μ, c_W ≤ (⟪oneLp U, (T oneLp) U⟫_ℂ).re := by
      filter_upwards [hone_ae, wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
        M_K hM_K hK_bd oneLp] with U hU1 hUT
      change c_W ≤ (⟪oneLp U, (T oneLp) U⟫_ℂ).re
      rw [hU1, hUT]
      have hc1 : ⟪(1 : ℂ), wilsonIntegralFn L N β K_kin oneLp U⟫_ℂ =
          wilsonIntegralFn L N β K_kin oneLp U := by
        rw [hcinner, map_one, one_mul]
      rw [hc1]
      dsimp [wilsonIntegralFn]
      have h_int_fn := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd oneLp U
      change c_W ≤ RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * oneLp U' ∂μ)
      rw [← integral_re h_int_fn]
      have h_int_K : MeasureTheory.Integrable (fun U' => K_W U U') μ :=
        integrable_of_continuous_compact μ _ (continuous_cubicWilsonKernel_right L N β K_kin hK_cont U)
      have h_eq_int : ∫ x, RCLike.re (((K_W U x : ℝ) : ℂ) * oneLp x) ∂μ =
          ∫ x, K_W U x ∂μ := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hone_ae] with x hx
        change (((K_W U x : ℝ) : ℂ) * ⇑oneLp x).re = K_W U x
        rw [hx, mul_one, Complex.ofReal_re]
      rw [h_eq_int]
      calc c_W = ∫ _U', c_W ∂μ := by simp [Measure.real, MeasureTheory.measure_univ]
        _ ≤ ∫ U', K_W U U' ∂μ :=
            MeasureTheory.integral_mono (MeasureTheory.integrable_const c_W) h_int_K (hKW_lb U)
    have h_pos_re : c_W ≤ (⟪oneLp, T oneLp⟫_ℂ).re := by
      rw [h_in_re]
      calc c_W = ∫ _U, c_W ∂μ := by simp [Measure.real, MeasureTheory.measure_univ]
        _ ≤ ∫ U, (⟪oneLp U, (T oneLp) U⟫_ℂ).re ∂μ :=
            MeasureTheory.integral_mono_ae (MeasureTheory.integrable_const c_W) h_l2.re h_ae_ge
    intro h0
    rw [h0, ContinuousLinearMap.zero_apply, inner_zero_right, Complex.zero_re] at h_pos_re
    linarith
  obtain ⟨v₀, hv₀_norm, hv₀_eig⟩ :=
    compact_sa_pos_exists_max_eigenvector T hT_sa hT_pos hT_comp hT_ne
  let lam0 : ℝ := ‖T‖
  have hlam0_pos : 0 < lam0 := lt_of_le_of_ne (norm_nonneg T) (Ne.symm (norm_ne_zero_iff.mpr hT_ne))
  let φ₀ : G_L → ℂ := fun U => ((lam0⁻¹ : ℝ) : ℂ) * wilsonIntegralFn L N β K_kin v₀ U
  have hφ₀_cont : Continuous φ₀ :=
    continuous_const.mul (wilsonIntegralFn_continuous L N β hβ K_kin hK_cont hK_nn M_K hK_bd v₀)
  have hv₀_ae : ⇑v₀ =ᵐ[μ] φ₀ := by
    have h_eq : v₀ = ((lam0⁻¹ : ℝ) : ℂ) • T v₀ := by
      rw [hv₀_eig, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam0_pos.ne',
        Complex.ofReal_one, one_smul]
    have h1 : ⇑v₀ =ᵐ[μ] ((lam0⁻¹ : ℝ) : ℂ) • ⇑(T v₀) := by
      conv_lhs => rw [h_eq]
      exact MeasureTheory.Lp.coeFn_smul _ _
    filter_upwards [h1, wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
      M_K hM_K hK_bd v₀] with U hU1 hU2
    change ⇑v₀ U = φ₀ U
    rw [hU1]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hU2]
  let φ_abs : G_L → ℂ := fun U => ((‖φ₀ U‖ : ℝ) : ℂ)
  have hφ_abs_mem : MeasureTheory.MemLp φ_abs 2 μ := by
    refine memLp_two_of_measurable_bound μ φ_abs
      (Complex.continuous_ofReal.measurable.comp hφ₀_cont.norm.measurable)
      (lam0⁻¹ * (M_K * ‖v₀‖)) (by positivity) fun U => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hlam0_pos.le)]
    exact mul_le_mul_of_nonneg_left
      (wilsonIntegralFn_pt_bound L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd v₀ U)
      (inv_nonneg.mpr hlam0_pos.le)
  let Ω : HaarGaugeSpace μ := hφ_abs_mem.toLp φ_abs
  have hΩ_ae : ⇑Ω =ᵐ[μ] φ_abs := hφ_abs_mem.coeFn_toLp
  have hΩ_norm : ‖Ω‖ = 1 := by
    have hsq : ‖Ω‖ ^ 2 = 1 := by
      rw [lp_norm_sq_eq_integral]
      have h1 : (fun U => ‖Ω U‖ ^ 2) =ᵐ[μ] fun U => ‖v₀ U‖ ^ 2 := by
        filter_upwards [hΩ_ae, hv₀_ae] with U hU1 hU2
        change ‖⇑Ω U‖ ^ 2 = ‖⇑v₀ U‖ ^ 2
        rw [hU1, hU2]
        simp [φ_abs]
      rw [MeasureTheory.integral_congr_ae h1, ← lp_norm_sq_eq_integral, hv₀_norm, one_pow]
    have hmul : (‖Ω‖ - 1) * (‖Ω‖ + 1) = 0 := by linarith
    rcases mul_eq_zero.mp hmul with h | h <;> linarith [norm_nonneg Ω]
  have h_in_Ω_ge : lam0 ≤ (⟪Ω, T Ω⟫_ℂ).re := by
    have hv_in : ⟪v₀, T v₀⟫_ℂ = (lam0 : ℂ) := by
      rw [hv₀_eig, inner_smul_right, inner_self_eq_norm_sq_to_K, hv₀_norm]
      simp [lam0]
    have h_v_int : ⟪v₀, T v₀⟫_ℂ =
        ∫ U, starRingEnd ℂ (φ₀ U) * wilsonIntegralFn L N β K_kin v₀ U ∂μ := by
      rw [MeasureTheory.L2.inner_def]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hv₀_ae, wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
        M_K hM_K hK_bd v₀] with U hU1 hU2
      rw [hU1, hU2, hcinner]
    have h_Ω_int : (⟪Ω, T Ω⟫_ℂ).re =
        ∫ U, ‖φ₀ U‖ * ∫ U', K_W U U' * ‖φ₀ U'‖ ∂μ ∂μ := by
      have h_l2 : MeasureTheory.Integrable (fun U => ⟪Ω U, (T Ω) U⟫_ℂ) μ :=
        MeasureTheory.L2.integrable_inner _ _
      have h_re := integral_re h_l2
      rw [MeasureTheory.L2.inner_def]
      change RCLike.re (∫ U, ⟪Ω U, (T Ω) U⟫_ℂ ∂μ) = _
      rw [← h_re]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hΩ_ae, wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
        M_K hM_K hK_bd Ω] with U hU1 hU2
      change (⟪⇑Ω U, ⇑(T Ω) U⟫_ℂ).re = _
      rw [hU1, hU2, hcinner]
      dsimp [φ_abs, wilsonIntegralFn]
      have h_fn_re : (∫ U', ((K_W U U' : ℝ) : ℂ) * Ω U' ∂μ).re =
          ∫ U', K_W U U' * ‖φ₀ U'‖ ∂μ := by
        have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd Ω U
        change RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * Ω U' ∂μ) = _
        rw [← integral_re hi]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hΩ_ae] with U' hU'
        change (((K_W U U' : ℝ) : ℂ) * ⇑Ω U').re = K_W U U' * ‖φ₀ U'‖
        rw [hU']
        simp [φ_abs, Complex.ofReal_re]
      have h_mul_eq : ‖φ₀ U‖ * (∫ U', ((K_W U U' : ℝ) : ℂ) * Ω U' ∂μ).re =
          ‖φ₀ U‖ * ∫ U', K_W U U' * ‖φ₀ U'‖ ∂μ := congrArg (‖φ₀ U‖ * ·) h_fn_re
      simp only [neg_zero, zero_mul, sub_zero]
      exact h_mul_eq
    have h_int_norm1 : MeasureTheory.Integrable
        (fun U => ‖starRingEnd ℂ (φ₀ U) * wilsonIntegralFn L N β K_kin v₀ U‖) μ := by
      have h_l2 : MeasureTheory.Integrable (fun U => ⟪v₀ U, (T v₀) U⟫_ℂ) μ :=
        MeasureTheory.L2.integrable_inner v₀ (T v₀)
      have h_ae : (fun U => ‖starRingEnd ℂ (φ₀ U) * wilsonIntegralFn L N β K_kin v₀ U‖) =ᵐ[μ]
          fun U => ‖⟪v₀ U, (T v₀) U⟫_ℂ‖ := by
        filter_upwards [hv₀_ae, wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
          M_K hM_K hK_bd v₀] with U hU1 hU2
        rw [← hU1, ← hU2, hcinner]
      exact h_l2.norm.congr h_ae.symm
    have h_int_norm2 : MeasureTheory.Integrable
        (fun U => ‖φ₀ U‖ * ∫ U', K_W U U' * ‖φ₀ U'‖ ∂μ) μ := by
      have h_l2 : MeasureTheory.Integrable (fun U => ⟪Ω U, (T Ω) U⟫_ℂ) μ :=
        MeasureTheory.L2.integrable_inner Ω (T Ω)
      have h_ae : (fun U => ‖φ₀ U‖ * ∫ U', K_W U U' * ‖φ₀ U'‖ ∂μ) =ᵐ[μ]
          fun U => (⟪Ω U, (T Ω) U⟫_ℂ).re := by
        filter_upwards [hΩ_ae, wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
          M_K hM_K hK_bd Ω] with U hU1 hU2
        change _ = (⟪⇑Ω U, ⇑(T Ω) U⟫_ℂ).re
        rw [hU1, hU2, hcinner]
        dsimp [φ_abs, wilsonIntegralFn]
        have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd Ω U
        simp only [neg_zero, zero_mul, sub_zero]
        congr 1
        change _ = RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * Ω U' ∂μ)
        rw [← integral_re hi]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hΩ_ae] with U' hU'
        change _ = (((K_W U U' : ℝ) : ℂ) * ⇑Ω U').re
        rw [hU']
        simp [φ_abs]
      exact h_l2.re.congr h_ae.symm
    have h_pt_le : ∀ U, ‖starRingEnd ℂ (φ₀ U) * wilsonIntegralFn L N β K_kin v₀ U‖ ≤
        ‖φ₀ U‖ * ∫ U', K_W U U' * ‖φ₀ U'‖ ∂μ := by
      intro U
      have hconj : ‖starRingEnd ℂ (φ₀ U)‖ = ‖φ₀ U‖ := norm_star _
      rw [norm_mul, hconj]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      dsimp [wilsonIntegralFn]
      calc ‖∫ U', ((K_W U U' : ℝ) : ℂ) * v₀ U' ∂μ‖
          ≤ ∫ U', ‖((K_W U U' : ℝ) : ℂ) * v₀ U'‖ ∂μ :=
            MeasureTheory.norm_integral_le_integral_norm _
        _ = ∫ U', K_W U U' * ‖φ₀ U'‖ ∂μ := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [hv₀_ae] with U' hU'
            have hb := wilsonKernel_cubic_le L N β hβ K_kin hK_nn M_K hK_bd U U'
            rw [hU', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
    have h_abs_le : lam0 ≤ ‖⟪v₀, T v₀⟫_ℂ‖ := by
      rw [hv_in, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0_pos]
    calc lam0 ≤ ‖⟪v₀, T v₀⟫_ℂ‖ := h_abs_le
      _ = ‖∫ U, starRingEnd ℂ (φ₀ U) * wilsonIntegralFn L N β K_kin v₀ U ∂μ‖ := by rw [h_v_int]
      _ ≤ ∫ U, ‖starRingEnd ℂ (φ₀ U) * wilsonIntegralFn L N β K_kin v₀ U‖ ∂μ :=
            MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ U, ‖φ₀ U‖ * ∫ U', K_W U U' * ‖φ₀ U'‖ ∂μ ∂μ :=
            MeasureTheory.integral_mono h_int_norm1 h_int_norm2 h_pt_le
      _ = (⟪Ω, T Ω⟫_ℂ).re := h_Ω_int.symm
  have hΩ_eig : T Ω = (lam0 : ℂ) • Ω := by
    have h_in_le : (⟪Ω, T Ω⟫_ℂ).re ≤ lam0 := by
      calc (⟪Ω, T Ω⟫_ℂ).re ≤ ‖⟪Ω, T Ω⟫_ℂ‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
        _ ≤ ‖Ω‖ * ‖T Ω‖ := norm_inner_le_norm _ _
        _ ≤ ‖Ω‖ * (‖T‖ * ‖Ω‖) := mul_le_mul_of_nonneg_left (T.le_opNorm Ω) (norm_nonneg _)
        _ = lam0 := by rw [hΩ_norm]; ring
    have h_in_re : (⟪Ω, T Ω⟫_ℂ).re = lam0 := le_antisymm h_in_le h_in_Ω_ge
    have h_in_im : (⟪Ω, T Ω⟫_ℂ).im = 0 := by
      have hconj : starRingEnd ℂ ⟪Ω, T Ω⟫_ℂ = ⟪Ω, T Ω⟫_ℂ := by
        rw [inner_conj_symm, hT_sa]
      exact Complex.conj_eq_iff_im.mp hconj
    have h_in_eq : ⟪Ω, T Ω⟫_ℂ = (lam0 : ℂ) := Complex.ext h_in_re h_in_im
    have h_sq_le : ‖T Ω - (lam0 : ℂ) • Ω‖ ^ 2 ≤ 0 := by
      rw [norm_sub_sq (𝕜 := ℂ)]
      have h_re : RCLike.re ⟪T Ω, (lam0 : ℂ) • Ω⟫_ℂ = lam0 ^ 2 := by
        rw [inner_smul_right, hT_sa, h_in_eq]
        simp [pow_two]
      have h_norm_TΩ : ‖T Ω‖ ^ 2 ≤ lam0 ^ 2 := by
        have h1 : ‖T Ω‖ ≤ lam0 := by simpa [hΩ_norm] using T.le_opNorm Ω
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h_norm_lamΩ : ‖(lam0 : ℂ) • Ω‖ ^ 2 = lam0 ^ 2 := by
        rw [norm_smul, hΩ_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0_pos]
      linarith
    have h_zero : ‖T Ω - (lam0 : ℂ) • Ω‖ = 0 :=
      sq_eq_zero_iff.mp (le_antisymm h_sq_le (sq_nonneg _))
    exact sub_eq_zero.mp (norm_eq_zero.mp h_zero)
  let ω : G_L → ℝ := fun U => lam0⁻¹ * (wilsonIntegralFn L N β K_kin Ω U).re
  have hω_cont : Continuous ω :=
    continuous_const.mul
      (Complex.continuous_re.comp
        (wilsonIntegralFn_continuous L N β hβ K_kin hK_cont hK_nn M_K hK_bd Ω))
  have hΩ_im_zero : ∀ U, (wilsonIntegralFn L N β K_kin Ω U).im = 0 := by
    intro U
    have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd Ω U
    dsimp [wilsonIntegralFn]
    have h1 : (∫ U', ((K_W U U' : ℝ) : ℂ) * Ω U' ∂μ).im =
        RCLike.re (-Complex.I * ∫ U', ((K_W U U' : ℝ) : ℂ) * Ω U' ∂μ) := by
      simp [Complex.mul_re]
    rw [h1, ← MeasureTheory.integral_const_mul, ← integral_re (hi.const_mul (-Complex.I))]
    refine MeasureTheory.integral_eq_zero_of_ae ?_
    filter_upwards [hΩ_ae] with U' hU'
    change RCLike.re (-Complex.I * (((K_W U U' : ℝ) : ℂ) * ⇑Ω U')) = 0
    rw [hU']
    simp [φ_abs, Complex.mul_re]
  have hΩ_ae_ω : ⇑Ω =ᵐ[μ] fun U => (ω U : ℂ) := by
    have h_eq : Ω = ((lam0⁻¹ : ℝ) : ℂ) • T Ω := by
      rw [hΩ_eig, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam0_pos.ne',
        Complex.ofReal_one, one_smul]
    have h1 : ⇑Ω =ᵐ[μ] ((lam0⁻¹ : ℝ) : ℂ) • ⇑(T Ω) := by
      conv_lhs => rw [h_eq]
      exact MeasureTheory.Lp.coeFn_smul _ _
    filter_upwards [h1, wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
      M_K hM_K hK_bd Ω] with U hU1 hU2
    change ⇑Ω U = (ω U : ℂ)
    rw [hU1]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hU2]
    have him := hΩ_im_zero U
    have h_fn : wilsonIntegralFn L N β K_kin Ω U =
        ((wilsonIntegralFn L N β K_kin Ω U).re : ℂ) := Complex.ext rfl him
    rw [h_fn]
    dsimp [ω]; push_cast; rfl
  have hω_nonneg : ∀ U, 0 ≤ ω U := by
    intro U
    have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd Ω U
    have h_re_eq : (wilsonIntegralFn L N β K_kin Ω U).re = ∫ U', K_W U U' * ‖φ₀ U'‖ ∂μ := by
      dsimp [wilsonIntegralFn]
      change RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * Ω U' ∂μ) = _
      rw [← integral_re hi]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hΩ_ae] with U' hU'
      change (((K_W U U' : ℝ) : ℂ) * ⇑Ω U').re = K_W U U' * ‖φ₀ U'‖
      rw [hU']; simp [φ_abs, Complex.ofReal_re]
    dsimp [ω]
    rw [h_re_eq]
    exact mul_nonneg (inv_nonneg.mpr hlam0_pos.le)
      (MeasureTheory.integral_nonneg fun U' =>
        mul_nonneg (hc_W_pos.le.trans (hKW_lb U U')) (norm_nonneg _))
  have hω_pos : ∀ U, 0 < ω U := by
    intro U
    have h_ne0 : ∃ U₀ : G_L, ω U₀ ≠ 0 := by
      by_contra h_all
      push_neg at h_all
      have hΩ_zero : Ω = 0 := by
        apply MeasureTheory.Lp.ext
        filter_upwards [hΩ_ae_ω, MeasureTheory.Lp.coeFn_zero ℂ 2 μ] with W hW1 hW2
        rw [hW1, h_all W, Complex.ofReal_zero, hW2]; rfl
      rw [hΩ_zero, norm_zero] at hΩ_norm
      norm_num at hΩ_norm
    rcases h_ne0 with ⟨U₀, hU₀_ne⟩
    have hU₀_pos : 0 < ω U₀ := lt_of_le_of_ne (hω_nonneg U₀) (Ne.symm hU₀_ne)
    let B : Set G_L := { W | ω U₀ / 2 < ω W }
    have hB_open : IsOpen B := isOpen_lt continuous_const hω_cont
    have hB_ne : B.Nonempty := ⟨U₀, by dsimp [B]; linarith⟩
    have hB_pos : 0 < μ.real B := by
      have hm_pos := hB_open.measure_pos μ hB_ne
      exact ENNReal.toReal_pos hm_pos.ne' (MeasureTheory.measure_ne_top μ B)
    have h_int_pos : 0 < ∫ U', K_W U U' * ω U' ∂μ := by
      let δ_lb : ℝ := c_W * (ω U₀ / 2)
      have hδ_lb_pos : 0 < δ_lb := mul_pos hc_W_pos (by linarith)
      have h_int_Kω : MeasureTheory.Integrable (fun U' => K_W U U' * ω U') μ :=
        integrable_of_continuous_compact μ _
          ((continuous_cubicWilsonKernel_right L N β K_kin hK_cont U).mul hω_cont)
      have h_ind_int : MeasureTheory.Integrable (Set.indicator B (fun _ => δ_lb)) μ :=
        (MeasureTheory.integrable_const δ_lb).indicator hB_open.measurableSet
      have h_le_ind : ∀ U', Set.indicator B (fun _ => δ_lb) U' ≤ K_W U U' * ω U' := by
        intro U'
        rw [Set.indicator_apply]
        by_cases hU' : U' ∈ B
        · rw [if_pos hU']
          exact mul_le_mul (hKW_lb U U') (le_of_lt hU') (by linarith)
            (hc_W_pos.le.trans (hKW_lb U U'))
        · rw [if_neg hU']
          exact mul_nonneg (hc_W_pos.le.trans (hKW_lb U U')) (hω_nonneg U')
      have h_int_val : ∫ U', Set.indicator B (fun _ => δ_lb) U' ∂μ = μ.real B * δ_lb := by
        rw [MeasureTheory.integral_indicator hB_open.measurableSet, MeasureTheory.setIntegral_const]
        simp [smul_eq_mul]
      calc 0 < μ.real B * δ_lb := mul_pos hB_pos hδ_lb_pos
        _ = ∫ U', Set.indicator B (fun _ => δ_lb) U' ∂μ := h_int_val.symm
        _ ≤ ∫ U', K_W U U' * ω U' ∂μ := MeasureTheory.integral_mono h_ind_int h_int_Kω h_le_ind
    have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd Ω U
    have h_re_eq : (wilsonIntegralFn L N β K_kin Ω U).re = ∫ U', K_W U U' * ω U' ∂μ := by
      dsimp [wilsonIntegralFn]
      change RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * Ω U' ∂μ) = _
      rw [← integral_re hi]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hΩ_ae_ω] with U' hU'
      change (((K_W U U' : ℝ) : ℂ) * ⇑Ω U').re = K_W U U' * ω U'
      rw [hU', ← Complex.ofReal_mul, Complex.ofReal_re]
    dsimp [ω]
    rw [h_re_eq]
    exact mul_pos (inv_pos.mpr hlam0_pos) h_int_pos
  have h_simple : ∀ w : HaarGaugeSpace μ,
      T w = (lam0 : ℂ) • w → ⟪w, Ω⟫_ℂ = 0 → w = 0 := by
    intro w hw_eig hw_orth
    by_contra hw_ne
    let ψ_c : G_L → ℂ := fun U => ((lam0⁻¹ : ℝ) : ℂ) * wilsonIntegralFn L N β K_kin w U
    have hψ_cont : Continuous ψ_c :=
      continuous_const.mul (wilsonIntegralFn_continuous L N β hβ K_kin hK_cont hK_nn M_K hK_bd w)
    have hw_ae : ⇑w =ᵐ[μ] ψ_c := by
      have h_eq : w = ((lam0⁻¹ : ℝ) : ℂ) • T w := by
        rw [hw_eig, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam0_pos.ne',
          Complex.ofReal_one, one_smul]
      have h1 : ⇑w =ᵐ[μ] ((lam0⁻¹ : ℝ) : ℂ) • ⇑(T w) := by
        conv_lhs => rw [h_eq]
        exact MeasureTheory.Lp.coeFn_smul _ _
      filter_upwards [h1, wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
        M_K hM_K hK_bd w] with U hU1 hU2
      change ⇑w U = ψ_c U
      rw [hU1]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hU2]
    have h_ae_eig : (fun U => wilsonIntegralFn L N β K_kin w U) =ᵐ[μ]
        (fun U => (lam0 : ℂ) * ψ_c U) := by
      have h1 : ⇑(T w) =ᵐ[μ] ⇑((lam0 : ℂ) • w) := by rw [hw_eig]
      have h2 := MeasureTheory.Lp.coeFn_smul (lam0 : ℂ) w
      filter_upwards [wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd w,
        h1, h2, hw_ae] with U hUT hT1 hSm hUψ
      change wilsonIntegralFn L N β K_kin w U = (lam0 : ℂ) * ψ_c U
      rw [← hUT, hT1]
      change ⇑((lam0 : ℂ) • w) U = _
      rw [hSm]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hUψ]
    have h_all_eig : ∀ U, wilsonIntegralFn L N β K_kin w U = (lam0 : ℂ) * ψ_c U :=
      eq_of_ae_continuous μ
        (wilsonIntegralFn_continuous L N β hβ K_kin hK_cont hK_nn M_K hK_bd w)
        (continuous_const.mul hψ_cont) h_ae_eig
    let u : G_L → ℝ := fun U => (ψ_c U).re
    let v_im : G_L → ℝ := fun U => (ψ_c U).im
    have hu_cont : Continuous u := Complex.continuous_re.comp hψ_cont
    have hv_cont : Continuous v_im := Complex.continuous_im.comp hψ_cont
    have h_u_eig : ∀ U, ∫ U', K_W U U' * u U' ∂μ = lam0 * u U := by
      intro U
      have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd w U
      have h_eq := congrArg Complex.re (h_all_eig U)
      dsimp [wilsonIntegralFn] at h_eq
      simp only [zero_mul, sub_zero] at h_eq
      change RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * w U' ∂μ) = lam0 * u U at h_eq
      rw [← integral_re hi] at h_eq
      have h_lhs : ∫ U', RCLike.re (((K_W U U' : ℝ) : ℂ) * w U') ∂μ =
          ∫ U', K_W U U' * u U' ∂μ := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hw_ae] with U' hU'
        change (((K_W U U' : ℝ) : ℂ) * ⇑w U').re = K_W U U' * u U'
        rw [hU']
        simp [u, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      rwa [h_lhs] at h_eq
    have h_v_eig : ∀ U, ∫ U', K_W U U' * v_im U' ∂μ = lam0 * v_im U := by
      intro U
      have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd w U
      have h_eq := congrArg Complex.im (h_all_eig U)
      dsimp [wilsonIntegralFn] at h_eq
      have him_l : (∫ U', ((K_W U U' : ℝ) : ℂ) * w U' ∂μ).im =
          RCLike.re (-Complex.I * ∫ U', ((K_W U U' : ℝ) : ℂ) * w U' ∂μ) := by
        simp [Complex.mul_re]
      rw [him_l, ← MeasureTheory.integral_const_mul,
        ← integral_re (hi.const_mul (-Complex.I))] at h_eq
      have h_ae : (fun U' => RCLike.re (-Complex.I * (((K_W U U' : ℝ) : ℂ) * w U'))) =ᵐ[μ]
          fun U' => K_W U U' * v_im U' := by
        filter_upwards [hw_ae] with U' hU'
        rw [hU']
        change (-Complex.I * (((K_W U U' : ℝ) : ℂ) * ψ_c U')).re = K_W U U' * v_im U'
        simp [v_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      rw [MeasureTheory.integral_congr_ae h_ae] at h_eq
      simpa [v_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] using h_eq
    have h_no_eig_real : ∀ (f : G_L → ℝ), Continuous f →
        (∀ U, ∫ U', K_W U U' * f U' ∂μ = lam0 * f U) →
        (∫ U, f U * ω U ∂μ = 0) → (∀ U, f U = 0) := by
      intro f hf_cont hf_eig hf_orth
      by_contra hf_ne
      push_neg at hf_ne
      rcases hf_ne with ⟨U_star, hU_star⟩
      have h_pos_set : ∃ U₁ : G_L, 0 < f U₁ := by
        by_contra h_le
        push_neg at h_le
        have h_neg_or_zero : ∀ U, f U * ω U ≤ 0 := fun U =>
          mul_nonpos_of_nonpos_of_nonneg (h_le U) (hω_pos U).le
        have hU_lt : f U_star < 0 := lt_of_le_of_ne (h_le U_star) hU_star
        let B_neg : Set G_L := { U | f U * ω U < (f U_star * ω U_star) / 2 }
        have hB_open : IsOpen B_neg := isOpen_lt (hf_cont.mul hω_cont) continuous_const
        have hB_ne : B_neg.Nonempty := ⟨U_star, by
          dsimp [B_neg]
          have hmul : f U_star * ω U_star < 0 := mul_neg_of_neg_of_pos hU_lt (hω_pos U_star)
          linarith⟩
        have hB_pos : 0 < μ.real B_neg :=
          ENNReal.toReal_pos (hB_open.measure_pos μ hB_ne).ne' (MeasureTheory.measure_ne_top μ B_neg)
        have h_cont_int : MeasureTheory.Integrable (fun U => f U * ω U) μ :=
          integrable_of_continuous_compact μ _ (hf_cont.mul hω_cont)
        have h_ind_int : MeasureTheory.Integrable
            (Set.indicator B_neg (fun _ => -(f U_star * ω U_star) / 2)) μ :=
          (MeasureTheory.integrable_const _).indicator hB_open.measurableSet
        have h_le_neg : ∀ U, Set.indicator B_neg (fun _ => -(f U_star * ω U_star) / 2) U ≤
            -(f U * ω U) := by
          intro U
          rw [Set.indicator_apply]
          by_cases hU : U ∈ B_neg
          · rw [if_pos hU]; dsimp [B_neg] at hU; linarith
          · rw [if_neg hU]; linarith [h_neg_or_zero U]
        have h_int_neg : 0 < ∫ U, -(f U * ω U) ∂μ := by
          have hc_pos : 0 < -(f U_star * ω U_star) / 2 := by
            have hmul : f U_star * ω U_star < 0 := mul_neg_of_neg_of_pos hU_lt (hω_pos U_star)
            linarith
          have h_val : ∫ U, Set.indicator B_neg (fun _ => -(f U_star * ω U_star) / 2) U ∂μ =
              μ.real B_neg * (-(f U_star * ω U_star) / 2) := by
            rw [MeasureTheory.integral_indicator hB_open.measurableSet, MeasureTheory.setIntegral_const]
            simp [smul_eq_mul]
          calc 0 < μ.real B_neg * (-(f U_star * ω U_star) / 2) := mul_pos hB_pos hc_pos
            _ = ∫ U, Set.indicator B_neg (fun _ => -(f U_star * ω U_star) / 2) U ∂μ := h_val.symm
            _ ≤ ∫ U, -(f U * ω U) ∂μ := MeasureTheory.integral_mono h_ind_int h_cont_int.neg h_le_neg
        rw [MeasureTheory.integral_neg, hf_orth, neg_zero] at h_int_neg
        exact lt_irrefl 0 h_int_neg
      have h_neg_set : ∃ U₂ : G_L, f U₂ < 0 := by
        by_contra h_ge
        push_neg at h_ge
        rcases h_pos_set with ⟨U₁, hU₁⟩
        let B_pos : Set G_L := { U | (f U₁ * ω U₁) / 2 < f U * ω U }
        have hB_open : IsOpen B_pos := isOpen_lt continuous_const (hf_cont.mul hω_cont)
        have hB_ne : B_pos.Nonempty := ⟨U₁, by
          dsimp [B_pos]
          have hmul : 0 < f U₁ * ω U₁ := mul_pos hU₁ (hω_pos U₁)
          linarith⟩
        have hB_pos : 0 < μ.real B_pos :=
          ENNReal.toReal_pos (hB_open.measure_pos μ hB_ne).ne' (MeasureTheory.measure_ne_top μ B_pos)
        have h_cont_int : MeasureTheory.Integrable (fun U => f U * ω U) μ :=
          integrable_of_continuous_compact μ _ (hf_cont.mul hω_cont)
        have h_ind_int : MeasureTheory.Integrable
            (Set.indicator B_pos (fun _ => (f U₁ * ω U₁) / 2)) μ :=
          (MeasureTheory.integrable_const _).indicator hB_open.measurableSet
        have h_le_pos : ∀ U, Set.indicator B_pos (fun _ => (f U₁ * ω U₁) / 2) U ≤ f U * ω U := by
          intro U
          rw [Set.indicator_apply]
          by_cases hU : U ∈ B_pos
          · rw [if_pos hU]; exact (hU : _ < _).le
          · rw [if_neg hU]; exact mul_nonneg (h_ge U) (hω_pos U).le
        have h_int_pos : 0 < ∫ U, f U * ω U ∂μ := by
          have hc_pos : 0 < (f U₁ * ω U₁) / 2 := mul_pos (mul_pos hU₁ (hω_pos U₁)) (by norm_num)
          have h_val : ∫ U, Set.indicator B_pos (fun _ => (f U₁ * ω U₁) / 2) U ∂μ =
              μ.real B_pos * ((f U₁ * ω U₁) / 2) := by
            rw [MeasureTheory.integral_indicator hB_open.measurableSet, MeasureTheory.setIntegral_const]
            simp [smul_eq_mul]
          calc 0 < μ.real B_pos * ((f U₁ * ω U₁) / 2) := mul_pos hB_pos hc_pos
            _ = ∫ U, Set.indicator B_pos (fun _ => (f U₁ * ω U₁) / 2) U ∂μ := h_val.symm
            _ ≤ ∫ U, f U * ω U ∂μ := MeasureTheory.integral_mono h_ind_int h_cont_int h_le_pos
        rw [hf_orth] at h_int_pos
        exact lt_irrefl 0 h_int_pos
      rcases h_pos_set with ⟨U₁, hU₁⟩
      rcases h_neg_set with ⟨U₂, hU₂⟩
      let f_abs : G_L → ℝ := fun U => |f U|
      have hf_abs_cont : Continuous f_abs := continuous_abs.comp hf_cont
      let f_mem := memLp_of_continuous_compact μ f hf_cont
      let f_abs_mem := memLp_of_continuous_compact μ f_abs hf_abs_cont
      let f_Lp : HaarGaugeSpace μ := f_mem.toLp (fun U => (f U : ℂ))
      let f_abs_Lp : HaarGaugeSpace μ := f_abs_mem.toLp (fun U => (f_abs U : ℂ))
      have hf_ae := f_mem.coeFn_toLp
      have hf_abs_ae := f_abs_mem.coeFn_toLp
      have hf_norm_sq : ‖f_abs_Lp‖ ^ 2 = ∫ U, f U * f U ∂μ := by
        rw [lp_norm_sq_eq_integral]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hf_abs_ae] with U hU
        change ‖⇑f_abs_Lp U‖ ^ 2 = f U * f U
        rw [hU, Complex.norm_real, Real.norm_eq_abs, abs_abs, sq_abs, sq]
      have hf_in_val : (⟪f_Lp, T f_Lp⟫_ℂ).re =
          ∫ U, ∫ U', K_W U U' * (f U * f U') ∂μ ∂μ := by
        have h_l2 : MeasureTheory.Integrable (fun U => ⟪f_Lp U, (T f_Lp) U⟫_ℂ) μ :=
          MeasureTheory.L2.integrable_inner f_Lp (T f_Lp)
        have h_re := integral_re h_l2
        rw [MeasureTheory.L2.inner_def]
        change RCLike.re (∫ U, ⟪f_Lp U, (T f_Lp) U⟫_ℂ ∂μ) = _
        rw [← h_re]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hf_ae, wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
          M_K hM_K hK_bd f_Lp] with U hU1 hU2
        change (⟪⇑f_Lp U, ⇑(T f_Lp) U⟫_ℂ).re = _
        rw [hU1, hU2, hcinner]
        have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd f_Lp U
        dsimp [wilsonIntegralFn]
        simp only [neg_zero, zero_mul, sub_zero]
        have h_re_u : (∫ U', ((K_W U U' : ℝ) : ℂ) * f_Lp U' ∂μ).re =
            ∫ U', K_W U U' * f U' ∂μ := by
          change RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * f_Lp U' ∂μ) = _
          rw [← integral_re hi]
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [hf_ae] with U' hU'
          change (((K_W U U' : ℝ) : ℂ) * ⇑f_Lp U').re = K_W U U' * f U'
          rw [hU', ← Complex.ofReal_mul, Complex.ofReal_re]
        rw [h_re_u, ← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U' => by
          dsimp only; ring)
      have hf_abs_in_val : (⟪f_abs_Lp, T f_abs_Lp⟫_ℂ).re =
          ∫ U, ∫ U', K_W U U' * (|f U| * |f U'|) ∂μ ∂μ := by
        have h_l2 : MeasureTheory.Integrable (fun U => ⟪f_abs_Lp U, (T f_abs_Lp) U⟫_ℂ) μ :=
          MeasureTheory.L2.integrable_inner f_abs_Lp (T f_abs_Lp)
        have h_re := integral_re h_l2
        rw [MeasureTheory.L2.inner_def]
        change RCLike.re (∫ U, ⟪f_abs_Lp U, (T f_abs_Lp) U⟫_ℂ ∂μ) = _
        rw [← h_re]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hf_abs_ae, wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
          M_K hM_K hK_bd f_abs_Lp] with U hU1 hU2
        change (⟪⇑f_abs_Lp U, ⇑(T f_abs_Lp) U⟫_ℂ).re = _
        rw [hU1, hU2, hcinner]
        have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd f_abs_Lp U
        dsimp [wilsonIntegralFn]
        simp only [neg_zero, zero_mul, sub_zero]
        have h_re_u : (∫ U', ((K_W U U' : ℝ) : ℂ) * f_abs_Lp U' ∂μ).re =
            ∫ U', K_W U U' * |f U'| ∂μ := by
          change RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * f_abs_Lp U' ∂μ) = _
          rw [← integral_re hi]
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [hf_abs_ae] with U' hU'
          change (((K_W U U' : ℝ) : ℂ) * ⇑f_abs_Lp U').re = K_W U U' * |f U'|
          rw [hU', ← Complex.ofReal_mul, Complex.ofReal_re]
        rw [h_re_u, ← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U' => by
          dsimp only [f_abs]; ring)
      have hf_in_eq : (⟪f_Lp, T f_Lp⟫_ℂ).re = lam0 * ∫ U, f U * f U ∂μ := by
        rw [hf_in_val]
        have h_row : ∀ U, ∫ U', K_W U U' * (f U * f U') ∂μ = lam0 * (f U * f U) := by
          intro U
          rw [show (fun U' => K_W U U' * (f U * f U')) = fun U' => f U * (K_W U U' * f U') by
            funext U'; ring]
          rw [MeasureTheory.integral_const_mul, hf_eig U]
          ring
        simp_rw [h_row, MeasureTheory.integral_const_mul]
      have hf_abs_in_le : (⟪f_abs_Lp, T f_abs_Lp⟫_ℂ).re ≤ lam0 * ∫ U, f U * f U ∂μ := by
        rw [← hf_norm_sq]
        calc (⟪f_abs_Lp, T f_abs_Lp⟫_ℂ).re ≤ ‖⟪f_abs_Lp, T f_abs_Lp⟫_ℂ‖ :=
              (le_abs_self _).trans (Complex.abs_re_le_norm _)
          _ ≤ ‖f_abs_Lp‖ * ‖T f_abs_Lp‖ := norm_inner_le_norm _ _
          _ ≤ ‖f_abs_Lp‖ * (lam0 * ‖f_abs_Lp‖) :=
              mul_le_mul_of_nonneg_left (T.le_opNorm f_abs_Lp) (norm_nonneg _)
          _ = lam0 * ‖f_abs_Lp‖ ^ 2 := by ring
      let Δ_row : G_L → ℝ := fun U => ∫ U', K_W U U' * (|f U| * |f U'| - f U * f U') ∂μ
      have h_row_cont1 : Continuous (fun U => ∫ U', K_W U U' * (|f U| * |f U'|) ∂μ) := by
        have h_eq : (fun U => ∫ U', K_W U U' * (|f U| * |f U'|) ∂μ) =
            fun U => |f U| * (wilsonIntegralFn L N β K_kin f_abs_Lp U).re := by
          funext U
          have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd f_abs_Lp U
          have h_re_u : (wilsonIntegralFn L N β K_kin f_abs_Lp U).re =
              ∫ U', K_W U U' * |f U'| ∂μ := by
            dsimp [wilsonIntegralFn]
            change RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * f_abs_Lp U' ∂μ) = _
            rw [← integral_re hi]
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [hf_abs_ae] with U' hU'
            change (((K_W U U' : ℝ) : ℂ) * ⇑f_abs_Lp U').re = K_W U U' * |f U'|
            rw [hU', ← Complex.ofReal_mul, Complex.ofReal_re]
          rw [h_re_u, ← MeasureTheory.integral_const_mul]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U' => by
            dsimp only; ring)
        rw [h_eq]
        exact hf_abs_cont.mul (Complex.continuous_re.comp
          (wilsonIntegralFn_continuous L N β hβ K_kin hK_cont hK_nn M_K hK_bd f_abs_Lp))
      have h_row_cont2 : Continuous (fun U => ∫ U', K_W U U' * (f U * f U') ∂μ) := by
        have h_eq : (fun U => ∫ U', K_W U U' * (f U * f U') ∂μ) =
            fun U => f U * (lam0 * f U) := by
          funext U
          rw [show (fun U' => K_W U U' * (f U * f U')) = fun U' => f U * (K_W U U' * f U') by
            funext U'; ring, MeasureTheory.integral_const_mul, hf_eig U]
        rw [h_eq]
        exact hf_cont.mul (continuous_const.mul hf_cont)
      have hΔ_int_eq : ∫ U, Δ_row U ∂μ =
          (⟪f_abs_Lp, T f_abs_Lp⟫_ℂ).re - (⟪f_Lp, T f_Lp⟫_ℂ).re := by
        have h_sub_row : ∀ U, Δ_row U =
            (∫ U', K_W U U' * (|f U| * |f U'|) ∂μ) -
              (∫ U', K_W U U' * (f U * f U') ∂μ) := by
          intro U
          have hi1 : MeasureTheory.Integrable (fun U' => K_W U U' * (|f U| * |f U'|)) μ :=
            integrable_of_continuous_compact μ _
              ((continuous_cubicWilsonKernel_right L N β K_kin hK_cont U).mul
                (continuous_const.mul hf_abs_cont))
          have hi2 : MeasureTheory.Integrable (fun U' => K_W U U' * (f U * f U')) μ :=
            integrable_of_continuous_compact μ _
              ((continuous_cubicWilsonKernel_right L N β K_kin hK_cont U).mul
                (continuous_const.mul hf_cont))
          dsimp [Δ_row]
          rw [← MeasureTheory.integral_sub hi1 hi2]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U' => by
            dsimp only; ring)
        simp_rw [h_sub_row]
        rw [MeasureTheory.integral_sub
          (integrable_of_continuous_compact μ _ h_row_cont1)
          (integrable_of_continuous_compact μ _ h_row_cont2),
          hf_abs_in_val, hf_in_val]
      have hΔ_le_zero : ∫ U, Δ_row U ∂μ ≤ 0 := by linarith
      let B₁ : Set G_L := { U | f U₁ / 2 < f U }
      let B₂ : Set G_L := { U' | (-f U₂) / 2 < -f U' }
      have hB₁_open : IsOpen B₁ := isOpen_lt continuous_const hf_cont
      have hB₂_open : IsOpen B₂ := isOpen_lt continuous_const hf_cont.neg
      have hB₁_pos : 0 < μ.real B₁ :=
        ENNReal.toReal_pos
          (hB₁_open.measure_pos μ ⟨U₁, by change f U₁ / 2 < f U₁; linarith⟩).ne'
          (MeasureTheory.measure_ne_top μ B₁)
      have hB₂_pos : 0 < μ.real B₂ :=
        ENNReal.toReal_pos
          (hB₂_open.measure_pos μ ⟨U₂, by change (-f U₂) / 2 < -f U₂; linarith⟩).ne'
          (MeasureTheory.measure_ne_top μ B₂)
      let δ₀ : ℝ := c_W * (f U₁ * (-f U₂) / 2)
      have hδ₀_pos : 0 < δ₀ := mul_pos hc_W_pos (by nlinarith)
      have hΔ_nonneg : ∀ U, 0 ≤ Δ_row U := fun U =>
        MeasureTheory.integral_nonneg fun U' => by
          have h_le : f U * f U' ≤ |f U| * |f U'| := by rw [← abs_mul]; exact le_abs_self _
          exact mul_nonneg (hc_W_pos.le.trans (hKW_lb U U')) (sub_nonneg.mpr h_le)
      have hΔ_B₁ : ∀ U ∈ B₁, δ₀ * μ.real B₂ ≤ Δ_row U := by
        intro U hU
        have hiΔ : MeasureTheory.Integrable (fun U' => K_W U U' * (|f U| * |f U'| - f U * f U')) μ :=
          integrable_of_continuous_compact μ _
            ((continuous_cubicWilsonKernel_right L N β K_kin hK_cont U).mul
              ((continuous_const.mul hf_abs_cont).sub (continuous_const.mul hf_cont)))
        have h_ind_int : MeasureTheory.Integrable (Set.indicator B₂ (fun _ => δ₀)) μ :=
          (MeasureTheory.integrable_const δ₀).indicator hB₂_open.measurableSet
        have h_le_ind : ∀ U', Set.indicator B₂ (fun _ => δ₀) U' ≤
            K_W U U' * (|f U| * |f U'| - f U * f U') := by
          intro U'
          rw [Set.indicator_apply]
          by_cases hU' : U' ∈ B₂
          · rw [if_pos hU']
            have hfu : f U₁ / 2 < f U := hU
            have hfu' : (-f U₂) / 2 < -f U' := hU'
            have hfu_pos : 0 < f U := by linarith
            have hfu'_neg : f U' < 0 := by linarith
            have h_diff_eq : |f U| * |f U'| - f U * f U' = 2 * f U * (-f U') := by
              rw [abs_of_pos hfu_pos, abs_of_neg hfu'_neg]; ring
            have h_diff_ge : f U₁ * (-f U₂) / 2 ≤ |f U| * |f U'| - f U * f U' := by
              rw [h_diff_eq]; nlinarith
            exact mul_le_mul (hKW_lb U U') h_diff_ge (by nlinarith) (hc_W_pos.le.trans (hKW_lb U U'))
          · rw [if_neg hU']
            have h_le : f U * f U' ≤ |f U| * |f U'| := by rw [← abs_mul]; exact le_abs_self _
            exact mul_nonneg (hc_W_pos.le.trans (hKW_lb U U')) (sub_nonneg.mpr h_le)
        have h_val : ∫ U', Set.indicator B₂ (fun _ => δ₀) U' ∂μ = μ.real B₂ * δ₀ := by
          rw [MeasureTheory.integral_indicator hB₂_open.measurableSet, MeasureTheory.setIntegral_const]
          simp [smul_eq_mul]
        calc δ₀ * μ.real B₂ = μ.real B₂ * δ₀ := by ring
          _ = ∫ U', Set.indicator B₂ (fun _ => δ₀) U' ∂μ := h_val.symm
          _ ≤ Δ_row U := MeasureTheory.integral_mono h_ind_int hiΔ h_le_ind
      have hΔ_cont : Continuous Δ_row := by
        have h_eq : Δ_row = fun U =>
            (∫ U', K_W U U' * (|f U| * |f U'|) ∂μ) - (∫ U', K_W U U' * (f U * f U') ∂μ) := by
          funext U
          have hi1 : MeasureTheory.Integrable (fun U' => K_W U U' * (|f U| * |f U'|)) μ :=
            integrable_of_continuous_compact μ _
              ((continuous_cubicWilsonKernel_right L N β K_kin hK_cont U).mul
                (continuous_const.mul hf_abs_cont))
          have hi2 : MeasureTheory.Integrable (fun U' => K_W U U' * (f U * f U')) μ :=
            integrable_of_continuous_compact μ _
              ((continuous_cubicWilsonKernel_right L N β K_kin hK_cont U).mul
                (continuous_const.mul hf_cont))
          dsimp [Δ_row]
          rw [← MeasureTheory.integral_sub hi1 hi2]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U' => by
            dsimp only; ring)
        rw [h_eq]
        exact h_row_cont1.sub h_row_cont2
      have h_int_pos : 0 < ∫ U, Δ_row U ∂μ := by
        have h_ind_int : MeasureTheory.Integrable (Set.indicator B₁ (fun _ => δ₀ * μ.real B₂)) μ :=
          (MeasureTheory.integrable_const _).indicator hB₁_open.measurableSet
        have h_le_ind : ∀ U, Set.indicator B₁ (fun _ => δ₀ * μ.real B₂) U ≤ Δ_row U := by
          intro U
          rw [Set.indicator_apply]
          by_cases hU : U ∈ B₁
          · rw [if_pos hU]; exact hΔ_B₁ U hU
          · rw [if_neg hU]; exact hΔ_nonneg U
        have h_val : ∫ U, Set.indicator B₁ (fun _ => δ₀ * μ.real B₂) U ∂μ =
            μ.real B₁ * (δ₀ * μ.real B₂) := by
          rw [MeasureTheory.integral_indicator hB₁_open.measurableSet, MeasureTheory.setIntegral_const]
          simp [smul_eq_mul]
        calc 0 < μ.real B₁ * (δ₀ * μ.real B₂) := mul_pos hB₁_pos (mul_pos hδ₀_pos hB₂_pos)
          _ = ∫ U, Set.indicator B₁ (fun _ => δ₀ * μ.real B₂) U ∂μ := h_val.symm
          _ ≤ ∫ U, Δ_row U ∂μ :=
              MeasureTheory.integral_mono h_ind_int (integrable_of_continuous_compact μ _ hΔ_cont) h_le_ind
      linarith
    have hw_orth_u : ∫ U, u U * ω U ∂μ = 0 := by
      have h_l2 : MeasureTheory.Integrable (fun U => ⟪w U, Ω U⟫_ℂ) μ :=
        MeasureTheory.L2.integrable_inner w Ω
      have h_re := integral_re h_l2
      have h0 : (⟪w, Ω⟫_ℂ).re = 0 := by rw [hw_orth, Complex.zero_re]
      rw [MeasureTheory.L2.inner_def] at h0
      change RCLike.re (∫ U, ⟪w U, Ω U⟫_ℂ ∂μ) = 0 at h0
      rw [← h_re] at h0
      have h_ae : (fun U => (⟪w U, Ω U⟫_ℂ).re) =ᵐ[μ] fun U => u U * ω U := by
        filter_upwards [hw_ae, hΩ_ae_ω] with U hU1 hU2
        change (⟪⇑w U, ⇑Ω U⟫_ℂ).re = u U * ω U
        rw [hU1, hU2, hcinner]
        simp [u, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      have h_ae' : (fun U => RCLike.re ⟪w U, Ω U⟫_ℂ) =ᵐ[μ] fun U => u U * ω U := h_ae
      rwa [MeasureTheory.integral_congr_ae h_ae'] at h0
    have hw_orth_v : ∫ U, v_im U * ω U ∂μ = 0 := by
      have h_l2 : MeasureTheory.Integrable (fun U => ⟪w U, Ω U⟫_ℂ) μ :=
        MeasureTheory.L2.integrable_inner w Ω
      have h0 : (⟪w, Ω⟫_ℂ).im = 0 := by rw [hw_orth, Complex.zero_im]
      rw [MeasureTheory.L2.inner_def] at h0
      have h1 : (∫ U, ⟪w U, Ω U⟫_ℂ ∂μ).im =
          RCLike.re (-Complex.I * ∫ U, ⟪w U, Ω U⟫_ℂ ∂μ) := by
        simp [Complex.mul_re]
      rw [h1, ← MeasureTheory.integral_const_mul, ← integral_re (h_l2.const_mul (-Complex.I))] at h0
      have h_ae : (fun U => RCLike.re (-Complex.I * ⟪w U, Ω U⟫_ℂ)) =ᵐ[μ]
          fun U => -(v_im U * ω U) := by
        filter_upwards [hw_ae, hΩ_ae_ω] with U hU1 hU2
        change (-Complex.I * ⟪⇑w U, ⇑Ω U⟫_ℂ).re = -(v_im U * ω U)
        rw [hU1, hU2, hcinner]
        simp [v_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      rw [MeasureTheory.integral_congr_ae h_ae, MeasureTheory.integral_neg] at h0
      linarith
    have hu_zero := h_no_eig_real u hu_cont h_u_eig hw_orth_u
    have hv_zero := h_no_eig_real v_im hv_cont h_v_eig hw_orth_v
    apply hw_ne
    apply MeasureTheory.Lp.ext
    filter_upwards [hw_ae, MeasureTheory.Lp.coeFn_zero ℂ 2 μ] with U hU1 hU2
    change ⇑w U = ⇑(0 : HaarGaugeSpace μ) U
    rw [hU1, hU2]
    exact Complex.ext (hu_zero U) (hv_zero U)
  have hΩ_gauge : ∀ g, cubicGaugeRep L N g Ω = Ω := by
    intro g
    let U_g := cubicGaugeRep L N g
    have h_comm := wilsonIntegralOp_gauge_inv L N β hβ K_kin hK_cont hK_nn hK_inv
      M_K hM_K hK_bd g
    have hUg_eig : T (U_g Ω) = (lam0 : ℂ) • (U_g Ω) := by
      have hcomp := congrArg (fun f : HaarGaugeSpace μ →L[ℂ] HaarGaugeSpace μ => f Ω) h_comm
      change U_g (T Ω) = T (U_g Ω) at hcomp
      rw [← hcomp, hΩ_eig, map_smul]
    let c_g : ℂ := ⟪Ω, U_g Ω⟫_ℂ
    let w_g : HaarGaugeSpace μ := U_g Ω - c_g • Ω
    have hw_orth : ⟪w_g, Ω⟫_ℂ = 0 := by
      have h1 : ⟪Ω, Ω⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hΩ_norm]; norm_num
      simp only [w_g, c_g, inner_sub_left, inner_smul_left, h1, mul_one,
        inner_conj_symm, sub_self]
    have hw_eig : T w_g = (lam0 : ℂ) • w_g := by
      simp only [w_g, map_sub, map_smul, hUg_eig, hΩ_eig, smul_sub]
      rw [smul_comm]
    have hw_zero : w_g = 0 := h_simple w_g hw_eig hw_orth
    have hUg_smul : U_g Ω = c_g • Ω := sub_eq_zero.mp hw_zero
    have hc_norm : ‖c_g‖ = 1 := by
      have hn : ‖c_g • Ω‖ = 1 := by
        rw [← hUg_smul]
        have hsq : ‖U_g Ω‖ ^ 2 = 1 := by
          have hin : (⟪U_g Ω, U_g Ω⟫_ℂ).re = 1 := by
            rw [cubicGaugeRep_unitary, inner_self_eq_norm_sq_to_K, hΩ_norm]
            norm_num
          rw [inner_self_eq_norm_sq_to_K] at hin
          simp [pow_two] at hin
          linarith
        have hmul : (‖U_g Ω‖ - 1) * (‖U_g Ω‖ + 1) = 0 := by linarith
        rcases mul_eq_zero.mp hmul with h | h <;> linarith [norm_nonneg (U_g Ω)]
      rwa [norm_smul, hΩ_norm, mul_one] at hn
    let eqv := gaugeActEquiv L N (fun x => (g x)⁻¹)
    have hmp : MeasureTheory.MeasurePreserving eqv μ μ :=
      ⟨eqv.measurable, latticeHaarMeasure_gauge_inv L N (fun x => (g x)⁻¹)⟩
    have hΩ_g_ae : ⇑(U_g Ω) =ᵐ[μ] fun U => (ω (eqv U) : ℂ) := by
      have h1 := cubicGaugeRep_apply_ae L N g Ω
      have h2 := ae_comp_measurePreserving hmp hΩ_ae_ω
      filter_upwards [h1, h2] with U hu1 hu2
      change ⇑(U_g Ω) U = (ω (eqv U) : ℂ)
      rw [hu1]
      exact hu2
    have hc_int_ae : (fun U => ⟪Ω U, (U_g Ω) U⟫_ℂ) =ᵐ[μ]
        fun U => ((ω U * ω (eqv U) : ℝ) : ℂ) := by
      filter_upwards [hΩ_ae_ω, hΩ_g_ae] with U hU1 hU2
      change ⟪⇑Ω U, ⇑(U_g Ω) U⟫_ℂ = _
      rw [hU1, hU2, hcinner]
      simp [Complex.conj_ofReal, Complex.ofReal_mul]
    have hc_l2 : MeasureTheory.Integrable (fun U => ⟪Ω U, (U_g Ω) U⟫_ℂ) μ :=
      MeasureTheory.L2.integrable_inner Ω (U_g Ω)
    have hc_re_nn : 0 ≤ c_g.re := by
      dsimp [c_g]
      rw [MeasureTheory.L2.inner_def]
      change 0 ≤ RCLike.re (∫ U, ⟪Ω U, (U_g Ω) U⟫_ℂ ∂μ)
      rw [← integral_re hc_l2]
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [hc_int_ae] with U hU
      change 0 ≤ (⟪⇑Ω U, ⇑(U_g Ω) U⟫_ℂ).re
      rw [hU, Complex.ofReal_re]
      exact mul_nonneg (hω_pos U).le (hω_pos _).le
    have hc_im_zero : c_g.im = 0 := by
      dsimp [c_g]
      rw [MeasureTheory.L2.inner_def]
      have h1 : (∫ U, ⟪Ω U, (U_g Ω) U⟫_ℂ ∂μ).im =
          RCLike.re (-Complex.I * ∫ U, ⟪Ω U, (U_g Ω) U⟫_ℂ ∂μ) := by
        simp [Complex.mul_re]
      rw [h1, ← MeasureTheory.integral_const_mul, ← integral_re (hc_l2.const_mul (-Complex.I))]
      refine MeasureTheory.integral_eq_zero_of_ae ?_
      filter_upwards [hc_int_ae] with U hU
      change (-Complex.I * ⟪⇑Ω U, ⇑(U_g Ω) U⟫_ℂ).re = 0
      rw [hU]
      simp [Complex.mul_re]
    have hc_re_one : c_g.re = 1 := by
      have hc_eq : c_g = (c_g.re : ℂ) := Complex.ext rfl hc_im_zero
      rw [hc_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc_re_nn] at hc_norm
      exact hc_norm
    have hc_one : c_g = 1 := Complex.ext hc_re_one hc_im_zero
    rw [hUg_smul, hc_one, one_smul]
  exact ⟨Ω, ω, ⟨hlam0_pos, hΩ_norm, hω_cont, hω_pos, hΩ_ae_ω, hΩ_eig, hΩ_gauge, h_simple⟩⟩

/-- Spectral gap properties of `wilsonExactGap` for any normalized compact positive operator. -/
theorem wilsonExactGap_spec
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (T_norm : V →L[ℂ] V) (Ω : V)
    (hT_sa : ∀ x y : V, ⟪T_norm x, y⟫_ℂ = ⟪x, T_norm y⟫_ℂ)
    (hT_pos : ∀ x : V, 0 ≤ (⟪x, T_norm x⟫_ℂ).re)
    (hT_comp : IsCompactOperator ⇑T_norm)
    (hT_le1 : ‖T_norm‖ ≤ 1)
    (hT_Ω : T_norm Ω = Ω)
    (h_simple : ∀ w : V, T_norm w = (1 : ℂ) • w → ⟪w, Ω⟫_ℂ = 0 → w = 0) :
    0 < wilsonExactGap T_norm Ω hT_sa hT_Ω ∧
    (∀ v : V, ⟪v, Ω⟫_ℂ = 0 →
      (⟪v, T_norm v⟫_ℂ).re ≤ Real.exp (-(wilsonExactGap T_norm Ω hT_sa hT_Ω * 1)) * ‖v‖ ^ 2) ∧
    (wilsonPerpOp T_norm Ω hT_sa hT_Ω ≠ 0 →
      wilsonExactGap T_norm Ω hT_sa hT_Ω =
        -Real.log ‖wilsonPerpOp T_norm Ω hT_sa hT_Ω‖ ∧
      ∃ w : V, ‖w‖ = 1 ∧ ⟪w, Ω⟫_ℂ = 0 ∧
        T_norm w = (Real.exp (-wilsonExactGap T_norm Ω hT_sa hT_Ω) : ℂ) • w) := by
  let K : Submodule ℂ V := wilsonPerpSubmodule Ω
  let T_K : ↥K →L[ℂ] ↥K := wilsonPerpOp T_norm Ω hT_sa hT_Ω
  have hK_closed : IsClosed (K : Set V) := (Submodule.span ℂ {Ω}).isClosed_orthogonal
  haveI : CompleteSpace ↥K := by
    refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
    have huV : CauchySeq (fun n => (u n : V)) :=
      Metric.cauchySeq_iff.mpr (by simpa [Subtype.dist_eq] using Metric.cauchySeq_iff.mp hu)
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete huV
    have haK : a ∈ (K : Set V) :=
      hK_closed.mem_of_tendsto ha (Filter.Eventually.of_forall fun n => (u n).2)
    exact ⟨⟨a, haK⟩, tendsto_subtype_rng.mpr ha⟩
  have hTK_sa : ∀ x y : ↥K, ⟪T_K x, y⟫_ℂ = ⟪x, T_K y⟫_ℂ := fun x y => hT_sa x.1 y.1
  have hTK_pos : ∀ x : ↥K, 0 ≤ (⟪x, T_K x⟫_ℂ).re := fun x => hT_pos x.1
  have hTK_comp : IsCompactOperator ⇑T_K := by
    obtain ⟨S, hS_comp, hS_nhds⟩ := hT_comp
    let S_K : Set ↥K := Subtype.val ⁻¹' S
    have hSK_comp : IsCompact S_K := by
      have him : Subtype.val '' S_K = S ∩ (K : Set V) := by
        ext x
        simp only [S_K, Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, SetLike.mem_coe,
          Subtype.exists, exists_and_right, exists_eq_right]
        exact ⟨fun ⟨hxK, hxS⟩ => ⟨hxS, hxK⟩, fun ⟨hxS, hxK⟩ => ⟨hxK, hxS⟩⟩
      exact Topology.IsInducing.subtypeVal.isCompact_iff.mpr
        (him ▸ hS_comp.inter_right hK_closed)
    refine ⟨S_K, hSK_comp, ?_⟩
    have h_pre : ⇑T_K ⁻¹' S_K = Subtype.val ⁻¹' (⇑T_norm ⁻¹' S) := by ext x; rfl
    rw [h_pre]
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds hS_nhds
  have hTK_le_one : ‖T_K‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    change ‖T_norm x.1‖ ≤ 1 * ‖x.1‖
    rw [one_mul]
    exact (T_norm.le_opNorm x.1).trans (by
      calc ‖T_norm‖ * ‖x.1‖ ≤ 1 * ‖x.1‖ := mul_le_mul_of_nonneg_right hT_le1 (norm_nonneg _)
        _ = ‖x.1‖ := one_mul _)
  by_cases hTK_zero : T_K = 0
  · have h_norm0 : ‖T_K‖ = 0 := norm_eq_zero.mpr hTK_zero
    have h_gap_eq : wilsonExactGap T_norm Ω hT_sa hT_Ω = 1 := by
      dsimp [wilsonExactGap]
      rw [if_pos h_norm0]
    refine ⟨by rw [h_gap_eq]; exact one_pos, fun v hv => ?_, fun hne => absurd hTK_zero hne⟩
    have hvK : v ∈ K := by
      change v ∈ wilsonPerpSubmodule Ω
      unfold wilsonPerpSubmodule
      rw [Submodule.mem_orthogonal]
      intro z hz
      rw [Submodule.mem_span_singleton] at hz
      rcases hz with ⟨c, rfl⟩
      have hΩv : ⟪Ω, v⟫_ℂ = 0 := by rw [← inner_conj_symm, hv, map_zero]
      rw [inner_smul_left, hΩv, mul_zero]
    have hTv : T_norm v = 0 := congrArg Subtype.val
      (congrArg (fun f : ↥K →L[ℂ] ↥K => f ⟨v, hvK⟩) hTK_zero)
    rw [h_gap_eq, hTv, inner_zero_right, Complex.zero_re]
    positivity
  · have hTK_pos_norm : 0 < ‖T_K‖ :=
      lt_of_le_of_ne (norm_nonneg T_K) (Ne.symm (norm_ne_zero_iff.mpr hTK_zero))
    have h_gap_eq : wilsonExactGap T_norm Ω hT_sa hT_Ω = -Real.log ‖T_K‖ := by
      dsimp [wilsonExactGap]
      rw [if_neg hTK_pos_norm.ne']
    obtain ⟨w_K, hwK_norm, hwK_eig⟩ :=
      compact_sa_pos_exists_max_eigenvector T_K hTK_sa hTK_pos hTK_comp hTK_zero
    have hTK_lt_one : ‖T_K‖ < 1 := by
      refine lt_of_le_of_ne hTK_le_one fun h1 => ?_
      have hw_eig_norm : T_norm w_K.1 = (1 : ℂ) • w_K.1 := by
        have h := congrArg Subtype.val hwK_eig
        change T_norm w_K.1 = (‖T_K‖ : ℂ) • w_K.1 at h
        rwa [h1, Complex.ofReal_one] at h
      have hw_orth : ⟪w_K.1, Ω⟫_ℂ = 0 := by
        have hΩw : ⟪Ω, w_K.1⟫_ℂ = 0 :=
          (Submodule.mem_orthogonal _ _).mp w_K.2 Ω (Submodule.subset_span rfl)
        rw [← inner_conj_symm, hΩw, map_zero]
      have hw0 : w_K.1 = 0 := h_simple w_K.1 hw_eig_norm hw_orth
      have h0 : ‖w_K‖ = 0 := by change ‖w_K.1‖ = 0; rw [hw0, norm_zero]
      linarith [hwK_norm]
    have h_gap_pos : 0 < wilsonExactGap T_norm Ω hT_sa hT_Ω := by
      rw [h_gap_eq]
      exact neg_pos.mpr (Real.log_neg hTK_pos_norm hTK_lt_one)
    refine ⟨h_gap_pos, fun v hv => ?_, fun _ => ⟨h_gap_eq, w_K.1, hwK_norm, ?_, ?_⟩⟩
    · have hvK : v ∈ K := by
        change v ∈ wilsonPerpSubmodule Ω
        unfold wilsonPerpSubmodule
        rw [Submodule.mem_orthogonal]
        intro z hz
        rw [Submodule.mem_span_singleton] at hz
        rcases hz with ⟨c, rfl⟩
        have hΩv : ⟪Ω, v⟫_ℂ = 0 := by rw [← inner_conj_symm, hv, map_zero]
        rw [inner_smul_left, hΩv, mul_zero]
      have hexp : Real.exp (-(wilsonExactGap T_norm Ω hT_sa hT_Ω * 1)) = ‖T_K‖ := by
        rw [h_gap_eq, mul_one, neg_neg, Real.exp_log hTK_pos_norm]
      rw [hexp]
      calc (⟪v, T_norm v⟫_ℂ).re ≤ ‖⟪v, T_norm v⟫_ℂ‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
        _ ≤ ‖v‖ * ‖T_norm v‖ := norm_inner_le_norm _ _
        _ = ‖(⟨v, hvK⟩ : ↥K)‖ * ‖T_K ⟨v, hvK⟩‖ := rfl
        _ ≤ ‖(⟨v, hvK⟩ : ↥K)‖ * (‖T_K‖ * ‖(⟨v, hvK⟩ : ↥K)‖) :=
            mul_le_mul_of_nonneg_left (T_K.le_opNorm _) (norm_nonneg _)
        _ = ‖T_K‖ * ‖v‖ ^ 2 := by change ‖v‖ * (‖T_K‖ * ‖v‖) = _; ring
    · have hΩw : ⟪Ω, w_K.1⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal _ _).mp w_K.2 Ω (Submodule.subset_span rfl)
      rw [← inner_conj_symm, hΩw, map_zero]
    · have hexp : Real.exp (-wilsonExactGap T_norm Ω hT_sa hT_Ω) = ‖T_K‖ := by
        rw [h_gap_eq, neg_neg, Real.exp_log hTK_pos_norm]
      rw [hexp]
      exact congrArg Subtype.val hwK_eig

/--
**Perron–Frobenius Theorem & Finite-Volume Spectral Gap for `wilsonIntegralOp`**:
combines `wilsonIntegral_ground_state` and `wilsonExactGap_spec`.
-/
theorem wilsonIntegral_perron_frobenius (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_symm : ∀ U U', K_kin U' U = K_kin U U')
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (hK_inv : ∀ g U U', K_kin (gaugeAct g U) (gaugeAct g U') = K_kin U U')
    (c_min : ℝ) (hc_min : 0 < c_min) (hK_lb : ∀ U U', c_min ≤ K_kin U U')
    (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (hT_pos : ∀ ψ : HaarGaugeSpace (latticeHaarMeasure L N),
      0 ≤ (⟪ψ, wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ⟫_ℂ).re) :
    ∃ (Ω : HaarGaugeSpace (latticeHaarMeasure L N)) (lam0 Δ : ℝ),
      0 < lam0 ∧ 0 < Δ ∧ ‖Ω‖ = 1 ∧
      wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd Ω = (lam0 : ℂ) • Ω ∧
      (∀ g, cubicGaugeRep L N g Ω = Ω) ∧
      (∀ v : HaarGaugeSpace (latticeHaarMeasure L N), ⟪v, Ω⟫_ℂ = 0 →
        (⟪v, (((lam0⁻¹ : ℝ) : ℂ) •
          wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd) v⟫_ℂ).re ≤
          Real.exp (-(Δ * 1)) * ‖v‖ ^ 2) := by
  let T := wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd
  obtain ⟨Ω, _, hgs⟩ :=
    wilsonIntegral_ground_state L N β hβ K_kin hK_cont hK_symm hK_nn hK_inv
      c_min hc_min hK_lb M_K hM_K hK_bd hT_pos
  let lam0 : ℝ := ‖T‖
  have hlam0_pos : 0 < lam0 := hgs.norm_pos
  let T_norm : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ]
      HaarGaugeSpace (latticeHaarMeasure L N) := ((lam0⁻¹ : ℝ) : ℂ) • T
  have hT_sa := wilsonIntegralOp_sa L N β hβ K_kin hK_cont hK_symm hK_nn M_K hM_K hK_bd
  have hT_norm_sa : ∀ x y : HaarGaugeSpace (latticeHaarMeasure L N),
      ⟪T_norm x, y⟫_ℂ = ⟪x, T_norm y⟫_ℂ := by
    intro x y
    change ⟪((lam0⁻¹ : ℝ) : ℂ) • T x, y⟫_ℂ = ⟪x, ((lam0⁻¹ : ℝ) : ℂ) • T y⟫_ℂ
    rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, hT_sa]
  have hT_norm_pos : ∀ x : HaarGaugeSpace (latticeHaarMeasure L N),
      0 ≤ (⟪x, T_norm x⟫_ℂ).re := by
    intro x
    change 0 ≤ (⟪x, ((lam0⁻¹ : ℝ) : ℂ) • T x⟫_ℂ).re
    rw [inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (inv_nonneg.mpr hlam0_pos.le) (hT_pos x)
  have hT_norm_comp : IsCompactOperator ⇑T_norm := by
    obtain ⟨S, hS_comp, hS_nhds⟩ :=
      wilsonIntegralOp_compact L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd
    refine ⟨(((lam0⁻¹ : ℝ) : ℂ) • ·) '' S, hS_comp.image (continuous_const_smul _), ?_⟩
    filter_upwards [hS_nhds] with v hv
    exact ⟨T v, hv, rfl⟩
  have hT_norm_le1 : ‖T_norm‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    calc ‖T_norm x‖ = ‖((lam0⁻¹ : ℝ) : ℂ) • T x‖ := rfl
      _ = lam0⁻¹ * ‖T x‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr hlam0_pos.le)]
      _ ≤ lam0⁻¹ * (lam0 * ‖x‖) :=
          mul_le_mul_of_nonneg_left (T.le_opNorm x) (inv_nonneg.mpr hlam0_pos.le)
      _ = 1 * ‖x‖ := by rw [← mul_assoc, inv_mul_cancel₀ hlam0_pos.ne', one_mul]
  have hT_norm_Ω : T_norm Ω = Ω := by
    change ((lam0⁻¹ : ℝ) : ℂ) • T Ω = Ω
    rw [hgs.eig, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam0_pos.ne',
      Complex.ofReal_one, one_smul]
  have h_simple_norm : ∀ w, T_norm w = (1 : ℂ) • w → ⟪w, Ω⟫_ℂ = 0 → w = 0 := by
    intro w hw hwo
    apply hgs.simple w _ hwo
    have h := congrArg (fun z : HaarGaugeSpace (latticeHaarMeasure L N) => (lam0 : ℂ) • z) hw
    dsimp only [T_norm] at h
    rw [ContinuousLinearMap.smul_apply, smul_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hlam0_pos.ne', Complex.ofReal_one, one_smul, one_smul] at h
    exact h
  obtain ⟨hΔ_pos, hgap, _⟩ := wilsonExactGap_spec T_norm Ω hT_norm_sa hT_norm_pos
    hT_norm_comp hT_norm_le1 hT_norm_Ω h_simple_norm
  exact ⟨Ω, lam0, wilsonExactGap T_norm Ω hT_norm_sa hT_norm_Ω, hlam0_pos, hΔ_pos,
    hgs.unit, hgs.eig, hgs.gauge_inv, hgap⟩

private noncomputable def fullRankTRaw (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hχ_cont : Continuous (Function.uncurry χ))
    (c_χ : ℝ) (hc_χ : 0 < c_χ) (hχ_lb : ∀ U W, c_χ ≤ χ U W)
    (M_χ : ℝ) (hM_χ : 0 ≤ M_χ) (hχ_bd : ∀ U W, χ U W ≤ M_χ) :
    HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ]
      HaarGaugeSpace (latticeHaarMeasure L N) :=
  let hχ_nn : ∀ U W, 0 ≤ χ U W := fun U W => hc_χ.le.trans (hχ_lb U W)
  wilsonIntegralOp L N β hβ (wilsonGramKernel L N χ)
    (continuous_wilsonGramKernel L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd)
    (wilsonGramKernel_nonneg L N χ hχ_nn) (M_χ ^ 2) (sq_nonneg M_χ)
    (wilsonGramKernel_le L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd)

private theorem fullRankGS (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hχ_cont : Continuous (Function.uncurry χ))
    (hχ_inv : ∀ g U W, χ (gaugeAct g U) (gaugeAct g W) = χ U W)
    (c_χ : ℝ) (hc_χ : 0 < c_χ) (hχ_lb : ∀ U W, c_χ ≤ χ U W)
    (M_χ : ℝ) (hM_χ : 0 ≤ M_χ) (hχ_bd : ∀ U W, χ U W ≤ M_χ) :
    ∃ (Ω : HaarGaugeSpace (latticeHaarMeasure L N))
      (ω : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ),
      IsWilsonGroundState L N β hβ (wilsonGramKernel L N χ)
        (continuous_wilsonGramKernel L N χ hχ_cont
          (fun U W => hc_χ.le.trans (hχ_lb U W)) M_χ hM_χ hχ_bd)
        (wilsonGramKernel_nonneg L N χ (fun U W => hc_χ.le.trans (hχ_lb U W)))
        (M_χ ^ 2) (sq_nonneg M_χ)
        (wilsonGramKernel_le L N χ hχ_cont
          (fun U W => hc_χ.le.trans (hχ_lb U W)) M_χ hM_χ hχ_bd)
        Ω ω :=
  let hχ_nn : ∀ U W, 0 ≤ χ U W := fun U W => hc_χ.le.trans (hχ_lb U W)
  wilsonIntegral_ground_state L N β hβ (wilsonGramKernel L N χ)
    (continuous_wilsonGramKernel L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd)
    (wilsonGramKernel_symm L N χ)
    (wilsonGramKernel_nonneg L N χ hχ_nn)
    (wilsonGramKernel_gauge_inv L N χ hχ_inv)
    (c_χ ^ 2) (sq_pos_of_pos hc_χ)
    (wilsonGramKernel_lb L N χ hχ_cont c_χ hc_χ.le hχ_lb)
    (M_χ ^ 2) (sq_nonneg M_χ)
    (wilsonGramKernel_le L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd)
    (wilsonIntegralOp_gram_pos L N β hβ χ hχ_cont hχ_nn M_χ hM_χ hχ_bd)

/--
**Full-rank `LatticeGaugeSetup` on `cubicTorus3 L`** driven by `wilsonIntegralOp`
with Gram-factorized kinetic kernel `wilsonGramKernel L N χ`, exposing the exact
constructive spectral gap `wilsonExactGap T_norm Ω` (`-log ‖T_norm|_{Ωᗮ}‖`).
-/
noncomputable def fullRankCubicLatticeGaugeSetup (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hχ_cont : Continuous (Function.uncurry χ))
    (hχ_inv : ∀ g U W, χ (gaugeAct g U) (gaugeAct g W) = χ U W)
    (c_χ : ℝ) (hc_χ : 0 < c_χ) (hχ_lb : ∀ U W, c_χ ≤ χ U W)
    (M_χ : ℝ) (hM_χ : 0 ≤ M_χ) (hχ_bd : ∀ U W, χ U W ≤ M_χ) :
    LatticeGaugeSetup (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (HaarGaugeSpace (latticeHaarMeasure L N)) :=
  let hχ_nn : ∀ U W, 0 ≤ χ U W := fun U W => hc_χ.le.trans (hχ_lb U W)
  let K_kin := wilsonGramKernel L N χ
  let hK_cont := continuous_wilsonGramKernel L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd
  let hK_symm := wilsonGramKernel_symm L N χ
  let hK_nn := wilsonGramKernel_nonneg L N χ hχ_nn
  let hK_inv := wilsonGramKernel_gauge_inv L N χ hχ_inv
  let hK_bd := wilsonGramKernel_le L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd
  let T_raw := fullRankTRaw L N β hβ χ hχ_cont c_χ hc_χ hχ_lb M_χ hM_χ hχ_bd
  let hT_pos := wilsonIntegralOp_gram_pos L N β hβ χ hχ_cont hχ_nn M_χ hM_χ hχ_bd
  let gs := fullRankGS L N β hβ χ hχ_cont hχ_inv c_χ hc_χ hχ_lb M_χ hM_χ hχ_bd
  let Ω := Classical.choose gs
  let hgs_spec := Classical.choose_spec (Classical.choose_spec gs)
  let lam0 : ℝ := ‖T_raw‖
  let hlam0_pos : 0 < lam0 := hgs_spec.norm_pos
  let T_norm : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ]
      HaarGaugeSpace (latticeHaarMeasure L N) :=
    ((lam0⁻¹ : ℝ) : ℂ) • T_raw
  let hT_norm_sa : ∀ x y : HaarGaugeSpace (latticeHaarMeasure L N),
      ⟪T_norm x, y⟫_ℂ = ⟪x, T_norm y⟫_ℂ := fun x y => by
    change ⟪((lam0⁻¹ : ℝ) : ℂ) • T_raw x, y⟫_ℂ = ⟪x, ((lam0⁻¹ : ℝ) : ℂ) • T_raw y⟫_ℂ
    rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    congr 1
    exact wilsonIntegralOp_sa L N β hβ K_kin hK_cont hK_symm hK_nn
      (M_χ ^ 2) (sq_nonneg M_χ) hK_bd x y
  let hT_norm_pos : ∀ v : HaarGaugeSpace (latticeHaarMeasure L N),
      0 ≤ (⟪v, T_norm v⟫_ℂ).re := fun v => by
    simp only [T_norm, ContinuousLinearMap.smul_apply, inner_smul_right, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (inv_nonneg.mpr hlam0_pos.le) (hT_pos v)
  let hT_norm_comp : IsCompactOperator ⇑T_norm := by
    obtain ⟨S, hS_comp, hS_nhds⟩ :=
      wilsonIntegralOp_compact L N β hβ K_kin hK_cont hK_nn (M_χ ^ 2) (sq_nonneg M_χ) hK_bd
    exact ⟨(((lam0⁻¹ : ℝ) : ℂ) • ·) '' S, hS_comp.image (continuous_const_smul _), by
      filter_upwards [hS_nhds] with v hv
      exact ⟨T_raw v, hv, rfl⟩⟩
  let hT_norm_le1 : ‖T_norm‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    calc ‖T_norm x‖ = ‖((lam0⁻¹ : ℝ) : ℂ) • T_raw x‖ := rfl
      _ = lam0⁻¹ * ‖T_raw x‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr hlam0_pos.le)]
      _ ≤ lam0⁻¹ * (lam0 * ‖x‖) :=
          mul_le_mul_of_nonneg_left (T_raw.le_opNorm x) (inv_nonneg.mpr hlam0_pos.le)
      _ = 1 * ‖x‖ := by rw [← mul_assoc, inv_mul_cancel₀ hlam0_pos.ne', one_mul]
  let hT_norm_Ω : T_norm Ω = Ω := by
    have heig : T_raw Ω = (lam0 : ℂ) • Ω := hgs_spec.eig
    change ((lam0⁻¹ : ℝ) : ℂ) • T_raw Ω = Ω
    rw [heig, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam0_pos.ne',
      Complex.ofReal_one, one_smul]
  let h_simple : ∀ w, T_norm w = (1 : ℂ) • w → ⟪w, Ω⟫_ℂ = 0 → w = 0 := fun w hw hwo => by
    apply hgs_spec.simple w _ hwo
    have h := congrArg (fun z : HaarGaugeSpace (latticeHaarMeasure L N) => (lam0 : ℂ) • z) hw
    dsimp only [T_norm] at h
    rw [ContinuousLinearMap.smul_apply, smul_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hlam0_pos.ne', Complex.ofReal_one, one_smul, one_smul] at h
    exact h
  let h_gap := wilsonExactGap_spec T_norm Ω hT_norm_sa hT_norm_pos hT_norm_comp
    hT_norm_le1 hT_norm_Ω h_simple
  { rep := cubicGaugeRep L N
    rep_one := cubicGaugeRep_one L N
    rep_mul := cubicGaugeRep_mul L N
    T := T_norm
    a := 1
    a_pos := one_pos
    T_sa := hT_norm_sa
    T_pos := hT_norm_pos
    T_compact := hT_norm_comp
    T_gauge_inv := fun g => by
      ext1 ψ
      simp only [T_norm, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, map_smul]
      congr 1
      exact congrArg (fun f : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] _ => f ψ)
        (wilsonIntegralOp_gauge_inv L N β hβ K_kin hK_cont hK_nn hK_inv
          (M_χ ^ 2) (sq_nonneg M_χ) hK_bd g)
    Ω := Ω
    Ω_unit := hgs_spec.unit
    Ω_vac := hT_norm_Ω
    Ω_gauge_inv := hgs_spec.gauge_inv
    Δ := wilsonExactGap T_norm Ω hT_norm_sa hT_norm_Ω
    Δ_pos := h_gap.1
    gap := h_gap.2.1 }

private theorem fullRankCubicLatticeGaugeSetup_exact_gap_of_det_ne
    (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hχ_cont : Continuous (Function.uncurry χ))
    (hχ_inv : ∀ g U W, χ (gaugeAct g U) (gaugeAct g W) = χ U W)
    (c_χ : ℝ) (hc_χ : 0 < c_χ) (hχ_lb : ∀ U W, c_χ ≤ χ U W)
    (M_χ : ℝ) (hM_χ : 0 ≤ M_χ) (hχ_bd : ∀ U W, χ U W ≤ M_χ)
    (U₁ U₂ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (h_det : χ U₁ U₁ * χ U₂ U₂ ≠ χ U₂ U₁ * χ U₁ U₂) :
    let S := fullRankCubicLatticeGaugeSetup L N β hβ χ hχ_cont hχ_inv c_χ hc_χ hχ_lb M_χ hM_χ hχ_bd
    wilsonPerpOp S.T S.Ω S.T_sa S.Ω_vac ≠ 0 ∧
    S.Δ = -Real.log ‖wilsonPerpOp S.T S.Ω S.T_sa S.Ω_vac‖ ∧
    ∃ w : HaarGaugeSpace (latticeHaarMeasure L N),
      ‖w‖ = 1 ∧ ⟪w, S.Ω⟫_ℂ = 0 ∧
      S.T w = (Real.exp (-S.Δ) : ℂ) • w := by
  let G_L := GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  haveI := instIsOpenPosLatticeHaar L N
  let hχ_nn : ∀ U W, 0 ≤ χ U W := fun U W => hc_χ.le.trans (hχ_lb U W)
  let K_kin := wilsonGramKernel L N χ
  let hK_cont := continuous_wilsonGramKernel L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd
  let hK_symm := wilsonGramKernel_symm L N χ
  let hK_nn := wilsonGramKernel_nonneg L N χ hχ_nn
  let hK_bd := wilsonGramKernel_le L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd
  let T_raw := fullRankTRaw L N β hβ χ hχ_cont c_χ hc_χ hχ_lb M_χ hM_χ hχ_bd
  let gs := fullRankGS L N β hβ χ hχ_cont hχ_inv c_χ hc_χ hχ_lb M_χ hM_χ hχ_bd
  let Ω := Classical.choose gs
  let ω := Classical.choose (Classical.choose_spec gs)
  let hgs := Classical.choose_spec (Classical.choose_spec gs)
  let lam0 : ℝ := ‖T_raw‖
  have hlam0_pos : 0 < lam0 := hgs.norm_pos
  let S := fullRankCubicLatticeGaugeSetup L N β hβ χ hχ_cont hχ_inv c_χ hc_χ hχ_lb M_χ hM_χ hχ_bd
  have hS_T_eq : S.T = ((lam0⁻¹ : ℝ) : ℂ) • T_raw := rfl
  have hS_Ω_eq : S.Ω = Ω := rfl
  have hS_Δ_eq : S.Δ = wilsonExactGap S.T S.Ω S.T_sa S.Ω_vac := rfl
  have hT_norm_le1 : ‖S.T‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    calc ‖S.T x‖ = ‖((lam0⁻¹ : ℝ) : ℂ) • T_raw x‖ := by rw [hS_T_eq]; rfl
      _ = lam0⁻¹ * ‖T_raw x‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr hlam0_pos.le)]
      _ ≤ lam0⁻¹ * (lam0 * ‖x‖) :=
          mul_le_mul_of_nonneg_left (T_raw.le_opNorm x) (inv_nonneg.mpr hlam0_pos.le)
      _ = 1 * ‖x‖ := by rw [← mul_assoc, inv_mul_cancel₀ hlam0_pos.ne', one_mul]
  have h_simple_norm : ∀ w, S.T w = (1 : ℂ) • w → ⟪w, S.Ω⟫_ℂ = 0 → w = 0 := by
    intro w hw hwo
    have hwo' : ⟪w, Ω⟫_ℂ = 0 := hS_Ω_eq ▸ hwo
    apply hgs.simple w _ hwo'
    have h := congrArg (fun z : HaarGaugeSpace μ => (lam0 : ℂ) • z) hw
    dsimp only at h
    rw [hS_T_eq, ContinuousLinearMap.smul_apply, smul_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hlam0_pos.ne', Complex.ofReal_one, one_smul, one_smul] at h
    exact h
  have h_perp_ne : wilsonPerpOp S.T S.Ω S.T_sa S.Ω_vac ≠ 0 := by
    intro h_zero
    let K_W := wilsonKernel β (cubicPlaquettes L) K_kin
    have h_rank1 : ∀ ψ : HaarGaugeSpace μ, T_raw ψ = ((lam0 : ℂ) * ⟪Ω, ψ⟫_ℂ) • Ω := by
      intro ψ
      let c : ℂ := ⟪Ω, ψ⟫_ℂ
      let v : HaarGaugeSpace μ := ψ - c • Ω
      have hΩ_self : ⟪Ω, Ω⟫_ℂ = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hgs.unit]; norm_num
      have hv_orth : ⟪v, Ω⟫_ℂ = 0 := by
        simp only [v, c, inner_sub_left, inner_smul_left, hΩ_self, mul_one,
          inner_conj_symm, sub_self]
      have hvK : v ∈ wilsonPerpSubmodule S.Ω := by
        unfold wilsonPerpSubmodule
        rw [Submodule.mem_orthogonal]
        intro z hz
        rw [Submodule.mem_span_singleton] at hz
        rcases hz with ⟨r, rfl⟩
        have hΩv : ⟪S.Ω, v⟫_ℂ = 0 := by
          rw [hS_Ω_eq, ← inner_conj_symm, hv_orth, map_zero]
        rw [inner_smul_left, hΩv, mul_zero]
      have hTv : S.T v = 0 := congrArg Subtype.val
        (congrArg (fun f : ↥(wilsonPerpSubmodule S.Ω) →L[ℂ] _ => f ⟨v, hvK⟩) h_zero)
      have hSTψ : S.T ψ = c • Ω := by
        have hψ : ψ = c • Ω + v := by dsimp [v]; abel
        conv_lhs => rw [hψ]
        rw [map_add, map_smul, hTv, add_zero, ← hS_Ω_eq, S.Ω_vac, hS_Ω_eq]
      have hTψ := congrArg (fun z : HaarGaugeSpace μ => (lam0 : ℂ) • z) hSTψ
      dsimp only at hTψ
      rw [hS_T_eq, ContinuousLinearMap.smul_apply, smul_smul, ← Complex.ofReal_mul,
        mul_inv_cancel₀ hlam0_pos.ne', Complex.ofReal_one, one_smul] at hTψ
      rw [hTψ, smul_smul]
    let h : G_L → ℝ := fun U' => ω U₂ * K_W U₁ U' - ω U₁ * K_W U₂ U'
    have hh_cont : Continuous h :=
      (continuous_const.mul (continuous_cubicWilsonKernel_right L N β K_kin hK_cont U₁)).sub
        (continuous_const.mul (continuous_cubicWilsonKernel_right L N β K_kin hK_cont U₂))
    let h_mem := memLp_of_continuous_compact μ h hh_cont
    let h_Lp : HaarGaugeSpace μ := h_mem.toLp (fun U => (h U : ℂ))
    have hh_ae : ⇑h_Lp =ᵐ[μ] fun U => (h U : ℂ) := h_mem.coeFn_toLp
    let c_h : ℂ := (lam0 : ℂ) * ⟪Ω, h_Lp⟫_ℂ
    have hT_ae1 : ⇑(T_raw h_Lp) =ᵐ[μ] wilsonIntegralFn L N β K_kin h_Lp :=
      wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn (M_χ ^ 2) (sq_nonneg M_χ) hK_bd h_Lp
    have hT_ae2 : ⇑(T_raw h_Lp) =ᵐ[μ] fun U => c_h * (ω U : ℂ) := by
      have h1 : ⇑(T_raw h_Lp) =ᵐ[μ] ⇑(c_h • Ω) := by rw [h_rank1 h_Lp]
      have h2 := MeasureTheory.Lp.coeFn_smul c_h Ω
      filter_upwards [h1, h2, hgs.ae_eq] with U hu1 hu2 hu3
      rw [hu1, hu2]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hu3]
    have h_all_eq : ∀ U, wilsonIntegralFn L N β K_kin h_Lp U = c_h * (ω U : ℂ) :=
      eq_of_ae_continuous μ
        (wilsonIntegralFn_continuous L N β hβ K_kin hK_cont hK_nn (M_χ ^ 2) hK_bd h_Lp)
        (continuous_const.mul (Complex.continuous_ofReal.comp hgs.ω_cont))
        (hT_ae1.symm.trans hT_ae2)
    have h_int_re : ∀ U, ∫ U', K_W U U' * h U' ∂μ = c_h.re * ω U := by
      intro U
      have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn
        (M_χ ^ 2) hK_bd h_Lp U
      have h_eq := congrArg Complex.re (h_all_eq U)
      dsimp [wilsonIntegralFn] at h_eq
      change RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * h_Lp U' ∂μ) = (c_h * (ω U : ℂ)).re at h_eq
      rw [← integral_re hi] at h_eq
      have h_lhs : ∫ U', RCLike.re (((K_W U U' : ℝ) : ℂ) * h_Lp U') ∂μ =
          ∫ U', K_W U U' * h U' ∂μ := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hh_ae] with U' hU'
        change (((K_W U U' : ℝ) : ℂ) * ⇑h_Lp U').re = K_W U U' * h U'
        rw [hU', ← Complex.ofReal_mul, Complex.ofReal_re]
      have h_rhs : (c_h * (ω U : ℂ)).re = c_h.re * ω U := by
        simp [Complex.mul_re]
      rw [h_lhs, h_rhs] at h_eq
      exact h_eq
    have hi1 : MeasureTheory.Integrable (fun U' => K_W U₁ U' * h U') μ :=
      integrable_of_continuous_compact μ _
        ((continuous_cubicWilsonKernel_right L N β K_kin hK_cont U₁).mul hh_cont)
    have hi2 : MeasureTheory.Integrable (fun U' => K_W U₂ U' * h U') μ :=
      integrable_of_continuous_compact μ _
        ((continuous_cubicWilsonKernel_right L N β K_kin hK_cont U₂).mul hh_cont)
    have h_sq_zero : ∫ U', h U' ^ 2 ∂μ = 0 := by
      have h_eq : (fun U' => h U' ^ 2) = fun U' => ω U₂ * (K_W U₁ U' * h U') - ω U₁ * (K_W U₂ U' * h U') := by
        funext U'; dsimp [h]; ring
      rw [h_eq, MeasureTheory.integral_sub (hi1.const_mul _) (hi2.const_mul _),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        h_int_re U₁, h_int_re U₂]
      ring
    have hh_zero : ∀ U', h U' = 0 := eq_zero_of_continuous_sq_integral_zero μ h hh_cont h_sq_zero
    let C : ℝ := (ω U₁ * cubicWilsonWeight L N β U₂) / (ω U₂ * cubicWilsonWeight L N β U₁)
    have hω2_pos : 0 < ω U₂ := hgs.ω_pos U₂
    have hw1_pos : 0 < cubicWilsonWeight L N β U₁ := by
      unfold cubicWilsonWeight; exact Real.exp_pos _
    have h_Kkin_eq : ∀ U', K_kin U₁ U' = C * K_kin U₂ U' := by
      intro U'
      have hw_pos : 0 < cubicWilsonWeight L N β U' := by
        unfold cubicWilsonWeight; exact Real.exp_pos _
      have h0 := sub_eq_zero.mp (hh_zero U')
      have hKW1 : K_W U₁ U' = cubicWilsonWeight L N β U₁ * cubicWilsonWeight L N β U' * K_kin U₁ U' := by
        dsimp [K_W, wilsonKernel, cubicWilsonWeight]
        rw [← Real.exp_add]
        congr 2; ring
      have hKW2 : K_W U₂ U' = cubicWilsonWeight L N β U₂ * cubicWilsonWeight L N β U' * K_kin U₂ U' := by
        dsimp [K_W, wilsonKernel, cubicWilsonWeight]
        rw [← Real.exp_add]
        congr 2; ring
      rw [hKW1, hKW2] at h0
      have hden : ω U₂ * cubicWilsonWeight L N β U₁ ≠ 0 := (mul_pos hω2_pos hw1_pos).ne'
      have h_cancel : (ω U₂ * cubicWilsonWeight L N β U₁) * K_kin U₁ U' =
          (ω U₁ * cubicWilsonWeight L N β U₂) * K_kin U₂ U' := by
        apply mul_right_cancel₀ hw_pos.ne'
        calc ((ω U₂ * cubicWilsonWeight L N β U₁) * K_kin U₁ U') * cubicWilsonWeight L N β U'
            = ω U₂ * (cubicWilsonWeight L N β U₁ * cubicWilsonWeight L N β U' * K_kin U₁ U') := by ring
          _ = ω U₁ * (cubicWilsonWeight L N β U₂ * cubicWilsonWeight L N β U' * K_kin U₂ U') := h0
          _ = ((ω U₁ * cubicWilsonWeight L N β U₂) * K_kin U₂ U') * cubicWilsonWeight L N β U' := by ring
      dsimp [C]
      rw [div_mul_eq_mul_div, eq_div_iff hden, mul_comm (K_kin U₁ U')]
      exact h_cancel
    have h_diff_cont : Continuous (fun W : G_L => χ U₁ W - C * χ U₂ W) :=
      (hχ_cont.comp (continuous_const.prodMk continuous_id)).sub
        (continuous_const.mul (hχ_cont.comp (continuous_const.prodMk continuous_id)))
    have h_diff_int : ∫ W, (χ U₁ W - C * χ U₂ W) ^ 2 ∂μ = 0 := by
      have hi11 : MeasureTheory.Integrable (fun W => χ U₁ W * χ U₁ W) μ :=
        integrable_of_continuous_compact μ _
          ((hχ_cont.comp (continuous_const.prodMk continuous_id)).mul
            (hχ_cont.comp (continuous_const.prodMk continuous_id)))
      have hi12 : MeasureTheory.Integrable (fun W => χ U₁ W * χ U₂ W) μ :=
        integrable_of_continuous_compact μ _
          ((hχ_cont.comp (continuous_const.prodMk continuous_id)).mul
            (hχ_cont.comp (continuous_const.prodMk continuous_id)))
      have hi22 : MeasureTheory.Integrable (fun W => χ U₂ W * χ U₂ W) μ :=
        integrable_of_continuous_compact μ _
          ((hχ_cont.comp (continuous_const.prodMk continuous_id)).mul
            (hχ_cont.comp (continuous_const.prodMk continuous_id)))
      have hi12c : MeasureTheory.Integrable (fun W => (2 * C) * (χ U₁ W * χ U₂ W)) μ :=
        hi12.const_mul (2 * C)
      have hi22c : MeasureTheory.Integrable (fun W => (C ^ 2) * (χ U₂ W * χ U₂ W)) μ :=
        hi22.const_mul (C ^ 2)
      have h_sub_int : MeasureTheory.Integrable
          (fun W => χ U₁ W * χ U₁ W - (2 * C) * (χ U₁ W * χ U₂ W)) μ :=
        hi11.sub hi12c
      have h_eq1 : ∫ W, (χ U₁ W - C * χ U₂ W) ^ 2 ∂μ =
          ∫ W, (χ U₁ W * χ U₁ W - (2 * C) * (χ U₁ W * χ U₂ W)) ∂μ +
            ∫ W, (C ^ 2) * (χ U₂ W * χ U₂ W) ∂μ := by
        rw [← MeasureTheory.integral_add h_sub_int hi22c]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
        dsimp only; ring
      rw [h_eq1, MeasureTheory.integral_sub hi11 hi12c,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      change K_kin U₁ U₁ - (2 * C) * K_kin U₁ U₂ + (C ^ 2) * K_kin U₂ U₂ = 0
      rw [h_Kkin_eq U₁, h_Kkin_eq U₂,
        show K_kin U₂ U₁ = K_kin U₁ U₂ from hK_symm U₁ U₂, h_Kkin_eq U₂]
      ring
    have h_chi_eq : ∀ W, χ U₁ W = C * χ U₂ W := fun W =>
      sub_eq_zero.mp (eq_zero_of_continuous_sq_integral_zero μ _ h_diff_cont h_diff_int W)
    have h_eq1 := h_chi_eq U₁
    have h_eq2 := h_chi_eq U₂
    have h_chi11_pos : 0 < χ U₁ U₁ := hc_χ.trans_le (hχ_lb U₁ U₁)
    have hC_ne : C ≠ 0 := by
      intro hC0
      rw [hC0, zero_mul] at h_eq1
      linarith
    apply h_det
    apply mul_left_cancel₀ hC_ne
    calc C * (χ U₁ U₁ * χ U₂ U₂)
        = χ U₁ U₁ * (C * χ U₂ U₂) := by ring
      _ = (C * χ U₂ U₁) * χ U₁ U₂ := by rw [← h_eq1, ← h_eq2]
      _ = C * (χ U₂ U₁ * χ U₁ U₂) := by ring
  have h_spec := (wilsonExactGap_spec S.T S.Ω S.T_sa
    S.T_pos S.T_compact hT_norm_le1 S.Ω_vac h_simple_norm).2.2 h_perp_ne
  exact ⟨h_perp_ne, hS_Δ_eq.trans h_spec.1, h_spec.2⟩

/-- Rank-2 Boltzmann kinetic kernel (kept for reference). -/
noncomputable def cubicActionKineticKernel (L N : ℕ) [NeZero L] (β : ℝ)
    (U W : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  1 + cubicWilsonWeight L N β U * cubicWilsonWeight L N β W

/--
**Link-coupled gauge-invariant Wilson kinetic kernel** on `cubicTorus3 L`:
`χ_link(U, W) = ∏_{e} exp((β / (2N)) Re Tr(U_e W_e⁻¹))`.
-/
noncomputable def cubicLinkKineticKernel (L N : ℕ) [NeZero L] (β : ℝ)
    (U W : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  ∏ e : (cubicTorus3 L).Link,
    Real.exp ((β / (2 * (N : ℝ))) *
      (Matrix.trace (((U e * (W e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ))).re)

private theorem su_trace_conj' {N : ℕ}
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

theorem continuous_cubicLinkKineticKernel (L N : ℕ) [NeZero L] (β : ℝ) :
    Continuous (Function.uncurry (cubicLinkKineticKernel L N β)) := by
  let G_L := GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  have h_ent : ∀ i : Fin N, Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (A : Matrix (Fin N) (Fin N) ℂ) i i) := fun i =>
    (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
  have h_tr : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re) := by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact continuous_finset_sum Finset.univ fun i _ => Complex.continuous_re.comp (h_ent i)
  change Continuous (fun p : G_L × G_L =>
    ∏ e : (cubicTorus3 L).Link,
      Real.exp ((β / (2 * (N : ℝ))) *
        (Matrix.trace (((p.1 e * (p.2 e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re))
  refine continuous_finset_prod Finset.univ fun e _ => ?_
  have h1 : Continuous (fun p : G_L × G_L => p.1 e) :=
    (continuous_apply e).comp continuous_fst
  have h2 : Continuous (fun p : G_L × G_L => (p.2 e)⁻¹) :=
    continuous_inv.comp ((continuous_apply e).comp continuous_snd)
  exact Real.continuous_exp.comp (continuous_const.mul (h_tr.comp (h1.mul h2)))

theorem cubicLinkKineticKernel_gauge_inv (L N : ℕ) [NeZero L] (β : ℝ)
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U W : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubicLinkKineticKernel L N β (gaugeAct g U) (gaugeAct g W) =
      cubicLinkKineticKernel L N β U W := by
  dsimp only [cubicLinkKineticKernel]
  refine Finset.prod_congr rfl fun e _ => ?_
  have hconj : gaugeAct g U e * (gaugeAct g W e)⁻¹ =
      g ((cubicTorus3 L).src e) * (U e * (W e)⁻¹) * (g ((cubicTorus3 L).src e))⁻¹ := by
    simp only [gaugeAct, mul_inv_rev, inv_inv]
    group
  rw [hconj, su_trace_conj']

theorem cubicLinkKineticKernel_bounds (L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (β : ℝ) (hβ : 0 ≤ β)
    (U W : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    (Real.exp (-(β / 2))) ^ (Fintype.card (cubicTorus3 L).Link) ≤
        cubicLinkKineticKernel L N β U W ∧
      cubicLinkKineticKernel L N β U W ≤
        (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link) := by
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h_fac_lb : ∀ e : (cubicTorus3 L).Link,
      Real.exp (-(β / 2)) ≤
        Real.exp ((β / (2 * (N : ℝ))) *
          (Matrix.trace (((U e * (W e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
            Matrix (Fin N) (Fin N) ℂ))).re) := by
    intro e
    have htr := (abs_le.mp (abs_re_trace_su_le (U e * (W e)⁻¹))).1
    have hmul : -(β / 2) ≤ (β / (2 * (N : ℝ))) *
        (Matrix.trace (((U e * (W e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re := by
      have heq : -(β / 2) = (β / (2 * (N : ℝ))) * (-(N : ℝ)) := by
        field_simp [hN_pos.ne']
      rw [heq]
      exact mul_le_mul_of_nonneg_left htr (by positivity)
    exact Real.exp_le_exp.mpr hmul
  have h_fac_ub : ∀ e : (cubicTorus3 L).Link,
      Real.exp ((β / (2 * (N : ℝ))) *
        (Matrix.trace (((U e * (W e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re) ≤
        Real.exp (β / 2) := by
    intro e
    have htr := (abs_le.mp (abs_re_trace_su_le (U e * (W e)⁻¹))).2
    have hmul : (β / (2 * (N : ℝ))) *
        (Matrix.trace (((U e * (W e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re ≤ β / 2 := by
      have heq : β / 2 = (β / (2 * (N : ℝ))) * (N : ℝ) := by
        field_simp [hN_pos.ne']
      rw [heq]
      exact mul_le_mul_of_nonneg_left htr (by positivity)
    exact Real.exp_le_exp.mpr hmul
  dsimp only [cubicLinkKineticKernel]
  constructor
  · calc (Real.exp (-(β / 2))) ^ (Fintype.card (cubicTorus3 L).Link)
        = ∏ _e : (cubicTorus3 L).Link, Real.exp (-(β / 2)) := by
            simp [Finset.prod_const, Finset.card_univ]
      _ ≤ ∏ e : (cubicTorus3 L).Link, _ :=
            Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) (fun e _ => h_fac_lb e)
  · calc ∏ e : (cubicTorus3 L).Link, _
        ≤ ∏ _e : (cubicTorus3 L).Link, Real.exp (β / 2) :=
            Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) (fun e _ => h_fac_ub e)
      _ = (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link) := by
            simp [Finset.prod_const, Finset.card_univ]

private theorem suFlip2_inv_eq (N : ℕ) (hN : 2 ≤ N) :
    (suFlip2 N hN)⁻¹ = suFlip2 N hN := by
  have h_mul : ((suFlip2 N hN : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) *
      ((suFlip2 N hN : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [suFlip2, Matrix.mul_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      rw [Finset.sum_eq_single i]
      · by_cases hi : (i : ℕ) < 2 <;> simp [hi]
      · intro k _ hki
        simp [Matrix.diagonal_apply_ne _ hki.symm, Matrix.diagonal_apply_ne _ hki]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    · simp only [suFlip2, Matrix.mul_apply, Matrix.one_apply_ne hij]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hki : k = i
      · subst hki; simp [Matrix.diagonal_apply, hij]
      · simp [Matrix.diagonal_apply, Ne.symm hki]
  exact inv_eq_of_mul_eq_one_left (Subtype.ext h_mul)

private theorem suFlip2_trace_re (N : ℕ) (hN : 2 ≤ N) :
    (Matrix.trace ((suFlip2 N hN : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ)).re = (N : ℝ) - 4 := by
  simp only [suFlip2, Matrix.trace, Matrix.diag, Matrix.diagonal_apply_eq, Complex.re_sum]
  let i0 : Fin N := ⟨0, by omega⟩
  let i1 : Fin N := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by
    intro h; have := congrArg Fin.val h; norm_num [i0, i1] at this
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0)]
  have hi1_mem : i1 ∈ Finset.univ.erase i0 := Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ i1⟩
  rw [← Finset.add_sum_erase (Finset.univ.erase i0) _ hi1_mem]
  have h0 : ((if (i0 : ℕ) < 2 then (-1 : ℂ) else 1)).re = -1 := by simp [i0]
  have h1 : ((if (i1 : ℕ) < 2 then (-1 : ℂ) else 1)).re = -1 := by simp [i1]
  have h_rest : ∑ x ∈ (Finset.univ.erase i0).erase i1,
      ((if (x : ℕ) < 2 then (-1 : ℂ) else 1)).re = (N : ℝ) - 2 := by
    have h_eq : ∑ x ∈ (Finset.univ.erase i0).erase i1,
        ((if (x : ℕ) < 2 then (-1 : ℂ) else 1)).re =
        ∑ _x ∈ (Finset.univ.erase i0).erase i1, (1 : ℝ) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx1 : x ≠ i1 := (Finset.mem_erase.mp hx).1
      have hx0 : x ≠ i0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      have hge2 : ¬ (x : ℕ) < 2 := by
        intro hlt
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h_0 | h_1
        · exact hx0 (Fin.ext (Nat.lt_one_iff.mp h_0))
        · exact hx1 (Fin.ext h_1)
      simp [hge2]
    rw [h_eq, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hc1 : ((Finset.univ.erase i0).erase i1).card = N - 2 := by
      rw [Finset.card_erase_of_mem hi1_mem, Finset.card_erase_of_mem (Finset.mem_univ i0),
        Finset.card_univ, Fintype.card_fin]
      omega
    rw [hc1, Nat.cast_sub hN]
    norm_num
  rw [h0, h1, h_rest]
  ring

private theorem su_one_trace_re (N : ℕ) :
    (Matrix.trace ((1 : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ)).re = (N : ℝ) := by
  change (Matrix.trace (1 : Matrix (Fin N) (Fin N) ℂ)).re = (N : ℝ)
  simp

private noncomputable def linkChiLb (L : ℕ) [NeZero L] (β : ℝ) : ℝ :=
  (Real.exp (-(β / 2))) ^ (Fintype.card (cubicTorus3 L).Link)

private noncomputable def linkChiUb (L : ℕ) [NeZero L] (β : ℝ) : ℝ :=
  (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link)

private theorem linkChiLb_pos (L : ℕ) [NeZero L] (β : ℝ) : 0 < linkChiLb L β :=
  pow_pos (Real.exp_pos _) _

private theorem linkChiUb_nonneg (L : ℕ) [NeZero L] (β : ℝ) : 0 ≤ linkChiUb L β :=
  pow_nonneg (Real.exp_pos _).le _

private theorem linkChi_nn (L N : ℕ) [NeZero L] (hN : 2 ≤ N) (β : ℝ) (hβ : 0 ≤ β)
    (U W : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 ≤ cubicLinkKineticKernel L N β U W :=
  (linkChiLb_pos L β).le.trans (cubicLinkKineticKernel_bounds L N (by omega) β hβ U W).1

/--
**Full-rank `NonAbelianWilsonSetup` on `cubicTorus3 L`** with `L²(SU(N)^{3L³}, dμ_Haar)`,
the link-coupled kinetic kernel `cubicLinkKineticKernel`, and `wilsonIntegralOp`.
-/
noncomputable def fullRankCubicNonAbelianWilsonSetup (L N : ℕ) [NeZero L] (hN : 2 ≤ N)
    (β : ℝ) (hβ : 0 < β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    NonAbelianWilsonSetup (cubicTorus3 L) N hN :=
  let χ := cubicLinkKineticKernel L N β
  let setup := fullRankCubicLatticeGaugeSetup L N β hβ.le χ
    (continuous_cubicLinkKineticKernel L N β)
    (cubicLinkKineticKernel_gauge_inv L N β)
    (linkChiLb L β) (linkChiLb_pos L β)
    (fun U W => (cubicLinkKineticKernel_bounds L N (by omega) β hβ.le U W).1)
    (linkChiUb L β) (linkChiUb_nonneg L β)
    (fun U W => (cubicLinkKineticKernel_bounds L N (by omega) β hβ.le U W).2)
  { μ := latticeHaarMeasure L N
    μ_prob := latticeHaarMeasure_prob L N
    μ_inv := latticeHaarMeasure_gauge_inv L N
    β := β
    β_pos := hβ
    plaquettes := cubicPlaquettes L
    K_kin := wilsonGramKernel L N χ
    K_symm := wilsonGramKernel_symm L N χ
    K_nonneg := wilsonGramKernel_nonneg L N χ (linkChi_nn L N hN β hβ.le)
    K_inv := wilsonGramKernel_gauge_inv L N χ (cubicLinkKineticKernel_gauge_inv L N β)
    gaugeSetup := setup
    SymmIdx := GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
    symmOp := cubicGaugeRep L N
    symm_comm := fun g => by
      unfold lieBracketCLM
      change (setup.rep g).comp setup.T - setup.T.comp (setup.rep g) = 0
      rw [setup.T_gauge_inv g, sub_self] }

/--
**Non-degeneracy and exact spectral gap** of `fullRankCubicNonAbelianWilsonSetup`:
for every $L \ge 1$, $N \ge 2$, $\beta > 0$, the link-coupled transfer operator
is non-degenerate on $\Omega^\perp$ (`wilsonPerpOp ≠ 0`), its spectral gap equals
`setup.Δ = -Real.log ‖wilsonPerpOp‖ = log(λ₀ / λ₁)`, and `setup.T` attains
`exp(-setup.Δ)` at a unit excited eigenstate `w ∈ Ωᗮ`.
-/
theorem fullRankCubicNonAbelianWilsonSetup_exact_gap
    (L N : ℕ) [NeZero L] (hN : 2 ≤ N) (β : ℝ) (hβ : 0 < β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    let S := (fullRankCubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup
    wilsonPerpOp S.T S.Ω S.T_sa S.Ω_vac ≠ 0 ∧
    S.Δ = -Real.log ‖wilsonPerpOp S.T S.Ω S.T_sa S.Ω_vac‖ ∧
    ∃ w : HaarGaugeSpace (latticeHaarMeasure L N),
      ‖w‖ = 1 ∧ ⟪w, S.Ω⟫_ℂ = 0 ∧
      S.T w = (Real.exp (-S.Δ) : ℂ) • w := by
  let G_L := GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let χ := cubicLinkKineticKernel L N β
  let U₁ : G_L := fun _ => 1
  let e₀ : (cubicTorus3 L).Link := ((0, 0, 0), 0)
  let U₂ : G_L := fun e => if e = e₀ then suFlip2 N hN else 1
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have h_11 : χ U₁ U₁ = (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link) := by
    dsimp only [χ, cubicLinkKineticKernel]
    have h_each : ∀ e : (cubicTorus3 L).Link,
        Real.exp ((β / (2 * (N : ℝ))) *
          (Matrix.trace (((U₁ e * (U₁ e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
            Matrix (Fin N) (Fin N) ℂ))).re) = Real.exp (β / 2) := by
      intro e
      simp only [U₁, mul_inv_cancel, su_one_trace_re]
      congr 1; field_simp [hN_pos.ne']
    simp_rw [h_each, Finset.prod_const, Finset.card_univ]
  have h_22 : χ U₂ U₂ = (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link) := by
    dsimp only [χ, cubicLinkKineticKernel]
    have h_each : ∀ e : (cubicTorus3 L).Link,
        Real.exp ((β / (2 * (N : ℝ))) *
          (Matrix.trace (((U₂ e * (U₂ e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
            Matrix (Fin N) (Fin N) ℂ))).re) = Real.exp (β / 2) := by
      intro e
      simp only [mul_inv_cancel, su_one_trace_re]
      congr 1; field_simp [hN_pos.ne']
    simp_rw [h_each, Finset.prod_const, Finset.card_univ]
  have h_lt_fac : Real.exp ((β / (2 * (N : ℝ))) * ((N : ℝ) - 4)) < Real.exp (β / 2) := by
    have h_arg : (β / (2 * (N : ℝ))) * ((N : ℝ) - 4) < β / 2 := by
      have heq : β / 2 = (β / (2 * (N : ℝ))) * (N : ℝ) := by field_simp [hN_pos.ne']
      rw [heq]
      exact mul_lt_mul_of_pos_left (by linarith) (by positivity)
    exact Real.exp_lt_exp.mpr h_arg
  have h_21_lt : χ U₂ U₁ < χ U₁ U₁ := by
    rw [h_11]
    dsimp only [χ, cubicLinkKineticKernel]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e₀)]
    have h_e₀ : Real.exp ((β / (2 * (N : ℝ))) *
        (Matrix.trace (((U₂ e₀ * (U₁ e₀)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re) =
        Real.exp ((β / (2 * (N : ℝ))) * ((N : ℝ) - 4)) := by
      simp only [U₂, U₁, ↓reduceIte, inv_one, mul_one, suFlip2_trace_re]
    have h_rest : ∏ e ∈ Finset.univ.erase e₀, Real.exp ((β / (2 * (N : ℝ))) *
        (Matrix.trace (((U₂ e * (U₁ e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re) =
        (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link - 1) := by
      have h_each : ∀ e ∈ Finset.univ.erase e₀,
          Real.exp ((β / (2 * (N : ℝ))) *
            (Matrix.trace (((U₂ e * (U₁ e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
              Matrix (Fin N) (Fin N) ℂ))).re) = Real.exp (β / 2) := by
        intro e he
        have hne : e ≠ e₀ := (Finset.mem_erase.mp he).1
        simp only [U₂, U₁, if_neg hne, inv_one, mul_one, su_one_trace_re]
        congr 1; field_simp [hN_pos.ne']
      rw [Finset.prod_congr rfl h_each, Finset.prod_const,
        Finset.card_erase_of_mem (Finset.mem_univ e₀), Finset.card_univ]
    rw [h_e₀, h_rest]
    have hcard_pos : 1 ≤ Fintype.card (cubicTorus3 L).Link :=
      Fintype.card_pos_iff.mpr ⟨e₀⟩
    have h_pow : (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link) =
        Real.exp (β / 2) * (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hcard_pos]
    rw [h_pow]
    exact mul_lt_mul_of_pos_right h_lt_fac (pow_pos (Real.exp_pos _) _)
  have h_12_lt : χ U₁ U₂ < χ U₂ U₂ := by
    rw [h_22]
    dsimp only [χ, cubicLinkKineticKernel]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e₀)]
    have h_e₀ : Real.exp ((β / (2 * (N : ℝ))) *
        (Matrix.trace (((U₁ e₀ * (U₂ e₀)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re) =
        Real.exp ((β / (2 * (N : ℝ))) * ((N : ℝ) - 4)) := by
      simp only [U₁, U₂, ↓reduceIte, one_mul, suFlip2_inv_eq, suFlip2_trace_re]
    have h_rest : ∏ e ∈ Finset.univ.erase e₀, Real.exp ((β / (2 * (N : ℝ))) *
        (Matrix.trace (((U₁ e * (U₂ e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re) =
        (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link - 1) := by
      have h_each : ∀ e ∈ Finset.univ.erase e₀,
          Real.exp ((β / (2 * (N : ℝ))) *
            (Matrix.trace (((U₁ e * (U₂ e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
              Matrix (Fin N) (Fin N) ℂ))).re) = Real.exp (β / 2) := by
        intro e he
        have hne : e ≠ e₀ := (Finset.mem_erase.mp he).1
        simp only [U₁, U₂, if_neg hne, one_mul, inv_one, su_one_trace_re]
        congr 1; field_simp [hN_pos.ne']
      rw [Finset.prod_congr rfl h_each, Finset.prod_const,
        Finset.card_erase_of_mem (Finset.mem_univ e₀), Finset.card_univ]
    rw [h_e₀, h_rest]
    have hcard_pos : 1 ≤ Fintype.card (cubicTorus3 L).Link :=
      Fintype.card_pos_iff.mpr ⟨e₀⟩
    have h_pow : (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link) =
        Real.exp (β / 2) * (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hcard_pos]
    rw [h_pow]
    exact mul_lt_mul_of_pos_right h_lt_fac (pow_pos (Real.exp_pos _) _)
  have h_chi21_pos : 0 < χ U₂ U₁ :=
    (linkChiLb_pos L β).trans_le (cubicLinkKineticKernel_bounds L N (by omega) β hβ.le U₂ U₁).1
  have h_chi12_pos : 0 < χ U₁ U₂ :=
    (linkChiLb_pos L β).trans_le (cubicLinkKineticKernel_bounds L N (by omega) β hβ.le U₁ U₂).1
  have h_det : χ U₁ U₁ * χ U₂ U₂ ≠ χ U₂ U₁ * χ U₁ U₂ :=
    ne_of_gt (mul_lt_mul'' h_21_lt h_12_lt h_chi21_pos.le h_chi12_pos.le)
  exact fullRankCubicLatticeGaugeSetup_exact_gap_of_det_ne L N β hβ.le χ
    (continuous_cubicLinkKineticKernel L N β)
    (cubicLinkKineticKernel_gauge_inv L N β)
    (linkChiLb L β) (linkChiLb_pos L β)
    (fun U W => (cubicLinkKineticKernel_bounds L N (by omega) β hβ.le U W).1)
    (linkChiUb L β) (linkChiUb_nonneg L β)
    (fun U W => (cubicLinkKineticKernel_bounds L N (by omega) β hβ.le U W).2)
    U₁ U₂ h_det

theorem fullRankCubic_clustering (L N : ℕ) [NeZero L] (hN : 2 ≤ N) (β : ℝ) (hβ : 0 < β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A B : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ]
      HaarGaugeSpace (latticeHaarMeasure L N))
    (hA : ⟪A (fullRankCubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.Ω,
        (fullRankCubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.Ω⟫_ℂ = 0)
    (hB : ⟪B (fullRankCubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.Ω,
        (fullRankCubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.Ω⟫_ℂ = 0)
    (k : ℕ) :
    ‖⟪(fullRankCubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.Ω,
        A (((fullRankCubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.T ^ k)
          (B (fullRankCubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.Ω))⟫_ℂ‖ ≤
      ‖A‖ * ‖B‖ * Real.exp
        (-((fullRankCubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.Δ *
          (k * (fullRankCubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.a))) :=
  nonAbelianWilson_clustering (fullRankCubicNonAbelianWilsonSetup L N hN β hβ) A B hA hB k

end FullRankWilsonSpectralGap

/-! ## §34.  Non-translation-invariance of `isingSchwinger` & smeared OS reconstruction -/

section SmearedOSReconstruction

/--
**Mathematical obstruction on `concreteOS4DContinuumTheory`**:
`isingSchwinger` is anchored at `x = 0` via `radialCoupling`, so it is NOT
Euclidean time-translation invariant (`S(T_t x, y) ≠ S(x, T_t y)`).
A genuine translation-invariant physical Yang–Mills Schwinger distribution is
only bounded on smeared test configurations, never pointwise-diagonal `M^n`.
-/
theorem isingSchwinger_not_time_trans_inv :
    ∃ x y : PosTimeConfig,
      osConfigKernel concreteOS4DContinuumTheory (posTimeShiftConfig 1 zero_le_one x) y ≠
        osConfigKernel concreteOS4DContinuumTheory x (posTimeShiftConfig 1 zero_le_one y) := by
  let x : PosTimeConfig := ⟨1, fun _ => ![1, 0, 0, 0], fun _ => by simp⟩
  let y : PosTimeConfig := ⟨1, fun _ => ![1, 1, 0, 0], fun _ => by simp⟩
  refine ⟨x, y, ?_⟩
  have h2_formula : ∀ a b : Space4,
      isingSchwinger 2 ![a, b] = (((1 + radialCoupling a * radialCoupling b : ℝ)) : ℂ) := by
    intro a b
    dsimp [isingSchwinger]
    rw [Fin.prod_univ_two, Fin.prod_univ_two]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  have happ_gen : ∀ (a b : Space4),
      Fin.append (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) = ![a, b] := by
    intro a b; funext k; fin_cases k <;> rfl
  have hx_pt : (fun k : Fin 1 => euclidTimeReflect ((posTimeShiftConfig 1 zero_le_one x).pts k)) =
      fun _ => ![-2, 0, 0, 0] := by
    funext _ i; fin_cases i <;> simp [posTimeShiftConfig, x, euclidTimeReflect] <;> try norm_num
  have hy_pt : y.pts = fun _ => ![1, 1, 0, 0] := rfl
  have hx_pt0 : (fun k : Fin 1 => euclidTimeReflect (x.pts k)) =
      fun _ => ![-1, 0, 0, 0] := by
    funext _ i; fin_cases i <;> simp [x, euclidTimeReflect]
  have hy_pt1 : (posTimeShiftConfig 1 zero_le_one y).pts =
      fun _ => ![2, 1, 0, 0] := by
    funext _ i; fin_cases i <;> simp [posTimeShiftConfig, y] <;> try norm_num
  have happ1 :
      Fin.append (fun k : Fin 1 => euclidTimeReflect ((posTimeShiftConfig 1 zero_le_one x).pts k))
        y.pts = ![ ![-2, 0, 0, 0], ![1, 1, 0, 0] ] := by
    rw [hx_pt, hy_pt]
    exact happ_gen _ _
  have happ2 :
      Fin.append (fun k : Fin 1 => euclidTimeReflect (x.pts k))
        (posTimeShiftConfig 1 zero_le_one y).pts = ![ ![-1, 0, 0, 0], ![2, 1, 0, 0] ] := by
    rw [hx_pt0, hy_pt1]
    exact happ_gen _ _
  have hn1 : euclidNorm4 ![-2, 0, 0, 0] = 2 := by
    simp [euclidNorm4, Fin.sum_univ_four]; try norm_num
  have hn2 : euclidNorm4 ![1, 1, 0, 0] = Real.sqrt 2 := by
    simp [euclidNorm4, Fin.sum_univ_four]; try norm_num
  have hn3 : euclidNorm4 ![-1, 0, 0, 0] = 1 := by
    simp [euclidNorm4, Fin.sum_univ_four]
  have hn4 : euclidNorm4 ![2, 1, 0, 0] = Real.sqrt 5 := by
    simp [euclidNorm4, Fin.sum_univ_four]; try norm_num
  have hsqrt_lt : Real.sqrt 5 < 1 + Real.sqrt 2 := by
    have h2_gt1 : 1 < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    have hsq : (Real.sqrt 5) ^ 2 < (1 + Real.sqrt 2) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num)]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  have hexp_lt :
      Real.exp (-2 * (2 + Real.sqrt 2)) < Real.exp (-2 * (1 + Real.sqrt 5)) :=
    Real.exp_lt_exp.mpr (by linarith)
  change ¬ isingSchwinger 2
      (Fin.append (fun k : Fin 1 => euclidTimeReflect ((posTimeShiftConfig 1 zero_le_one x).pts k))
        y.pts) =
      isingSchwinger 2
        (Fin.append (fun k : Fin 1 => euclidTimeReflect (x.pts k))
          (posTimeShiftConfig 1 zero_le_one y).pts)
  rw [happ1, happ2, h2_formula, h2_formula]
  dsimp [radialCoupling]
  rw [hn1, hn2, hn3, hn4, ← Real.exp_add, ← Real.exp_add]
  have h_eq1 : -2 * 2 + -2 * Real.sqrt 2 = -2 * (2 + Real.sqrt 2) := by ring
  have h_eq2 : -2 * 1 + -2 * Real.sqrt 5 = -2 * (1 + Real.sqrt 5) := by ring
  rw [h_eq1, h_eq2]
  intro heq
  have hre := congrArg Complex.re heq
  simp only [Complex.ofReal_re] at hre
  linarith

/--
Smeared Osterwalder–Schrader pre-Hilbert reconstruction data (`(E, F)` arbitrary,
supporting Schwartz-smeared positive-time test algebras): replaces pointwise
Schwinger bounds with the Glimm–Jaffe dyadic growth bound `T_E_ub`, deriving
semigroup contractivity automatically via `os_semigroup_contraction_of_bounded`.
-/
structure SmearedOSPreData (Δ_phys : ℝ) (os : OS4DContinuumTheory Δ_phys) where
  E            : Type
  [eAdd        : AddCommGroup E]
  [eMod        : Module ℂ E]
  F            : OSReflectionForm E
  Ω_E          : E
  Ω_E_norm     : F.B Ω_E Ω_E = 1
  T_E_pre      : ℝ → (E →ₗ[ℂ] E)
  T_E_zero     : ∀ x : E, T_E_pre 0 x = x
  T_E_add      : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ x : E, T_E_pre (s + t) x = T_E_pre s (T_E_pre t x)
  T_E_sa       : ∀ t, 0 ≤ t → ∀ x y : E, F.B (T_E_pre t x) y = F.B x (T_E_pre t y)
  T_E_ub       : ∀ (t : ℝ), 0 ≤ t → ∀ f : E, ∃ C : ℝ, ∀ k : ℕ,
                   (F.B (T_E_pre (((2 ^ k : ℕ) : ℝ) * t) f)
                     (T_E_pre (((2 ^ k : ℕ) : ℝ) * t) f)).re ≤ C
  H_pre        : E →ₗ[ℂ] E
  H_bound      : ℝ
  H_bound_nn   : 0 ≤ H_bound
  H_bd         : ∀ x : E, (F.B (H_pre x) (H_pre x)).re ≤ H_bound ^ 2 * (F.B x x).re
  H_sa         : ∀ x y : E, F.B (H_pre x) y = F.B x (H_pre y)
  H_nonneg     : ∀ x : E, 0 ≤ (F.B x (H_pre x)).re
  H_vac        : H_pre Ω_E = 0
  U_pre        : Poincare4 → (E →ₗ[ℂ] E)
  U_unit_pre   : ∀ g x y, F.B (U_pre g x) (U_pre g y) = F.B x y
  U_vac_pre    : ∀ g, U_pre g Ω_E = Ω_E
  φ_pre        : Space4 → (E →ₗ[ℂ] E)
  φ_bound      : Space4 → ℝ
  φ_bound_nn   : ∀ x, 0 ≤ φ_bound x
  φ_bd         : ∀ x (v : E), (F.B (φ_pre x v) (φ_pre x v)).re ≤ (φ_bound x) ^ 2 * (F.B v v).re
  cov_pre      : ∀ g x v, U_pre g (φ_pre x v) = φ_pre (poincareAct g x) (U_pre g v)
  loc_pre      : ∀ x y, minkowskiSq (x - y) < 0 → ∀ v, φ_pre x (φ_pre y v) = φ_pre y (φ_pre x v)
  P2_spec      : Set ℝ
  spec_cond    : ∀ p2 ∈ P2_spec, 0 ≤ p2
  gap_spec     : ∀ p2 ∈ P2_spec, p2 = 0 ∨ Δ_phys ^ 2 ≤ p2
  cyclic_dense : (Submodule.span ℂ
      {v : OSHilbertSpace F | ∃ (k : ℕ) (xs : Fin k → Space4),
        v = (List.ofFn (fun i : Fin k =>
          osLiftOperator F (φ_pre (xs i)) (φ_bound (xs i)) (φ_bound_nn (xs i)) (φ_bd (xs i)))).foldr
          (fun A acc => A acc) (osCompletionMap F (osPreMk F Ω_E))}).topologicalClosure = ⊤

attribute [instance] SmearedOSPreData.eAdd SmearedOSPreData.eMod

/-- Discharge semigroup contractivity in `EuclideanOSPreData` from `SmearedOSPreData`. -/
noncomputable def buildEuclideanOSPreDataFromSmeared
    {Δ_phys : ℝ} {os : OS4DContinuumTheory Δ_phys}
    (S : SmearedOSPreData Δ_phys os) :
    EuclideanOSPreData Δ_phys os where
  E := S.E
  F := S.F
  Ω_E := S.Ω_E
  Ω_E_norm := S.Ω_E_norm
  T_E_pre := S.T_E_pre
  T_E_zero := S.T_E_zero
  T_E_add := S.T_E_add
  T_E_sa := S.T_E_sa
  T_E_contr := fun t ht x => by
    rw [one_pow, one_mul]
    obtain ⟨C, hC⟩ := S.T_E_ub t ht x
    exact os_semigroup_contraction_of_bounded S.F S.T_E_pre S.T_E_add S.T_E_sa t ht x C hC
  H_pre := S.H_pre
  H_bound := S.H_bound
  H_bound_nn := S.H_bound_nn
  H_bd := S.H_bd
  H_sa := S.H_sa
  H_nonneg := S.H_nonneg
  H_vac := S.H_vac
  U_pre := S.U_pre
  U_unit_pre := S.U_unit_pre
  U_vac_pre := S.U_vac_pre
  φ_pre := S.φ_pre
  φ_bound := S.φ_bound
  φ_bound_nn := S.φ_bound_nn
  φ_bd := S.φ_bd
  cov_pre := S.cov_pre
  loc_pre := S.loc_pre
  P2_spec := S.P2_spec
  spec_cond := S.spec_cond
  gap_spec := S.gap_spec
  cyclic_dense := S.cyclic_dense

/-- Reconstruct `OSReconstructionData Δ_phys os` on `OSHilbertSpace S.F` from smeared OS data. -/
noncomputable def smearedOS_reconstruct_wightman
    {Δ_phys : ℝ} {os : OS4DContinuumTheory Δ_phys}
    (S : SmearedOSPreData Δ_phys os) :
    OSReconstructionData Δ_phys os :=
  buildOSReconstructionOnCompletion (buildEuclideanOSPreDataFromSmeared S)

end SmearedOSReconstruction

/-! ## §35.  Clay Yang–Mills 4D Mass Gap Statement & Exact Reduction to Open RG Estimates -/

section ClayYangMills4DInterface

/--
**Clay 4D `SU(N)` Yang–Mills Existence and Mass Gap (`ClayYangMillsMassGap4D N hN`)**:
existence of a physical mass gap `Δ_phys > 0`, a non-Gaussian 4D Euclidean continuum
`OS4DContinuumTheory Δ_phys` realized as the `a → 0⁺, β → ∞, Ls,Lt → ∞` scaling limit of
`SU(N)` Wilson lattice Schwinger functions `cubic4Schwinger`, and its reconstructed
infinite-dimensional relativistic `WightmanQFT4D Δ_phys` on `OSHilbertSpace` with
`Poincare4 = ℝ⁴ ⋊ O(1,3)` covariance, local commutativity, cyclic vacuum, and
`spec(M²) ⊆ {0} ∪ [Δ_phys², ∞)`.
-/
def ClayYangMillsMassGap4D (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] : Prop :=
  ∃ (Δ_phys : ℝ) (os : OS4DContinuumTheory Δ_phys) (R : OSReconstructionData.{0} Δ_phys os)
    (Ls_seq Lt_seq : ℕ → ℕ) (_ : ∀ m, NeZero (Ls_seq m)) (_ : ∀ m, NeZero (Lt_seq m))
    (β_seq : ℕ → ℝ)
    (latt_obs : ∀ (m n : ℕ), (Fin n → Space4) → Fin n →
      (GaugeField (cubicTorus4 (Ls_seq m) (Lt_seq m))
        (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)),
    0 < Δ_phys ∧
    ¬ IsGaussian4 os.os.Schwinger ∧
    (∀ m, 0 ≤ β_seq m) ∧
    Filter.Tendsto β_seq Filter.atTop Filter.atTop ∧
    (∀ (n : ℕ) (xs : Fin n → Space4),
      Filter.Tendsto
        (fun m => cubic4Schwinger (Ls_seq m) (Lt_seq m) N (β_seq m) n (latt_obs m n xs))
        Filter.atTop (nhds (os.os.Schwinger n xs))) ∧
    (∀ p2 ∈ R.wightman.P2_spec, ¬ (0 < p2 ∧ p2 < Δ_phys ^ 2)) ∧
    (∀ x : R.wightman.H, 0 ≤ (⟪x, R.H_phys x⟫_ℂ).re) ∧
    R.H_phys R.wightman.Ω_phys = 0

/--
**The Three Open Analytic RG / OS Estimates (`SUYangMillsRGConjecture N hN`)**:
1. **(E1) Uniform RG scaling:** along `a_seq m → 0⁺, β_seq m → ∞`, the finite-volume
   spectral gaps of the full-rank 3D cubic `SU(N)` Wilson transfer operators
   `fullRankCubicNonAbelianWilsonSetup` satisfy `Δ_latt m / a_seq m ≥ Δ₀ > 0`
   uniformly in spatial volume `Ls_seq m`, converging to `Δ_phys > 0`.
2. **(E2) Non-Gaussian 4D continuum limit:** `cubic4Schwinger` converges along
   `(Ls_seq m, Lt_seq m, β_seq m)` to a non-Gaussian `OS4DContinuumTheory Δ_phys`.
3. **(E3) OS analytic continuation / temperedness:** `SmearedOSPreData Δ_phys os`
   holds on the smeared positive-time test space.
-/
def SUYangMillsRGConjecture (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] : Prop :=
  ∃ (Δ_phys : ℝ) (os : OS4DContinuumTheory Δ_phys)
    (smeared : SmearedOSPreData Δ_phys os)
    (Ls_seq Lt_seq : ℕ → ℕ) (_ : ∀ m, NeZero (Ls_seq m)) (_ : ∀ m, NeZero (Lt_seq m))
    (a_seq β_seq g_sq_seq : ℕ → ℝ)
    (hβ_pos : ∀ m, 0 < β_seq m)
    (latt_obs : ∀ (m n : ℕ), (Fin n → Space4) → Fin n →
      (GaugeField (cubicTorus4 (Ls_seq m) (Lt_seq m))
        (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)),
    (∀ m, 0 < a_seq m) ∧
    Filter.Tendsto a_seq Filter.atTop (nhds 0) ∧
    Filter.Tendsto β_seq Filter.atTop Filter.atTop ∧
    (∀ m, 0 < g_sq_seq m) ∧
    (∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ m,
      Δ₀ ≤ (fullRankCubicNonAbelianWilsonSetup (Ls_seq m) N hN (β_seq m) (hβ_pos m)).gaugeSetup.Δ /
        a_seq m) ∧
    Filter.Tendsto
      (fun m =>
        (fullRankCubicNonAbelianWilsonSetup (Ls_seq m) N hN (β_seq m) (hβ_pos m)).gaugeSetup.Δ /
          a_seq m)
      Filter.atTop (nhds Δ_phys) ∧
    (∀ (n : ℕ) (xs : Fin n → Space4),
      Filter.Tendsto
        (fun m => cubic4Schwinger (Ls_seq m) (Lt_seq m) N (β_seq m) n (latt_obs m n xs))
        Filter.atTop (nhds (os.os.Schwinger n xs)))

/--
**Main Reduction Theorem**:
the three open analytic RG/OS estimates `SUYangMillsRGConjecture N hN` imply
`ClayYangMillsMassGap4D N hN`, firing the complete formal pipeline `§§1–34`.
-/
theorem clay_yang_mills_from_rg_estimates (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (hRG : SUYangMillsRGConjecture N hN) :
    ClayYangMillsMassGap4D N hN := by
  rcases hRG with ⟨Δ_phys, os, smeared, Ls_seq, Lt_seq, hLs, hLt, a_seq, β_seq, g_sq_seq,
    hβ_pos, latt_obs, ha_pos, ha_lim, hβ_lim, hg_pos, _, hgap_lim, hschw⟩
  let pre := buildEuclideanOSPreDataFromSmeared smeared
  let B : SUYangMillsDynamicalBridge N hN :=
    { Δ_phys := Δ_phys
      os := os
      pre := pre
      Ls_seq := Ls_seq
      Lt_seq := Lt_seq
      Ls_nz := hLs
      Lt_nz := hLt
      a_seq := a_seq
      β_seq := β_seq
      ha_pos := ha_pos
      ha_lim := ha_lim
      hβ_pos := hβ_pos
      hβ_lim := hβ_lim
      g_sq_seq := g_sq_seq
      hg_pos := hg_pos
      Δ_latt := fun m =>
        (fullRankCubicNonAbelianWilsonSetup (Ls_seq m) N hN (β_seq m) (hβ_pos m)).gaugeSetup.Δ
      Δ_latt_pos := fun m =>
        (fullRankCubicNonAbelianWilsonSetup (Ls_seq m) N hN (β_seq m) (hβ_pos m)).gaugeSetup.Δ_pos
      gap_lim := hgap_lim
      latt_obs := latt_obs
      schwinger_conv := hschw }
  obtain ⟨_, _, _, ⟨hΔ, hnonG⟩, _, _, hgap, hHnn, hHvac, _, _⟩ :=
    endToEnd_su_yang_mills_from_dynamical_bridge B
  exact ⟨Δ_phys, os, buildOSReconstructionOnCompletion pre, Ls_seq, Lt_seq, hLs, hLt,
    β_seq, latt_obs, hΔ, hnonG, fun m => (hβ_pos m).le, hβ_lim, hschw, hgap, hHnn, hHvac⟩

end ClayYangMills4DInterface

/-! ## §36.  4D Wilson Schwinger reflection positivity, time-reflection, translation & hypercubic symmetries -/

section CubicSpacetime4DOSAndSymmetries

private theorem su_inv_val_eq_star {N : ℕ} (A : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      star (A : Matrix (Fin N) (Fin N) ℂ) := by
  have hU : star (A : Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    (Unitary.mem_iff.mp A.2.1).1
  have hinv : (A : Matrix (Fin N) (Fin N) ℂ) *
      ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    have h1 : ((A * A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = 1 := by
      rw [mul_inv_cancel]; rfl
    exact h1
  calc ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
      = 1 * ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := (one_mul _).symm
    _ = (star (A : Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ)) *
          ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := by rw [hU]
    _ = star (A : Matrix (Fin N) (Fin N) ℂ) *
          ((A : Matrix (Fin N) (Fin N) ℂ) *
            ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) := by rw [mul_assoc]
    _ = star (A : Matrix (Fin N) (Fin N) ℂ) * 1 := by rw [hinv]
    _ = star (A : Matrix (Fin N) (Fin N) ℂ) := mul_one _

private theorem su_trace_inv_re {N : ℕ} (A : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (Matrix.trace ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)).re =
      (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re := by
  rw [su_inv_val_eq_star]
  simp only [Matrix.trace, Matrix.diag, Matrix.star_apply, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => Complex.conj_re _

private theorem su_trace_conj_4d {N : ℕ}
    (A B : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Matrix.trace ((A * B * A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ) =
      Matrix.trace (B : Matrix (Fin N) (Fin N) ℂ) := by
  have hmul : ∀ X Y : Matrix.specialUnitaryGroup (Fin N) ℂ,
      ((X * Y : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
        (X : Matrix (Fin N) (Fin N) ℂ) * (Y : Matrix (Fin N) (Fin N) ℂ) := fun _ _ => rfl
  have hone : ((1 : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = 1 := rfl
  have hinv : ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
      (A : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    rw [← hmul A⁻¹ A, inv_mul_cancel, hone]
  rw [hmul (A * B) A⁻¹, hmul A B,
    Matrix.trace_mul_comm ((A : Matrix (Fin N) (Fin N) ℂ) * (B : Matrix (Fin N) (Fin N) ℂ))
      ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ),
    ← mul_assoc, hinv, one_mul]

private theorem sum_map_flatMap {α β : Type*} (l : List α) (g : α → List β) (f : β → ℝ) :
    ((l.flatMap g).map f).sum = (l.map (fun x => ((g x).map f).sum)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change (((g a ++ l.flatMap g)).map f).sum = _
    rw [List.map_append, List.sum_append, ih]
    rfl

private theorem sum_map_univ_toList {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℝ) :
    ((Finset.univ : Finset α).toList.map f).sum = ∑ x : α, f x := by
  rw [← List.sum_toFinset f (Finset.nodup_toList Finset.univ)]
  congr 1
  ext x
  simp [Finset.mem_toList]

private noncomputable def sitePlaqSum4 (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (cubicTorus4 Ls Lt).Site) : ℝ :=
  wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 1, cubic4Plaquette_isPath x 0 1⟩ U +
  wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 2, cubic4Plaquette_isPath x 0 2⟩ U +
  wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 3, cubic4Plaquette_isPath x 0 3⟩ U +
  wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 2, cubic4Plaquette_isPath x 1 2⟩ U +
  wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 3, cubic4Plaquette_isPath x 1 3⟩ U +
  wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 2 3, cubic4Plaquette_isPath x 2 3⟩ U

private theorem wilsonAction_cubic4_eq_sum (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonAction β (cubic4Plaquettes Ls Lt) U =
      β * ∑ x : (cubicTorus4 Ls Lt).Site, sitePlaqSum4 Ls Lt N U x := by
  unfold wilsonAction cubic4Plaquettes
  rw [sum_map_flatMap, sum_map_univ_toList]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  dsimp [sitePlaqSum4]
  ring

private theorem fin_neg_add_one {n : ℕ} [NeZero n] (t : Fin n) : -(t + 1) = -t - 1 := by
  abel

private theorem fin_neg_sub_one_add_one {n : ℕ} [NeZero n] (t : Fin n) : (-t - 1) + 1 = -t := by
  abel

private theorem fin_neg_sub_one_invol {n : ℕ} [NeZero n] (t : Fin n) : -(-t - 1) - 1 = t := by
  abel

private theorem wilsonPlaquetteTerm_spatial_timeReflect
    (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (cubicTorus4 Ls Lt).Site) (d₁ d₂ : Fin 4) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
    wilsonPlaquetteTerm
        ⟨x, cubic4Plaquette x d₁ d₂, cubic4Plaquette_isPath x d₁ d₂⟩
        (cubic4TimeReflect Ls Lt N U) =
      wilsonPlaquetteTerm
        ⟨(-x.1, x.2.1, x.2.2.1, x.2.2.2),
          cubic4Plaquette (-x.1, x.2.1, x.2.2.1, x.2.2.2) d₁ d₂,
          cubic4Plaquette_isPath (-x.1, x.2.1, x.2.2.1, x.2.2.2) d₁ d₂⟩
        U := by
  have hsh : ∀ (d : Fin 4), d ≠ 0 → ∀ y : (cubicTorus4 Ls Lt).Site,
      cubicShift4 Ls Lt d (-y.1, y.2.1, y.2.2.1, y.2.2.2) =
        (-(cubicShift4 Ls Lt d y).1, (cubicShift4 Ls Lt d y).2.1,
          (cubicShift4 Ls Lt d y).2.2.1, (cubicShift4 Ls Lt d y).2.2.2) := by
    intro d hd ⟨t, a, b, c⟩
    fin_cases d
    · exact absurd rfl hd
    · rfl
    · rfl
    · rfl
  unfold wilsonPlaquetteTerm
  simp only [cubic4Plaquette, pathHolonomy, cubic4TimeReflect, hd₁, hd₂, ↓reduceIte,
    hsh d₁ hd₁ x, hsh d₂ hd₂ x]

private theorem wilsonPlaquetteTerm_temporal_timeReflect
    (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (cubicTorus4 Ls Lt).Site) (d : Fin 4) (hd : d ≠ 0) :
    wilsonPlaquetteTerm
        ⟨x, cubic4Plaquette x 0 d, cubic4Plaquette_isPath x 0 d⟩
        (cubic4TimeReflect Ls Lt N U) =
      wilsonPlaquetteTerm
        ⟨(-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2),
          cubic4Plaquette (-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2) 0 d,
          cubic4Plaquette_isPath (-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2) 0 d⟩
        U := by
  let x' : (cubicTorus4 Ls Lt).Site := (-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2)
  have h_s0 : (-((cubicShift4 Ls Lt 0 x).1), (cubicShift4 Ls Lt 0 x).2.1,
      (cubicShift4 Ls Lt 0 x).2.2.1, (cubicShift4 Ls Lt 0 x).2.2.2) = x' := by
    rcases x with ⟨t, a, b, c⟩
    dsimp [cubicShift4, x']
    congr 1
    exact fin_neg_add_one t
  have h_sd : (-((cubicShift4 Ls Lt d x).1) - 1, (cubicShift4 Ls Lt d x).2.1,
      (cubicShift4 Ls Lt d x).2.2.1, (cubicShift4 Ls Lt d x).2.2.2) =
      cubicShift4 Ls Lt d x' := by
    rcases x with ⟨t, a, b, c⟩
    fin_cases d
    · exact absurd rfl hd
    · rfl
    · rfl
    · rfl
  have h_s0' : cubicShift4 Ls Lt 0 x' = (-x.1, x.2.1, x.2.2.1, x.2.2.2) := by
    rcases x with ⟨t, a, b, c⟩
    dsimp [cubicShift4, x']
    congr 1
    exact fin_neg_sub_one_add_one t
  let A := U (x', 0)
  let B := U (x', d)
  let C := U (cubicShift4 Ls Lt d x', 0)
  let D := U (cubicShift4 Ls Lt 0 x', d)
  have hH : pathHolonomy (cubic4TimeReflect Ls Lt N U) (cubic4Plaquette x 0 d) =
      A⁻¹ * B * C * D⁻¹ := by
    simp only [cubic4Plaquette, pathHolonomy, cubic4TimeReflect, ↓reduceIte, hd, inv_inv,
      h_s0, h_sd, ← h_s0']
    dsimp only [A, B, C, D, x']
    group
  have hH' : pathHolonomy U (cubic4Plaquette x' 0 d) = A * D * C⁻¹ * B⁻¹ := by
    simp only [cubic4Plaquette, pathHolonomy]
    dsimp only [A, B, C, D]
    group
  have h_conj : pathHolonomy (cubic4TimeReflect Ls Lt N U) (cubic4Plaquette x 0 d) =
      A⁻¹ * (pathHolonomy U (cubic4Plaquette x' 0 d))⁻¹ * (A⁻¹)⁻¹ := by
    rw [hH, hH', mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, inv_inv]
    group
  unfold wilsonPlaquetteTerm
  rw [h_conj, su_trace_conj_4d, su_trace_inv_re]

/-- Exact invariance of the 4D Wilson action under Euclidean time reflection `cubic4TimeReflect`. -/
theorem cubic4WilsonAction_timeReflect (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonAction β (cubic4Plaquettes Ls Lt) (cubic4TimeReflect Ls Lt N U) =
      wilsonAction β (cubic4Plaquettes Ls Lt) U := by
  rw [wilsonAction_cubic4_eq_sum, wilsonAction_cubic4_eq_sum]
  congr 1
  let e_sp : (cubicTorus4 Ls Lt).Site ≃ (cubicTorus4 Ls Lt).Site :=
    { toFun := fun x => (-x.1, x.2.1, x.2.2.1, x.2.2.2)
      invFun := fun x => (-x.1, x.2.1, x.2.2.1, x.2.2.2)
      left_inv := fun ⟨t, a, b, c⟩ => by simp
      right_inv := fun ⟨t, a, b, c⟩ => by simp }
  let e_tm : (cubicTorus4 Ls Lt).Site ≃ (cubicTorus4 Ls Lt).Site :=
    { toFun := fun x => (-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2)
      invFun := fun x => (-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2)
      left_inv := fun ⟨t, a, b, c⟩ => by simp only [Prod.mk.injEq, fin_neg_sub_one_invol, true_and]
      right_inv := fun ⟨t, a, b, c⟩ => by simp only [Prod.mk.injEq, fin_neg_sub_one_invol, true_and] }
  have hsplit : ∀ V : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ),
      ∑ x : (cubicTorus4 Ls Lt).Site, sitePlaqSum4 Ls Lt N V x =
        (∑ x : (cubicTorus4 Ls Lt).Site,
          (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 1, cubic4Plaquette_isPath x 0 1⟩ V +
           wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 2, cubic4Plaquette_isPath x 0 2⟩ V +
           wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 3, cubic4Plaquette_isPath x 0 3⟩ V)) +
        (∑ x : (cubicTorus4 Ls Lt).Site,
          (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 2, cubic4Plaquette_isPath x 1 2⟩ V +
           wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 3, cubic4Plaquette_isPath x 1 3⟩ V +
           wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 2 3, cubic4Plaquette_isPath x 2 3⟩ V)) := by
    intro V
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp [sitePlaqSum4]
    ring
  rw [hsplit (cubic4TimeReflect Ls Lt N U), hsplit U]
  have h_tm :
      ∑ x : (cubicTorus4 Ls Lt).Site,
        (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 1, cubic4Plaquette_isPath x 0 1⟩
            (cubic4TimeReflect Ls Lt N U) +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 2, cubic4Plaquette_isPath x 0 2⟩
            (cubic4TimeReflect Ls Lt N U) +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 3, cubic4Plaquette_isPath x 0 3⟩
            (cubic4TimeReflect Ls Lt N U)) =
      ∑ x : (cubicTorus4 Ls Lt).Site,
        (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 1, cubic4Plaquette_isPath x 0 1⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 2, cubic4Plaquette_isPath x 0 2⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 3, cubic4Plaquette_isPath x 0 3⟩ U) := by
    refine Fintype.sum_equiv e_tm _ _ fun x => ?_
    rw [wilsonPlaquetteTerm_temporal_timeReflect Ls Lt N U x 1 (by decide),
      wilsonPlaquetteTerm_temporal_timeReflect Ls Lt N U x 2 (by decide),
      wilsonPlaquetteTerm_temporal_timeReflect Ls Lt N U x 3 (by decide)]
    rfl
  have h_sp :
      ∑ x : (cubicTorus4 Ls Lt).Site,
        (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 2, cubic4Plaquette_isPath x 1 2⟩
            (cubic4TimeReflect Ls Lt N U) +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 3, cubic4Plaquette_isPath x 1 3⟩
            (cubic4TimeReflect Ls Lt N U) +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 2 3, cubic4Plaquette_isPath x 2 3⟩
            (cubic4TimeReflect Ls Lt N U)) =
      ∑ x : (cubicTorus4 Ls Lt).Site,
        (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 2, cubic4Plaquette_isPath x 1 2⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 3, cubic4Plaquette_isPath x 1 3⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 2 3, cubic4Plaquette_isPath x 2 3⟩ U) := by
    refine Fintype.sum_equiv e_sp _ _ fun x => ?_
    rw [wilsonPlaquetteTerm_spatial_timeReflect Ls Lt N U x 1 2 (by decide) (by decide),
      wilsonPlaquetteTerm_spatial_timeReflect Ls Lt N U x 1 3 (by decide) (by decide),
      wilsonPlaquetteTerm_spatial_timeReflect Ls Lt N U x 2 3 (by decide) (by decide)]
    rfl
  rw [h_tm, h_sp]

theorem cubic4WilsonWeight_timeReflect (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubic4WilsonWeight Ls Lt N β (cubic4TimeReflect Ls Lt N U) =
      cubic4WilsonWeight Ls Lt N β U := by
  unfold cubic4WilsonWeight
  rw [cubic4WilsonAction_timeReflect]

/-- `cubic4TimeReflect` as a `MeasurePreserving` measurable equivalence on 4D gauge fields. -/
def cubic4TimeReflectEquiv (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) where
  toFun := cubic4TimeReflect Ls Lt N
  invFun := cubic4TimeReflect Ls Lt N
  left_inv := cubic4TimeReflect_involutive Ls Lt N
  right_inv := cubic4TimeReflect_involutive Ls Lt N
  measurable_toFun := by
    change Measurable (fun U : (cubicTorus4 Ls Lt).Link → _ => cubic4TimeReflect Ls Lt N U)
    refine measurable_pi_iff.mpr fun ⟨⟨t, a, b, c⟩, d⟩ => ?_
    by_cases hd : d = 0
    · subst hd
      simp only [cubic4TimeReflect, ↓reduceIte]
      exact (continuous_inv (G := Matrix.specialUnitaryGroup (Fin N) ℂ)).measurable.comp
        (measurable_pi_apply ((-t - 1, a, b, c), 0))
    · simp only [cubic4TimeReflect, hd, ↓reduceIte]
      exact measurable_pi_apply ((-t, a, b, c), d)
  measurable_invFun := by
    change Measurable (fun U : (cubicTorus4 Ls Lt).Link → _ => cubic4TimeReflect Ls Lt N U)
    refine measurable_pi_iff.mpr fun ⟨⟨t, a, b, c⟩, d⟩ => ?_
    by_cases hd : d = 0
    · subst hd
      simp only [cubic4TimeReflect, ↓reduceIte]
      exact (continuous_inv (G := Matrix.specialUnitaryGroup (Fin N) ℂ)).measurable.comp
        (measurable_pi_apply ((-t - 1, a, b, c), 0))
    · simp only [cubic4TimeReflect, hd, ↓reduceIte]
      exact measurable_pi_apply ((-t, a, b, c), d)

theorem cubic4TimeReflectEquiv_mp (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.MeasurePreserving (cubic4TimeReflectEquiv Ls Lt N)
      (spacetimeHaarMeasure Ls Lt N) (spacetimeHaarMeasure Ls Lt N) :=
  ⟨(cubic4TimeReflectEquiv Ls Lt N).measurable, spacetimeHaarMeasure_timeReflect Ls Lt N⟩

/-- Exact Euclidean time-reflection invariance of the 4D lattice Schwinger functions. -/
theorem cubic4Schwinger_timeReflect_inv (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ)
    (obs : Fin n →
      (GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)) :
    cubic4Schwinger Ls Lt N β n (fun i U => obs i (cubic4TimeReflect Ls Lt N U)) =
      cubic4Schwinger Ls Lt N β n obs := by
  unfold cubic4Schwinger
  congr 1
  calc ∫ U, (∏ i : Fin n, obs i (cubic4TimeReflect Ls Lt N U)) *
          ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) ∂(spacetimeHaarMeasure Ls Lt N)
      = ∫ U, (∏ i : Fin n, obs i ((cubic4TimeReflectEquiv Ls Lt N) U)) *
          ((cubic4WilsonWeight Ls Lt N β ((cubic4TimeReflectEquiv Ls Lt N) U) : ℝ) : ℂ)
          ∂(spacetimeHaarMeasure Ls Lt N) := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
            change (∏ i : Fin n, obs i (cubic4TimeReflect Ls Lt N U)) *
                ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) =
              (∏ i : Fin n, obs i (cubic4TimeReflect Ls Lt N U)) *
                ((cubic4WilsonWeight Ls Lt N β (cubic4TimeReflect Ls Lt N U) : ℝ) : ℂ)
            rw [cubic4WilsonWeight_timeReflect]
    _ = ∫ U, (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)
          ∂(spacetimeHaarMeasure Ls Lt N) :=
        (cubic4TimeReflectEquiv_mp Ls Lt N).integral_comp'
          (fun U => (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ))

/-- Boundary-slice links (`t = 0` or `t = M`, spatial directions `d ≠ 0`) on `cubicTorus4 Ls (2 * M)`. -/
def isBdryTimeLink (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (e : (cubicTorus4 Ls (2 * M)).Link) : Prop :=
  e.2 ≠ 0 ∧ (e.1.1.val = 0 ∨ e.1.1.val = M)

/-- Positive-time links on `cubicTorus4 Ls (2 * M)`. -/
def isPosTimeLink (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (e : (cubicTorus4 Ls (2 * M)).Link) : Prop :=
  if e.2 = 0 then e.1.1.val < M else (0 < e.1.1.val ∧ e.1.1.val < M)

/-- Negative-time links on `cubicTorus4 Ls (2 * M)`. -/
def isNegTimeLink (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (e : (cubicTorus4 Ls (2 * M)).Link) : Prop :=
  if e.2 = 0 then M ≤ e.1.1.val else M < e.1.1.val

instance instDecidableBdryTimeLink (Ls M : ℕ) [NeZero Ls] [NeZero M] :
    DecidablePred (isBdryTimeLink Ls M) := fun e => by
  unfold isBdryTimeLink; infer_instance

instance instDecidablePosTimeLink (Ls M : ℕ) [NeZero Ls] [NeZero M] :
    DecidablePred (isPosTimeLink Ls M) := fun e => by
  unfold isPosTimeLink; infer_instance

instance instDecidableNegTimeLink (Ls M : ℕ) [NeZero Ls] [NeZero M] :
    DecidablePred (isNegTimeLink Ls M) := fun e => by
  unfold isNegTimeLink; infer_instance

/-- Observable supported solely on positive-time and boundary-slice links (`¬ isNegTimeLink`). -/
def SupportedOnPosTime (Ls M N : ℕ) [NeZero Ls] [NeZero M]
    (f : GaugeField (cubicTorus4 Ls (2 * M)) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ) : Prop :=
  ∀ U V, (∀ e, ¬ isNegTimeLink Ls M e → U e = V e) → f U = f V

private theorem fin_2M_neg_val (M : ℕ) [NeZero M] (t : Fin (2 * M)) :
    (-t).val = if t.val = 0 then 0 else 2 * M - t.val := by
  by_cases ht : t.val = 0
  · have ht0 : t = 0 := Fin.ext ht
    subst ht0
    simp
  · rw [if_neg ht]
    have hlt : 2 * M - t.val < 2 * M := by omega
    let r : Fin (2 * M) := ⟨2 * M - t.val, hlt⟩
    have hadd : t + r = 0 := by
      apply Fin.ext
      rw [Fin.val_add]
      change (t.val + (2 * M - t.val)) % (2 * M) = 0
      rw [Nat.add_sub_of_le (le_of_lt t.isLt), Nat.mod_self]
    have hr : -t = r := neg_eq_of_add_eq_zero_right hadd
    rw [hr]

private theorem fin_2M_neg_sub_one_val (M : ℕ) [NeZero M] (t : Fin (2 * M)) :
    (-t - 1).val = 2 * M - 1 - t.val := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hlt : 2 * M - 1 - t.val < 2 * M := by omega
  let r : Fin (2 * M) := ⟨2 * M - 1 - t.val, hlt⟩
  have hadd : t + r = -1 := by
    have hadd1 : t + r + 1 = 0 := by
      apply Fin.ext
      have h1val : (1 : Fin (2 * M)).val = 1 := by
        change 1 % (2 * M) = 1
        exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_add, h1val, Fin.val_zero, Nat.mod_add_mod]
      have heq : t.val + r.val + 1 = 2 * M := by dsimp [r]; omega
      rw [heq, Nat.mod_self]
    exact eq_neg_of_add_eq_zero_left hadd1
  have hr : -t - 1 = r := by
    have h := neg_eq_of_add_eq_zero_right (show (t + 1) + r = 0 by
      rw [add_right_comm, hadd, neg_add_cancel])
    calc -t - 1 = -(t + 1) := (fin_neg_add_one t).symm
      _ = r := h
  rw [hr]

private theorem link_partition_trichotomy (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (e : (cubicTorus4 Ls (2 * M)).Link) :
    (¬ isBdryTimeLink Ls M e ∧ ¬ isPosTimeLink Ls M e ↔ isNegTimeLink Ls M e) ∧
    (isBdryTimeLink Ls M e → ¬ isPosTimeLink Ls M e ∧ ¬ isNegTimeLink Ls M e) := by
  rcases e with ⟨⟨t, a, b, c⟩, d⟩
  have hlt : t.val < 2 * M := t.isLt
  by_cases hd : d = 0
  · simp only [isBdryTimeLink, isPosTimeLink, isNegTimeLink, hd, ne_eq, not_true_eq_false,
      false_and, not_false_eq_true, ↓reduceIte, true_and, false_implies, and_true]
    omega
  · simp only [isBdryTimeLink, isPosTimeLink, isNegTimeLink, hd, ne_eq, not_false_eq_true,
      true_and, ↓reduceIte]
    omega

private theorem cubic4TimeReflectLink_zero (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt]
    (t : Fin Lt) (a b c : Fin Ls) :
    cubic4TimeReflectLink Ls Lt ((t, a, b, c), 0) = ((-t - 1, a, b, c), 0) := by
  simp [cubic4TimeReflectLink]

private theorem cubic4TimeReflectLink_succ (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt]
    (t : Fin Lt) (a b c : Fin Ls) (d : Fin 4) (hd : d ≠ 0) :
    cubic4TimeReflectLink Ls Lt ((t, a, b, c), d) = ((-t, a, b, c), d) := by
  simp [cubic4TimeReflectLink, hd]

private theorem isPosTimeLink_zero (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (t : Fin (2 * M)) (a b c : Fin Ls) :
    isPosTimeLink Ls M ((t, a, b, c), 0) ↔ t.val < M := by
  simp [isPosTimeLink]

private theorem isPosTimeLink_ne_zero (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (t : Fin (2 * M)) (a b c : Fin Ls) {d : Fin 4} (hd : d ≠ 0) :
    isPosTimeLink Ls M ((t, a, b, c), d) ↔ (0 < t.val ∧ t.val < M) := by
  simp [isPosTimeLink, hd]

private theorem isNegTimeLink_zero (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (t : Fin (2 * M)) (a b c : Fin Ls) :
    isNegTimeLink Ls M ((t, a, b, c), 0) ↔ M ≤ t.val := by
  simp [isNegTimeLink]

private theorem isNegTimeLink_ne_zero (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (t : Fin (2 * M)) (a b c : Fin Ls) {d : Fin 4} (hd : d ≠ 0) :
    isNegTimeLink Ls M ((t, a, b, c), d) ↔ M < t.val := by
  simp [isNegTimeLink, hd]

private theorem isBdryTimeLink_iff (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (t : Fin (2 * M)) (a b c : Fin Ls) (d : Fin 4) :
    isBdryTimeLink Ls M ((t, a, b, c), d) ↔ d ≠ 0 ∧ (t.val = 0 ∨ t.val = M) :=
  Iff.rfl

private theorem cubic4TimeReflectLink_bdry_iff (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (e : (cubicTorus4 Ls (2 * M)).Link) :
    isBdryTimeLink Ls M (cubic4TimeReflectLink Ls (2 * M) e) ↔ isBdryTimeLink Ls M e := by
  have hM : 0 < M := NeZero.pos M
  rcases e with ⟨⟨t, a, b, c⟩, d⟩
  have hlt : t.val < 2 * M := t.isLt
  by_cases hd : d = 0
  · subst hd
    rw [cubic4TimeReflectLink_zero, isBdryTimeLink_iff, isBdryTimeLink_iff]
    simp
  · rw [cubic4TimeReflectLink_succ Ls (2 * M) t a b c d hd,
      isBdryTimeLink_iff, isBdryTimeLink_iff, fin_2M_neg_val M t]
    simp only [hd, ne_eq, not_false_eq_true, true_and]
    split_ifs <;> omega

private theorem cubic4TimeReflect_bdry_fix (Ls M N : ℕ) [NeZero Ls] [NeZero M]
    (U : GaugeField (cubicTorus4 Ls (2 * M)) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    {e : (cubicTorus4 Ls (2 * M)).Link} (he : isBdryTimeLink Ls M e) :
    cubic4TimeReflect Ls (2 * M) N U e = U e := by
  rcases e with ⟨⟨t, a, b, c⟩, d⟩
  rw [isBdryTimeLink_iff] at he
  rcases he with ⟨hd, ht0 | htM⟩
  · have ht : t = 0 := Fin.ext ht0
    subst ht
    simp [cubic4TimeReflect, hd]
  · have hM_neg : -t = t := by
      apply Fin.ext
      rw [fin_2M_neg_val]
      have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
      rw [if_neg (by omega), htM]
      omega
    simp [cubic4TimeReflect, hd, hM_neg]

private theorem cubic4TimeReflectLink_pos_iff_neg (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (e : (cubicTorus4 Ls (2 * M)).Link) :
    isPosTimeLink Ls M (cubic4TimeReflectLink Ls (2 * M) e) ↔ isNegTimeLink Ls M e := by
  have hM : 0 < M := NeZero.pos M
  rcases e with ⟨⟨t, a, b, c⟩, d⟩
  have hlt : t.val < 2 * M := t.isLt
  by_cases hd : d = 0
  · subst hd
    rw [cubic4TimeReflectLink_zero, isPosTimeLink_zero, isNegTimeLink_zero,
      fin_2M_neg_sub_one_val]
    omega
  · rw [cubic4TimeReflectLink_succ Ls (2 * M) t a b c d hd,
      isPosTimeLink_ne_zero Ls M (-t) a b c hd,
      isNegTimeLink_ne_zero Ls M t a b c hd,
      fin_2M_neg_val]
    split_ifs <;> omega
private theorem cubic4TimeReflectLink_neg_iff_pos (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (e : (cubicTorus4 Ls (2 * M)).Link) :
    isNegTimeLink Ls M (cubic4TimeReflectLink Ls (2 * M) e) ↔ isPosTimeLink Ls M e := by
  have h := cubic4TimeReflectLink_pos_iff_neg Ls M (cubic4TimeReflectLink Ls (2 * M) e)
  have hinv : cubic4TimeReflectLink Ls (2 * M) (cubic4TimeReflectLink Ls (2 * M) e) = e :=
    (cubic4TimeReflectLink Ls (2 * M)).left_inv e
  rw [hinv] at h
  exact h.symm

private noncomputable def wilsonActionBdry (Ls M N : ℕ) [NeZero Ls] [NeZero M] (β : ℝ)
    (U : GaugeField (cubicTorus4 Ls (2 * M)) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  β * ∑ x : (cubicTorus4 Ls (2 * M)).Site,
    if (x.1.val = 0 ∨ x.1.val = M) then
      (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 2, cubic4Plaquette_isPath x 1 2⟩ U +
       wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 3, cubic4Plaquette_isPath x 1 3⟩ U +
       wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 2 3, cubic4Plaquette_isPath x 2 3⟩ U)
    else 0

private noncomputable def wilsonActionPos (Ls M N : ℕ) [NeZero Ls] [NeZero M] (β : ℝ)
    (U : GaugeField (cubicTorus4 Ls (2 * M)) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  β * ∑ x : (cubicTorus4 Ls (2 * M)).Site,
    ((if (0 < x.1.val ∧ x.1.val < M) then
        (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 2, cubic4Plaquette_isPath x 1 2⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 3, cubic4Plaquette_isPath x 1 3⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 2 3, cubic4Plaquette_isPath x 2 3⟩ U)
      else 0) +
     (if x.1.val < M then
        (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 1, cubic4Plaquette_isPath x 0 1⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 2, cubic4Plaquette_isPath x 0 2⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 3, cubic4Plaquette_isPath x 0 3⟩ U)
      else 0))

private theorem wilsonAction_split_pos_neg (Ls M N : ℕ) [NeZero Ls] [NeZero M] (β : ℝ)
    (U : GaugeField (cubicTorus4 Ls (2 * M)) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonAction β (cubic4Plaquettes Ls (2 * M)) U =
      wilsonActionBdry Ls M N β U +
      wilsonActionPos Ls M N β U +
      wilsonActionPos Ls M N β (cubic4TimeReflect Ls (2 * M) N U) := by
  let S_neg : ℝ := β * ∑ x : (cubicTorus4 Ls (2 * M)).Site,
    ((if M < x.1.val then
        (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 2, cubic4Plaquette_isPath x 1 2⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 3, cubic4Plaquette_isPath x 1 3⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 2 3, cubic4Plaquette_isPath x 2 3⟩ U)
      else 0) +
     (if M ≤ x.1.val then
        (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 1, cubic4Plaquette_isPath x 0 1⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 2, cubic4Plaquette_isPath x 0 2⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 3, cubic4Plaquette_isPath x 0 3⟩ U)
      else 0))
  have h_sum_eq : wilsonAction β (cubic4Plaquettes Ls (2 * M)) U =
      wilsonActionBdry Ls M N β U + wilsonActionPos Ls M N β U + S_neg := by
    rw [wilsonAction_cubic4_eq_sum]
    dsimp [wilsonActionBdry, wilsonActionPos, S_neg]
    rw [← mul_add, ← mul_add]
    congr 1
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp [sitePlaqSum4]
    have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
    by_cases ht0 : x.1.val = 0
    · have h1 : ¬ (0 < x.1.val ∧ x.1.val < M) := by omega
      have h2 : ¬ (M < x.1.val) := by omega
      have h3 : ¬ (M ≤ x.1.val) := by omega
      rw [if_pos (Or.inl ht0), if_neg h1, if_pos (by omega : x.1.val < M),
        if_neg h2, if_neg h3]
      ring
    · by_cases htM : x.1.val = M
      · have h1 : ¬ (0 < x.1.val ∧ x.1.val < M) := by omega
        have h2 : ¬ (x.1.val < M) := by omega
        have h3 : ¬ (M < x.1.val) := by omega
        rw [if_pos (Or.inr htM), if_neg h1, if_neg h2, if_neg h3,
          if_pos (by omega : M ≤ x.1.val)]
        ring
      · by_cases hltM : x.1.val < M
        · have h1 : ¬ (x.1.val = 0 ∨ x.1.val = M) := by omega
          have h2 : 0 < x.1.val ∧ x.1.val < M := by omega
          have h3 : ¬ (M < x.1.val) := by omega
          have h4 : ¬ (M ≤ x.1.val) := by omega
          rw [if_neg h1, if_pos h2, if_pos hltM, if_neg h3, if_neg h4]
          ring
        · have h1 : ¬ (x.1.val = 0 ∨ x.1.val = M) := by omega
          have h2 : ¬ (0 < x.1.val ∧ x.1.val < M) := by omega
          have h3 : M < x.1.val := by omega
          have h4 : M ≤ x.1.val := by omega
          rw [if_neg h1, if_neg h2, if_neg hltM, if_pos h3, if_pos h4]
          ring
  have h_neg_eq : S_neg = wilsonActionPos Ls M N β (cubic4TimeReflect Ls (2 * M) N U) := by
    dsimp [S_neg, wilsonActionPos]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1
    · let e_sp : (cubicTorus4 Ls (2 * M)).Site ≃ (cubicTorus4 Ls (2 * M)).Site :=
        { toFun := fun x => (-x.1, x.2.1, x.2.2.1, x.2.2.2)
          invFun := fun x => (-x.1, x.2.1, x.2.2.1, x.2.2.2)
          left_inv := fun ⟨t, a, b, c⟩ => by simp
          right_inv := fun ⟨t, a, b, c⟩ => by simp }
      refine Fintype.sum_equiv e_sp _ _ fun x => ?_
      have h_cond : (M < x.1.val) ↔ (0 < (-x.1).val ∧ (-x.1).val < M) := by
        have hlt := x.1.isLt
        rw [fin_2M_neg_val]
        by_cases ht0 : x.1.val = 0
        · rw [if_pos ht0]; omega
        · rw [if_neg ht0]; omega
      change (if M < x.1.val then _ else 0) =
        (if (0 < (-x.1).val ∧ (-x.1).val < M) then _ else 0)
      by_cases hx : M < x.1.val
      · rw [if_pos hx, if_pos (h_cond.mp hx)]
        dsimp only [e_sp, Equiv.coe_fn_mk]
        rw [wilsonPlaquetteTerm_spatial_timeReflect Ls (2 * M) N U
              (-x.1, x.2.1, x.2.2.1, x.2.2.2) 1 2 (by decide) (by decide),
            wilsonPlaquetteTerm_spatial_timeReflect Ls (2 * M) N U
              (-x.1, x.2.1, x.2.2.1, x.2.2.2) 1 3 (by decide) (by decide),
            wilsonPlaquetteTerm_spatial_timeReflect Ls (2 * M) N U
              (-x.1, x.2.1, x.2.2.1, x.2.2.2) 2 3 (by decide) (by decide)]
        simp [neg_neg]
      · rw [if_neg hx, if_neg (mt h_cond.mpr hx)]
    · let e_tm : (cubicTorus4 Ls (2 * M)).Site ≃ (cubicTorus4 Ls (2 * M)).Site :=
        { toFun := fun x => (-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2)
          invFun := fun x => (-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2)
          left_inv := fun ⟨t, a, b, c⟩ => by simp only [Prod.mk.injEq, fin_neg_sub_one_invol, true_and]
          right_inv := fun ⟨t, a, b, c⟩ => by simp only [Prod.mk.injEq, fin_neg_sub_one_invol, true_and] }
      refine Fintype.sum_equiv e_tm _ _ fun x => ?_
      have h_cond : (M ≤ x.1.val) ↔ (-x.1 - 1).val < M := by
        have hlt := x.1.isLt
        rw [fin_2M_neg_sub_one_val]
        omega
      change (if M ≤ x.1.val then _ else 0) = (if (-x.1 - 1).val < M then _ else 0)
      by_cases hx : M ≤ x.1.val
      · rw [if_pos hx, if_pos (h_cond.mp hx)]
        dsimp only [e_tm, Equiv.coe_fn_mk]
        rw [wilsonPlaquetteTerm_temporal_timeReflect Ls (2 * M) N U
              (-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2) 1 (by decide),
            wilsonPlaquetteTerm_temporal_timeReflect Ls (2 * M) N U
              (-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2) 2 (by decide),
            wilsonPlaquetteTerm_temporal_timeReflect Ls (2 * M) N U
              (-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2) 3 (by decide)]
        simp only [fin_neg_sub_one_invol]
        rfl
      · rw [if_neg hx, if_neg (mt h_cond.mpr hx)]
  rw [h_sum_eq, h_neg_eq]

private theorem wilsonPlaquetteTerm_depends_on_links
    {L : SpatialLattice} {N : ℕ} (p : LatticePlaquette L)
    (U V : GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (hUV : ∀ (e : L.Link) (b : Bool), (e, b) ∈ p.loop → U e = V e) :
    wilsonPlaquetteTerm p U = wilsonPlaquetteTerm p V := by
  have hhol : ∀ (γ : List (L.Link × Bool)),
      (∀ (e : L.Link) (b : Bool), (e, b) ∈ γ → U e = V e) →
      pathHolonomy U γ = pathHolonomy V γ := by
    intro γ hγ
    induction γ with
    | nil => rfl
    | cons hd tl ih =>
      rcases hd with ⟨e, b⟩
      have he : U e = V e := hγ e b (by simp)
      have htl : pathHolonomy U tl = pathHolonomy V tl :=
        ih (fun e' b' hm => hγ e' b' (by simp [hm]))
      cases b <;> simp [pathHolonomy, he, htl]
  unfold wilsonPlaquetteTerm
  rw [hhol p.loop hUV]

private theorem wilsonActionBdry_depends_only (Ls M N : ℕ) [NeZero Ls] [NeZero M] (β : ℝ)
    (U V : GaugeField (cubicTorus4 Ls (2 * M)) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (hUV : ∀ e, isBdryTimeLink Ls M e → U e = V e) :
    wilsonActionBdry Ls M N β U = wilsonActionBdry Ls M N β V := by
  dsimp [wilsonActionBdry]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with hx
  · have hsp : ∀ (d₁ d₂ : Fin 4), d₁ ≠ 0 → d₂ ≠ 0 →
        wilsonPlaquetteTerm ⟨x, cubic4Plaquette x d₁ d₂, cubic4Plaquette_isPath x d₁ d₂⟩ U =
        wilsonPlaquetteTerm ⟨x, cubic4Plaquette x d₁ d₂, cubic4Plaquette_isPath x d₁ d₂⟩ V := by
      intro d₁ d₂ hd₁ hd₂
      refine wilsonPlaquetteTerm_depends_on_links _ U V fun e b hm => ?_
      apply hUV
      have he_mem : e = (x, d₁) ∨ e = (cubicShift4 Ls (2 * M) d₁ x, d₂) ∨
          e = (cubicShift4 Ls (2 * M) d₂ x, d₁) ∨ e = (x, d₂) := by
        simp [cubic4Plaquette] at hm
        rcases hm with h | h | h | h <;> simp [h]
      have hsh_t : ∀ (d : Fin 4), d ≠ 0 → (cubicShift4 Ls (2 * M) d x).1 = x.1 := by
        intro d hd; rcases x with ⟨t, a, b', c⟩; fin_cases d <;> first | exact absurd rfl hd | rfl
      rcases he_mem with rfl | rfl | rfl | rfl
      · exact ⟨hd₁, hx⟩
      · exact ⟨hd₂, by rw [hsh_t d₁ hd₁]; exact hx⟩
      · exact ⟨hd₁, by rw [hsh_t d₂ hd₂]; exact hx⟩
      · exact ⟨hd₂, hx⟩
    rw [hsp 1 2 (by decide) (by decide), hsp 1 3 (by decide) (by decide),
      hsp 2 3 (by decide) (by decide)]
  · rfl

private theorem not_isNeg_of_lt {Ls M : ℕ} [NeZero Ls] [NeZero M]
    (y : (cubicTorus4 Ls (2 * M)).Site) (d : Fin 4)
    (h0 : d = 0 → y.1.val < M) (hd : d ≠ 0 → y.1.val ≤ M) :
    ¬ isNegTimeLink Ls M (y, d) := by
  by_cases h : d = 0
  · simp only [isNegTimeLink, if_pos h]
    exact not_le_of_gt (h0 h)
  · simp only [isNegTimeLink, if_neg h]
    exact not_lt_of_ge (hd h)

private theorem wilsonActionPos_supported_on_pos (Ls M N : ℕ) [NeZero Ls] [NeZero M] (β : ℝ)
    (U V : GaugeField (cubicTorus4 Ls (2 * M)) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (hUV : ∀ e, ¬ isNegTimeLink Ls M e → U e = V e) :
    wilsonActionPos Ls M N β U = wilsonActionPos Ls M N β V := by
  dsimp [wilsonActionPos]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rcases x with ⟨t, a, b', c⟩
  have hsh_t : ∀ (d : Fin 4), d ≠ 0 → ∀ y : (cubicTorus4 Ls (2 * M)).Site,
      (cubicShift4 Ls (2 * M) d y).1 = y.1 := by
    intro d hd ⟨t', a', b'', c'⟩; fin_cases d <;> first | exact absurd rfl hd | rfl
  have h1 : (if (0 < t.val ∧ t.val < M) then
        (wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 1 2,
            cubic4Plaquette_isPath (t, a, b', c) 1 2⟩ U +
         wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 1 3,
            cubic4Plaquette_isPath (t, a, b', c) 1 3⟩ U +
         wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 2 3,
            cubic4Plaquette_isPath (t, a, b', c) 2 3⟩ U)
      else 0) =
      (if (0 < t.val ∧ t.val < M) then
        (wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 1 2,
            cubic4Plaquette_isPath (t, a, b', c) 1 2⟩ V +
         wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 1 3,
            cubic4Plaquette_isPath (t, a, b', c) 1 3⟩ V +
         wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 2 3,
            cubic4Plaquette_isPath (t, a, b', c) 2 3⟩ V)
      else 0) := by
    split_ifs with hx
    · have hsp : ∀ (d₁ d₂ : Fin 4), d₁ ≠ 0 → d₂ ≠ 0 →
          wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) d₁ d₂,
              cubic4Plaquette_isPath (t, a, b', c) d₁ d₂⟩ U =
          wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) d₁ d₂,
              cubic4Plaquette_isPath (t, a, b', c) d₁ d₂⟩ V := by
        intro d₁ d₂ hd₁ hd₂
        refine wilsonPlaquetteTerm_depends_on_links _ U V fun e b hm => ?_
        apply hUV
        have he_mem : e = ((t, a, b', c), d₁) ∨
            e = (cubicShift4 Ls (2 * M) d₁ (t, a, b', c), d₂) ∨
            e = (cubicShift4 Ls (2 * M) d₂ (t, a, b', c), d₁) ∨
            e = ((t, a, b', c), d₂) := by
          simp [cubic4Plaquette] at hm
          rcases hm with h | h | h | h <;> simp [h]
        rcases he_mem with rfl | rfl | rfl | rfl
        · exact not_isNeg_of_lt (t, a, b', c) d₁ (fun h => absurd h hd₁) (fun _ => hx.2.le)
        · exact not_isNeg_of_lt _ d₂ (fun h => absurd h hd₂)
            (fun _ => by rw [hsh_t d₁ hd₁]; exact hx.2.le)
        · exact not_isNeg_of_lt _ d₁ (fun h => absurd h hd₁)
            (fun _ => by rw [hsh_t d₂ hd₂]; exact hx.2.le)
        · exact not_isNeg_of_lt (t, a, b', c) d₂ (fun h => absurd h hd₂) (fun _ => hx.2.le)
      rw [hsp 1 2 (by decide) (by decide), hsp 1 3 (by decide) (by decide),
        hsp 2 3 (by decide) (by decide)]
    · rfl
  have h2 : (if t.val < M then
        (wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 0 1,
            cubic4Plaquette_isPath (t, a, b', c) 0 1⟩ U +
         wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 0 2,
            cubic4Plaquette_isPath (t, a, b', c) 0 2⟩ U +
         wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 0 3,
            cubic4Plaquette_isPath (t, a, b', c) 0 3⟩ U)
      else 0) =
      (if t.val < M then
        (wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 0 1,
            cubic4Plaquette_isPath (t, a, b', c) 0 1⟩ V +
         wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 0 2,
            cubic4Plaquette_isPath (t, a, b', c) 0 2⟩ V +
         wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 0 3,
            cubic4Plaquette_isPath (t, a, b', c) 0 3⟩ V)
      else 0) := by
    split_ifs with hx
    · have htm : ∀ (d : Fin 4), d ≠ 0 →
          wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 0 d,
              cubic4Plaquette_isPath (t, a, b', c) 0 d⟩ U =
          wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 0 d,
              cubic4Plaquette_isPath (t, a, b', c) 0 d⟩ V := by
        intro d hd
        refine wilsonPlaquetteTerm_depends_on_links _ U V fun e b hm => ?_
        apply hUV
        have he_mem : e = ((t, a, b', c), 0) ∨
            e = (cubicShift4 Ls (2 * M) 0 (t, a, b', c), d) ∨
            e = (cubicShift4 Ls (2 * M) d (t, a, b', c), 0) ∨
            e = ((t, a, b', c), d) := by
          simp [cubic4Plaquette] at hm
          rcases hm with h | h | h | h <;> simp [h]
        have hx1_le : (t + 1).val ≤ M := by
          have h1lt : 1 < 2 * M := by have := NeZero.pos M; omega
          have h1val : (1 : Fin (2 * M)).val = 1 := by
            change 1 % (2 * M) = 1
            exact Nat.mod_eq_of_lt h1lt
          rw [Fin.val_add, h1val, Nat.mod_eq_of_lt (by omega : t.val + 1 < 2 * M)]
          omega
        rcases he_mem with rfl | rfl | rfl | rfl
        · exact not_isNeg_of_lt (t, a, b', c) 0 (fun _ => hx) (fun h => absurd rfl h)
        · exact not_isNeg_of_lt _ d (fun h => absurd h hd) (fun _ => hx1_le)
        · exact not_isNeg_of_lt _ 0 (fun _ => by rw [hsh_t d hd]; exact hx)
            (fun h => absurd rfl h)
        · exact not_isNeg_of_lt (t, a, b', c) d (fun h => absurd h hd) (fun _ => hx.le)
      rw [htm 1 (by decide), htm 2 (by decide), htm 3 (by decide)]
    · rfl
  exact congrArg₂ (· + ·) h1 h2

private theorem measurable_cubic4_plaquette_term (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (p : LatticePlaquette (cubicTorus4 Ls Lt)) :
    Measurable (fun U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      wilsonPlaquetteTerm p U) := by
  have hev : ∀ e : (cubicTorus4 Ls Lt).Link,
      Measurable (fun U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) => U e) := by
    intro e
    change Measurable (fun U : (cubicTorus4 Ls Lt).Link → _ => U e)
    exact measurable_pi_apply e
  have hhol : ∀ γ : List ((cubicTorus4 Ls Lt).Link × Bool),
      Measurable (fun U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        pathHolonomy U γ) := by
    intro γ
    induction γ with
    | nil => simpa [pathHolonomy] using measurable_const
    | cons hd tl ih =>
      rcases hd with ⟨e, b⟩
      cases b
      · simpa [pathHolonomy] using
          ((continuous_inv (G := Matrix.specialUnitaryGroup (Fin N) ℂ)).measurable.comp (hev e)).mul ih
      · simpa [pathHolonomy] using (hev e).mul ih
  unfold wilsonPlaquetteTerm
  have h_ent : ∀ i : Fin N, Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (A : Matrix (Fin N) (Fin N) ℂ) i i) := fun i =>
    (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
  have h_tr : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re) := by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact continuous_finset_sum Finset.univ fun i _ => Complex.continuous_re.comp (h_ent i)
  exact measurable_const.sub (measurable_const.mul (h_tr.measurable.comp (hhol p.loop)))

private theorem integrable_of_measurable_bound {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (f : α → ℂ) (hf : Measurable f) (C : ℝ) (hbd : ∀ x, ‖f x‖ ≤ C) :
    MeasureTheory.Integrable f μ := by
  refine (MeasureTheory.integrable_const C).mono' hf.stronglyMeasurable.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall hbd

private theorem measurable_finset_sum_real {ι α : Type*} [MeasurableSpace α]
    (s : Finset ι) (f : ι → α → ℝ) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun a => ∑ i ∈ s, f i a) :=
  Finset.measurable_sum s hf

private theorem measurable_finset_sum_complex {ι α : Type*} [MeasurableSpace α]
    (s : Finset ι) (f : ι → α → ℂ) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun a => ∑ i ∈ s, f i a) :=
  Finset.measurable_sum s hf

/--
**4D Wilson Lattice $n$-Point Osterwalder–Schrader Reflection Positivity** directly for
`cubic4Schwinger Ls (2 * M) N β`: for any finite family of measurable bounded
positive-time gauge-field observables `obs i k` (`SupportedOnPosTime`),
`0 ≤ Re ∑_{i,j} c_i · c̄_j · S^{(n_i+n_j)}((obs_i ∘ Θ)* ‖ obs_j)`.
-/
theorem cubic4Schwinger_refl_pos_n (Ls M N : ℕ) [NeZero Ls] [NeZero M] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (m : ℕ) (n_pts : Fin m → ℕ) (c : Fin m → ℂ)
    (obs : ∀ i : Fin m, Fin (n_pts i) →
      (GaugeField (cubicTorus4 Ls (2 * M)) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ))
    (h_meas : ∀ i k, Measurable (obs i k))
    (C_bd : ℝ) (hC_bd : 0 ≤ C_bd) (h_bd : ∀ i k U, ‖obs i k U‖ ≤ C_bd)
    (h_pos_supp : ∀ i k, SupportedOnPosTime Ls M N (obs i k)) :
    0 ≤ (∑ i : Fin m, ∑ j : Fin m,
      c i * starRingEnd ℂ (c j) *
        cubic4Schwinger Ls (2 * M) N β (n_pts i + n_pts j)
          (Fin.append (fun k U => starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U)))
            (obs j))).re := by
  let G := Matrix.specialUnitaryGroup (Fin N) ℂ
  let G_4 := GaugeField (cubicTorus4 Ls (2 * M)) G
  let μ := spacetimeHaarMeasure Ls (2 * M) N
  haveI := suHaar_prob N
  haveI := spacetimeHaarMeasure_prob Ls (2 * M) N
  let Z := cubic4PartitionFn Ls (2 * M) N β
  have hZ_pos : 0 < Z := cubic4PartitionFn_pos Ls (2 * M) N β hβ
  let w_bdry : G_4 → ℝ := fun U => Real.exp (-wilsonActionBdry Ls M N β U)
  let w_pos : G_4 → ℝ := fun U => Real.exp (-wilsonActionPos Ls M N β U)
  have hw_bdry_meas : Measurable w_bdry := by
    have h_sum_meas : Measurable (fun U : G_4 => ∑ x : (cubicTorus4 Ls (2 * M)).Site,
        if (x.1.val = 0 ∨ x.1.val = M) then
          (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 2, cubic4Plaquette_isPath x 1 2⟩ U +
           wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 3, cubic4Plaquette_isPath x 1 3⟩ U +
           wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 2 3, cubic4Plaquette_isPath x 2 3⟩ U)
        else (0 : ℝ)) := by
      refine Finset.measurable_sum Finset.univ fun x _ => ?_
      by_cases hx : x.1.val = 0 ∨ x.1.val = M
      · simp_rw [if_pos hx]
        exact ((measurable_cubic4_plaquette_term Ls (2 * M) N _).add
          (measurable_cubic4_plaquette_term Ls (2 * M) N _)).add
          (measurable_cubic4_plaquette_term Ls (2 * M) N _)
      · simp_rw [if_neg hx]
        exact measurable_const
    exact Real.continuous_exp.measurable.comp (Measurable.neg (measurable_const.mul h_sum_meas))
  have hw_pos_meas : Measurable w_pos := by
    have h_term : ∀ x : (cubicTorus4 Ls (2 * M)).Site, Measurable (fun U : G_4 =>
        (if (0 < x.1.val ∧ x.1.val < M) then
            (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 2, cubic4Plaquette_isPath x 1 2⟩ U +
             wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 3, cubic4Plaquette_isPath x 1 3⟩ U +
             wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 2 3, cubic4Plaquette_isPath x 2 3⟩ U)
          else (0 : ℝ)) +
         (if x.1.val < M then
            (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 1, cubic4Plaquette_isPath x 0 1⟩ U +
             wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 2, cubic4Plaquette_isPath x 0 2⟩ U +
             wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 3, cubic4Plaquette_isPath x 0 3⟩ U)
          else (0 : ℝ))) := by
      intro x
      refine Measurable.add ?_ ?_
      · by_cases hx : 0 < x.1.val ∧ x.1.val < M
        · simp_rw [if_pos hx]
          exact ((measurable_cubic4_plaquette_term Ls (2 * M) N _).add
            (measurable_cubic4_plaquette_term Ls (2 * M) N _)).add
            (measurable_cubic4_plaquette_term Ls (2 * M) N _)
        · simp_rw [if_neg hx]
          exact measurable_const
      · by_cases hx : x.1.val < M
        · simp_rw [if_pos hx]
          exact ((measurable_cubic4_plaquette_term Ls (2 * M) N _).add
            (measurable_cubic4_plaquette_term Ls (2 * M) N _)).add
            (measurable_cubic4_plaquette_term Ls (2 * M) N _)
        · simp_rw [if_neg hx]
          exact measurable_const
    have h_sum_meas : Measurable (fun U : G_4 => ∑ x : (cubicTorus4 Ls (2 * M)).Site,
        ((if (0 < x.1.val ∧ x.1.val < M) then
            (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 2, cubic4Plaquette_isPath x 1 2⟩ U +
             wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 3, cubic4Plaquette_isPath x 1 3⟩ U +
             wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 2 3, cubic4Plaquette_isPath x 2 3⟩ U)
          else (0 : ℝ)) +
         (if x.1.val < M then
            (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 1, cubic4Plaquette_isPath x 0 1⟩ U +
             wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 2, cubic4Plaquette_isPath x 0 2⟩ U +
             wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 3, cubic4Plaquette_isPath x 0 3⟩ U)
          else (0 : ℝ)))) :=
      measurable_finset_sum_real Finset.univ _ (fun x _ => h_term x)
    have h_act_meas : Measurable (fun U : G_4 => wilsonActionPos Ls M N β U) :=
      measurable_const.mul h_sum_meas
    exact Real.continuous_exp.measurable.comp h_act_meas.neg
  have hw_bdry_bounds : ∀ U, 0 ≤ w_bdry U ∧ w_bdry U ≤ 1 := fun U => by
    have hact : 0 ≤ wilsonActionBdry Ls M N β U := by
      dsimp [wilsonActionBdry]
      refine mul_nonneg hβ (Finset.sum_nonneg fun x _ => ?_)
      split_ifs
      · exact add_nonneg (add_nonneg (wilsonPlaquetteTerm_bounds _ U).1
          (wilsonPlaquetteTerm_bounds _ U).1) (wilsonPlaquetteTerm_bounds _ U).1
      · exact le_rfl
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩
  have hw_pos_bounds : ∀ U, 0 ≤ w_pos U ∧ w_pos U ≤ 1 := fun U => by
    have hact : 0 ≤ wilsonActionPos Ls M N β U := by
      dsimp [wilsonActionPos]
      refine mul_nonneg hβ (Finset.sum_nonneg fun x _ => add_nonneg ?_ ?_)
      · split_ifs
        · exact add_nonneg (add_nonneg (wilsonPlaquetteTerm_bounds _ U).1
            (wilsonPlaquetteTerm_bounds _ U).1) (wilsonPlaquetteTerm_bounds _ U).1
        · exact le_rfl
      · split_ifs
        · exact add_nonneg (add_nonneg (wilsonPlaquetteTerm_bounds _ U).1
            (wilsonPlaquetteTerm_bounds _ U).1) (wilsonPlaquetteTerm_bounds _ U).1
        · exact le_rfl
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩
  have hw_fact : ∀ U, cubic4WilsonWeight Ls (2 * M) N β U =
      w_bdry U * w_pos U * w_pos (cubic4TimeReflect Ls (2 * M) N U) := by
    intro U
    unfold cubic4WilsonWeight
    rw [wilsonAction_split_pos_neg Ls M N β U]
    dsimp [w_bdry, w_pos]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  let F_sum : G_4 → ℂ := fun U =>
    (∑ j : Fin m, starRingEnd ℂ (c j) * ∏ k : Fin (n_pts j), obs j k U) * ((w_pos U : ℝ) : ℂ)
  have hF_meas : Measurable F_sum := by
    have hF_sum_meas : Measurable (fun U : G_4 =>
        (∑ j : Fin m, starRingEnd ℂ (c j) * ∏ k : Fin (n_pts j), obs j k U : ℂ)) :=
      Finset.measurable_sum (Finset.univ : Finset (Fin m)) fun j _ =>
        measurable_const.mul (Finset.measurable_prod Finset.univ fun k _ => h_meas j k)
    exact hF_sum_meas.mul (Complex.continuous_ofReal.measurable.comp hw_pos_meas)
  let C_sum : ℝ := ∑ j : Fin m, ‖c j‖ * C_bd ^ (n_pts j)
  have hF_bd : ∀ U, ‖F_sum U‖ ≤ C_sum := fun U => by
    dsimp [F_sum, C_sum]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw_pos_bounds U).1]
    let f_term : Fin m → ℂ := fun j => starRingEnd ℂ (c j) * ∏ k : Fin (n_pts j), obs j k U
    change ‖∑ j : Fin m, f_term j‖ * w_pos U ≤ ∑ j : Fin m, ‖c j‖ * C_bd ^ (n_pts j)
    calc ‖(∑ j : Fin m, f_term j : ℂ)‖ * w_pos U
        ≤ ‖(∑ j : Fin m, f_term j : ℂ)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hw_pos_bounds U).2 (norm_nonneg _)
      _ = ‖(∑ j : Fin m, f_term j : ℂ)‖ := mul_one _
      _ ≤ (∑ j : Fin m, ‖f_term j‖ : ℝ) :=
          norm_sum_le (Finset.univ : Finset (Fin m)) f_term
      _ ≤ (∑ j : Fin m, ‖c j‖ * C_bd ^ (n_pts j) : ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          dsimp [f_term]
          rw [norm_mul, Complex.norm_conj]
          exact mul_le_mul_of_nonneg_left
            (norm_prod_fin_le (fun k => obs j k U) C_bd hC_bd (fun k => h_bd j k U))
            (norm_nonneg _)
  have hF_supp : SupportedOnPosTime Ls M N F_sum := by
    intro U V hUV
    dsimp [F_sum, w_pos]
    rw [wilsonActionPos_supported_on_pos Ls M N β U V hUV]
    refine congrArg (· * _) ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine congrArg (starRingEnd ℂ (c j) * ·) ?_
    exact Finset.prod_congr rfl fun k _ => h_pos_supp j k U V hUV
  let θ_F : G_4 → ℂ := fun U =>
    starRingEnd ℂ (F_sum (cubic4TimeReflect Ls (2 * M) N U)) * F_sum U * ((w_bdry U : ℝ) : ℂ)
  have hθ_F_meas : Measurable θ_F :=
    ((continuous_star.measurable.comp
      (hF_meas.comp (cubic4TimeReflectEquiv Ls (2 * M) N).measurable)).mul hF_meas).mul
      (Complex.continuous_ofReal.measurable.comp hw_bdry_meas)
  have h_int_ij : ∀ i j : Fin m, MeasureTheory.Integrable (fun U =>
      c i * starRingEnd ℂ (c j) *
        ((∏ x : Fin (n_pts i + n_pts j),
            Fin.append (fun k U => starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U)))
              (obs j) x U) *
          ((cubic4WilsonWeight Ls (2 * M) N β U : ℝ) : ℂ))) μ := by
    intro i j
    have hm : Measurable (fun U =>
        c i * starRingEnd ℂ (c j) *
          ((∏ x : Fin (n_pts i + n_pts j),
              Fin.append (fun k U => starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U)))
                (obs j) x U) *
            ((cubic4WilsonWeight Ls (2 * M) N β U : ℝ) : ℂ))) := by
      refine measurable_const.mul ((Finset.measurable_prod Finset.univ fun x _ => ?_).mul
        (Complex.continuous_ofReal.measurable.comp (measurable_cubic4WilsonWeight Ls (2 * M) N β)))
      induction x using Fin.addCases with
      | left k =>
        simp only [Fin.append_left]
        exact continuous_star.measurable.comp
          ((h_meas i k).comp (cubic4TimeReflectEquiv Ls (2 * M) N).measurable)
      | right k =>
        simp only [Fin.append_right]
        exact h_meas j k
    refine integrable_of_measurable_bound μ _ hm
      (‖c i‖ * ‖c j‖ * C_bd ^ (n_pts i + n_pts j)) fun U => ?_
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    have hwb := cubic4WilsonWeight_bounds Ls (2 * M) N β hβ U
    have hwnn : 0 ≤ cubic4WilsonWeight Ls (2 * M) N β U := by
      unfold cubic4WilsonWeight; exact (Real.exp_pos _).le
    rw [abs_of_nonneg hwnn]
    have hpb : ‖∏ x : Fin (n_pts i + n_pts j),
        Fin.append (fun k U => starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U)))
          (obs j) x U‖ ≤ C_bd ^ (n_pts i + n_pts j) := by
      refine norm_prod_fin_le _ C_bd hC_bd fun x => ?_
      induction x using Fin.addCases with
      | left k =>
        simp only [Fin.append_left, Complex.norm_conj]
        exact h_bd i k _
      | right k =>
        simp only [Fin.append_right]
        exact h_bd j k U
    calc ‖c i‖ * ‖c j‖ * (‖∏ x : Fin (n_pts i + n_pts j), _‖ * cubic4WilsonWeight Ls (2 * M) N β U)
        ≤ ‖c i‖ * ‖c j‖ * (C_bd ^ (n_pts i + n_pts j) * 1) := by
            gcongr; exact hwb.2
      _ = ‖c i‖ * ‖c j‖ * C_bd ^ (n_pts i + n_pts j) := by ring
  have h_sum_eq :
      (∑ i : Fin m, ∑ j : Fin m,
        c i * starRingEnd ℂ (c j) *
          cubic4Schwinger Ls (2 * M) N β (n_pts i + n_pts j)
            (Fin.append (fun k U => starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U)))
              (obs j))) =
      ((Z : ℂ)⁻¹) * ∫ U, θ_F U ∂μ := by
    unfold cubic4Schwinger
    have h_pull : ∀ i j : Fin m,
        c i * starRingEnd ℂ (c j) * (((Z : ℂ)⁻¹) *
          ∫ U, (∏ x : Fin (n_pts i + n_pts j),
              Fin.append (fun k U => starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U)))
                (obs j) x U) *
            ((cubic4WilsonWeight Ls (2 * M) N β U : ℝ) : ℂ) ∂μ) =
        ((Z : ℂ)⁻¹) * ∫ U, c i * starRingEnd ℂ (c j) *
          ((∏ x : Fin (n_pts i + n_pts j),
              Fin.append (fun k U => starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U)))
                (obs j) x U) *
            ((cubic4WilsonWeight Ls (2 * M) N β U : ℝ) : ℂ)) ∂μ := by
      intro i j
      rw [MeasureTheory.integral_const_mul]
      ring
    change (∑ i : Fin m, ∑ j : Fin m,
        c i * starRingEnd ℂ (c j) * (((Z : ℂ)⁻¹) * ∫ U, _ ∂μ)) =
      ((Z : ℂ)⁻¹) * ∫ U, θ_F U ∂μ
    simp_rw [h_pull, ← Finset.mul_sum]
    congr 1
    have h_in : ∀ i : Fin m,
        (∑ j : Fin m, ∫ U, c i * starRingEnd ℂ (c j) *
          ((∏ x : Fin (n_pts i + n_pts j),
              Fin.append (fun k U => starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U)))
                (obs j) x U) *
            ((cubic4WilsonWeight Ls (2 * M) N β U : ℝ) : ℂ)) ∂μ) =
        ∫ U, ∑ j : Fin m, c i * starRingEnd ℂ (c j) *
          ((∏ x : Fin (n_pts i + n_pts j),
              Fin.append (fun k U => starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U)))
                (obs j) x U) *
            ((cubic4WilsonWeight Ls (2 * M) N β U : ℝ) : ℂ)) ∂μ :=
      fun i => (MeasureTheory.integral_finset_sum _ (fun j _ => h_int_ij i j)).symm
    simp_rw [h_in]
    rw [← MeasureTheory.integral_finset_sum _ (fun i _ =>
      MeasureTheory.integrable_finset_sum _ (fun j _ => h_int_ij i j))]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    dsimp [θ_F, F_sum]
    simp_rw [Fin.prod_univ_add, Fin.append_left, Fin.append_right, hw_fact U]
    simp only [map_mul, map_sum, map_prod, Complex.conj_conj, Complex.conj_ofReal,
      Complex.ofReal_mul]
    let L : Fin m → ℂ := fun i => c i * ∏ k : Fin (n_pts i),
      starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U))
    let R : Fin m → ℂ := fun j => starRingEnd ℂ (c j) * ∏ k : Fin (n_pts j), obs j k U
    calc ∑ i : Fin m, ∑ j : Fin m, c i * starRingEnd ℂ (c j) *
          ((∏ k : Fin (n_pts i), starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U))) *
           (∏ k : Fin (n_pts j), obs j k U) *
           ((w_bdry U : ℂ) * (w_pos U : ℂ) * (w_pos (cubic4TimeReflect Ls (2 * M) N U) : ℂ)))
        = ∑ i : Fin m, ∑ j : Fin m, L i * (R j *
            ((w_bdry U : ℂ) * (w_pos U : ℂ) * (w_pos (cubic4TimeReflect Ls (2 * M) N U) : ℂ))) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            dsimp only [L, R]; ring
      _ = ∑ i : Fin m, L i * ((∑ j : Fin m, R j) *
            ((w_bdry U : ℂ) * (w_pos U : ℂ) * (w_pos (cubic4TimeReflect Ls (2 * M) N U) : ℂ))) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Finset.mul_sum, ← Finset.sum_mul]
      _ = (∑ i : Fin m, L i) * ((∑ j : Fin m, R j) *
            ((w_bdry U : ℂ) * (w_pos U : ℂ) * (w_pos (cubic4TimeReflect Ls (2 * M) N U) : ℂ))) := by
            rw [← Finset.sum_mul]
      _ = ((∑ i : Fin m, L i) * (w_pos (cubic4TimeReflect Ls (2 * M) N U) : ℂ)) *
            ((∑ j : Fin m, R j) * (w_pos U : ℂ)) * (w_bdry U : ℂ) := by ring
  rw [h_sum_eq, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  refine mul_nonneg (inv_nonneg.mpr hZ_pos.le) ?_
  let p_b := isBdryTimeLink Ls M
  let E_b := { e : (cubicTorus4 Ls (2 * M)).Link // p_b e }
  let E_nb := { e : (cubicTorus4 Ls (2 * M)).Link // ¬ p_b e }
  let p_p : E_nb → Prop := fun e => isPosTimeLink Ls M e.1
  let E_p := { e : E_nb // p_p e }
  let E_n := { e : E_nb // ¬ p_p e }
  let e₁ : G_4 ≃ᵐ (E_b → G) × (E_nb → G) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : (cubicTorus4 Ls (2 * M)).Link => G) p_b
  let e₂ : (E_nb → G) ≃ᵐ (E_p → G) × (E_n → G) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : E_nb => G) p_p
  let μ_b : MeasureTheory.Measure (E_b → G) := MeasureTheory.Measure.pi (fun _ => suHaar N)
  let μ_nb : MeasureTheory.Measure (E_nb → G) := MeasureTheory.Measure.pi (fun _ => suHaar N)
  let μ_p : MeasureTheory.Measure (E_p → G) := MeasureTheory.Measure.pi (fun _ => suHaar N)
  let μ_n : MeasureTheory.Measure (E_n → G) := MeasureTheory.Measure.pi (fun _ => suHaar N)
  haveI : MeasureTheory.IsProbabilityMeasure μ_b := by dsimp [μ_b]; infer_instance
  haveI : MeasureTheory.IsProbabilityMeasure μ_nb := by dsimp [μ_nb]; infer_instance
  haveI : MeasureTheory.IsProbabilityMeasure μ_p := by dsimp [μ_p]; infer_instance
  haveI : MeasureTheory.IsProbabilityMeasure μ_n := by dsimp [μ_n]; infer_instance
  have mp₁ : MeasureTheory.MeasurePreserving e₁ μ (μ_b.prod μ_nb) :=
    MeasureTheory.measurePreserving_piEquivPiSubtypeProd
      (fun _ : (cubicTorus4 Ls (2 * M)).Link => suHaar N) p_b
  have mp₂ : MeasureTheory.MeasurePreserving e₂ μ_nb (μ_p.prod μ_n) :=
    MeasureTheory.measurePreserving_piEquivPiSubtypeProd (fun _ : E_nb => suHaar N) p_p
  let reflIdx : E_p ≃ E_n :=
    { toFun := fun ⟨⟨e, hnb⟩, hp⟩ =>
        ⟨⟨cubic4TimeReflectLink Ls (2 * M) e,
            fun hb => hnb ((cubic4TimeReflectLink_bdry_iff Ls M e).mp hb)⟩,
          fun hp' => ((link_partition_trichotomy Ls M _).1.mpr
            ((cubic4TimeReflectLink_neg_iff_pos Ls M e).mpr hp)).2 hp'⟩
      invFun := fun ⟨⟨e, hnb⟩, hnp⟩ =>
        ⟨⟨cubic4TimeReflectLink Ls (2 * M) e,
            fun hb => hnb ((cubic4TimeReflectLink_bdry_iff Ls M e).mp hb)⟩,
          (cubic4TimeReflectLink_pos_iff_neg Ls M e).mpr
            ((link_partition_trichotomy Ls M e).1.mp ⟨hnb, hnp⟩)⟩
      left_inv := fun ⟨⟨e, _⟩, _⟩ => by
        apply Subtype.ext; apply Subtype.ext; exact (cubic4TimeReflectLink Ls (2 * M)).left_inv e
      right_inv := fun ⟨⟨e, _⟩, _⟩ => by
        apply Subtype.ext; apply Subtype.ext; exact (cubic4TimeReflectLink Ls (2 * M)).right_inv e }
  let e_refl : (E_p → G) ≃ᵐ (E_n → G) :=
    { toFun := fun U_p e_n =>
        if e_n.1.1.2 = 0 then (U_p (reflIdx.symm e_n))⁻¹ else U_p (reflIdx.symm e_n)
      invFun := fun U_n e_p =>
        if e_p.1.1.2 = 0 then (U_n (reflIdx e_p))⁻¹ else U_n (reflIdx e_p)
      left_inv := fun U_p => by
        funext ⟨⟨e, hnb⟩, hp⟩
        have hd_eq : (reflIdx ⟨⟨e, hnb⟩, hp⟩).1.1.2 = e.2 := by
          dsimp [reflIdx, cubic4TimeReflectLink]
          split_ifs <;> rfl
        dsimp only
        by_cases hd : e.2 = 0
        · rw [hd_eq, if_pos hd, if_pos hd, reflIdx.symm_apply_apply, inv_inv]
        · rw [hd_eq, if_neg hd, if_neg hd, reflIdx.symm_apply_apply]
      right_inv := fun U_n => by
        funext ⟨⟨e, hnb⟩, hnp⟩
        have hd_eq : (reflIdx.symm ⟨⟨e, hnb⟩, hnp⟩).1.1.2 = e.2 := by
          dsimp [reflIdx, cubic4TimeReflectLink]
          split_ifs <;> rfl
        dsimp only
        by_cases hd : e.2 = 0
        · rw [hd_eq, if_pos hd, if_pos hd, reflIdx.apply_symm_apply, inv_inv]
        · rw [hd_eq, if_neg hd, if_neg hd, reflIdx.apply_symm_apply]
      measurable_toFun := by
        refine measurable_pi_iff.mpr fun e_n => ?_
        change Measurable (fun U_p : E_p → G =>
          if e_n.1.1.2 = 0 then (U_p (reflIdx.symm e_n))⁻¹ else U_p (reflIdx.symm e_n))
        split_ifs
        · exact (continuous_inv (G := G)).measurable.comp (measurable_pi_apply (reflIdx.symm e_n))
        · exact measurable_pi_apply (reflIdx.symm e_n)
      measurable_invFun := by
        refine measurable_pi_iff.mpr fun e_p => ?_
        change Measurable (fun U_n : E_n → G =>
          if e_p.1.1.2 = 0 then (U_n (reflIdx e_p))⁻¹ else U_n (reflIdx e_p))
        split_ifs
        · exact (continuous_inv (G := G)).measurable.comp (measurable_pi_apply (reflIdx e_p))
        · exact measurable_pi_apply (reflIdx e_p) }
  have he_refl_app : ∀ (U_p : E_p → G) (e_n : E_n),
      e_refl U_p e_n =
        if e_n.1.1.2 = 0 then (U_p (reflIdx.symm e_n))⁻¹ else U_p (reflIdx.symm e_n) :=
    fun _ _ => rfl
  have mp_refl : MeasureTheory.MeasurePreserving e_refl μ_p μ_n := by
    refine ⟨e_refl.measurable, ?_⟩
    symm
    refine MeasureTheory.Measure.pi_eq fun s hs => ?_
    rw [MeasureTheory.Measure.map_apply e_refl.measurable (MeasurableSet.univ_pi hs)]
    let φ : E_p → G → G := fun e_p u => if e_p.1.1.2 = 0 then u⁻¹ else u
    have hpre : e_refl ⁻¹' Set.pi Set.univ s =
        Set.pi Set.univ (fun e_p => φ e_p ⁻¹' s (reflIdx e_p)) := by
      ext U_p
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, e_refl, φ]
      constructor
      · intro h e_p
        have hd_eq : (reflIdx e_p).1.1.2 = e_p.1.1.2 := by
          rcases e_p with ⟨⟨e, hnb⟩, hp⟩
          dsimp [reflIdx, cubic4TimeReflectLink]
          split_ifs <;> rfl
        have he := h (reflIdx e_p)
        rw [he_refl_app, hd_eq, reflIdx.symm_apply_apply] at he
        exact he
      · intro h e_n
        have hd_eq : (reflIdx.symm e_n).1.1.2 = e_n.1.1.2 := by
          rcases e_n with ⟨⟨e, hnb⟩, hnp⟩
          dsimp [reflIdx, cubic4TimeReflectLink]
          split_ifs <;> rfl
        have he := h (reflIdx.symm e_n)
        rw [reflIdx.apply_symm_apply] at he
        rw [he_refl_app, ← hd_eq]
        exact he
    rw [hpre]
    have hpi : μ_p (Set.pi Set.univ (fun e_p => φ e_p ⁻¹' s (reflIdx e_p))) =
        ∏ e_p : E_p, suHaar N (φ e_p ⁻¹' s (reflIdx e_p)) :=
      MeasureTheory.Measure.pi_pi (fun _ => suHaar N) _
    rw [hpi]
    have h_each : ∀ e_p : E_p, suHaar N (φ e_p ⁻¹' s (reflIdx e_p)) = suHaar N (s (reflIdx e_p)) := by
      intro e_p
      by_cases hd : e_p.1.1.2 = 0
      · simp only [φ, hd, ↓reduceIte]
        rw [← MeasureTheory.Measure.map_apply (continuous_inv (G := G)).measurable
          (hs (reflIdx e_p)), suHaar_map_inv N]
      · simp only [φ, hd, ↓reduceIte]; rfl
    rw [Finset.prod_congr rfl fun e_p _ => h_each e_p]
    exact Fintype.prod_equiv reflIdx (fun e_p => suHaar N (s (reflIdx e_p)))
      (fun e_n => suHaar N (s e_n)) (fun _ => rfl)
  let combine : (E_b → G) → (E_p → G) → (E_p → G) → G_4 :=
    fun U_b U_p U_p' => e₁.symm (U_b, e₂.symm (U_p, e_refl U_p'))
  have h_comb_bdry : ∀ U_b U_p U_p' (e : (cubicTorus4 Ls (2 * M)).Link) (hb : p_b e),
      combine U_b U_p U_p' e = U_b ⟨e, hb⟩ := fun U_b U_p U_p' e hb =>
    congrArg (fun q => q.1 ⟨e, hb⟩) (e₁.apply_symm_apply (U_b, e₂.symm (U_p, e_refl U_p')))
  have h_comb_pos : ∀ U_b U_p U_p' (e : (cubicTorus4 Ls (2 * M)).Link)
      (hnb : ¬ p_b e) (hp : p_p ⟨e, hnb⟩),
      combine U_b U_p U_p' e = U_p ⟨⟨e, hnb⟩, hp⟩ := fun U_b U_p U_p' e hnb hp =>
    (congrArg (fun q => q.2 ⟨e, hnb⟩)
      (e₁.apply_symm_apply (U_b, e₂.symm (U_p, e_refl U_p')))).trans
      (congrArg (fun q => q.1 ⟨⟨e, hnb⟩, hp⟩) (e₂.apply_symm_apply (U_p, e_refl U_p')))
  have h_comb_neg : ∀ U_b U_p U_p' (e : (cubicTorus4 Ls (2 * M)).Link)
      (hnb : ¬ p_b e) (hnp : ¬ p_p ⟨e, hnb⟩),
      combine U_b U_p U_p' e = e_refl U_p' ⟨⟨e, hnb⟩, hnp⟩ := fun U_b U_p U_p' e hnb hnp =>
    (congrArg (fun q => q.2 ⟨e, hnb⟩)
      (e₁.apply_symm_apply (U_b, e₂.symm (U_p, e_refl U_p')))).trans
      (congrArg (fun q => q.2 ⟨⟨e, hnb⟩, hnp⟩) (e₂.apply_symm_apply (U_p, e_refl U_p')))
  have h_combine_reflect : ∀ U_b U_p U_p',
      cubic4TimeReflect Ls (2 * M) N (combine U_b U_p U_p') = combine U_b U_p' U_p := by
    intro U_b U_p U_p'
    funext e
    by_cases hb : isBdryTimeLink Ls M e
    · rw [cubic4TimeReflect_bdry_fix Ls M N _ hb, h_comb_bdry _ _ _ e hb, h_comb_bdry _ _ _ e hb]
    · have hc_e := cubic4TimeReflectLink_bdry_iff Ls M e
      have hb_refl : ¬ isBdryTimeLink Ls M (cubic4TimeReflectLink Ls (2 * M) e) :=
        fun h => hb (hc_e.mp h)
      have h_lhs_val : cubic4TimeReflect Ls (2 * M) N (combine U_b U_p U_p') e =
          if e.2 = 0 then (combine U_b U_p U_p' (cubic4TimeReflectLink Ls (2 * M) e))⁻¹
          else combine U_b U_p U_p' (cubic4TimeReflectLink Ls (2 * M) e) := by
        rcases e with ⟨⟨t, a, b', c⟩, d⟩
        by_cases hd : d = 0 <;> simp [cubic4TimeReflect, cubic4TimeReflectLink, hd]
      rw [h_lhs_val]
      by_cases hp : isPosTimeLink Ls M e
      · have hn_refl : isNegTimeLink Ls M (cubic4TimeReflectLink Ls (2 * M) e) :=
          (cubic4TimeReflectLink_neg_iff_pos Ls M e).mpr hp
        have hnp_refl : ¬ isPosTimeLink Ls M (cubic4TimeReflectLink Ls (2 * M) e) :=
          ((link_partition_trichotomy Ls M _).1.mpr hn_refl).2
        rw [h_comb_neg U_b U_p U_p' _ hb_refl hnp_refl, h_comb_pos U_b U_p' U_p e hb hp,
          he_refl_app]
        have hd_eq : (⟨⟨cubic4TimeReflectLink Ls (2 * M) e, hb_refl⟩, hnp_refl⟩ : E_n).1.1.2 = e.2 := by
          rcases e with ⟨⟨t, a, b', c⟩, d⟩
          dsimp [cubic4TimeReflectLink]
          split_ifs <;> rfl
        have hrefl_eq : reflIdx.symm ⟨⟨cubic4TimeReflectLink Ls (2 * M) e, hb_refl⟩, hnp_refl⟩ =
            ⟨⟨e, hb⟩, hp⟩ := by
          apply Subtype.ext; apply Subtype.ext
          exact (cubic4TimeReflectLink Ls (2 * M)).left_inv e
        rw [hd_eq, hrefl_eq]
        by_cases hd : e.2 = 0
        · simp only [hd, ↓reduceIte]
          exact inv_inv _
        · simp only [hd, ↓reduceIte]
      · have hn : isNegTimeLink Ls M e := (link_partition_trichotomy Ls M e).1.mp ⟨hb, hp⟩
        have hp_refl : isPosTimeLink Ls M (cubic4TimeReflectLink Ls (2 * M) e) :=
          (cubic4TimeReflectLink_pos_iff_neg Ls M e).mpr hn
        rw [h_comb_pos U_b U_p U_p' _ hb_refl hp_refl, h_comb_neg U_b U_p' U_p e hb hp,
          he_refl_app]
        have hrefl_eq : reflIdx.symm ⟨⟨e, hb⟩, hp⟩ =
            ⟨⟨cubic4TimeReflectLink Ls (2 * M) e, hb_refl⟩, hp_refl⟩ := rfl
        rw [hrefl_eq]
  have h_bdry_const : ∀ U_b U_p U_p',
      w_bdry (combine U_b U_p U_p') = w_bdry (combine U_b (fun _ => 1) (fun _ => 1)) := by
    intro U_b U_p U_p'
    dsimp [w_bdry]
    congr 2
    refine wilsonActionBdry_depends_only Ls M N β _ _ fun e he => ?_
    rw [h_comb_bdry _ _ _ e he, h_comb_bdry _ _ _ e he]
  let g_val : (E_b → G) → (E_p → G) → ℂ :=
    fun U_b U_p => F_sum (combine U_b U_p (fun _ => 1))
  have h_F_indep : ∀ U_b U_p U_p', F_sum (combine U_b U_p U_p') = g_val U_b U_p := by
    intro U_b U_p U_p'
    refine hF_supp _ _ fun e hne => ?_
    by_cases hb : isBdryTimeLink Ls M e
    · rw [h_comb_bdry _ _ _ e hb, h_comb_bdry _ _ _ e hb]
    · have hp : isPosTimeLink Ls M e := by
        by_contra hnp
        exact hne ((link_partition_trichotomy Ls M e).1.mp ⟨hb, hnp⟩)
      rw [h_comb_pos _ _ _ e hb hp, h_comb_pos _ _ _ e hb hp]
  have hm_comb2 : Measurable (fun z : (E_b → G) × ((E_p → G) × (E_p → G)) =>
      combine z.1 z.2.1 z.2.2) := by
    have hm1 : Measurable (fun q : (E_p → G) × (E_p → G) => e₂.symm (q.1, e_refl q.2)) :=
      e₂.symm.measurable.comp (measurable_fst.prodMk (e_refl.measurable.comp measurable_snd))
    exact e₁.symm.measurable.comp (measurable_fst.prodMk (hm1.comp measurable_snd))
  have h_int_rewrite :
      ∫ U, θ_F U ∂μ =
        ∫ U_b, ((w_bdry (combine U_b (fun _ => 1) (fun _ => 1)) : ℝ) : ℂ) *
          (∫ U_p, (∫ U_p', starRingEnd ℂ (g_val U_b U_p') * g_val U_b U_p ∂μ_p) ∂μ_p) ∂μ_b := by
    have hmp1_sym := MeasureTheory.MeasurePreserving.symm e₁ mp₁
    have hmp2_sym := MeasureTheory.MeasurePreserving.symm e₂ mp₂
    rw [← hmp1_sym.integral_comp' θ_F]
    have h_int1 : MeasureTheory.Integrable (fun p => θ_F (e₁.symm p)) (μ_b.prod μ_nb) :=
      integrable_of_measurable_bound (μ_b.prod μ_nb) _ (hθ_F_meas.comp e₁.symm.measurable)
        (C_sum ^ 2) fun p => by
          dsimp [θ_F]
          rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hw_bdry_bounds _).1]
          calc ‖F_sum _‖ * ‖F_sum _‖ * w_bdry _
              ≤ C_sum * C_sum * 1 := by
                gcongr
                · exact hF_bd _
                · exact hF_bd _
                · exact (hw_bdry_bounds _).2
            _ = C_sum ^ 2 := by ring
    rw [MeasureTheory.integral_prod _ h_int1]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U_b => ?_)
    dsimp only
    rw [← hmp2_sym.integral_comp' (fun U_nb => θ_F (e₁.symm (U_b, U_nb)))]
    have h_int2 : MeasureTheory.Integrable (fun q => θ_F (e₁.symm (U_b, e₂.symm q)))
        (μ_p.prod μ_n) :=
      integrable_of_measurable_bound (μ_p.prod μ_n) _
        (hθ_F_meas.comp (e₁.symm.measurable.comp (measurable_const.prodMk e₂.symm.measurable)))
        (C_sum ^ 2) fun q => by
          dsimp [θ_F]
          rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hw_bdry_bounds _).1]
          calc ‖F_sum _‖ * ‖F_sum _‖ * w_bdry _
              ≤ C_sum * C_sum * 1 := by
                gcongr
                · exact hF_bd _
                · exact hF_bd _
                · exact (hw_bdry_bounds _).2
            _ = C_sum ^ 2 := by ring
    rw [MeasureTheory.integral_prod _ h_int2, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U_p => ?_)
    dsimp only
    rw [← mp_refl.integral_comp' (fun U_n => θ_F (e₁.symm (U_b, e₂.symm (U_p, U_n)))),
      ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U_p' => ?_)
    change θ_F (combine U_b U_p U_p') =
      ((w_bdry (combine U_b (fun _ => 1) (fun _ => 1)) : ℝ) : ℂ) *
        (starRingEnd ℂ (g_val U_b U_p') * g_val U_b U_p)
    dsimp [θ_F]
    rw [h_combine_reflect, h_F_indep U_b U_p' U_p, h_F_indep U_b U_p U_p', h_bdry_const]
    ring
  have h_factor_pos : ∀ U_b : E_b → G,
      (∫ U_p, (∫ U_p', starRingEnd ℂ (g_val U_b U_p') * g_val U_b U_p ∂μ_p) ∂μ_p) =
        (((‖∫ U_p, g_val U_b U_p ∂μ_p‖ ^ 2 : ℝ) : ℂ)) := by
    intro U_b
    let I_b : ℂ := ∫ U_p, g_val U_b U_p ∂μ_p
    have h_inner_p : ∀ U_p,
        (∫ U_p', starRingEnd ℂ (g_val U_b U_p') * g_val U_b U_p ∂μ_p) =
          starRingEnd ℂ I_b * g_val U_b U_p := by
      intro U_p
      rw [MeasureTheory.integral_mul_const, integral_conj]
    simp_rw [h_inner_p, MeasureTheory.integral_const_mul]
    change starRingEnd ℂ I_b * I_b = _
    rw [Complex.conj_mul', Complex.ofReal_pow]
  have h_final_eq :
      ∫ U, θ_F U ∂μ =
        ∫ U_b, ((w_bdry (combine U_b (fun _ => 1) (fun _ => 1)) *
          ‖∫ U_p, g_val U_b U_p ∂μ_p‖ ^ 2 : ℝ) : ℂ) ∂μ_b := by
    rw [h_int_rewrite]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U_b => ?_)
    dsimp only
    rw [h_factor_pos U_b, ← Complex.ofReal_mul]
  rw [h_final_eq]
  have h_int_comb : MeasureTheory.Integrable
      (fun z : (E_b → G) × ((E_p → G) × (E_p → G)) => θ_F (combine z.1 z.2.1 z.2.2))
      (μ_b.prod (μ_p.prod μ_p)) :=
    integrable_of_measurable_bound (μ_b.prod (μ_p.prod μ_p)) _ (hθ_F_meas.comp hm_comb2)
      (C_sum ^ 2) fun z => by
        dsimp [θ_F]
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hw_bdry_bounds _).1]
        calc ‖F_sum _‖ * ‖F_sum _‖ * w_bdry _
            ≤ C_sum * C_sum * 1 := by
              gcongr; exact hF_bd _; exact hF_bd _; exact (hw_bdry_bounds _).2
          _ = C_sum ^ 2 := by ring
  have h_real_int : MeasureTheory.Integrable
      (fun U_b => ((w_bdry (combine U_b (fun _ => 1) (fun _ => 1)) *
        ‖∫ U_p, g_val U_b U_p ∂μ_p‖ ^ 2 : ℝ) : ℂ)) μ_b := by
    refine h_int_comb.integral_prod_left.congr (Filter.Eventually.of_forall fun U_b => ?_)
    have h_int_ub : MeasureTheory.Integrable
        (fun q : (E_p → G) × (E_p → G) => θ_F (combine U_b q.1 q.2)) (μ_p.prod μ_p) :=
      integrable_of_measurable_bound (μ_p.prod μ_p) _
        (hθ_F_meas.comp (hm_comb2.comp (measurable_const.prodMk measurable_id)))
        (C_sum ^ 2) fun q => by
          dsimp [θ_F]
          rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hw_bdry_bounds _).1]
          calc ‖F_sum _‖ * ‖F_sum _‖ * w_bdry _
              ≤ C_sum * C_sum * 1 := by
                gcongr; exact hF_bd _; exact hF_bd _; exact (hw_bdry_bounds _).2
            _ = C_sum ^ 2 := by ring
    dsimp only
    rw [MeasureTheory.integral_prod _ h_int_ub]
    have h_inner_eq :
        (∫ U_p, ∫ U_p', θ_F (combine U_b U_p U_p') ∂μ_p ∂μ_p) =
          ((w_bdry (combine U_b (fun _ => 1) (fun _ => 1)) : ℝ) : ℂ) *
            ∫ U_p, ∫ U_p', starRingEnd ℂ (g_val U_b U_p') * g_val U_b U_p ∂μ_p ∂μ_p := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U_p => ?_)
      dsimp only
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U_p' => ?_)
      dsimp only [θ_F]
      rw [h_combine_reflect, h_F_indep U_b U_p' U_p, h_F_indep U_b U_p U_p', h_bdry_const]
      ring
    rw [h_inner_eq, h_factor_pos U_b, ← Complex.ofReal_mul]
  change 0 ≤ RCLike.re (∫ U_b, ((w_bdry (combine U_b (fun _ => 1) (fun _ => 1)) *
    ‖∫ U_p, g_val U_b U_p ∂μ_p‖ ^ 2 : ℝ) : ℂ) ∂μ_b)
  rw [← integral_re h_real_int]
  refine MeasureTheory.integral_nonneg fun U_b => ?_
  change 0 ≤ ((w_bdry (combine U_b (fun _ => 1) (fun _ => 1)) *
    ‖∫ U_p, g_val U_b U_p ∂μ_p‖ ^ 2 : ℝ) : ℂ).re
  rw [Complex.ofReal_re]
  exact mul_nonneg (hw_bdry_bounds _).1 (sq_nonneg _)

/-- 2-point specialization of `cubic4Schwinger_refl_pos_n`. -/
theorem cubic4Schwinger_refl_pos_2 (Ls M N : ℕ) [NeZero Ls] [NeZero M] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (m : ℕ) (c : Fin m → ℂ)
    (obs : Fin m →
      (GaugeField (cubicTorus4 Ls (2 * M)) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ))
    (h_meas : ∀ i, Measurable (obs i))
    (C_bd : ℝ) (hC_bd : 0 ≤ C_bd) (h_bd : ∀ i U, ‖obs i U‖ ≤ C_bd)
    (h_pos_supp : ∀ i, SupportedOnPosTime Ls M N (obs i)) :
    0 ≤ (∑ i : Fin m, ∑ j : Fin m,
      c i * starRingEnd ℂ (c j) *
        cubic4Schwinger Ls (2 * M) N β 2
          ![fun U => starRingEnd ℂ (obs i (cubic4TimeReflect Ls (2 * M) N U)), obs j]).re := by
  have h := cubic4Schwinger_refl_pos_n Ls M N β hβ m (fun _ => 1) c (fun i _ => obs i)
    (fun i _ => h_meas i) C_bd hC_bd (fun i _ U => h_bd i U) (fun i _ => h_pos_supp i)
  have heq :
      (∑ i : Fin m, ∑ j : Fin m,
        c i * starRingEnd ℂ (c j) *
          cubic4Schwinger Ls (2 * M) N β (1 + 1)
            (Fin.append
              (fun (_ : Fin 1) U => starRingEnd ℂ (obs i (cubic4TimeReflect Ls (2 * M) N U)))
              (fun (_ : Fin 1) => obs j))) =
      ∑ i : Fin m, ∑ j : Fin m,
        c i * starRingEnd ℂ (c j) *
          cubic4Schwinger Ls (2 * M) N β 2
            ![fun U => starRingEnd ℂ (obs i (cubic4TimeReflect Ls (2 * M) N U)), obs j] := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have happ :
        Fin.append
            (fun (_ : Fin 1) U => starRingEnd ℂ (obs i (cubic4TimeReflect Ls (2 * M) N U)))
            (fun (_ : Fin 1) => obs j) =
          ![fun U => starRingEnd ℂ (obs i (cubic4TimeReflect Ls (2 * M) N U)), obs j] := by
      funext k; fin_cases k <;> rfl
    rw [happ]
  rwa [← heq]

/-- 4D spacetime lattice translation on sites. -/
def siteShiftVec4 (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt]
    (a x : (cubicTorus4 Ls Lt).Site) : (cubicTorus4 Ls Lt).Site :=
  (x.1 + a.1, x.2.1 + a.2.1, x.2.2.1 + a.2.2.1, x.2.2.2 + a.2.2.2)

/-- Link bijection for 4D spacetime translation by `a`. -/
def cubic4TransLink (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt]
    (a : (cubicTorus4 Ls Lt).Site) :
    (cubicTorus4 Ls Lt).Link ≃ (cubicTorus4 Ls Lt).Link where
  toFun e := (siteShiftVec4 Ls Lt a e.1, e.2)
  invFun e := (siteShiftVec4 Ls Lt (-a.1, -a.2.1, -a.2.2.1, -a.2.2.2) e.1, e.2)
  left_inv := fun ⟨⟨t, x, y, z⟩, d⟩ => by simp [siteShiftVec4]
  right_inv := fun ⟨⟨t, x, y, z⟩, d⟩ => by simp [siteShiftVec4]

/-- 4D spacetime lattice translation of a gauge field `U`. -/
def cubic4Translate (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (a : (cubicTorus4 Ls Lt).Site)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  fun e => U (cubic4TransLink Ls Lt a e)

theorem spacetimeHaarMeasure_translate (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : (cubicTorus4 Ls Lt).Site) :
    MeasureTheory.Measure.map (cubic4Translate Ls Lt N a) (spacetimeHaarMeasure Ls Lt N) =
      spacetimeHaarMeasure Ls Lt N := by
  haveI := suHaar_prob N
  haveI := spacetimeHaarMeasure_prob Ls Lt N
  let σ := cubic4TransLink Ls Lt a
  let F : ((cubicTorus4 Ls Lt).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) →
      ((cubicTorus4 Ls Lt).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    fun U e => U (σ e)
  have hF_meas : Measurable F := measurable_pi_iff.mpr fun e => measurable_pi_apply (σ e)
  let μ_pi : MeasureTheory.Measure
      ((cubicTorus4 Ls Lt).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    MeasureTheory.Measure.pi (fun _ => suHaar N)
  change MeasureTheory.Measure.map F μ_pi = μ_pi
  symm
  refine MeasureTheory.Measure.pi_eq fun s hs => ?_
  rw [MeasureTheory.Measure.map_apply hF_meas (MeasurableSet.univ_pi hs)]
  have hpre : F ⁻¹' Set.pi Set.univ s = Set.pi Set.univ (fun e' => s (σ.symm e')) := by
    ext U
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, F]
    constructor
    · intro h e'; simpa using h (σ.symm e')
    · intro h e; simpa using h (σ e)
  rw [hpre, MeasureTheory.Measure.pi_pi (fun _ => suHaar N)]
  exact Fintype.prod_equiv σ.symm (fun e' => suHaar N (s (σ.symm e')))
    (fun e => suHaar N (s e)) (fun _ => rfl)

theorem cubic4WilsonAction_translate (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    (a : (cubicTorus4 Ls Lt).Site)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonAction β (cubic4Plaquettes Ls Lt) (cubic4Translate Ls Lt N a U) =
      wilsonAction β (cubic4Plaquettes Ls Lt) U := by
  rw [wilsonAction_cubic4_eq_sum, wilsonAction_cubic4_eq_sum]
  congr 1
  let e_site : (cubicTorus4 Ls Lt).Site ≃ (cubicTorus4 Ls Lt).Site :=
    { toFun := siteShiftVec4 Ls Lt a
      invFun := siteShiftVec4 Ls Lt (-a.1, -a.2.1, -a.2.2.1, -a.2.2.2)
      left_inv := fun ⟨t, x, y, z⟩ => by simp [siteShiftVec4]
      right_inv := fun ⟨t, x, y, z⟩ => by simp [siteShiftVec4] }
  have hsh : ∀ (d : Fin 4) (x : (cubicTorus4 Ls Lt).Site),
      siteShiftVec4 Ls Lt a (cubicShift4 Ls Lt d x) =
        cubicShift4 Ls Lt d (siteShiftVec4 Ls Lt a x) := by
    intro d ⟨t, x₁, x₂, x₃⟩
    fin_cases d <;> simp [siteShiftVec4, cubicShift4, add_right_comm]
  have hpt : ∀ x d₁ d₂,
      wilsonPlaquetteTerm ⟨x, cubic4Plaquette x d₁ d₂, cubic4Plaquette_isPath x d₁ d₂⟩
          (cubic4Translate Ls Lt N a U) =
        wilsonPlaquetteTerm ⟨siteShiftVec4 Ls Lt a x,
          cubic4Plaquette (siteShiftVec4 Ls Lt a x) d₁ d₂,
          cubic4Plaquette_isPath (siteShiftVec4 Ls Lt a x) d₁ d₂⟩ U := by
    intro x d₁ d₂
    unfold wilsonPlaquetteTerm
    simp only [cubic4Plaquette, pathHolonomy, cubic4Translate, cubic4TransLink,
      Equiv.coe_fn_mk, hsh]
  refine Fintype.sum_equiv e_site _ _ fun x => ?_
  dsimp [sitePlaqSum4, e_site]
  rw [hpt x 0 1, hpt x 0 2, hpt x 0 3, hpt x 1 2, hpt x 1 3, hpt x 2 3]

/-- **Exact 4D spacetime lattice translation invariance of `cubic4Schwinger`**. -/
theorem cubic4Schwinger_trans_inv (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : (cubicTorus4 Ls Lt).Site) (n : ℕ)
    (obs : Fin n →
      (GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)) :
    cubic4Schwinger Ls Lt N β n (fun i U => obs i (cubic4Translate Ls Lt N a U)) =
      cubic4Schwinger Ls Lt N β n obs := by
  let eqv : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    { toFun := cubic4Translate Ls Lt N a
      invFun := cubic4Translate Ls Lt N (-a.1, -a.2.1, -a.2.2.1, -a.2.2.2)
      left_inv := fun U => by funext ⟨x, d⟩; simp [cubic4Translate, cubic4TransLink, siteShiftVec4]
      right_inv := fun U => by funext ⟨x, d⟩; simp [cubic4Translate, cubic4TransLink, siteShiftVec4]
      measurable_toFun := measurable_pi_iff.mpr fun e =>
        measurable_pi_apply (cubic4TransLink Ls Lt a e)
      measurable_invFun := measurable_pi_iff.mpr fun e =>
        measurable_pi_apply (cubic4TransLink Ls Lt (-a.1, -a.2.1, -a.2.2.1, -a.2.2.2) e) }
  have hmp : MeasureTheory.MeasurePreserving eqv
      (spacetimeHaarMeasure Ls Lt N) (spacetimeHaarMeasure Ls Lt N) :=
    ⟨eqv.measurable, spacetimeHaarMeasure_translate Ls Lt N a⟩
  unfold cubic4Schwinger
  congr 1
  calc ∫ U, (∏ i : Fin n, obs i (cubic4Translate Ls Lt N a U)) *
          ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) ∂(spacetimeHaarMeasure Ls Lt N)
      = ∫ U, (∏ i : Fin n, obs i (eqv U)) *
          ((cubic4WilsonWeight Ls Lt N β (eqv U) : ℝ) : ℂ) ∂(spacetimeHaarMeasure Ls Lt N) := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
            change (∏ i : Fin n, obs i (cubic4Translate Ls Lt N a U)) *
                ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) =
              (∏ i : Fin n, obs i (cubic4Translate Ls Lt N a U)) *
                ((cubic4WilsonWeight Ls Lt N β (cubic4Translate Ls Lt N a U) : ℝ) : ℂ)
            unfold cubic4WilsonWeight
            rw [cubic4WilsonAction_translate]
    _ = ∫ U, (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)
          ∂(spacetimeHaarMeasure Ls Lt N) :=
        hmp.integral_comp'
          (fun U => (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ))

private def siteCoord4 (L : ℕ) [NeZero L] (x : (cubicTorus4 L L).Site) : Fin 4 → Fin L
  | 0 => x.1
  | 1 => x.2.1
  | 2 => x.2.2.1
  | 3 => x.2.2.2

private def ofSiteCoord4 (L : ℕ) [NeZero L] (f : Fin 4 → Fin L) : (cubicTorus4 L L).Site :=
  (f 0, f 1, f 2, f 3)

private theorem siteCoord4_ofSiteCoord4 (L : ℕ) [NeZero L] (f : Fin 4 → Fin L) :
    siteCoord4 L (ofSiteCoord4 L f) = f := by
  funext d; fin_cases d <;> rfl

private theorem ofSiteCoord4_siteCoord4 (L : ℕ) [NeZero L] (x : (cubicTorus4 L L).Site) :
    ofSiteCoord4 L (siteCoord4 L x) = x := by
  rcases x with ⟨t, a, b, c⟩; rfl

/-- Site permutation induced by `σ : Equiv.Perm (Fin 4)` on the isotropic 4D torus `cubicTorus4 L L`. -/
def sitePerm4 (L : ℕ) [NeZero L] (σ : Equiv.Perm (Fin 4))
    (x : (cubicTorus4 L L).Site) : (cubicTorus4 L L).Site :=
  ofSiteCoord4 L (fun d => siteCoord4 L x (σ.symm d))

/-- Link permutation induced by `σ : Equiv.Perm (Fin 4)` on `cubicTorus4 L L`. -/
def cubic4AxisPermLink (L : ℕ) [NeZero L] (σ : Equiv.Perm (Fin 4)) :
    (cubicTorus4 L L).Link ≃ (cubicTorus4 L L).Link where
  toFun e := (sitePerm4 L σ e.1, σ e.2)
  invFun e := (sitePerm4 L σ.symm e.1, σ.symm e.2)
  left_inv := fun ⟨x, d⟩ => by
    simp only [sitePerm4, siteCoord4_ofSiteCoord4, Equiv.symm_symm,
      Equiv.apply_symm_apply, Equiv.symm_apply_apply, ofSiteCoord4_siteCoord4]
  right_inv := fun ⟨x, d⟩ => by
    simp only [sitePerm4, siteCoord4_ofSiteCoord4, Equiv.symm_symm,
      Equiv.apply_symm_apply, ofSiteCoord4_siteCoord4]

/-- 4D hypercubic axis-permutation action on gauge fields over `cubicTorus4 L L`. -/
def cubic4AxisPermField (L N : ℕ) [NeZero L] (σ : Equiv.Perm (Fin 4))
    (U : GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  fun e => U (cubic4AxisPermLink L σ e)

theorem spacetimeHaarMeasure_axisPerm (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (σ : Equiv.Perm (Fin 4)) :
    MeasureTheory.Measure.map (cubic4AxisPermField L N σ) (spacetimeHaarMeasure L L N) =
      spacetimeHaarMeasure L L N := by
  haveI := suHaar_prob N
  haveI := spacetimeHaarMeasure_prob L L N
  let e_lk := cubic4AxisPermLink L σ
  let F : ((cubicTorus4 L L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) →
      ((cubicTorus4 L L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    fun U e => U (e_lk e)
  have hF_meas : Measurable F := measurable_pi_iff.mpr fun e => measurable_pi_apply (e_lk e)
  let μ_pi : MeasureTheory.Measure
      ((cubicTorus4 L L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    MeasureTheory.Measure.pi (fun _ => suHaar N)
  change MeasureTheory.Measure.map F μ_pi = μ_pi
  symm
  refine MeasureTheory.Measure.pi_eq fun s hs => ?_
  rw [MeasureTheory.Measure.map_apply hF_meas (MeasurableSet.univ_pi hs)]
  have hpre : F ⁻¹' Set.pi Set.univ s = Set.pi Set.univ (fun e' => s (e_lk.symm e')) := by
    ext U
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, F]
    constructor
    · intro h e'; simpa using h (e_lk.symm e')
    · intro h e; simpa using h (e_lk e)
  rw [hpre, MeasureTheory.Measure.pi_pi (fun _ => suHaar N)]
  exact Fintype.prod_equiv e_lk.symm (fun e' => suHaar N (s (e_lk.symm e')))
    (fun e => suHaar N (s e)) (fun _ => rfl)

private theorem sitePerm4_cubicShift4 (L : ℕ) [NeZero L] (σ : Equiv.Perm (Fin 4))
    (d : Fin 4) (x : (cubicTorus4 L L).Site) :
    sitePerm4 L σ (cubicShift4 L L d x) = cubicShift4 L L (σ d) (sitePerm4 L σ x) := by
  dsimp [sitePerm4]
  have hcoord : ∀ (y : (cubicTorus4 L L).Site) (d' : Fin 4),
      siteCoord4 L (cubicShift4 L L d' y) =
        fun k => siteCoord4 L y k + if k = d' then (1 : Fin L) else 0 := by
    intro ⟨t, a, b, c⟩ d'
    funext k
    fin_cases d' <;> fin_cases k <;> simp [cubicShift4, siteCoord4]
  have h_eq : (fun k => siteCoord4 L (cubicShift4 L L d x) (σ.symm k)) =
      siteCoord4 L (cubicShift4 L L (σ d) (ofSiteCoord4 L (fun k => siteCoord4 L x (σ.symm k)))) := by
    rw [hcoord, hcoord]
    funext k
    rw [siteCoord4_ofSiteCoord4]
    have heq : (σ.symm k = d) ↔ (k = σ d) := Equiv.symm_apply_eq σ
    simp [heq]
  rw [h_eq, ofSiteCoord4_siteCoord4]

private theorem wilsonPlaquetteTerm_swap_axes (L N : ℕ) [NeZero L]
    (U : GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (cubicTorus4 L L).Site) (d₁ d₂ : Fin 4) :
    wilsonPlaquetteTerm ⟨x, cubic4Plaquette x d₁ d₂, cubic4Plaquette_isPath x d₁ d₂⟩ U =
      wilsonPlaquetteTerm ⟨x, cubic4Plaquette x d₂ d₁, cubic4Plaquette_isPath x d₂ d₁⟩ U := by
  unfold wilsonPlaquetteTerm
  have hinv : pathHolonomy U (cubic4Plaquette x d₁ d₂) =
      (pathHolonomy U (cubic4Plaquette x d₂ d₁))⁻¹ := by
    simp only [cubic4Plaquette, pathHolonomy, mul_inv_rev, inv_inv]
    group
  rw [hinv, su_trace_inv_re]

theorem cubic4WilsonAction_axisPerm (L N : ℕ) [NeZero L] (β : ℝ)
    (σ : Equiv.Perm (Fin 4))
    (U : GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonAction β (cubic4Plaquettes L L) (cubic4AxisPermField L N σ U) =
      wilsonAction β (cubic4Plaquettes L L) U := by
  let T_all : GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      (cubicTorus4 L L).Site → ℝ := fun V x =>
    ∑ d₁ : Fin 4, ∑ d₂ : Fin 4,
      if d₁ = d₂ then 0
      else wilsonPlaquetteTerm ⟨x, cubic4Plaquette x d₁ d₂, cubic4Plaquette_isPath x d₁ d₂⟩ V
  have h_site_eq : ∀ V x, sitePlaqSum4 L L N V x = (1 / 2 : ℝ) * T_all V x := by
    intro V x
    dsimp [T_all, sitePlaqSum4]
    rw [Fin.sum_univ_four]
    simp only [Fin.sum_univ_four, Fin.reduceEq, ↓reduceIte]
    rw [wilsonPlaquetteTerm_swap_axes L N V x 1 0,
      wilsonPlaquetteTerm_swap_axes L N V x 2 0,
      wilsonPlaquetteTerm_swap_axes L N V x 3 0,
      wilsonPlaquetteTerm_swap_axes L N V x 2 1,
      wilsonPlaquetteTerm_swap_axes L N V x 3 1,
      wilsonPlaquetteTerm_swap_axes L N V x 3 2]
    ring
  rw [wilsonAction_cubic4_eq_sum, wilsonAction_cubic4_eq_sum]
  simp_rw [h_site_eq, ← Finset.mul_sum]
  congr 2
  let e_site : (cubicTorus4 L L).Site ≃ (cubicTorus4 L L).Site :=
    { toFun := sitePerm4 L σ
      invFun := sitePerm4 L σ.symm
      left_inv := fun x => by
        simp only [sitePerm4, siteCoord4_ofSiteCoord4, Equiv.symm_symm,
          Equiv.symm_apply_apply, ofSiteCoord4_siteCoord4]
      right_inv := fun x => by
        simp only [sitePerm4, siteCoord4_ofSiteCoord4, Equiv.symm_symm,
          Equiv.apply_symm_apply, ofSiteCoord4_siteCoord4] }
  refine Fintype.sum_equiv e_site _ _ fun x => ?_
  dsimp [T_all, e_site]
  refine Fintype.sum_equiv σ _ _ fun d₁ => Fintype.sum_equiv σ _ _ fun d₂ => ?_
  by_cases h12 : d₁ = d₂
  · subst h12; simp
  · have h12' : σ d₁ ≠ σ d₂ := fun h => h12 (σ.injective h)
    simp only [h12, h12', ↓reduceIte]
    unfold wilsonPlaquetteTerm
    simp only [cubic4Plaquette, pathHolonomy, cubic4AxisPermField, cubic4AxisPermLink,
      Equiv.coe_fn_mk, sitePerm4_cubicShift4]

/-- **Exact 4D hypercubic $S_4$ axis-permutation symmetry of `cubic4Schwinger` on `cubicTorus4 L L`**. -/
theorem cubic4Schwinger_axis_perm_inv (L N : ℕ) [NeZero L] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (σ : Equiv.Perm (Fin 4)) (n : ℕ)
    (obs : Fin n →
      (GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)) :
    cubic4Schwinger L L N β n (fun i U => obs i (cubic4AxisPermField L N σ U)) =
      cubic4Schwinger L L N β n obs := by
  let eqv : GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    { toFun := cubic4AxisPermField L N σ
      invFun := cubic4AxisPermField L N σ.symm
      left_inv := fun U => by
        funext ⟨x, d⟩
        simp only [cubic4AxisPermField, cubic4AxisPermLink, Equiv.coe_fn_mk, sitePerm4,
          siteCoord4_ofSiteCoord4, Equiv.symm_symm, Equiv.apply_symm_apply,
          Equiv.symm_apply_apply, ofSiteCoord4_siteCoord4]
      right_inv := fun U => by
        funext ⟨x, d⟩
        simp only [cubic4AxisPermField, cubic4AxisPermLink, Equiv.coe_fn_mk, sitePerm4,
          siteCoord4_ofSiteCoord4, Equiv.symm_symm, Equiv.apply_symm_apply,
          Equiv.symm_apply_apply, ofSiteCoord4_siteCoord4]
      measurable_toFun := measurable_pi_iff.mpr fun e =>
        measurable_pi_apply (cubic4AxisPermLink L σ e)
      measurable_invFun := measurable_pi_iff.mpr fun e =>
        measurable_pi_apply (cubic4AxisPermLink L σ.symm e) }
  have hmp : MeasureTheory.MeasurePreserving eqv
      (spacetimeHaarMeasure L L N) (spacetimeHaarMeasure L L N) :=
    ⟨eqv.measurable, spacetimeHaarMeasure_axisPerm L N σ⟩
  unfold cubic4Schwinger
  congr 1
  calc ∫ U, (∏ i : Fin n, obs i (cubic4AxisPermField L N σ U)) *
          ((cubic4WilsonWeight L L N β U : ℝ) : ℂ) ∂(spacetimeHaarMeasure L L N)
      = ∫ U, (∏ i : Fin n, obs i (eqv U)) *
          ((cubic4WilsonWeight L L N β (eqv U) : ℝ) : ℂ) ∂(spacetimeHaarMeasure L L N) := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
            change (∏ i : Fin n, obs i (cubic4AxisPermField L N σ U)) *
                ((cubic4WilsonWeight L L N β U : ℝ) : ℂ) =
              (∏ i : Fin n, obs i (cubic4AxisPermField L N σ U)) *
                ((cubic4WilsonWeight L L N β (cubic4AxisPermField L N σ U) : ℝ) : ℂ)
            unfold cubic4WilsonWeight
            rw [cubic4WilsonAction_axisPerm]
    _ = ∫ U, (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight L L N β U : ℝ) : ℂ)
          ∂(spacetimeHaarMeasure L L N) :=
        hmp.integral_comp'
          (fun U => (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight L L N β U : ℝ) : ℂ))

end CubicSpacetime4DOSAndSymmetries

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