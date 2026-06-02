-- Imscribing/Primitives/ZFCs.lean
-- ZFC$_s$: ZFC extended with Spatiality, Isotropy, and Homotopy Winding.
-- Spatial extension analogous to ZFCt's temporal extension.
-- Key asymmetry: ZFC_s is O_inf (P_pm_sym); ZFC_t is O_2dag (P_pm).
-- Fundamental collapse: ZFC_st = ZFC_s ⊗ ZFC_t = ZFC_t.

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Primitives.ZFCt
import Imscribing.Algebra
import Mathlib.Data.Real.Basic

namespace Imscribing.Primitives.ZFCs

open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality
open Imscribing.Primitives.ZFCt (zfc zfc_t)
set_option relaxedAutoImplicit true
set_option autoImplicit false
set_option linter.style.longLine false

/- ZFC baseline (spatial reference):
   zfc = { dim:=D_infty, top:=T_network, rel:=R_super, pol:=P_asym,
           fid:=F_hbar, kin:=K_slow, gran:=G_aleph, gram:=Gamma_and,
           crit:=Phi_c, chir:=H0, stoi:=n_m, prot:=Omega_0 } -/

/-- ZFC_s: ZFC with five spatial promotions.
    Space is isotropic (P_pm_sym = SO(n) invariance = Frobenius condition),
    concurrent (Gamma_or: spatial operations run in parallel),
    nested-domain (T_in: spaces have interiors and boundaries),
    metrically symmetric (R_dagger: d(x,y) = d(y,x)),
    and homotopy-protected (Omega_Z: π_n carry ℤ-valued winding invariants).
    Chirality does NOT promote: isotropic space has no preferred handedness. -/
def zfc_s : Imscription := {
  dim  := D_infty    -- infinite-dimensional: abstract spatial unfolding (unchanged)
  top  := T_in       -- inclusion/nested: spaces have bounded domains and interiors
  rel  := R_dagger   -- dagger/reciprocal: metric symmetry d(x,y) = d(y,x)
  pol  := P_pm_sym   -- Special Frobenius: spatial isotropy SO(n), μ ∘ δ = id
  fid  := F_hbar     -- quantum-coherent (unchanged)
  kin  := K_slow     -- thermally activated (unchanged)
  gran := G_aleph    -- global/fine-grained: all-to-all spatial correlations (unchanged)
  gram := Gamma_or   -- concurrent: spatial operations are parallel, not sequential
  crit := Phi_c      -- real-axis criticality (unchanged)
  chir := H0         -- achiral: isotropic space has no preferred handedness (unchanged)
  stoi := n_m        -- many-to-many spatial correspondences (unchanged)
  prot := Omega_Z }  -- integer winding: homotopy groups π_n carry ℤ-valued invariants

/-- The five promotion channels from ZFC to ZFC_s.
    (Chirality does not promote — compare with ZFCt's six promotions.) -/
def zfc_to_zfc_s_promotions : List (String × String) := [
  ("top",  "T_network → T_in"),
  ("rel",  "R_super → R_dagger"),
  ("pol",  "P_asym → P_pm_sym"),
  ("gram", "Gamma_and → Gamma_or"),
  ("prot", "Omega_0 → Omega_Z") ]

-- ============================================================
-- TIER ANALYSIS
-- ============================================================

/-- ZFC_s attains O_inf: spatial isotropy (P_pm_sym) at Phi_c satisfies the
    Frobenius condition — the same gate as quantum gravity and the Higgs field. -/
theorem zfc_s_is_O_inf : imscriptionTier zfc_s = .O_inf := by decide

/-- ZFC_t is O_inf: temporal Frobenius symmetry (P_pm_sym) at Phi_c.
    Space and time are structurally symmetric at the tier level — both Frobenius-open. -/
theorem zfc_t_is_O_inf : imscriptionTier zfc_t = .O_inf := by decide

/-- Both ZFC_s and ZFC_t are O_inf: the Frobenius condition holds in both extensions.
    They differ in HOW they attain it: isotropy (space) vs bidirectional chirality (time). -/
theorem both_extensions_O_inf :
    imscriptionTier zfc_s = .O_inf ∧ imscriptionTier zfc_t = .O_inf := by decide

-- ============================================================
-- SPACETIME TENSOR: ZFC_st = ZFC_s ⊗ ZFC_t
-- ============================================================

/-- ZFC_st: the spacetime imscription, computed as tensorProduct zfc_s zfc_t.
    Tensor rules (from Imscription.lean): P and F use min (bottleneck); all others max.
    · pol:  min(P_pm_sym, P_pm_sym) = P_pm_sym — no bottleneck: both extensions Frobenius
    · top:  max(T_in, T_odot)       = T_odot   — holographic topology dominates inclusion
    · rel:  max(R_dagger, R_lr)     = R_lr     — lateral exchange dominates metric symmetry
    · gram: max(Gamma_or, Gamma_seq) = Gamma_seq — sequentiality dominates concurrency
    · chir: max(H0, H2)             = H2       — temporal chirality dominates spatial isotropy
    · prot: max(Omega_Z, Omega_Z)   = Omega_Z
    Result: ZFC_st = ZFC_t. Temporal structure dominates all max-primitives;
    the Frobenius gate stays open because both partners already hold it. -/
def zfc_st : Imscription := {
  dim  := D_infty    -- max(D_infty, D_infty)
  top  := T_odot     -- max(T_in, T_odot)        = T_odot
  rel  := R_lr       -- max(R_dagger, R_lr)      = R_lr
  pol  := P_pm_sym   -- min(P_pm_sym, P_pm_sym)  = P_pm_sym  [no bottleneck]
  fid  := F_hbar     -- min(F_hbar, F_hbar)
  kin  := K_slow     -- max(K_slow, K_slow)
  gran := G_aleph    -- max(G_aleph, G_aleph)
  gram := Gamma_seq  -- max(Gamma_or, Gamma_seq) = Gamma_seq
  crit := Phi_c      -- max(Phi_c, Phi_c)
  chir := H2         -- max(H0, H2)              = H2
  stoi := n_m        -- max(n_m, n_m)
  prot := Omega_Z }  -- max(Omega_Z, Omega_Z)

/-- ZFC_st equals the tensor product of ZFC_s and ZFC_t. -/
theorem zfc_st_is_tensor : zfc_st = tensorProduct zfc_s zfc_t := by decide

/-- ZFC_st = ZFC_t: temporal structure dominates all max-primitives.
    The Frobenius gate stays open (no polarity bottleneck) because both
    ZFC_s and ZFC_t already carry P_pm_sym. -/
theorem zfc_st_eq_zfc_t : zfc_st = zfc_t := by decide

/-- ZFC_st is O_inf: the Frobenius gate is open at the spacetime level. -/
theorem zfc_st_is_O_inf : imscriptionTier zfc_st = .O_inf := by decide

-- ============================================================
-- MEET AND JOIN OPERATIONS
-- Component-wise min (∧) and max (∨) — distinct from the tensor product.
-- ============================================================

/-- Component-wise minimum of two imscriptions (lattice meet). -/
def meetProduct (a b : Imscription) : Imscription := {
  dim  := if compare a.dim  b.dim  = .lt then a.dim  else b.dim
  top  := if compare a.top  b.top  = .lt then a.top  else b.top
  rel  := if compare a.rel  b.rel  = .lt then a.rel  else b.rel
  pol  := if compare a.pol  b.pol  = .lt then a.pol  else b.pol
  fid  := if compare a.fid  b.fid  = .lt then a.fid  else b.fid
  kin  := if compare a.kin  b.kin  = .lt then a.kin  else b.kin
  gran := if compare a.gran b.gran = .lt then a.gran else b.gran
  gram := if compare a.gram b.gram = .lt then a.gram else b.gram
  crit := if compare a.crit b.crit = .lt then a.crit else b.crit
  chir := if compare a.chir b.chir = .lt then a.chir else b.chir
  stoi := if compare a.stoi b.stoi = .lt then a.stoi else b.stoi
  prot := if compare a.prot b.prot = .lt then a.prot else b.prot }

/-- Component-wise maximum of two imscriptions (lattice join). -/
def joinProduct (a b : Imscription) : Imscription := {
  dim  := if compare a.dim  b.dim  = .lt then b.dim  else a.dim
  top  := if compare a.top  b.top  = .lt then b.top  else a.top
  rel  := if compare a.rel  b.rel  = .lt then b.rel  else a.rel
  pol  := if compare a.pol  b.pol  = .lt then b.pol  else a.pol
  fid  := if compare a.fid  b.fid  = .lt then b.fid  else a.fid
  kin  := if compare a.kin  b.kin  = .lt then b.kin  else a.kin
  gran := if compare a.gran b.gran = .lt then b.gran else a.gran
  gram := if compare a.gram b.gram = .lt then b.gram else a.gram
  crit := if compare a.crit b.crit = .lt then b.crit else a.crit
  chir := if compare a.chir b.chir = .lt then b.chir else a.chir
  stoi := if compare a.stoi b.stoi = .lt then b.stoi else a.stoi
  prot := if compare a.prot b.prot = .lt then b.prot else a.prot }

-- ZFC ∧ X = ZFC for any X that is a pure promotion of ZFC (X ≥ ZFC everywhere).
-- ZFC ∨ X = X for the same reason.

/-- ZFC ∧ ZFC_s = ZFC: ZFC is the shared lower bound. -/
theorem meet_zfc_zfc_s : meetProduct zfc zfc_s = zfc := by decide

/-- ZFC ∧ ZFC_t = ZFC: ZFC is the shared lower bound. -/
theorem meet_zfc_zfc_t : meetProduct zfc zfc_t = zfc := by decide

/-- ZFC ∨ ZFC_s = ZFC_s: ZFC_s is the minimal upper bound over ZFC. -/
theorem join_zfc_zfc_s : joinProduct zfc zfc_s = zfc_s := by decide

/-- ZFC ∨ ZFC_t = ZFC_t: ZFC_t is the minimal upper bound over ZFC. -/
theorem join_zfc_zfc_t : joinProduct zfc zfc_t = zfc_t := by decide

/-- ZFC_s ∧ ZFC_t: the spatial-temporal meet.
    Resolves to ZFC_s on top/rel/gram, to ZFC_t on chir, to shared prot.
    Polarity: both P_pm_sym → P_pm_sym. -/
def zfc_s_meet_zfc_t : Imscription := meetProduct zfc_s zfc_t

/-- ZFC_s ∨ ZFC_t: the spatial-temporal join — O_inf.
    Takes T_odot, R_lr, Gamma_seq from ZFC_t; P_pm_sym from both; H2 from ZFC_t.
    The join of two O_inf systems is O_inf. -/
def zfc_s_join_zfc_t : Imscription := joinProduct zfc_s zfc_t

theorem zfc_s_join_zfc_t_is_O_inf : imscriptionTier zfc_s_join_zfc_t = .O_inf := by decide

/-- The join ZFC_s ∨ ZFC_t equals the tensor ZFC_s ⊗ ZFC_t (= ZFC_t) here,
    because both carry the same polarity (P_pm_sym) so max=min on that slot. -/
theorem join_eq_tensor_eq_zfc_t : zfc_s_join_zfc_t = zfc_st := by decide

-- ============================================================
-- DISTANCE THEOREMS
-- ============================================================

/-- ZFC → ZFC_s: five primitive promotions. -/
theorem zfc_to_zfc_s_dist : primitiveMismatches zfc zfc_s = 5 := by decide

/-- ZFC → ZFC_t: six primitive promotions (chirality promotes in time, not space). -/
theorem zfc_to_zfc_t_dist : primitiveMismatches zfc zfc_t = 6 := by decide

/-- ZFC_s ↔ ZFC_t: four primitive mismatches.
    top(T_in≠T_odot), rel(R_dagger≠R_lr), gram(Gamma_or≠Gamma_seq), chir(H0≠H2).
    Polarity no longer separates them: both carry P_pm_sym. -/
theorem zfc_s_zfc_t_dist : primitiveMismatches zfc_s zfc_t = 4 := by decide

/-- ZFC_st ↔ ZFC_t: zero distance — tensor collapses to ZFC_t exactly. -/
theorem zfc_st_zfc_t_dist : primitiveMismatches zfc_st zfc_t = 0 := by decide

/-- ZFC_s ↔ ZFC_st: four primitive mismatches (same as ZFC_s ↔ ZFC_t). -/
theorem zfc_s_zfc_st_dist : primitiveMismatches zfc_s zfc_st = 4 := by decide

-- ============================================================
-- SPATIAL MATHEMATICS IMSCRIPTIONS
-- ============================================================

/-- Riemannian metric.
    Symmetric positive-definite bilinear form on the tangent bundle.
    P_sym (SO(n)-invariant) but not P_pm_sym: no global Frobenius condition. -/
def riemannian_metric : Imscription := {
  dim  := D_infty,  top  := T_in,      rel  := R_dagger,  pol  := P_sym
  fid  := F_hbar,   kin  := K_mod,     gran := G_aleph,   gram := Gamma_and
  crit := Phi_sub,  chir := H0,        stoi := n_n,       prot := Omega_0 }

/-- Fundamental group π₁.
    Based loop space; concatenation μ and path-reversal δ satisfy μ∘δ=id (Frobenius). -/
def fundamental_group : Imscription := {
  dim  := D_infty,  top  := T_bowtie,  rel  := R_dagger,  pol  := P_pm_sym
  fid  := F_hbar,   kin  := K_slow,    gran := G_aleph,   gram := Gamma_or
  crit := Phi_c,    chir := H0,        stoi := n_m,       prot := Omega_Z }

/-- de Rham cohomology.
    Exterior derivative d: Ω^k → Ω^(k+1), d²=0; Hodge duality Ω^k ↔ Ω^(n-k).
    Sequential (cochain complex) and Frobenius (cap product pairing). -/
def de_rham_cohomology : Imscription := {
  dim  := D_infty,  top  := T_bowtie,  rel  := R_dagger,  pol  := P_pm_sym
  fid  := F_hbar,   kin  := K_slow,    gran := G_aleph,   gram := Gamma_seq
  crit := Phi_c,    chir := H0,        stoi := n_m,       prot := Omega_Z }

/-- Poincaré duality.
    H^k(M) ≅ H^(n-k)(M) on a compact oriented n-manifold.
    Orientation = soft chirality (H1); cap product pairing is Frobenius. -/
def poincare_duality : Imscription := {
  dim  := D_infty,  top  := T_in,      rel  := R_dagger,  pol  := P_pm_sym
  fid  := F_hbar,   kin  := K_slow,    gran := G_aleph,   gram := Gamma_seq
  crit := Phi_c,    chir := H1,        stoi := n_m,       prot := Omega_Z }

/-- Fiber bundle.
    Projection π: E → B with structure group G; local trivializations are concurrent. -/
def fiber_bundle : Imscription := {
  dim  := D_infty,  top  := T_network,  rel := R_super,   pol  := P_pm
  fid  := F_hbar,   kin  := K_slow,    gran := G_aleph,   gram := Gamma_or
  crit := Phi_sub,  chir := H0,        stoi := n_m,       prot := Omega_Z }

/-- Covering space.
    Universal cover p: Ẽ → E with deck group acting freely and transitively.
    Deck transformations satisfy the Frobenius condition (free + transitive). -/
def covering_space : Imscription := {
  dim  := D_infty,  top  := T_in,      rel  := R_super,   pol  := P_pm_sym
  fid  := F_hbar,   kin  := K_slow,    gran := G_aleph,   gram := Gamma_or
  crit := Phi_c,    chir := H0,        stoi := n_n,       prot := Omega_Z }

/-- Hodge decomposition.
    α = dβ + δγ + h on a compact Riemannian manifold.
    L² adjointness ⟨dα,β⟩ = ⟨α,δβ⟩ is the Frobenius pairing. -/
def hodge_decomposition : Imscription := {
  dim  := D_infty,  top  := T_in,      rel  := R_dagger,  pol  := P_pm_sym
  fid  := F_hbar,   kin  := K_slow,    gran := G_aleph,   gram := Gamma_seq
  crit := Phi_c,    chir := H0,        stoi := n_m,       prot := Omega_Z }

-- ============================================================
-- TIER THEOREMS FOR SPATIAL MATHEMATICS
-- ============================================================

/-- Fundamental group is O_inf: loop concatenation satisfies the Frobenius condition. -/
theorem fundamental_group_is_O_inf : imscriptionTier fundamental_group = .O_inf := by decide

/-- de Rham cohomology is O_inf: the exterior algebra is a Frobenius algebra. -/
theorem de_rham_is_O_inf : imscriptionTier de_rham_cohomology = .O_inf := by decide

/-- Poincaré duality is O_inf: the cap product is a Frobenius pairing. -/
theorem poincare_duality_is_O_inf : imscriptionTier poincare_duality = .O_inf := by decide

/-- Covering space is O_inf: deck group action satisfies the Frobenius condition. -/
theorem covering_space_is_O_inf : imscriptionTier covering_space = .O_inf := by decide

/-- Hodge decomposition is O_inf: L² adjointness is the Frobenius pairing. -/
theorem hodge_is_O_inf : imscriptionTier hodge_decomposition = .O_inf := by decide

/-- Riemannian metric is O_0: subcritical — classical smooth geometry, no topological gate. -/
theorem riemannian_is_O_0 : imscriptionTier riemannian_metric = .O_0 := by decide

/-- Fiber bundle is O_0: the projection is subcritical — local structure, no Frobenius. -/
theorem fiber_bundle_is_O_0 : imscriptionTier fiber_bundle = .O_0 := by decide

-- ============================================================
-- STRUCTURAL DISTANCE THEOREMS FOR SPATIAL MATHEMATICS
-- ============================================================

/-- Hodge decomposition and de Rham cohomology are adjacent: one primitive separates them
    (topology: T_in vs T_bowtie). -/
theorem hodge_deRham_adjacent :
    primitiveMismatches hodge_decomposition de_rham_cohomology = 1 := by decide

/-- Poincaré duality differs from de Rham cohomology on two primitives
    (top: T_in vs T_bowtie; chir: H1 vs H0 — orientation is the gap). -/
theorem poincare_deRham_dist :
    primitiveMismatches poincare_duality de_rham_cohomology = 2 := by decide

/-- Riemannian metric sits six primitives below ZFC_s
    (pol, kin, gram, crit, stoi, prot). -/
theorem riemannian_below_zfc_s :
    primitiveMismatches riemannian_metric zfc_s = 6 := by decide

/-- Fundamental group is 2 primitives from ZFC_s
    (top: T_bowtie vs T_in; gram: Gamma_or vs Gamma_or — wait, same; stoi: same).
    Actually: top(T_bowtie≠T_in) and rel(R_dagger=R_dagger): 1 mismatch. -/
theorem fundamental_group_near_zfc_s :
    primitiveMismatches fundamental_group zfc_s = 1 := by decide

/-- Hodge decomposition is one primitive from ZFC_s
    (gram: Gamma_seq vs Gamma_or — sequential decomposition vs concurrent spatial logic). -/
theorem hodge_near_zfc_s :
    primitiveMismatches hodge_decomposition zfc_s = 1 := by decide

-- ============================================================
-- SPATIAL DEPTH FUNCTION (analogue of temporalDepth in ZFCt)
-- ============================================================

/-- Vary the homotopy winding protection of a spatial imscription.
    Depth 0: no protection; depth 1: Z₂; depth 2: Z (standard); depth ≥ 3: non-Abelian. -/
def spatialDepth (n : ℕ) (s : Imscription) : Imscription :=
  { s with prot :=
    if n = 0 then Omega_0 else if n = 1 then Omega_Z2 else if n = 2 then Omega_Z
    else Omega_NA }

-- ============================================================
-- HOMOTOPY WINDING STRUCTURE
-- ============================================================

structure HomotopyPath where
  base : Type
  loopAt : base → Type
  winding : ∀ b, loopAt b → ℤ
  exists_nontrivial : ∃ b, ∃ l : loopAt b, winding b l ≠ 0

def example_circle_winding : HomotopyPath := {
  base := Unit
  loopAt := fun _ => ℤ
  winding := fun _ n => n
  exists_nontrivial := ⟨(), 1, by decide⟩ }

-- ============================================================
-- IMAGINARY NUMBERS CONNECTION
-- ============================================================

/-- Planck-scale imaginary time imscription.
    Under the Wick rotation t → iτ, imaginary time acquires spatial character:
    T_in (bounded domain) and R_dagger (metric symmetry d(x,y)=d(y,x)) match ZFC_s exactly.
    Diverges from ZFC_s in: criticality (Phi_c_complex), chirality (H_inf),
    polarity (P_psi), grammar (Gamma_seq), protection (Omega_Z2). -/
def planck_imaginary_time : Imscription := {
  dim  := D_infty,       top  := T_in,       rel  := R_dagger,   pol  := P_psi
  fid  := F_hbar,        kin  := K_slow,     gran := G_aleph,    gram := Gamma_seq
  crit := Phi_c_complex, chir := H_inf,      stoi := n_m,        prot := Omega_Z2 }

/-- Planck imaginary time shares its spatial skeleton (T_in, R_dagger) with ZFC_s:
    imaginary time is geometrically a spatial direction. -/
theorem planck_imaginary_time_spatial_skeleton :
    planck_imaginary_time.top = T_in ∧ planck_imaginary_time.rel = R_dagger := by decide

/-- Distance from Planck imaginary time to ZFC_s: five mismatches
    (pol, gram, crit, chir, prot). Topology and relational mode are shared. -/
theorem planck_imag_time_to_zfc_s_dist :
    primitiveMismatches planck_imaginary_time zfc_s = 5 := by decide

/-- Frobenius cliff: no tensor composition can bring imaginary-time polarity (P_psi)
    to the spatial Frobenius condition (P_pm_sym).
    The Wick rotation is a structural promotion, not a tensor product. -/
theorem imaginary_time_frobenius_cliff :
    ∀ other : Imscription, (tensorProduct planck_imaginary_time other).pol ≠ P_pm_sym := by
  intro other
  simp [tensorProduct, planck_imaginary_time]
  cases other.pol <;> decide

/-- The imaginary unit is further from ZFC_s than from ZFC_t:
    spatial isotropy (H0, Gamma_or) is more alien to i than temporal chirality. -/
def imaginary_unit : Imscription := {
  dim  := D_triangle,  top  := T_bowtie,  rel  := R_lr,     pol  := P_psi
  fid  := F_ell,       kin  := K_slow,    gran := G_aleph,  gram := Gamma_seq
  crit := Phi_c,       chir := H2,        stoi := one_one,  prot := Omega_Z }

theorem imaginary_unit_to_zfc_s_dist :
    primitiveMismatches imaginary_unit zfc_s = 8 := by decide

-- ============================================================
-- SPATIAL ↔ TEMPORAL COMPARISON TABLE
-- ============================================================

def zfc_s_vs_zfc_t_comparison : List (String × String × String) := [
  ("top",  "T_in      (spatial: nested domains)",    "T_odot    (temporal: holographic)"),
  ("rel",  "R_dagger  (spatial: metric symmetry)",   "R_lr      (temporal: lateral exchange)"),
  ("pol",  "P_pm_sym  (both: Frobenius condition)",  "P_pm_sym  (both: Frobenius condition)"),
  ("gram", "Gamma_or  (spatial: concurrent)",         "Gamma_seq (temporal: sequential)"),
  ("chir", "H0        (spatial: isotropic)",          "H2        (temporal: arrow of time)"),
  ("tier", "O_inf     (Frobenius gate: open)",        "O_inf     (Frobenius gate: open)") ]

end ZFCs
end Imscribing.Primitives
