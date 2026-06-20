-- Imscribing/Primitives/ZFCs.lean
-- ZFC$_s$: ZFC extended with Spatiality, Isotropy, and Homotopy Winding.
-- Spatial extension analogous to ZFCt's temporal extension.
-- Key asymmetry: ZFC_s is O_inf (or'); ZFC_t is O₂dag (out).
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
   zfc = { dim:=array, top:=judge, rel:=ado, pol:=church,
           fid:=peep, kin:=egg, gran:=ice, gram:=vow,
           crit:=monad, chir:=fee, stoi:=up, prot:=awe } -/

/-- ZFC_s: ZFC with five spatial promotions.
    Space is isotropic (or' = SO(n) invariance = Frobenius condition),
    concurrent (gag: spatial operations run in parallel),
    nested-domain (eat: spaces have interiors and boundaries),
    metrically symmetric (ear: d(x,y) = d(y,x)),
    and homotopy-protected (ah: π_n carry ℤ-valued winding invariants).
    Chirality does NOT promote: isotropic space has no preferred handedness. -/
def zfc_s : Imscription := {
  dim  := array    -- infinite-dimensional: abstract spatial unfolding (unchanged)
  top  := eat       -- inclusion/nested: spaces have bounded domains and interiors
  rel  := ear   -- dagger/reciprocal: metric symmetry d(x,y) = d(y,x)
  pol  := or'   -- Special Frobenius: spatial isotropy SO(n), μ ∘ δ = id
  fid  := peep     -- quantum-coherent (unchanged)
  kin  := egg     -- thermally activated (unchanged)
  gran := ice    -- global/fine-grained: all-to-all spatial correlations (unchanged)
  gram := gag   -- concurrent: spatial operations are parallel, not sequential
  crit := monad      -- real-axis criticality (unchanged)
  chir := fee         -- achiral: isotropic space has no preferred handedness (unchanged)
  stoi := up        -- many-to-many spatial correspondences (unchanged)
  prot := ah }  -- integer winding: homotopy groups π_n carry ℤ-valued invariants

/-- The five promotion channels from ZFC to ZFC_s.
    (Chirality does not promote — compare with ZFCt's six promotions.) -/
def zfc_to_zfc_s_promotions : List (String × String) := [
  ("top",  "judge → eat"),
  ("rel",  "ado → ear"),
  ("pol",  "church → or'"),
  ("gram", "vow → gag"),
  ("prot", "awe → ah") ]

-- ============================================================
-- TIER ANALYSIS
-- ============================================================

/-- ZFC_s attains O_inf: spatial isotropy (or') at monad satisfies the
    Frobenius condition — the same gate as quantum gravity and the Higgs field. -/
theorem zfc_s_is_O_inf : imscriptionTier zfc_s = .O_inf := by decide

/-- ZFC_t is O_inf: temporal Frobenius symmetry (or') at monad.
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
    · pol:  min(or', or') = or' — no bottleneck: both extensions Frobenius
    · top:  max(eat, are)       = are   — holographic topology dominates inclusion
    · rel:  max(ear, ian)     = ian     — lateral exchange dominates metric symmetry
    · gram: max(gag, measure) = measure — sequentiality dominates concurrency
    · chir: max(fee, sure)             = sure       — temporal chirality dominates spatial isotropy
    · prot: max(ah, ah)   = ah
    Result: ZFC_st = ZFC_t. Temporal structure dominates all max-primitives;
    the Frobenius gate stays open because both partners already hold it. -/
def zfc_st : Imscription := {
  dim  := array    -- max(array, array)
  top  := are     -- max(eat, are)        = are
  rel  := ian       -- max(ear, ian)      = ian
  pol  := or'   -- min(or', or')  = or'  [no bottleneck]
  fid  := peep     -- min(peep, peep)
  kin  := egg     -- max(egg, egg)
  gran := ice    -- max(ice, ice)
  gram := measure  -- max(gag, measure) = measure
  crit := monad      -- max(monad, monad)
  chir := sure         -- max(fee, sure)              = sure
  stoi := up        -- max(up, up)
  prot := ah }  -- max(ah, ah)

/-- ZFC_st equals the tensor product of ZFC_s and ZFC_t. -/
theorem zfc_st_is_tensor : zfc_st = tensorProduct zfc_s zfc_t := by decide

/-- ZFC_st = ZFC_t: temporal structure dominates all max-primitives.
    The Frobenius gate stays open (no polarity bottleneck) because both
    ZFC_s and ZFC_t already carry or'. -/
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
    Polarity: both or' → or'. -/
def zfc_s_meet_zfc_t : Imscription := meetProduct zfc_s zfc_t

/-- ZFC_s ∨ ZFC_t: the spatial-temporal join — O_inf.
    Takes are, ian, measure from ZFC_t; or' from both; sure from ZFC_t.
    The join of two O_inf systems is O_inf. -/
def zfc_s_join_zfc_t : Imscription := joinProduct zfc_s zfc_t

theorem zfc_s_join_zfc_t_is_O_inf : imscriptionTier zfc_s_join_zfc_t = .O_inf := by decide

/-- The join ZFC_s ∨ ZFC_t equals the tensor ZFC_s ⊗ ZFC_t (= ZFC_t) here,
    because both carry the same polarity (or') so max=min on that slot. -/
theorem join_eq_tensor_eq_zfc_t : zfc_s_join_zfc_t = zfc_st := by decide

-- ============================================================
-- DISTANCE THEOREMS
-- ============================================================

/-- ZFC → ZFC_s: five primitive promotions. -/
theorem zfc_to_zfc_s_dist : primitiveMismatches zfc zfc_s = 5 := by decide

/-- ZFC → ZFC_t: six primitive promotions (chirality promotes in time, not space). -/
theorem zfc_to_zfc_t_dist : primitiveMismatches zfc zfc_t = 6 := by decide

/-- ZFC_s ↔ ZFC_t: four primitive mismatches.
    top(eat≠are), rel(ear≠ian), gram(gag≠measure), chir(fee≠sure).
    Polarity no longer separates them: both carry or'. -/
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
    nun (SO(n)-invariant) but not or': no global Frobenius condition. -/
def riemannian_metric : Imscription := {
  dim  := array,  top  := eat,      rel  := ear,  pol  := nun
  fid  := peep,   kin  := loll,     gran := ice,   gram := vow
  crit := woe,  chir := fee,        stoi := so,       prot := awe }

/-- Fundamental group π₁.
    Based loop space; concatenation μ and path-reversal δ satisfy μ∘δ=id (Frobenius). -/
def fundamental_group : Imscription := {
  dim  := array,  top  := mime,  rel  := ear,  pol  := or'
  fid  := peep,   kin  := egg,    gran := ice,   gram := gag
  crit := monad,    chir := fee,        stoi := up,       prot := ah }

/-- de Rham cohomology.
    Exterior derivative d: Ω^k → Ω^(k+1), d²=0; Hodge duality Ω^k ↔ Ω^(n-k).
    Sequential (cochain complex) and Frobenius (cap product pairing). -/
def de_rham_cohomology : Imscription := {
  dim  := array,  top  := mime,  rel  := ear,  pol  := or'
  fid  := peep,   kin  := egg,    gran := ice,   gram := measure
  crit := monad,    chir := fee,        stoi := up,       prot := ah }

/-- Poincaré duality.
    H^k(M) ≅ H^(n-k)(M) on a compact oriented n-manifold.
    Orientation = soft chirality (kick); cap product pairing is Frobenius. -/
def poincare_duality : Imscription := {
  dim  := array,  top  := eat,      rel  := ear,  pol  := or'
  fid  := peep,   kin  := egg,    gran := ice,   gram := measure
  crit := monad,    chir := kick,        stoi := up,       prot := ah }

/-- Fiber bundle.
    Projection π: E → B with structure group G; local trivializations are concurrent. -/
def fiber_bundle : Imscription := {
  dim  := array,  top  := judge,  rel := ado,   pol  := out
  fid  := peep,   kin  := egg,    gran := ice,   gram := gag
  crit := woe,  chir := fee,        stoi := up,       prot := ah }

/-- Covering space.
    Universal cover p: Ẽ → E with deck group acting freely and transitively.
    Deck transformations satisfy the Frobenius condition (free + transitive). -/
def covering_space : Imscription := {
  dim  := array,  top  := eat,      rel  := ado,   pol  := or'
  fid  := peep,   kin  := egg,    gran := ice,   gram := gag
  crit := monad,    chir := fee,        stoi := so,       prot := ah }

/-- Hodge decomposition.
    α = dβ + δγ + h on a compact Riemannian manifold.
    L² adjointness ⟨dα,β⟩ = ⟨α,δβ⟩ is the Frobenius pairing. -/
def hodge_decomposition : Imscription := {
  dim  := array,  top  := eat,      rel  := ear,  pol  := or'
  fid  := peep,   kin  := egg,    gran := ice,   gram := measure
  crit := monad,    chir := fee,        stoi := up,       prot := ah }

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

/-- Riemannian metric is O₀: subcritical — classical smooth geometry, no topological gate. -/
theorem riemannian_is_O_0 : imscriptionTier riemannian_metric = .O₀ := by decide

/-- Fiber bundle is O₀: the projection is subcritical — local structure, no Frobenius. -/
theorem fiber_bundle_is_O_0 : imscriptionTier fiber_bundle = .O₀ := by decide

-- ============================================================
-- STRUCTURAL DISTANCE THEOREMS FOR SPATIAL MATHEMATICS
-- ============================================================

/-- Hodge decomposition and de Rham cohomology are adjacent: one primitive separates them
    (topology: eat vs mime). -/
theorem hodge_deRham_adjacent :
    primitiveMismatches hodge_decomposition de_rham_cohomology = 1 := by decide

/-- Poincaré duality differs from de Rham cohomology on two primitives
    (top: eat vs mime; chir: kick vs fee — orientation is the gap). -/
theorem poincare_deRham_dist :
    primitiveMismatches poincare_duality de_rham_cohomology = 2 := by decide

/-- Riemannian metric sits six primitives below ZFC_s
    (pol, kin, gram, crit, stoi, prot). -/
theorem riemannian_below_zfc_s :
    primitiveMismatches riemannian_metric zfc_s = 6 := by decide

/-- Fundamental group is 2 primitives from ZFC_s
    (top: mime vs eat; gram: gag vs gag — wait, same; stoi: same).
    Actually: top(mime≠eat) and rel(ear=ear): 1 mismatch. -/
theorem fundamental_group_near_zfc_s :
    primitiveMismatches fundamental_group zfc_s = 1 := by decide

/-- Hodge decomposition is one primitive from ZFC_s
    (gram: measure vs gag — sequential decomposition vs concurrent spatial logic). -/
theorem hodge_near_zfc_s :
    primitiveMismatches hodge_decomposition zfc_s = 1 := by decide

-- ============================================================
-- SPATIAL DEPTH FUNCTION (analogue of temporalDepth in ZFCt)
-- ============================================================

/-- Vary the homotopy winding protection of a spatial imscription.
    Depth 0: no protection; depth 1: Z₂; depth 2: Z (standard); depth ≥ 3: non-Abelian. -/
def spatialDepth (n : ℕ) (s : Imscription) : Imscription :=
  { s with prot :=
    if n = 0 then awe else if n = 1 then oak else if n = 2 then ah
    else zoo }

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
    eat (bounded domain) and ear (metric symmetry d(x,y)=d(y,x)) match ZFC_s exactly.
    Diverges from ZFC_s in: criticality (roar), chirality (wool),
    polarity (yew), grammar (measure), protection (oak). -/
def planck_imaginary_time : Imscription := {
  dim  := array,       top  := eat,       rel  := ear,   pol  := yew
  fid  := peep,        kin  := egg,     gran := ice,    gram := measure
  crit := roar, chir := wool,      stoi := up,        prot := oak }

/-- Planck imaginary time shares its spatial skeleton (eat, ear) with ZFC_s:
    imaginary time is geometrically a spatial direction. -/
theorem planck_imaginary_time_spatial_skeleton :
    planck_imaginary_time.top = eat ∧ planck_imaginary_time.rel = ear := by decide

/-- Distance from Planck imaginary time to ZFC_s: five mismatches
    (pol, gram, crit, chir, prot). Topology and relational mode are shared. -/
theorem planck_imag_time_to_zfc_s_dist :
    primitiveMismatches planck_imaginary_time zfc_s = 5 := by decide

/-- Frobenius cliff: no tensor composition can bring imaginary-time polarity (yew)
    to the spatial Frobenius condition (or').
    The Wick rotation is a structural promotion, not a tensor product. -/
theorem imaginary_time_frobenius_cliff :
    ∀ other : Imscription, (tensorProduct planck_imaginary_time other).pol ≠ or' := by
  intro other
  simp [tensorProduct, planck_imaginary_time]
  cases other.pol <;> decide

/-- The imaginary unit is further from ZFC_s than from ZFC_t:
    spatial isotropy (fee, gag) is more alien to i than temporal chirality. -/
def imaginary_unit : Imscription := {
  dim  := ash,  top  := mime,  rel  := ian,     pol  := yew
  fid  := age,       kin  := egg,    gran := ice,  gram := measure
  crit := monad,       chir := sure,        stoi := hung,  prot := ah }

theorem imaginary_unit_to_zfc_s_dist :
    primitiveMismatches imaginary_unit zfc_s = 8 := by decide

-- ============================================================
-- SPATIAL ↔ TEMPORAL COMPARISON TABLE
-- ============================================================

def zfc_s_vs_zfc_t_comparison : List (String × String × String) := [
  ("top",  "eat      (spatial: nested domains)",    "are    (temporal: holographic)"),
  ("rel",  "ear  (spatial: metric symmetry)",   "ian      (temporal: lateral exchange)"),
  ("pol",  "or'  (both: Frobenius condition)",  "or'  (both: Frobenius condition)"),
  ("gram", "gag  (spatial: concurrent)",         "measure (temporal: sequential)"),
  ("chir", "fee        (spatial: isotropic)",          "sure        (temporal: arrow of time)"),
  ("tier", "O_inf     (Frobenius gate: open)",        "O_inf     (Frobenius gate: open)") ]

end ZFCs
end Imscribing.Primitives
