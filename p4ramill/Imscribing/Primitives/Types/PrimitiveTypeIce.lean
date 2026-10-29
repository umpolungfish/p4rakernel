/-
  Imscribing.Primitives.Types.PrimitiveTypeIce

  Formalization of the primitive value type 'ice'
  Family: Granularity (ordinal 2)
  Surface tokens: global correlation, fine-grained resolution, all-to-all coupling
  Author: Lando⊗⊙perator
-/

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Primitives.TierCrossing
import Imscribing.IGMorphism
import Imscribing.IGFunctor
import Imscribing.ConventionalRegister

namespace Imscribing.Primitives.Types
open Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

/-- Surface tokens for 'ice' -/
def the_primitive_type_called_ice_surfaceTokens : List String := ["global correlation", "fine-grained resolution", "all-to-all coupling"]

/-- Boundary condition for 'ice' -/
def the_primitive_type_called_ice_boundaryCondition : String := "The universal scope of the 17,280,000-type crystal lattice."

/-- Belnap FOUR register descriptions -/
def the_primitive_type_called_ice_registerVoid : String := "uninitialized granularity state"
def the_primitive_type_called_ice_registerTrue : String := "complete global correlation"
def the_primitive_type_called_ice_registerFalse : String := "disconnected local fragments"
def the_primitive_type_called_ice_registerBoth : String := "entangled multi-scale granularity"

/-- Opcode domain-semantic mapping -/
-- AFWD: correlation expansion
--   The transformation from local mesoscale bib to global fine-grained ice.
-- AREV: granularity reduction
--   The descent from all-to-all correlations back to intermediate collective thigh structures.
-- CLINK: correlation chaining
--   The sequential linking of local correlations to form a global network.
-- ENGAGR: meso-global superposition
--   A state where local bib and global ice granularities are held simultaneously without collapse.
-- EVALF: correlation gap
--   The failure to maintain fine-grained connectivity across the entire scope.
-- EVALT: total coupling
--   The state where all-to-all correlations are successfully established.
-- FFUSE: global integration
--   The reconstitution of the total coupling map and nodes back into the unified ice scope.
-- FSPLIT: correlation bifurcation
--   The division of a global state into its constituent fine-grained nodes and their total coupling map.
-- IFIX: granularity record
--   The permanent fixation of the ice state in the crystal stoichiometry.
-- IMSCRIB: self-consistent scope
--   The recognition of the ice state as a stable, self-referential global configuration.
-- TANCH: ice boundary
--   The terminal limit where every element in the system is correlated with every other element.
-- VINIT: unscoped data
--   The raw information before any granularity or correlation scale is applied.

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def the_primitive_type_called_ice_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ice_s1 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ice_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ice_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ice_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ice_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_ice_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_primitive_type_called_ice_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_ice_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_ice_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_ice_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_primitive_type_called_ice_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def the_primitive_type_called_ice_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ice_l1 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ice_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ice_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ice_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ice_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_ice_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_primitive_type_called_ice_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ice_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ice_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ice_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_ice_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def the_primitive_type_called_ice_protocol : IGProtocol the_primitive_type_called_ice_s0 the_primitive_type_called_ice_s11 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct the_primitive_type_called_ice_s7 the_primitive_type_called_ice_s7 = the_primitive_type_called_ice_s7 (idempotent)
  (.seq (.arrow the_primitive_type_called_ice_l0 the_primitive_type_called_ice_s0 the_primitive_type_called_ice_s1) (.seq (.arrow the_primitive_type_called_ice_l1 the_primitive_type_called_ice_s1 the_primitive_type_called_ice_s2) (.seq (.arrow the_primitive_type_called_ice_l2 the_primitive_type_called_ice_s2 the_primitive_type_called_ice_s3) (.seq (.prod (.arrow the_primitive_type_called_ice_l3 the_primitive_type_called_ice_s3 the_primitive_type_called_ice_s7) (.arrow the_primitive_type_called_ice_l3 the_primitive_type_called_ice_s3 the_primitive_type_called_ice_s7)) (.seq (.arrow the_primitive_type_called_ice_l7 the_primitive_type_called_ice_s7 the_primitive_type_called_ice_s7) (.seq (.arrow the_primitive_type_called_ice_l7 the_primitive_type_called_ice_s7 the_primitive_type_called_ice_s8) (.seq (.arrow the_primitive_type_called_ice_l8 the_primitive_type_called_ice_s8 the_primitive_type_called_ice_s9) (.seq (.arrow the_primitive_type_called_ice_l9 the_primitive_type_called_ice_s9 the_primitive_type_called_ice_s10) (.arrow the_primitive_type_called_ice_l10 the_primitive_type_called_ice_s10 the_primitive_type_called_ice_s11)))))))))

def the_primitive_type_called_ice_tier : OuroboricityTier := TierFunctor.obj the_primitive_type_called_ice_s0
theorem the_primitive_type_called_ice_frobenius :
    igFrobeniusAlg.mul the_primitive_type_called_ice_s0 the_primitive_type_called_ice_s0 = the_primitive_type_called_ice_s0 :=
  igFrobAlg_self_fusion the_primitive_type_called_ice_s0

#eval the_primitive_type_called_ice_tier  -- the Grammar's own verdict on its tier

/-- 'ice' belongs to the Granularity family at ordinal 2 -/
def the_primitive_type_called_ice_family : String := "Granularity"
def the_primitive_type_called_ice_ordinal : Nat := 2

/-- The CLINK L8 fragment for 'ice' (∈ = 𐑲), as the organism-layer
    navigator emits it. Not authored here: the string is the navigator's. -/
def the_primitive_type_called_ice_clinkFragmentL8 : String := "∀y( y ⊂ x → |y| < |x| )"

/-- Its L8 proximity to the reference layer, and the atom it promotes. -/
def the_primitive_type_called_ice_proximityL8 : String := "match"
def the_primitive_type_called_ice_promotedAtomL8 : String := ""

/-- The CLINK L9 fragment — the replicative-lateral reading of the same value.
    Where L9 annotates, the annotation is the transcendence content. -/
def the_primitive_type_called_ice_clinkFragmentL9 : String := "∀y( y ⊂ x → |y| < |x| )"
def the_primitive_type_called_ice_proximityL9 : String := "distant"
def the_primitive_type_called_ice_promotedAtomL9 : String := ""

/-- The fragment in ordinary mathematics, which is what a reader outside the
    Grammar reads. -/
def the_primitive_type_called_ice_conventionalReading : String := "every proper subset is strictly smaller: x is Dedekind-finite."

/-- Whether the fragment IS the conventional statement rather than a picture of
    it: "always", "contextual" or "never". Read off the ★ marks in
    ig-docs/OVMs/conventional_statements.md, counted against the theorems that
    carry the value rather than assumed from one appearance. "contextual" means
    the same fragment is the statement in some domains and not in others, which
    the coordinate alone does not settle. -/
def the_primitive_type_called_ice_fragmentIsStatement : String := "always"

/-- The count behind that verdict, so its strength is visible. -/
def the_primitive_type_called_ice_fragmentIsStatementEvidence : String := "starred in 1 of the 1 sampled theorem(s) that carry it"
def the_primitive_type_called_ice_bootstrapSteps : Nat := 9

/-- Ordered executable construction retained alongside the typed protocol. -/
def the_primitive_type_called_ice_opcodes : List String := ["VINIT", "AFWD", "CLINK", "FSPLIT", "EVALT", "IMSCRIB", "FFUSE", "IFIX", "TANCH"]
def the_primitive_type_called_ice_domainActions : List String := ["initialize raw information without defined scope", "expand correlation range from local to intermediate", "chain intermediate correlations to approach global scale", "branch the emerging global state into nodes and coupling maps", "verify that every node is coupled to every other node", "identify the resulting state as the ice primitive", "integrate the verified couplings into a unified global scope", "record the ice granularity state into the crystal memory", "anchor the system within the holographic boundary"]
def the_primitive_type_called_ice_forkFusePairs : List (Nat × Nat) := [(3, 6)]
def the_primitive_type_called_ice_glyphWord : String := Imscribing.glyphWordOf the_primitive_type_called_ice_opcodes

theorem the_primitive_type_called_ice_program_length :
    the_primitive_type_called_ice_opcodes.length = the_primitive_type_called_ice_bootstrapSteps := by decide
theorem the_primitive_type_called_ice_actions_cover_program :
    the_primitive_type_called_ice_domainActions.length = the_primitive_type_called_ice_opcodes.length := by decide
theorem the_primitive_type_called_ice_program_uses_native_opcodes :
    (the_primitive_type_called_ice_opcodes.all fun op => Imscribing.glyphOf op != "?") = true := by decide
theorem the_primitive_type_called_ice_pairs_name_fork_and_fuse :
    (the_primitive_type_called_ice_forkFusePairs.all fun p =>
      (the_primitive_type_called_ice_opcodes[p.1]? == some "FSPLIT") &&
      (the_primitive_type_called_ice_opcodes[p.2]? == some "FFUSE")) = true := by decide

end Imscribing.Primitives.Types
