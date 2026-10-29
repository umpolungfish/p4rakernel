/-
  Imscribing.Primitives.Types.PrimitiveTypeBib

  Formalization of the primitive value type 'bib'
  Family: Granularity (ordinal 0)
  Surface tokens: mesoscale, correlation, neighborhood
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

/-- Surface tokens for 'bib' -/
def the_primitive_type_called_bib_surfaceTokens : List String := ["mesoscale", "correlation", "neighborhood"]

/-- Boundary condition for 'bib' -/
def the_primitive_type_called_bib_boundaryCondition : String := "local correlation length"

/-- Belnap FOUR register descriptions -/
def the_primitive_type_called_bib_registerVoid : String := "unscoped data"
def the_primitive_type_called_bib_registerTrue : String := "valid local correlation"
def the_primitive_type_called_bib_registerFalse : String := "local noise"
def the_primitive_type_called_bib_registerBoth : String := "mesoscale interference"

/-- Opcode domain-semantic mapping -/
-- AFWD: spatial mapping
--   projection of data into a local coordinate system
-- AREV: inverse projection
--   mapping local coordinates back to the global field
-- CLINK: neighborhood chaining
--   sequential linking of adjacent local points
-- ENGAGR: boundary overlap
--   a state where a point belongs to two adjacent mesoscale regions
-- EVALF: noise detection
--   failure to find local structure within the bib radius
-- EVALT: correlation match
--   successful identification of a local pattern
-- FFUSE: signal reconstruction
--   recombining components to recover the original local signal
-- FSPLIT: correlation fork
--   splitting a signal into correlated and uncorrelated components
-- IFIX: granularity record
--   permanent fixation of the bib scale in the type registry
-- IMSCRIB: local identity
--   recognition of a point as its own center within the bib scope
-- TANCH: bib boundary
--   the limit of the mesoscale beyond which correlations become collective
-- VINIT: unbounded field
--   the raw data space before local constraints are applied

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def the_primitive_type_called_bib_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_bib_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_bib_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_bib_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_bib_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_bib_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_bib_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_bib_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_bib_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_primitive_type_called_bib_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_bib_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_bib_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_primitive_type_called_bib_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def the_primitive_type_called_bib_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_bib_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_bib_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_bib_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_bib_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_bib_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_bib_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_bib_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_bib_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_primitive_type_called_bib_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_bib_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_bib_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_bib_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def the_primitive_type_called_bib_protocol : IGProtocol the_primitive_type_called_bib_s0 the_primitive_type_called_bib_s12 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct the_primitive_type_called_bib_s9 the_primitive_type_called_bib_s9 = the_primitive_type_called_bib_s9 (idempotent)
  (.seq (.arrow the_primitive_type_called_bib_l0 the_primitive_type_called_bib_s0 the_primitive_type_called_bib_s1) (.seq (.prod (.arrow the_primitive_type_called_bib_l1 the_primitive_type_called_bib_s1 the_primitive_type_called_bib_s9) (.arrow the_primitive_type_called_bib_l1 the_primitive_type_called_bib_s1 the_primitive_type_called_bib_s9)) (.seq (.arrow the_primitive_type_called_bib_l9 the_primitive_type_called_bib_s9 the_primitive_type_called_bib_s9) (.seq (.arrow the_primitive_type_called_bib_l9 the_primitive_type_called_bib_s9 the_primitive_type_called_bib_s10) (.seq (.arrow the_primitive_type_called_bib_l10 the_primitive_type_called_bib_s10 the_primitive_type_called_bib_s11) (.arrow the_primitive_type_called_bib_l11 the_primitive_type_called_bib_s11 the_primitive_type_called_bib_s12))))))

def the_primitive_type_called_bib_tier : OuroboricityTier := TierFunctor.obj the_primitive_type_called_bib_s0
theorem the_primitive_type_called_bib_frobenius :
    igFrobeniusAlg.mul the_primitive_type_called_bib_s0 the_primitive_type_called_bib_s0 = the_primitive_type_called_bib_s0 :=
  igFrobAlg_self_fusion the_primitive_type_called_bib_s0

#eval the_primitive_type_called_bib_tier  -- the Grammar's own verdict on its tier

/-- 'bib' belongs to the Granularity family at ordinal 0 -/
def the_primitive_type_called_bib_family : String := "Granularity"
def the_primitive_type_called_bib_ordinal : Nat := 0

/-- The CLINK L8 fragment for 'bib' (∈ = 𐑚), as the organism-layer
    navigator emits it. Not authored here: the string is the navigator's. -/
def the_primitive_type_called_bib_clinkFragmentL8 : String := "∀y∈x( |y| < |x| )"

/-- Its L8 proximity to the reference layer, and the atom it promotes. -/
def the_primitive_type_called_bib_proximityL8 : String := "distant"
def the_primitive_type_called_bib_promotedAtomL8 : String := ""

/-- The CLINK L9 fragment — the replicative-lateral reading of the same value.
    Where L9 annotates, the annotation is the transcendence content. -/
def the_primitive_type_called_bib_clinkFragmentL9 : String := "∀y∈x( |y| < |x| )"
def the_primitive_type_called_bib_proximityL9 : String := "distant"
def the_primitive_type_called_bib_promotedAtomL9 : String := ""

/-- The fragment in ordinary mathematics, which is what a reader outside the
    Grammar reads. -/
def the_primitive_type_called_bib_conventionalReading : String := "every member strictly smaller than x: x is a regular cardinal."

/-- Whether the fragment IS the conventional statement rather than a picture of
    it: "always", "contextual" or "never". Read off the ★ marks in
    ig-docs/OVMs/conventional_statements.md, counted against the theorems that
    carry the value rather than assumed from one appearance. "contextual" means
    the same fragment is the statement in some domains and not in others, which
    the coordinate alone does not settle. -/
def the_primitive_type_called_bib_fragmentIsStatement : String := "always"

/-- The count behind that verdict, so its strength is visible. -/
def the_primitive_type_called_bib_fragmentIsStatementEvidence : String := "starred in 1 of the 1 sampled theorem(s) that carry it"
def the_primitive_type_called_bib_bootstrapSteps : Nat := 11

/-- Ordered executable construction retained alongside the typed protocol. -/
def the_primitive_type_called_bib_opcodes : List String := ["VINIT", "AFWD", "IMSCRIB", "FSPLIT", "EVALT", "EVALF", "FFUSE", "CLINK", "ENGAGR", "IFIX", "TANCH"]
def the_primitive_type_called_bib_domainActions : List String := ["initialize the raw field for granularity assignment", "project the field into a local coordinate frame", "identify the central point of the bib neighborhood", "branch the local signal into pattern and noise", "confirm the presence of short-range correlations", "isolate the uncorrelated background noise", "reconstitute the original local signal from the branches", "chain the local signal to adjacent mesoscale neighbors", "hold the overlap between neighboring bib regions", "record the bib granularity as a fixed type attribute", "close the system within the mesoscale boundary"]
def the_primitive_type_called_bib_forkFusePairs : List (Nat × Nat) := [(3, 6)]
def the_primitive_type_called_bib_glyphWord : String := Imscribing.glyphWordOf the_primitive_type_called_bib_opcodes

theorem the_primitive_type_called_bib_program_length :
    the_primitive_type_called_bib_opcodes.length = the_primitive_type_called_bib_bootstrapSteps := by decide
theorem the_primitive_type_called_bib_actions_cover_program :
    the_primitive_type_called_bib_domainActions.length = the_primitive_type_called_bib_opcodes.length := by decide
theorem the_primitive_type_called_bib_program_uses_native_opcodes :
    (the_primitive_type_called_bib_opcodes.all fun op => Imscribing.glyphOf op != "?") = true := by decide
theorem the_primitive_type_called_bib_pairs_name_fork_and_fuse :
    (the_primitive_type_called_bib_forkFusePairs.all fun p =>
      (the_primitive_type_called_bib_opcodes[p.1]? == some "FSPLIT") &&
      (the_primitive_type_called_bib_opcodes[p.2]? == some "FFUSE")) = true := by decide

end Imscribing.Primitives.Types
