/-
  Imscribing.Primitives.Types.PrimitiveTypeChurch

  Formalization of the primitive value type 'church'
  Family: Polarity (ordinal 0)
  Surface tokens: asymmetry, parity-break, singleton
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

/-- Surface tokens for 'church' -/
def the_primitive_type_called_church_surfaceTokens : List String := ["asymmetry", "parity-break", "singleton"]

/-- Boundary condition for 'church' -/
def the_primitive_type_called_church_boundaryCondition : String := "Polarity Type System"

/-- Belnap FOUR register descriptions -/
def the_primitive_type_called_church_registerVoid : String := "uninitialized polarity register"
def the_primitive_type_called_church_registerTrue : String := "asymmetric church state confirmed"
def the_primitive_type_called_church_registerFalse : String := "symmetric or higher-order parity state"
def the_primitive_type_called_church_registerBoth : String := "ambiguous parity state during type inference"

/-- Opcode domain-semantic mapping -/
-- AFWD: symmetry-breaking-morphism
--   The active transition from a symmetric state to a specific asymmetric orientation.
-- AREV: parity-restoration-attempt
--   The reverse operation attempting to recover symmetry from an asymmetric instance.
-- CLINK: constructor-chaining
--   The sequential application of the church constructor to the Polarity base type.
-- ENGAGR: parity-superposition
--   A state where the system holds both church and yew properties before type resolution.
-- EVALF: symmetry-detected
--   The negative state where the church constructor fails to match due to detected symmetry.
-- EVALT: asymmetry-confirmed
--   The affirmative state where the church constructor is successfully matched.
-- FFUSE: polarity-reunification
--   Reconstitutes the Polarity type from its specific branch instances.
-- FSPLIT: parity-check-fork
--   Splits the type into a branch for asymmetric church and a branch for symmetric alternatives.
-- IFIX: ordinal-zero-fixation
--   The permanent record of church as the 0-index element in the Polarity F5 family.
-- IMSCRIB: church-self-identity
--   The recognition that church is the lowest ordinal value in the Polarity lattice.
-- TANCH: type-checker-seal
--   The final validation that the church primitive is correctly typed within the Polarity inductive.
-- VINIT: untyped-vacuum
--   The state before any parity or symmetry assignment exists.

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def the_primitive_type_called_church_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_church_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_church_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_church_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_church_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_church_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_church_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_church_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_primitive_type_called_church_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_primitive_type_called_church_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_primitive_type_called_church_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_primitive_type_called_church_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_primitive_type_called_church_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def the_primitive_type_called_church_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_church_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_church_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_church_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_church_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_church_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_church_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_church_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_primitive_type_called_church_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_church_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_church_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_church_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_church_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def the_primitive_type_called_church_protocol : IGProtocol the_primitive_type_called_church_s0 the_primitive_type_called_church_s12 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct the_primitive_type_called_church_s11 the_primitive_type_called_church_s11 = the_primitive_type_called_church_s11 (idempotent)
  (.seq (.arrow the_primitive_type_called_church_l0 the_primitive_type_called_church_s0 the_primitive_type_called_church_s1) (.seq (.prod (.arrow the_primitive_type_called_church_l1 the_primitive_type_called_church_s1 the_primitive_type_called_church_s11) (.arrow the_primitive_type_called_church_l1 the_primitive_type_called_church_s1 the_primitive_type_called_church_s11)) (.seq (.arrow the_primitive_type_called_church_l11 the_primitive_type_called_church_s11 the_primitive_type_called_church_s11) (.arrow the_primitive_type_called_church_l11 the_primitive_type_called_church_s11 the_primitive_type_called_church_s12))))

def the_primitive_type_called_church_tier : OuroboricityTier := TierFunctor.obj the_primitive_type_called_church_s0
theorem the_primitive_type_called_church_frobenius :
    igFrobeniusAlg.mul the_primitive_type_called_church_s0 the_primitive_type_called_church_s0 = the_primitive_type_called_church_s0 :=
  igFrobAlg_self_fusion the_primitive_type_called_church_s0

#eval the_primitive_type_called_church_tier  -- the Grammar's own verdict on its tier

/-- 'church' belongs to the Polarity family at ordinal 0 -/
def the_primitive_type_called_church_family : String := "Polarity"
def the_primitive_type_called_church_ordinal : Nat := 0

/-- The CLINK L8 fragment for 'church' (≺ = 𐑗), as the organism-layer
    navigator emits it. Not authored here: the string is the navigator's. -/
def the_primitive_type_called_church_clinkFragmentL8 : String := "¬∃sym(x)"

/-- Its L8 proximity to the reference layer, and the atom it promotes. -/
def the_primitive_type_called_church_proximityL8 : String := "distant"
def the_primitive_type_called_church_promotedAtomL8 : String := ""

/-- The CLINK L9 fragment — the replicative-lateral reading of the same value.
    Where L9 annotates, the annotation is the transcendence content. -/
def the_primitive_type_called_church_clinkFragmentL9 : String := "¬∃sym(x)"
def the_primitive_type_called_church_proximityL9 : String := "distant"
def the_primitive_type_called_church_promotedAtomL9 : String := ""

/-- The fragment in ordinary mathematics, which is what a reader outside the
    Grammar reads. -/
def the_primitive_type_called_church_conventionalReading : String := "trivial automorphism group, Aut(x) = 1: rigid."

/-- Whether the fragment IS the conventional statement rather than a picture of
    it: "always", "contextual" or "never". Read off the ★ marks in
    ig-docs/OVMs/conventional_statements.md, counted against the theorems that
    carry the value rather than assumed from one appearance. "contextual" means
    the same fragment is the statement in some domains and not in others, which
    the coordinate alone does not settle. -/
def the_primitive_type_called_church_fragmentIsStatement : String := "never"

/-- The count behind that verdict, so its strength is visible. -/
def the_primitive_type_called_church_fragmentIsStatementEvidence : String := "not carried by any of the seven sampled theorems"
def the_primitive_type_called_church_bootstrapSteps : Nat := 10

/-- Ordered executable construction retained alongside the typed protocol. -/
def the_primitive_type_called_church_opcodes : List String := ["VINIT", "IMSCRIB", "AFWD", "FSPLIT", "EVALT", "IFIX", "FFUSE", "CLINK", "AREV", "TANCH"]
def the_primitive_type_called_church_domainActions : List String := ["initialize the polarity register to null", "identify the church primitive as a unique singleton within F5", "apply the church constructor to the uninitialized state", "fork the process to validate the absence of symmetry axes", "confirm the lack of phase or discrete symmetry", "record the church assignment to the permanent type-log", "merge the validation branch back into the main type flow", "compose the church instance with the ordinal comparison logic", "verify that church cannot be reduced to a simpler symmetric form", "seal the church instance within the Polarity boundary"]
def the_primitive_type_called_church_forkFusePairs : List (Nat × Nat) := [(3, 6)]
def the_primitive_type_called_church_glyphWord : String := Imscribing.glyphWordOf the_primitive_type_called_church_opcodes

theorem the_primitive_type_called_church_program_length :
    the_primitive_type_called_church_opcodes.length = the_primitive_type_called_church_bootstrapSteps := by decide
theorem the_primitive_type_called_church_actions_cover_program :
    the_primitive_type_called_church_domainActions.length = the_primitive_type_called_church_opcodes.length := by decide
theorem the_primitive_type_called_church_program_uses_native_opcodes :
    (the_primitive_type_called_church_opcodes.all fun op => Imscribing.glyphOf op != "?") = true := by decide
theorem the_primitive_type_called_church_pairs_name_fork_and_fuse :
    (the_primitive_type_called_church_forkFusePairs.all fun p =>
      (the_primitive_type_called_church_opcodes[p.1]? == some "FSPLIT") &&
      (the_primitive_type_called_church_opcodes[p.2]? == some "FFUSE")) = true := by decide

end Imscribing.Primitives.Types
