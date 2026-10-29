/-
  Imscribing.Primitives.Types.PrimitiveTypeEat

  Formalization of the primitive value type 'eat'
  Family: Topology (ordinal 1)
  Surface tokens: inclusion, nesting, containment
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

/-- Surface tokens for 'eat' -/
def the_primitive_type_called_eat_surfaceTokens : List String := ["inclusion", "nesting", "containment"]

/-- Boundary condition for 'eat' -/
def the_primitive_type_called_eat_boundaryCondition : String := "the outermost set boundary defining the scope of the hierarchy"

/-- Belnap FOUR register descriptions -/
def the_primitive_type_called_eat_registerVoid : String := "the absence of any topological structure or elements"
def the_primitive_type_called_eat_registerTrue : String := "successful containment within the nested hierarchy"
def the_primitive_type_called_eat_registerFalse : String := "exclusion from the nested hierarchy"
def the_primitive_type_called_eat_registerBoth : String := "partial containment or boundary overlap"

/-- Opcode domain-semantic mapping -/
-- AFWD: subset injection
--   the forward morphism that places an element into a container
-- AREV: element extraction
--   the reverse morphism that retrieves an element from its container
-- CLINK: transitive nesting
--   the composition of inclusion relations where A is in B and B is in C
-- ENGAGR: boundary intersection
--   the state where an element exists on the boundary, simultaneously inside and outside
-- EVALF: disjointness
--   the negative state where the element exists outside the specified container
-- EVALT: proper inclusion
--   the affirmative state where the subset is strictly contained within the superset
-- FFUSE: set union
--   the reconstitution of the original set from its disjoint partitions
-- FSPLIT: partitioning
--   the division of a set into distinct disjoint subsets
-- IFIX: membership record
--   the permanent fixation of an element's position within the hierarchy
-- IMSCRIB: self-containment identity
--   the recognition that a set is a subset of itself
-- TANCH: universal set
--   the terminal boundary that contains all nested hierarchies
-- VINIT: empty set
--   the uninitialized state before any elements or subsets are defined

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def the_primitive_type_called_eat_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_eat_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_eat_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_eat_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_eat_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_eat_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_eat_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_eat_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_eat_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_eat_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_eat_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_primitive_type_called_eat_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_primitive_type_called_eat_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_primitive_type_called_eat_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def the_primitive_type_called_eat_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_eat_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_eat_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_eat_l3 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_eat_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_eat_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_eat_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_eat_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_eat_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_eat_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_eat_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_eat_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_primitive_type_called_eat_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_eat_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def the_primitive_type_called_eat_protocol : IGProtocol the_primitive_type_called_eat_s0 the_primitive_type_called_eat_s13 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct the_primitive_type_called_eat_s8 the_primitive_type_called_eat_s8 = the_primitive_type_called_eat_s8 (idempotent)
  (.seq (.arrow the_primitive_type_called_eat_l0 the_primitive_type_called_eat_s0 the_primitive_type_called_eat_s1) (.seq (.arrow the_primitive_type_called_eat_l1 the_primitive_type_called_eat_s1 the_primitive_type_called_eat_s2) (.seq (.prod (.arrow the_primitive_type_called_eat_l2 the_primitive_type_called_eat_s2 the_primitive_type_called_eat_s8) (.arrow the_primitive_type_called_eat_l2 the_primitive_type_called_eat_s2 the_primitive_type_called_eat_s8)) (.seq (.arrow the_primitive_type_called_eat_l8 the_primitive_type_called_eat_s8 the_primitive_type_called_eat_s8) (.seq (.arrow the_primitive_type_called_eat_l8 the_primitive_type_called_eat_s8 the_primitive_type_called_eat_s9) (.seq (.arrow the_primitive_type_called_eat_l9 the_primitive_type_called_eat_s9 the_primitive_type_called_eat_s10) (.seq (.arrow the_primitive_type_called_eat_l10 the_primitive_type_called_eat_s10 the_primitive_type_called_eat_s11) (.seq (.arrow the_primitive_type_called_eat_l11 the_primitive_type_called_eat_s11 the_primitive_type_called_eat_s12) (.arrow the_primitive_type_called_eat_l12 the_primitive_type_called_eat_s12 the_primitive_type_called_eat_s13)))))))))

def the_primitive_type_called_eat_tier : OuroboricityTier := TierFunctor.obj the_primitive_type_called_eat_s0

#eval the_primitive_type_called_eat_tier  -- the Grammar's own verdict on its tier

/-- 'eat' belongs to the Topology family at ordinal 1 -/
def the_primitive_type_called_eat_family : String := "Topology"
def the_primitive_type_called_eat_ordinal : Nat := 1

/-- The CLINK L8 fragment for 'eat' (⊣ = 𐑰), as the organism-layer
    navigator emits it. Not authored here: the string is the navigator's. -/
def the_primitive_type_called_eat_clinkFragmentL8 : String := "x ⊆ y ∧ cont(y)"

/-- Its L8 proximity to the reference layer, and the atom it promotes. -/
def the_primitive_type_called_eat_proximityL8 : String := "distant"
def the_primitive_type_called_eat_promotedAtomL8 : String := ""

/-- The CLINK L9 fragment — the replicative-lateral reading of the same value.
    Where L9 annotates, the annotation is the transcendence content. -/
def the_primitive_type_called_eat_clinkFragmentL9 : String := "x ⊆ y ∧ cont(y)"
def the_primitive_type_called_eat_proximityL9 : String := "distant"
def the_primitive_type_called_eat_promotedAtomL9 : String := ""

/-- The fragment in ordinary mathematics, which is what a reader outside the
    Grammar reads. -/
def the_primitive_type_called_eat_conventionalReading : String := "embedding in a continuum."

/-- Whether the fragment IS the conventional statement rather than a picture of
    it: "always", "contextual" or "never". Read off the ★ marks in
    ig-docs/OVMs/conventional_statements.md, counted against the theorems that
    carry the value rather than assumed from one appearance. "contextual" means
    the same fragment is the statement in some domains and not in others, which
    the coordinate alone does not settle. -/
def the_primitive_type_called_eat_fragmentIsStatement : String := "never"

/-- The count behind that verdict, so its strength is visible. -/
def the_primitive_type_called_eat_fragmentIsStatementEvidence : String := "not carried by any of the seven sampled theorems"
def the_primitive_type_called_eat_bootstrapSteps : Nat := 20

/-- Ordered executable construction retained alongside the typed protocol. -/
def the_primitive_type_called_eat_opcodes : List String := ["VINIT", "IMSCRIB", "AFWD", "IFIX", "FSPLIT", "EVALT", "AFWD", "CLINK", "IMSCRIB", "IFIX", "FFUSE", "FSPLIT", "EVALF", "AREV", "FFUSE", "FSPLIT", "ENGAGR", "IFIX", "FFUSE", "TANCH"]
def the_primitive_type_called_eat_domainActions : List String := ["establish the empty topological space", "identify the space as a self-consistent domain", "inject the first level of containment", "record the primary container boundary", "branch the container into potential sub-regions", "confirm the existence of a nested subset", "perform deep nesting of a secondary element", "chain the primary and secondary inclusion relations", "verify the identity of the nested element", "fix the nested position in the hierarchy", "reunite the sub-regions into the primary container", "branch to check for external elements", "identify an element that is not contained", "reverse the inclusion attempt for the external element", "return to the primary container state", "evaluate a boundary condition", "hold the state of an element intersecting the boundary", "record the boundary intersection event", "resolve the topological state", "close the universal set boundary"]
def the_primitive_type_called_eat_forkFusePairs : List (Nat × Nat) := [(4, 10), (11, 14), (15, 18)]
def the_primitive_type_called_eat_glyphWord : String := Imscribing.glyphWordOf the_primitive_type_called_eat_opcodes

theorem the_primitive_type_called_eat_program_length :
    the_primitive_type_called_eat_opcodes.length = the_primitive_type_called_eat_bootstrapSteps := by decide
theorem the_primitive_type_called_eat_actions_cover_program :
    the_primitive_type_called_eat_domainActions.length = the_primitive_type_called_eat_opcodes.length := by decide
theorem the_primitive_type_called_eat_program_uses_native_opcodes :
    (the_primitive_type_called_eat_opcodes.all fun op => Imscribing.glyphOf op != "?") = true := by decide
theorem the_primitive_type_called_eat_pairs_name_fork_and_fuse :
    (the_primitive_type_called_eat_forkFusePairs.all fun p =>
      (the_primitive_type_called_eat_opcodes[p.1]? == some "FSPLIT") &&
      (the_primitive_type_called_eat_opcodes[p.2]? == some "FFUSE")) = true := by decide

end Imscribing.Primitives.Types
