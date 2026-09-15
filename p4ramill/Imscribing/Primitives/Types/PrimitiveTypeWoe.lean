/-
  Imscribing.Primitives.Types.PrimitiveTypeWoe

  Formalization of the primitive value type 'woe'
  Family: Criticality (ordinal 0)
  Surface tokens: subcriticality, ordered phase, stable state
  Author: Lando⊗⊙perator
-/

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Primitives.TierCrossing
import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing.Primitives.Types
open Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

/-- Surface tokens for 'woe' -/
def the_primitive_type_called_woe_surfaceTokens : List String := ["subcriticality", "ordered phase", "stable state"]

/-- Boundary condition for 'woe' -/
def the_primitive_type_called_woe_boundaryCondition : String := "the subcritical phase space boundary"

/-- Belnap FOUR register descriptions -/
def the_primitive_type_called_woe_registerVoid : String := "uninitialized criticality register"
def the_primitive_type_called_woe_registerTrue : String := "confirmed subcritical order"
def the_primitive_type_called_woe_registerFalse : String := "criticality threshold breach"
def the_primitive_type_called_woe_registerBoth : String := "metastable phase coexistence"

/-- Opcode domain-semantic mapping -/
-- AFWD: ordering morphism
--   the transformation toward a stable ordered phase
-- AREV: fluctuation descent
--   the reduction of thermal or quantum noise to maintain order
-- CLINK: state composition
--   the sequential chaining of stable configurations
-- ENGAGR: metastability
--   the simultaneous presence of ordered and disordered tendencies
-- EVALF: instability detection
--   the negative evaluation indicating a phase transition
-- EVALT: stable confirmation
--   the affirmative evaluation of subcritical order
-- FFUSE: state recovery
--   the reconstitution of the original state from its components
-- FSPLIT: stability test
--   the branching of a state into stable and unstable components
-- IFIX: type fixation
--   the permanent record of the woe primitive in the crystal
-- IMSCRIB: self-consistency check
--   the recognition of the state as woe
-- TANCH: phase boundary
--   the limit where subcriticality transitions to criticality
-- VINIT: untyped vacuum
--   the state before the assignment of criticality values

-- Stage Imscriptions (per-node cumulative)
private def the_primitive_type_called_woe_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_woe_s1 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_woe_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_woe_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_woe_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_woe_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_woe_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_woe_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_woe_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }

-- Label Imscriptions (per-node delta)
private def the_primitive_type_called_woe_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_woe_l1 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_woe_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_woe_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_woe_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_woe_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_woe_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_woe_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_woe_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- Main IGProtocol term
noncomputable def the_primitive_type_called_woe_protocol : IGProtocol the_primitive_type_called_woe_s0 the_primitive_type_called_woe_s8 :=
  .withGram Grammar.measure <|
  (.seq (.arrow the_primitive_type_called_woe_l0 the_primitive_type_called_woe_s0 the_primitive_type_called_woe_s1) (.seq (.arrow the_primitive_type_called_woe_l1 the_primitive_type_called_woe_s1 the_primitive_type_called_woe_s2) (.seq (.arrow the_primitive_type_called_woe_l2 the_primitive_type_called_woe_s2 the_primitive_type_called_woe_s3) (.seq (.prod (.arrow the_primitive_type_called_woe_l3 the_primitive_type_called_woe_s3 the_primitive_type_called_woe_s5) (.arrow the_primitive_type_called_woe_l3 the_primitive_type_called_woe_s3 the_primitive_type_called_woe_s5)) (.seq (.arrow the_primitive_type_called_woe_l5 the_primitive_type_called_woe_s5 the_primitive_type_called_woe_s5) (.seq (.arrow the_primitive_type_called_woe_l5 the_primitive_type_called_woe_s5 the_primitive_type_called_woe_s6) (.seq (.arrow the_primitive_type_called_woe_l6 the_primitive_type_called_woe_s6 the_primitive_type_called_woe_s7) (.arrow the_primitive_type_called_woe_l7 the_primitive_type_called_woe_s7 the_primitive_type_called_woe_s8))))))))

-- Evaluation arm sub-defs
noncomputable def the_primitive_type_called_woe_true_arm : IGProtocol the_primitive_type_called_woe_s0 the_primitive_type_called_woe_s8 :=
  (the_primitive_type_called_woe_protocol).restrictToEVALT

-- Verification theorems
def the_primitive_type_called_woe_tier : OuroboricityTier := TierFunctor.obj the_primitive_type_called_woe_s0
theorem the_primitive_type_called_woe_frobenius :
    igFrobeniusAlg.mul the_primitive_type_called_woe_s0 the_primitive_type_called_woe_s0 = the_primitive_type_called_woe_s0 :=
  igFrobAlg_self_fusion the_primitive_type_called_woe_s0

#eval the_primitive_type_called_woe_tier  -- the Grammar's own verdict on its tier

/-- 'woe' belongs to the Criticality family at ordinal 0 -/
def the_primitive_type_called_woe_family : String := "Criticality"
def the_primitive_type_called_woe_ordinal : Nat := 0

/-- The CLINK L8 fragment for 'woe' (⊙ = 𐑢), as the organism-layer
    navigator emits it. Not authored here: the string is the navigator's. -/
def the_primitive_type_called_woe_clinkFragmentL8 : String := "¬∃ξ( diverges(ξ) )"

/-- Its L8 proximity to the reference layer, and the atom it promotes. -/
def the_primitive_type_called_woe_proximityL8 : String := "distant"
def the_primitive_type_called_woe_promotedAtomL8 : String := ""

/-- The CLINK L9 fragment — the replicative-lateral reading of the same value.
    Where L9 annotates, the annotation is the transcendence content. -/
def the_primitive_type_called_woe_clinkFragmentL9 : String := "¬∃ξ( diverges(ξ) )"
def the_primitive_type_called_woe_proximityL9 : String := "distant"
def the_primitive_type_called_woe_promotedAtomL9 : String := ""

/-- The fragment in ordinary mathematics, which is what a reader outside the
    Grammar reads. -/
def the_primitive_type_called_woe_conventionalReading : String := "no diverging correlation length: gapped, away from criticality."

/-- Whether the fragment IS the conventional statement rather than a picture of
    it: "always", "contextual" or "never". Read off the ★ marks in
    ig-docs/OVMs/conventional_statements.md, counted against the theorems that
    carry the value rather than assumed from one appearance. "contextual" means
    the same fragment is the statement in some domains and not in others, which
    the coordinate alone does not settle. -/
def the_primitive_type_called_woe_fragmentIsStatement : String := "always"

/-- The count behind that verdict, so its strength is visible. -/
def the_primitive_type_called_woe_fragmentIsStatementEvidence : String := "starred in 1 of the 1 sampled theorem(s) that carry it"
def the_primitive_type_called_woe_bootstrapSteps : Nat := 9

end Imscribing.Primitives.Types
