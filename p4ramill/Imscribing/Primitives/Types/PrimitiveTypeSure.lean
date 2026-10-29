/-
  Imscribing.Primitives.Types.PrimitiveTypeSure

  Formalization of the primitive value type 'sure'
  Family: Chirality (ordinal 2)
  Surface tokens: chirality, asymmetry, persistence
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

/-- Surface tokens for 'sure' -/
def the_primitive_type_called_sure_surfaceTokens : List String := ["chirality", "asymmetry", "persistence"]

/-- Boundary condition for 'sure' -/
def the_primitive_type_called_sure_boundaryCondition : String := "the temporal memory horizon of the primitive type system"

/-- Belnap FOUR register descriptions -/
def the_primitive_type_called_sure_registerVoid : String := "uninitialized temporal state with no defined handedness"
def the_primitive_type_called_sure_registerTrue : String := "persistent chiral state with strong temporal asymmetry"
def the_primitive_type_called_sure_registerFalse : String := "achiral state where temporal memory is lost"
def the_primitive_type_called_sure_registerBoth : String := "superposed chiral state holding both orientations simultaneously"

/-- Opcode domain-semantic mapping -/
-- AFWD: right-handed propagation
--   the forward transformation of a chiral signal through time
-- AREV: left-handed propagation
--   the reverse or parity-flipped transformation of a chiral signal
-- CLINK: temporal chaining
--   the sequential composition of chiral states across successive clock cycles
-- ENGAGR: racemic mixture
--   the simultaneous presence of both chiralities without resolution into a single dominant hand
-- EVALF: symmetry restoration
--   the failure to maintain chirality resulting in a return to achiral state
-- EVALT: strong asymmetry
--   the affirmative detection of persistent temporal directionality
-- FFUSE: chirality synthesis
--   the reconstitution of the original signal from its parity-split components
-- FSPLIT: parity bifurcation
--   the branching of a neutral signal into distinct right-handed and left-handed paths
-- IFIX: persistent record
--   the permanent fixation of the chiral state into the type system memory
-- IMSCRIB: chirality recognition
--   the self-identification of the state as possessing a specific handedness
-- TANCH: sure type definition
--   the final boundary that contains the persistent chiral state
-- VINIT: achiral vacuum
--   the state of zero temporal memory where no directionality is established

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def the_primitive_type_called_sure_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_sure_s1 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_sure_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_sure_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_sure_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_sure_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_primitive_type_called_sure_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_primitive_type_called_sure_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_primitive_type_called_sure_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_primitive_type_called_sure_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_primitive_type_called_sure_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_primitive_type_called_sure_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def the_primitive_type_called_sure_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_sure_l1 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_sure_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_sure_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_sure_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_sure_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_primitive_type_called_sure_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_sure_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_sure_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_sure_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_sure_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_sure_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def the_primitive_type_called_sure_protocol : IGProtocol the_primitive_type_called_sure_s0 the_primitive_type_called_sure_s11 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct the_primitive_type_called_sure_s10 the_primitive_type_called_sure_s10 = the_primitive_type_called_sure_s10 (idempotent)
  (.seq (.arrow the_primitive_type_called_sure_l0 the_primitive_type_called_sure_s0 the_primitive_type_called_sure_s1) (.seq (.arrow the_primitive_type_called_sure_l1 the_primitive_type_called_sure_s1 the_primitive_type_called_sure_s2) (.seq (.prod (.arrow the_primitive_type_called_sure_l2 the_primitive_type_called_sure_s2 the_primitive_type_called_sure_s10) (.arrow the_primitive_type_called_sure_l2 the_primitive_type_called_sure_s2 the_primitive_type_called_sure_s10)) (.seq (.arrow the_primitive_type_called_sure_l10 the_primitive_type_called_sure_s10 the_primitive_type_called_sure_s10) (.arrow the_primitive_type_called_sure_l10 the_primitive_type_called_sure_s10 the_primitive_type_called_sure_s11)))))

def the_primitive_type_called_sure_tier : OuroboricityTier := TierFunctor.obj the_primitive_type_called_sure_s0
theorem the_primitive_type_called_sure_frobenius :
    igFrobeniusAlg.mul the_primitive_type_called_sure_s0 the_primitive_type_called_sure_s0 = the_primitive_type_called_sure_s0 :=
  igFrobAlg_self_fusion the_primitive_type_called_sure_s0

#eval the_primitive_type_called_sure_tier  -- the Grammar's own verdict on its tier

/-- 'sure' belongs to the Chirality family at ordinal 2 -/
def the_primitive_type_called_sure_family : String := "Chirality"
def the_primitive_type_called_sure_ordinal : Nat := 2

/-- The CLINK L8 fragment for 'sure' (⊥ = 𐑖), as the organism-layer
    navigator emits it. Not authored here: the string is the navigator's. -/
def the_primitive_type_called_sure_clinkFragmentL8 : String := "∃y∃z( y ∈ x ∧ z ∈ y ∧ ¬ z ∈ x ∧ rank(z) < rank(y) )"

/-- Its L8 proximity to the reference layer, and the atom it promotes. -/
def the_primitive_type_called_sure_proximityL8 : String := "close"
def the_primitive_type_called_sure_promotedAtomL8 : String := "TEMPD2"

/-- The CLINK L9 fragment — the replicative-lateral reading of the same value.
    Where L9 annotates, the annotation is the transcendence content. -/
def the_primitive_type_called_sure_clinkFragmentL9 : String := "∃y∃z( y ∈ x ∧ z ∈ y ∧ ¬ z ∈ x ∧ rank(z) < rank(y) )"
def the_primitive_type_called_sure_proximityL9 : String := "close"
def the_primitive_type_called_sure_promotedAtomL9 : String := "TEMPD2"

/-- The fragment in ordinary mathematics, which is what a reader outside the
    Grammar reads. -/
def the_primitive_type_called_sure_conventionalReading : String := "failure of transitivity witnessed two levels down, with rank descending: return in exactly two steps."

/-- Whether the fragment IS the conventional statement rather than a picture of
    it: "always", "contextual" or "never". Read off the ★ marks in
    ig-docs/OVMs/conventional_statements.md, counted against the theorems that
    carry the value rather than assumed from one appearance. "contextual" means
    the same fragment is the statement in some domains and not in others, which
    the coordinate alone does not settle. -/
def the_primitive_type_called_sure_fragmentIsStatement : String := "never"

/-- The count behind that verdict, so its strength is visible. -/
def the_primitive_type_called_sure_fragmentIsStatementEvidence : String := "starred in none of the 1 sampled theorem(s) that carry it"
def the_primitive_type_called_sure_bootstrapSteps : Nat := 12

/-- Ordered executable construction retained alongside the typed protocol. -/
def the_primitive_type_called_sure_opcodes : List String := ["VINIT", "IMSCRIB", "FSPLIT", "AFWD", "EVALT", "AREV", "EVALF", "FFUSE", "CLINK", "IMSCRIB", "IFIX", "TANCH"]
def the_primitive_type_called_sure_domainActions : List String := ["initialize the achiral vacuum state", "identify the potential for temporal memory", "branch the signal into parity-distinct paths", "propagate the right-handed signal forward in time", "confirm the presence of strong temporal asymmetry", "propagate the left-handed signal as a parity flip", "detect the loss of directionality in the reverse path", "reunite the parity paths to verify signal integrity", "chain the resulting state to the next temporal cycle", "recognize the persistent identity of the sure type", "record the persistent chirality into the permanent type register", "anchor the sure type within the interaction grammar boundary"]
def the_primitive_type_called_sure_forkFusePairs : List (Nat × Nat) := [(2, 7)]
def the_primitive_type_called_sure_glyphWord : String := Imscribing.glyphWordOf the_primitive_type_called_sure_opcodes

theorem the_primitive_type_called_sure_program_length :
    the_primitive_type_called_sure_opcodes.length = the_primitive_type_called_sure_bootstrapSteps := by decide
theorem the_primitive_type_called_sure_actions_cover_program :
    the_primitive_type_called_sure_domainActions.length = the_primitive_type_called_sure_opcodes.length := by decide
theorem the_primitive_type_called_sure_program_uses_native_opcodes :
    (the_primitive_type_called_sure_opcodes.all fun op => Imscribing.glyphOf op != "?") = true := by decide
theorem the_primitive_type_called_sure_pairs_name_fork_and_fuse :
    (the_primitive_type_called_sure_forkFusePairs.all fun p =>
      (the_primitive_type_called_sure_opcodes[p.1]? == some "FSPLIT") &&
      (the_primitive_type_called_sure_opcodes[p.2]? == some "FFUSE")) = true := by decide

end Imscribing.Primitives.Types
