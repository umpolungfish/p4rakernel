/-
  Imscribing.Primitives.Types.PrimitiveTypeOr

  Formalization of the primitive value type 'or'
  Family: Polarity (ordinal 4)
  Surface tokens: Frobenius, singularity, encoding
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

/-- Surface tokens for 'or' -/
def the_primitive_type_called_or_surfaceTokens : List String := ["Frobenius", "singularity", "encoding"]

/-- Boundary condition for 'or' -/
def the_primitive_type_called_or_boundaryCondition : String := "Axiom D Holographic Closure"

/-- Belnap FOUR register descriptions -/
def the_primitive_type_called_or_registerVoid : String := "unpolarized state before symmetry breaking"
def the_primitive_type_called_or_registerTrue : String := "exact holographic correspondence"
def the_primitive_type_called_or_registerFalse : String := "symmetry mismatch or lossy encoding"
def the_primitive_type_called_or_registerBoth : String := "Frobenius singularity at the critical point"

/-- Opcode domain-semantic mapping -/
-- AFWD: encoding map δ
--   The forward morphism projecting bulk data onto the boundary.
-- AREV: decoding map μ
--   The reverse morphism reconstructing the bulk from the boundary projection.
-- CLINK: composition μ ∘ δ
--   The sequential chaining of the encoding and decoding operations.
-- ENGAGR: criticality ⊙
--   The paradice state where the system is simultaneously bulk and boundary at the phase transition.
-- EVALF: lossy projection
--   The negative state where information is lost during the dimensionality split.
-- EVALT: exact correspondence
--   The affirmative state where the boundary fully encodes the bulk.
-- FFUSE: bulk reconstruction
--   Reconstitutes the original bulk object from the boundary data and constraints.
-- FSPLIT: boundary projection
--   Splits the bulk object into its boundary representation and its internal constraints.
-- IFIX: or' fixation
--   The permanent fixation of the Frobenius property in the type record.
-- IMSCRIB: identity id
--   The self-recognition where the reconstructed bulk matches the original.
-- TANCH: O_inf tier
--   The terminal state of the grammar where the Frobenius condition is satisfied.
-- VINIT: untyped vacuum
--   The state before any polarity or symmetry assignment exists.

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def the_primitive_type_called_or_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_or_s1 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_or_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_or_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_or_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_or_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_primitive_type_called_or_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_or_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_or_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_or_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_primitive_type_called_or_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def the_primitive_type_called_or_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_or_l1 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_or_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_or_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_or_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_or_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_primitive_type_called_or_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_or_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_or_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_or_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_or_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def the_primitive_type_called_or_protocol : IGProtocol the_primitive_type_called_or_s0 the_primitive_type_called_or_s10 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct the_primitive_type_called_or_s6 the_primitive_type_called_or_s6 = the_primitive_type_called_or_s6 (idempotent)
  (.seq (.arrow the_primitive_type_called_or_l0 the_primitive_type_called_or_s0 the_primitive_type_called_or_s1) (.seq (.arrow the_primitive_type_called_or_l1 the_primitive_type_called_or_s1 the_primitive_type_called_or_s2) (.seq (.prod (.arrow the_primitive_type_called_or_l2 the_primitive_type_called_or_s2 the_primitive_type_called_or_s6) (.arrow the_primitive_type_called_or_l2 the_primitive_type_called_or_s2 the_primitive_type_called_or_s6)) (.seq (.arrow the_primitive_type_called_or_l6 the_primitive_type_called_or_s6 the_primitive_type_called_or_s6) (.seq (.arrow the_primitive_type_called_or_l6 the_primitive_type_called_or_s6 the_primitive_type_called_or_s7) (.seq (.arrow the_primitive_type_called_or_l7 the_primitive_type_called_or_s7 the_primitive_type_called_or_s8) (.seq (.arrow the_primitive_type_called_or_l8 the_primitive_type_called_or_s8 the_primitive_type_called_or_s9) (.arrow the_primitive_type_called_or_l9 the_primitive_type_called_or_s9 the_primitive_type_called_or_s10))))))))

def the_primitive_type_called_or_tier : OuroboricityTier := TierFunctor.obj the_primitive_type_called_or_s0
theorem the_primitive_type_called_or_frobenius :
    igFrobeniusAlg.mul the_primitive_type_called_or_s0 the_primitive_type_called_or_s0 = the_primitive_type_called_or_s0 :=
  igFrobAlg_self_fusion the_primitive_type_called_or_s0

#eval the_primitive_type_called_or_tier  -- the Grammar's own verdict on its tier

/-- 'or' belongs to the Polarity family at ordinal 4 -/
def the_primitive_type_called_or_family : String := "Polarity"
def the_primitive_type_called_or_ordinal : Nat := 4

/-- The CLINK L8 fragment for 'or' (≺ = 𐑹), as the organism-layer
    navigator emits it. Not authored here: the string is the navigator's. -/
def the_primitive_type_called_or_clinkFragmentL8 : String := "ℤ₂(x) ∧ ∀g∈G( gx = x ) ∧ μ∘δ = id"

/-- Its L8 proximity to the reference layer, and the atom it promotes. -/
def the_primitive_type_called_or_proximityL8 : String := "match"
def the_primitive_type_called_or_promotedAtomL8 : String := "PM_Z2"

/-- The CLINK L9 fragment — the replicative-lateral reading of the same value.
    Where L9 annotates, the annotation is the transcendence content. -/
def the_primitive_type_called_or_clinkFragmentL9 : String := "ℤ₂(x) ∧ ∀g∈G( gx = x ) ∧ μ∘δ = id"
def the_primitive_type_called_or_proximityL9 : String := "distant"
def the_primitive_type_called_or_promotedAtomL9 : String := "PM_Z2"

/-- The fragment in ordinary mathematics, which is what a reader outside the
    Grammar reads. -/
def the_primitive_type_called_or_conventionalReading : String := "a special commutative Frobenius algebra — multiplication after comultiplication is the identity — carrying a ℤ₂ grading on which the group acts trivially."

/-- Whether the fragment IS the conventional statement rather than a picture of
    it: "always", "contextual" or "never". Read off the ★ marks in
    ig-docs/OVMs/conventional_statements.md, counted against the theorems that
    carry the value rather than assumed from one appearance. "contextual" means
    the same fragment is the statement in some domains and not in others, which
    the coordinate alone does not settle. -/
def the_primitive_type_called_or_fragmentIsStatement : String := "never"

/-- The count behind that verdict, so its strength is visible. -/
def the_primitive_type_called_or_fragmentIsStatementEvidence : String := "starred in none of the 5 sampled theorem(s) that carry it"
def the_primitive_type_called_or_bootstrapSteps : Nat := 11

/-- Ordered executable construction retained alongside the typed protocol. -/
def the_primitive_type_called_or_opcodes : List String := ["VINIT", "FSPLIT", "EVALT", "AFWD", "AREV", "CLINK", "IMSCRIB", "FFUSE", "ENGAGR", "IFIX", "TANCH"]
def the_primitive_type_called_or_domainActions : List String := ["initialize the primitive type without polarity", "branch the type into its boundary encoding and bulk interior", "verify the boundary fully encodes the bulk via are topology", "apply the encoding morphism δ to the bulk", "apply the decoding morphism μ to the boundary", "compose the morphisms into the loop μ ∘ δ", "identify the result as the original identity id", "reconstitute the bulk type from the exact correspondence", "hold the bulk-boundary duality at the monad criticality", "record the or' polarity in the permanent type crystal", "anchor the type in the O_inf tier"]
def the_primitive_type_called_or_forkFusePairs : List (Nat × Nat) := [(1, 7)]
def the_primitive_type_called_or_glyphWord : String := Imscribing.glyphWordOf the_primitive_type_called_or_opcodes

theorem the_primitive_type_called_or_program_length :
    the_primitive_type_called_or_opcodes.length = the_primitive_type_called_or_bootstrapSteps := by decide
theorem the_primitive_type_called_or_actions_cover_program :
    the_primitive_type_called_or_domainActions.length = the_primitive_type_called_or_opcodes.length := by decide
theorem the_primitive_type_called_or_program_uses_native_opcodes :
    (the_primitive_type_called_or_opcodes.all fun op => Imscribing.glyphOf op != "?") = true := by decide
theorem the_primitive_type_called_or_pairs_name_fork_and_fuse :
    (the_primitive_type_called_or_forkFusePairs.all fun p =>
      (the_primitive_type_called_or_opcodes[p.1]? == some "FSPLIT") &&
      (the_primitive_type_called_or_opcodes[p.2]? == some "FFUSE")) = true := by decide

end Imscribing.Primitives.Types
