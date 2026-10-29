/-
  Imscribing.Primitives.Types.PrimitiveTypeEar

  Formalization of the primitive value type 'ear'
  Family: Relational (ordinal 2)
  Surface tokens: adjoint, reciprocity, duality
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

/-- Surface tokens for 'ear' -/
def the_primitive_type_called_ear_surfaceTokens : List String := ["adjoint", "reciprocity", "duality"]

/-- Boundary condition for 'ear' -/
def the_primitive_type_called_ear_boundaryCondition : String := "The Relational Mode (R) type space within the Imscriptive Primitives Core"

/-- Belnap FOUR register descriptions -/
def the_primitive_type_called_ear_registerVoid : String := "uninitialized relational mode"
def the_primitive_type_called_ear_registerTrue : String := "reciprocal consistency achieved"
def the_primitive_type_called_ear_registerFalse : String := "asymmetric relational breakdown"
def the_primitive_type_called_ear_registerBoth : String := "entangled adjoint pair"

/-- Opcode domain-semantic mapping -/
-- AFWD: morphism A
--   The primary directed transformation from source to target.
-- AREV: adjoint A†
--   The contravariant transformation that reverses the morphism direction.
-- CLINK: functorial composition
--   The chaining of relational mappings to form a coherent structure.
-- ENGAGR: biorthogonal state
--   The simultaneous holding of both A and A† as a single reciprocal unit.
-- EVALF: orthogonality failure
--   The failure of the adjoint to map back to the identity.
-- EVALT: unitary match
--   The successful verification of the reciprocal identity.
-- FFUSE: reciprocal unification
--   The reconstitution of the original relation from its forward and adjoint parts.
-- FSPLIT: dagger bifurcation
--   The separation of a single relation into its forward and adjoint components.
-- IFIX: type assignment
--   The permanent fixation of the 'ear' mode in the Lean kernel.
-- IMSCRIB: self-duality
--   The recognition of the relation as its own dual or identity.
-- TANCH: Relational.ear
--   The terminal definition of the bidirectional dagger mode within the F4 family.
-- VINIT: untyped relation
--   The state before a specific relational mode is assigned to the primitive.

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def the_primitive_type_called_ear_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_primitive_type_called_ear_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_primitive_type_called_ear_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_primitive_type_called_ear_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def the_primitive_type_called_ear_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_l4 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_l8 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_primitive_type_called_ear_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ear_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_ear_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def the_primitive_type_called_ear_protocol : IGProtocol the_primitive_type_called_ear_s0 the_primitive_type_called_ear_s16 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct the_primitive_type_called_ear_s14 the_primitive_type_called_ear_s14 = the_primitive_type_called_ear_s14 (idempotent)
  (.seq (.arrow the_primitive_type_called_ear_l0 the_primitive_type_called_ear_s0 the_primitive_type_called_ear_s1) (.seq (.arrow the_primitive_type_called_ear_l1 the_primitive_type_called_ear_s1 the_primitive_type_called_ear_s2) (.seq (.arrow the_primitive_type_called_ear_l2 the_primitive_type_called_ear_s2 the_primitive_type_called_ear_s3) (.seq (.prod (.arrow the_primitive_type_called_ear_l3 the_primitive_type_called_ear_s3 the_primitive_type_called_ear_s14) (.arrow the_primitive_type_called_ear_l3 the_primitive_type_called_ear_s3 the_primitive_type_called_ear_s14)) (.seq (.arrow the_primitive_type_called_ear_l14 the_primitive_type_called_ear_s14 the_primitive_type_called_ear_s14) (.seq (.arrow the_primitive_type_called_ear_l14 the_primitive_type_called_ear_s14 the_primitive_type_called_ear_s15) (.arrow the_primitive_type_called_ear_l15 the_primitive_type_called_ear_s15 the_primitive_type_called_ear_s16)))))))

def the_primitive_type_called_ear_tier : OuroboricityTier := TierFunctor.obj the_primitive_type_called_ear_s0
theorem the_primitive_type_called_ear_frobenius :
    igFrobeniusAlg.mul the_primitive_type_called_ear_s0 the_primitive_type_called_ear_s0 = the_primitive_type_called_ear_s0 :=
  igFrobAlg_self_fusion the_primitive_type_called_ear_s0

#eval the_primitive_type_called_ear_tier  -- the Grammar's own verdict on its tier

/-- 'ear' belongs to the Relational family at ordinal 2 -/
def the_primitive_type_called_ear_family : String := "Relational"
def the_primitive_type_called_ear_ordinal : Nat := 2

/-- The CLINK L8 fragment for 'ear' (≻ = 𐑽), as the organism-layer
    navigator emits it. Not authored here: the string is the navigator's. -/
def the_primitive_type_called_ear_clinkFragmentL8 : String := "f ⊣ g ∧ L Adj(f, g)"

/-- Its L8 proximity to the reference layer, and the atom it promotes. -/
def the_primitive_type_called_ear_proximityL8 : String := "close"
def the_primitive_type_called_ear_promotedAtomL8 : String := ""

/-- The CLINK L9 fragment — the replicative-lateral reading of the same value.
    Where L9 annotates, the annotation is the transcendence content. -/
def the_primitive_type_called_ear_clinkFragmentL9 : String := "f ⊣ g ∧ L Adj(f, g)"
def the_primitive_type_called_ear_proximityL9 : String := "close"
def the_primitive_type_called_ear_promotedAtomL9 : String := ""

/-- The fragment in ordinary mathematics, which is what a reader outside the
    Grammar reads. -/
def the_primitive_type_called_ear_conventionalReading : String := "f is left adjoint to g: Hom(f a, b) ≅ Hom(a, g b), naturally in a and b."

/-- Whether the fragment IS the conventional statement rather than a picture of
    it: "always", "contextual" or "never". Read off the ★ marks in
    ig-docs/OVMs/conventional_statements.md, counted against the theorems that
    carry the value rather than assumed from one appearance. "contextual" means
    the same fragment is the statement in some domains and not in others, which
    the coordinate alone does not settle. -/
def the_primitive_type_called_ear_fragmentIsStatement : String := "never"

/-- The count behind that verdict, so its strength is visible. -/
def the_primitive_type_called_ear_fragmentIsStatementEvidence : String := "starred in none of the 7 sampled theorem(s) that carry it"
def the_primitive_type_called_ear_bootstrapSteps : Nat := 12

/-- Ordered executable construction retained alongside the typed protocol. -/
def the_primitive_type_called_ear_opcodes : List String := ["VINIT", "IMSCRIB", "FSPLIT", "AFWD", "EVALT", "AREV", "EVALF", "FFUSE", "CLINK", "ENGAGR", "IFIX", "TANCH"]
def the_primitive_type_called_ear_domainActions : List String := ["initialize the relational primitive slot", "identify the primitive as a candidate for the R family", "branch the relation into its constituent directions", "define the forward morphism A", "validate the forward path", "define the contravariant adjoint A†", "check for non-reciprocal residuals", "reunite A and A† into a single reciprocal mode", "compose the unified mode with the Relational type definition", "hold the bidirectional tension as a stable state", "record the ear primitive to the Core.lean registry", "close the definition of the ear relational mode"]
def the_primitive_type_called_ear_forkFusePairs : List (Nat × Nat) := [(2, 7)]
def the_primitive_type_called_ear_glyphWord : String := Imscribing.glyphWordOf the_primitive_type_called_ear_opcodes

theorem the_primitive_type_called_ear_program_length :
    the_primitive_type_called_ear_opcodes.length = the_primitive_type_called_ear_bootstrapSteps := by decide
theorem the_primitive_type_called_ear_actions_cover_program :
    the_primitive_type_called_ear_domainActions.length = the_primitive_type_called_ear_opcodes.length := by decide
theorem the_primitive_type_called_ear_program_uses_native_opcodes :
    (the_primitive_type_called_ear_opcodes.all fun op => Imscribing.glyphOf op != "?") = true := by decide
theorem the_primitive_type_called_ear_pairs_name_fork_and_fuse :
    (the_primitive_type_called_ear_forkFusePairs.all fun p =>
      (the_primitive_type_called_ear_opcodes[p.1]? == some "FSPLIT") &&
      (the_primitive_type_called_ear_opcodes[p.2]? == some "FFUSE")) = true := by decide

end Imscribing.Primitives.Types
