/-
  Imscribing.Primitives.Types.PrimitiveTypeNun

  Formalization of the primitive value type 'nun'
  Family: Polarity (ordinal 3)
  Surface tokens: isometry, manifold, invariance
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

/-- Surface tokens for 'nun' -/
def the_primitive_type_called_nun_surfaceTokens : List String := ["isometry", "manifold", "invariance"]

/-- Boundary condition for 'nun' -/
def the_primitive_type_called_nun_boundaryCondition : String := "The Lie group SO(n) defining the continuous symmetry space"

/-- Belnap FOUR register descriptions -/
def the_primitive_type_called_nun_registerVoid : String := "unmapped coordinate vacuum"
def the_primitive_type_called_nun_registerTrue : String := "invariant state maintained"
def the_primitive_type_called_nun_registerFalse : String := "symmetry broken"
def the_primitive_type_called_nun_registerBoth : String := "coherent orbital state"

/-- Opcode domain-semantic mapping -/
-- AFWD: infinitesimal rotation
--   A forward transformation within the Lie algebra toward a new orientation.
-- AREV: inverse rotation
--   The contravariant operation that returns the vector to its previous state.
-- CLINK: matrix multiplication
--   The sequential composition of two symmetry operations.
-- ENGAGR: superposition of orientations
--   A state where multiple rotations are held simultaneously without collapse.
-- EVALF: metric distortion
--   The failure state where the transformation violates the symmetry constraint.
-- EVALT: norm preservation
--   The affirmative state where the transformation is a valid isometry.
-- FFUSE: isometry reconstruction
--   Recombining radial and angular components to recover the original transformation.
-- FSPLIT: symmetry decomposition
--   Splitting a transformation into its radial and angular components.
-- IFIX: determinant record
--   The permanent fixation of the transformation's orientation parity.
-- IMSCRIB: identity matrix
--   The self-recognition of the system where no transformation occurs.
-- TANCH: SO(n) group closure
--   The terminal boundary that contains all valid rotations and preserves the norm.
-- VINIT: unstructured vector space
--   The raw coordinate space before any metric or symmetry is imposed.

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def the_primitive_type_called_nun_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_nun_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_nun_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_nun_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_nun_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_nun_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_nun_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_nun_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_primitive_type_called_nun_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_primitive_type_called_nun_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_primitive_type_called_nun_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_primitive_type_called_nun_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def the_primitive_type_called_nun_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_nun_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_nun_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_nun_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_nun_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_nun_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_nun_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_nun_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_primitive_type_called_nun_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_nun_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_nun_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_nun_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def the_primitive_type_called_nun_protocol : IGProtocol the_primitive_type_called_nun_s0 the_primitive_type_called_nun_s11 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct the_primitive_type_called_nun_s10 the_primitive_type_called_nun_s10 = the_primitive_type_called_nun_s10 (idempotent)
  (.seq (.arrow the_primitive_type_called_nun_l0 the_primitive_type_called_nun_s0 the_primitive_type_called_nun_s1) (.seq (.prod (.arrow the_primitive_type_called_nun_l1 the_primitive_type_called_nun_s1 the_primitive_type_called_nun_s10) (.arrow the_primitive_type_called_nun_l1 the_primitive_type_called_nun_s1 the_primitive_type_called_nun_s10)) (.seq (.arrow the_primitive_type_called_nun_l10 the_primitive_type_called_nun_s10 the_primitive_type_called_nun_s10) (.arrow the_primitive_type_called_nun_l10 the_primitive_type_called_nun_s10 the_primitive_type_called_nun_s11))))

def the_primitive_type_called_nun_tier : OuroboricityTier := TierFunctor.obj the_primitive_type_called_nun_s0
theorem the_primitive_type_called_nun_frobenius :
    igFrobeniusAlg.mul the_primitive_type_called_nun_s0 the_primitive_type_called_nun_s0 = the_primitive_type_called_nun_s0 :=
  igFrobAlg_self_fusion the_primitive_type_called_nun_s0

#eval the_primitive_type_called_nun_tier  -- the Grammar's own verdict on its tier

/-- 'nun' belongs to the Polarity family at ordinal 3 -/
def the_primitive_type_called_nun_family : String := "Polarity"
def the_primitive_type_called_nun_ordinal : Nat := 3

/-- The CLINK L8 fragment for 'nun' (≺ = 𐑯), as the organism-layer
    navigator emits it. Not authored here: the string is the navigator's. -/
def the_primitive_type_called_nun_clinkFragmentL8 : String := "∀g∈G( gx = x )"

/-- Its L8 proximity to the reference layer, and the atom it promotes. -/
def the_primitive_type_called_nun_proximityL8 : String := "distant"
def the_primitive_type_called_nun_promotedAtomL8 : String := ""

/-- The CLINK L9 fragment — the replicative-lateral reading of the same value.
    Where L9 annotates, the annotation is the transcendence content. -/
def the_primitive_type_called_nun_clinkFragmentL9 : String := "∀g∈G( gx = x )"
def the_primitive_type_called_nun_proximityL9 : String := "distant"
def the_primitive_type_called_nun_promotedAtomL9 : String := ""

/-- The fragment in ordinary mathematics, which is what a reader outside the
    Grammar reads. -/
def the_primitive_type_called_nun_conventionalReading : String := "x is a fixed point of the group action; invariant."

/-- Whether the fragment IS the conventional statement rather than a picture of
    it: "always", "contextual" or "never". Read off the ★ marks in
    ig-docs/OVMs/conventional_statements.md, counted against the theorems that
    carry the value rather than assumed from one appearance. "contextual" means
    the same fragment is the statement in some domains and not in others, which
    the coordinate alone does not settle. -/
def the_primitive_type_called_nun_fragmentIsStatement : String := "never"

/-- The count behind that verdict, so its strength is visible. -/
def the_primitive_type_called_nun_fragmentIsStatementEvidence : String := "not carried by any of the seven sampled theorems"
def the_primitive_type_called_nun_bootstrapSteps : Nat := 12

/-- Ordered executable construction retained alongside the typed protocol. -/
def the_primitive_type_called_nun_opcodes : List String := ["VINIT", "IMSCRIB", "FSPLIT", "EVALT", "AFWD", "CLINK", "IFIX", "AREV", "EVALF", "FFUSE", "ENGAGR", "TANCH"]
def the_primitive_type_called_nun_domainActions : List String := ["initialize the raw coordinate manifold", "identify the base identity state of the manifold", "decompose the initial state into potential transformation paths", "verify the path maintains continuous symmetry", "apply a generator of the Lie algebra to rotate the state", "compose the rotation with a secondary symmetry operation", "record the resulting orientation in the permanent trace", "apply the inverse generator to test reversibility", "check for any accumulated metric drift or error", "reconstitute the original state from the transformation components", "hold the transformed and original states in a paradice of invariance", "seal the operation within the SO(n) boundary"]
def the_primitive_type_called_nun_forkFusePairs : List (Nat × Nat) := [(2, 9)]
def the_primitive_type_called_nun_glyphWord : String := Imscribing.glyphWordOf the_primitive_type_called_nun_opcodes

theorem the_primitive_type_called_nun_program_length :
    the_primitive_type_called_nun_opcodes.length = the_primitive_type_called_nun_bootstrapSteps := by decide
theorem the_primitive_type_called_nun_actions_cover_program :
    the_primitive_type_called_nun_domainActions.length = the_primitive_type_called_nun_opcodes.length := by decide
theorem the_primitive_type_called_nun_program_uses_native_opcodes :
    (the_primitive_type_called_nun_opcodes.all fun op => Imscribing.glyphOf op != "?") = true := by decide
theorem the_primitive_type_called_nun_pairs_name_fork_and_fuse :
    (the_primitive_type_called_nun_forkFusePairs.all fun p =>
      (the_primitive_type_called_nun_opcodes[p.1]? == some "FSPLIT") &&
      (the_primitive_type_called_nun_opcodes[p.2]? == some "FFUSE")) = true := by decide

end Imscribing.Primitives.Types
