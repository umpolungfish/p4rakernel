/-
  Imscribing.Primitives.Types.PrimitiveTypeAh

  Formalization of the primitive value type 'ah'
  Family: Protection (ordinal 2)
  Surface tokens: winding number, integer invariant, homotopy class
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

/-- Surface tokens for 'ah' -/
def the_primitive_type_called_ah_surfaceTokens : List String := ["winding number", "integer invariant", "homotopy class"]

/-- Boundary condition for 'ah' -/
def the_primitive_type_called_ah_boundaryCondition : String := "the fundamental group of the configuration space"

/-- Belnap FOUR register descriptions -/
def the_primitive_type_called_ah_registerVoid : String := "unmapped manifold without defined paths"
def the_primitive_type_called_ah_registerTrue : String := "stable integer winding preserved"
def the_primitive_type_called_ah_registerFalse : String := "invariant collapse or non-integer transition"
def the_primitive_type_called_ah_registerBoth : String := "entangled homotopy states"

/-- Opcode domain-semantic mapping -/
-- AFWD: positive increment
--   a clockwise traversal increasing the winding count
-- AREV: negative increment
--   a counter-clockwise traversal decreasing the winding count
-- CLINK: concatenation
--   the group operation joining two paths into a single continuous trajectory
-- ENGAGR: superposition of classes
--   a state where the system occupies multiple winding numbers simultaneously
-- EVALF: topological defect
--   a failure where the path crosses a singularity, changing the invariant
-- EVALT: integer stability
--   successful maintenance of the winding number under deformation
-- FFUSE: path integration
--   the recombination of path segments to recover the total net winding
-- FSPLIT: homotopy bifurcation
--   the division of a path into distinct potential winding sectors
-- IFIX: chern number record
--   the permanent registration of the integer winding in the system history
-- IMSCRIB: self-intersection check
--   the verification that the path remains within its defined homotopy class
-- TANCH: topological invariant
--   the global constraint that preserves the integer value against local perturbations
-- VINIT: trivial loop
--   the contractible identity element before any winding occurs

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def the_primitive_type_called_ah_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ah_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ah_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ah_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ah_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ah_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_ah_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_ah_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_ah_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_primitive_type_called_ah_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_ah_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_primitive_type_called_ah_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def the_primitive_type_called_ah_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ah_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ah_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ah_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ah_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ah_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_ah_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ah_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ah_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_primitive_type_called_ah_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_ah_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_ah_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def the_primitive_type_called_ah_protocol : IGProtocol the_primitive_type_called_ah_s0 the_primitive_type_called_ah_s11 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct the_primitive_type_called_ah_s9 the_primitive_type_called_ah_s9 = the_primitive_type_called_ah_s9 (idempotent)
  (.seq (.arrow the_primitive_type_called_ah_l0 the_primitive_type_called_ah_s0 the_primitive_type_called_ah_s1) (.seq (.prod (.arrow the_primitive_type_called_ah_l1 the_primitive_type_called_ah_s1 the_primitive_type_called_ah_s9) (.arrow the_primitive_type_called_ah_l1 the_primitive_type_called_ah_s1 the_primitive_type_called_ah_s9)) (.seq (.arrow the_primitive_type_called_ah_l9 the_primitive_type_called_ah_s9 the_primitive_type_called_ah_s9) (.seq (.arrow the_primitive_type_called_ah_l9 the_primitive_type_called_ah_s9 the_primitive_type_called_ah_s10) (.arrow the_primitive_type_called_ah_l10 the_primitive_type_called_ah_s10 the_primitive_type_called_ah_s11)))))

def the_primitive_type_called_ah_tier : OuroboricityTier := TierFunctor.obj the_primitive_type_called_ah_s0
theorem the_primitive_type_called_ah_frobenius :
    igFrobeniusAlg.mul the_primitive_type_called_ah_s0 the_primitive_type_called_ah_s0 = the_primitive_type_called_ah_s0 :=
  igFrobAlg_self_fusion the_primitive_type_called_ah_s0

#eval the_primitive_type_called_ah_tier  -- the Grammar's own verdict on its tier

/-- 'ah' belongs to the Protection family at ordinal 2 -/
def the_primitive_type_called_ah_family : String := "Protection"
def the_primitive_type_called_ah_ordinal : Nat := 2

/-- The CLINK L8 fragment for 'ah' (⊡ = 𐑭), as the organism-layer
    navigator emits it. Not authored here: the string is the navigator's. -/
def the_primitive_type_called_ah_clinkFragmentL8 : String := "∮_γ A = 2πn ∧ n ∈ ℤ ∧ wind(γ) ≠ 0"

/-- Its L8 proximity to the reference layer, and the atom it promotes. -/
def the_primitive_type_called_ah_proximityL8 : String := "close"
def the_primitive_type_called_ah_promotedAtomL8 : String := "ZWIND"

/-- The CLINK L9 fragment — the replicative-lateral reading of the same value.
    Where L9 annotates, the annotation is the transcendence content. -/
def the_primitive_type_called_ah_clinkFragmentL9 : String := "∮_γ A = 2πn ∧ n ∈ ℤ ∧ wind(γ) ≠ 0 — winding bridge"
def the_primitive_type_called_ah_proximityL9 : String := "match"
def the_primitive_type_called_ah_promotedAtomL9 : String := "WIND_BRIDGE"

/-- The fragment in ordinary mathematics, which is what a reader outside the
    Grammar reads. -/
def the_primitive_type_called_ah_conventionalReading : String := "quantized flux with nonzero winding: a nonzero first Chern class, c₁ ≠ 0."

/-- Whether the fragment IS the conventional statement rather than a picture of
    it: "always", "contextual" or "never". Read off the ★ marks in
    ig-docs/OVMs/conventional_statements.md, counted against the theorems that
    carry the value rather than assumed from one appearance. "contextual" means
    the same fragment is the statement in some domains and not in others, which
    the coordinate alone does not settle. -/
def the_primitive_type_called_ah_fragmentIsStatement : String := "contextual"

/-- The count behind that verdict, so its strength is visible. -/
def the_primitive_type_called_ah_fragmentIsStatementEvidence : String := "starred in 3 of the 5 sampled theorem(s) that carry it"
def the_primitive_type_called_ah_bootstrapSteps : Nat := 10

/-- Ordered executable construction retained alongside the typed protocol. -/
def the_primitive_type_called_ah_opcodes : List String := ["VINIT", "IMSCRIB", "AFWD", "FSPLIT", "EVALT", "CLINK", "FFUSE", "IMSCRIB", "IFIX", "TANCH"]
def the_primitive_type_called_ah_domainActions : List String := ["initialize the manifold at the base point", "identify the base point as the self-referential origin", "initiate a forward traversal along the loop", "branch the trajectory to evaluate potential winding directions", "confirm the path maintains a positive orientation", "compose the segments into a complete rotation", "integrate the segments back into a unified loop", "verify the loop has returned to the base point", "record the resulting integer winding number in the topological ledger", "anchor the state within the global protection boundary"]
def the_primitive_type_called_ah_forkFusePairs : List (Nat × Nat) := [(3, 6)]
def the_primitive_type_called_ah_glyphWord : String := Imscribing.glyphWordOf the_primitive_type_called_ah_opcodes

theorem the_primitive_type_called_ah_program_length :
    the_primitive_type_called_ah_opcodes.length = the_primitive_type_called_ah_bootstrapSteps := by decide
theorem the_primitive_type_called_ah_actions_cover_program :
    the_primitive_type_called_ah_domainActions.length = the_primitive_type_called_ah_opcodes.length := by decide
theorem the_primitive_type_called_ah_program_uses_native_opcodes :
    (the_primitive_type_called_ah_opcodes.all fun op => Imscribing.glyphOf op != "?") = true := by decide
theorem the_primitive_type_called_ah_pairs_name_fork_and_fuse :
    (the_primitive_type_called_ah_forkFusePairs.all fun p =>
      (the_primitive_type_called_ah_opcodes[p.1]? == some "FSPLIT") &&
      (the_primitive_type_called_ah_opcodes[p.2]? == some "FFUSE")) = true := by decide

end Imscribing.Primitives.Types
