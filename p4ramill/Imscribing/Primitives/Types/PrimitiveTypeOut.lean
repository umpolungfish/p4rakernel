/-
  Imscribing.Primitives.Types.PrimitiveTypeOut

  Formalization of the primitive value type 'out'
  Family: Polarity (ordinal 2)
  Surface tokens: primitive, crystal, ouroboros
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

/-- Surface tokens for 'out' -/
def the_primitive_type_called_out_surfaceTokens : List String := ["primitive", "crystal", "ouroboros"]

/-- Boundary condition for 'out' -/
def the_primitive_type_called_out_boundaryCondition : String := "Imscribing.Primitives namespace"

/-- Belnap FOUR register descriptions -/
def the_primitive_type_called_out_registerVoid : String := "uninitialized Lean environment without primitive definitions"
def the_primitive_type_called_out_registerTrue : String := "valid type satisfying all cross-primitive axioms"
def the_primitive_type_called_out_registerFalse : String := "inconsistent type assignment violating Axiom C or Axiom D"
def the_primitive_type_called_out_registerBoth : String := "exceptional-point criticality where eigenvectors coalesce and phases overlap"

/-- Opcode domain-semantic mapping -/
-- AFWD: successor cycle
--   The directed mapping from 3 to 4 to 5 in the Arithmetic Ouroboros.
-- AREV: 5 - 2 = 3
--   The reverse transformation that closes the successor cycle back to the base family.
-- CLINK: composition of P < or' partners
--   The sequential chaining of polarity values under the tensor bottleneck rule.
-- ENGAGR: roar criticality
--   Complex-axis criticality requiring analytic continuation where stability and instability are held simultaneously.
-- EVALF: O₀
--   The failure to reach criticality or topological protection.
-- EVALT: O_inf
--   The affirmative attainment of the Special Frobenius tier.
-- FFUSE: holographic_closure
--   The reconstitution of a unified type from its boundary and bulk components.
-- FSPLIT: ouroboricityTier match
--   The branching of a system state into distinct O-tiers based on gate primitives.
-- IFIX: axiom declaration
--   The permanent fixation of structural constraints like Axiom D into the kernel.
-- IMSCRIB: self-anchored fixed point
--   The identity of the successor cycle where the exponent equals the primitive count.
-- TANCH: crystal_total
--   The final cardinality of 17,280,000 which bounds the entire type space.
-- VINIT: untyped void
--   The state before any inductive type or ordinal value is defined in the Lean environment.

-- Stage Imscriptions (per-node cumulative)
private def the_primitive_type_called_out_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s3 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s4 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s5 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s6 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s7 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s8 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s9 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s10 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s11 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s12 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s13 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s14 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s15 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s16 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s17 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }

-- Label Imscriptions (per-node delta)
private def the_primitive_type_called_out_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_l18 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }

-- Main IGProtocol term
noncomputable def the_primitive_type_called_out_protocol : IGProtocol the_primitive_type_called_out_s0 the_primitive_type_called_out_s21 :=
  .withGram Grammar.measure <|
  (.seq (.arrow the_primitive_type_called_out_l0 the_primitive_type_called_out_s0 the_primitive_type_called_out_s1) (.seq (.arrow the_primitive_type_called_out_l1 the_primitive_type_called_out_s1 the_primitive_type_called_out_s2) (.seq (.arrow the_primitive_type_called_out_l2 the_primitive_type_called_out_s2 the_primitive_type_called_out_s3) (.seq (.arrow the_primitive_type_called_out_l3 the_primitive_type_called_out_s3 the_primitive_type_called_out_s4) (.seq (.arrow the_primitive_type_called_out_l4 the_primitive_type_called_out_s4 the_primitive_type_called_out_s5) (.seq (.arrow the_primitive_type_called_out_l5 the_primitive_type_called_out_s5 the_primitive_type_called_out_s6) (.seq (.arrow the_primitive_type_called_out_l6 the_primitive_type_called_out_s6 the_primitive_type_called_out_s7) (.seq (.arrow the_primitive_type_called_out_l7 the_primitive_type_called_out_s7 the_primitive_type_called_out_s8) (.seq (.arrow the_primitive_type_called_out_l8 the_primitive_type_called_out_s8 the_primitive_type_called_out_s9) (.seq (.arrow the_primitive_type_called_out_l9 the_primitive_type_called_out_s9 the_primitive_type_called_out_s10) (.seq (.arrow the_primitive_type_called_out_l10 the_primitive_type_called_out_s10 the_primitive_type_called_out_s11) (.seq (.arrow the_primitive_type_called_out_l11 the_primitive_type_called_out_s11 the_primitive_type_called_out_s12) (.seq (.arrow the_primitive_type_called_out_l12 the_primitive_type_called_out_s12 the_primitive_type_called_out_s13) (.seq (.arrow the_primitive_type_called_out_l13 the_primitive_type_called_out_s13 the_primitive_type_called_out_s14) (.seq (.arrow the_primitive_type_called_out_l14 the_primitive_type_called_out_s14 the_primitive_type_called_out_s15) (.seq (.arrow the_primitive_type_called_out_l15 the_primitive_type_called_out_s15 the_primitive_type_called_out_s16) (.seq (.prod (.arrow the_primitive_type_called_out_l16 the_primitive_type_called_out_s16 the_primitive_type_called_out_s20) (.arrow the_primitive_type_called_out_l16 the_primitive_type_called_out_s16 the_primitive_type_called_out_s20)) (.seq (.arrow the_primitive_type_called_out_l20 the_primitive_type_called_out_s20 the_primitive_type_called_out_s20) (.arrow the_primitive_type_called_out_l20 the_primitive_type_called_out_s20 the_primitive_type_called_out_s21)))))))))))))))))))

-- Evaluation arm sub-defs
noncomputable def the_primitive_type_called_out_true_arm : IGProtocol the_primitive_type_called_out_s0 the_primitive_type_called_out_s21 :=
  (the_primitive_type_called_out_protocol).restrictToEVALT

-- Verification theorems
def the_primitive_type_called_out_tier : OuroboricityTier := TierFunctor.obj the_primitive_type_called_out_s0
theorem the_primitive_type_called_out_frobenius :
    igFrobeniusAlg.mul the_primitive_type_called_out_s0 the_primitive_type_called_out_s0 = the_primitive_type_called_out_s0 :=
  igFrobAlg_self_fusion the_primitive_type_called_out_s0

#eval the_primitive_type_called_out_tier  -- the Grammar's own verdict on its tier

/-- 'out' belongs to the Polarity family at ordinal 2 -/
def the_primitive_type_called_out_family : String := "Polarity"
def the_primitive_type_called_out_ordinal : Nat := 2

/-- The CLINK L8 fragment for 'out' (≺ = 𐑬), as the organism-layer
    navigator emits it. Not authored here: the string is the navigator's. -/
def the_primitive_type_called_out_clinkFragmentL8 : String := "ℤ₂(x) ∧ ¬(x = -x)"

/-- Its L8 proximity to the reference layer, and the atom it promotes. -/
def the_primitive_type_called_out_proximityL8 : String := "close"
def the_primitive_type_called_out_promotedAtomL8 : String := ""

/-- The CLINK L9 fragment — the replicative-lateral reading of the same value.
    Where L9 annotates, the annotation is the transcendence content. -/
def the_primitive_type_called_out_clinkFragmentL9 : String := "ℤ₂(x) ∧ ¬(x = -x) — parity of moat"
def the_primitive_type_called_out_proximityL9 : String := "match"
def the_primitive_type_called_out_promotedAtomL9 : String := "MOAT_PARITY"

/-- The fragment in ordinary mathematics, which is what a reader outside the
    Grammar reads. -/
def the_primitive_type_called_out_conventionalReading : String := "a nonzero element of a ℤ₂-graded module in characteristic ≠ 2."

/-- Whether the fragment IS the conventional statement rather than a picture of
    it: "always", "contextual" or "never". Read off the ★ marks in
    ig-docs/OVMs/conventional_statements.md, counted against the theorems that
    carry the value rather than assumed from one appearance. "contextual" means
    the same fragment is the statement in some domains and not in others, which
    the coordinate alone does not settle. -/
def the_primitive_type_called_out_fragmentIsStatement : String := "never"

/-- The count behind that verdict, so its strength is visible. -/
def the_primitive_type_called_out_fragmentIsStatementEvidence : String := "not carried by any of the seven sampled theorems"
def the_primitive_type_called_out_bootstrapSteps : Nat := 22

end Imscribing.Primitives.Types
