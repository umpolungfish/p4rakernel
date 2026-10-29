/-
  Imscribing.Primitives.Types.PrimitiveTypeAge

  Formalization of the primitive value type 'age'
  Family: Fidelity (ordinal 0)
  Surface tokens: classical search, lossy fidelity, bottleneck
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

/-- Surface tokens for 'age' -/
def the_primitive_type_called_age_surfaceTokens : List String := ["classical search", "lossy fidelity", "bottleneck"]

/-- Boundary condition for 'age' -/
def the_primitive_type_called_age_boundaryCondition : String := "The \u2113-fidelity classical search space"

/-- Belnap FOUR register descriptions -/
def the_primitive_type_called_age_registerVoid : String := "pre-search state with no defined fidelity"
def the_primitive_type_called_age_registerTrue : String := "successful search step within age fidelity bounds"
def the_primitive_type_called_age_registerFalse : String := "search failure or excessive information loss"
def the_primitive_type_called_age_registerBoth : String := "a state of partial information where signal and noise are indistinguishable"

/-- Opcode domain-semantic mapping -/
-- AFWD: search progression
--   The forward movement through the search space toward a target.
-- AREV: backtracking
--   The reversal of search steps when a path is exhausted or invalid.
-- CLINK: step composition
--   The chaining of individual search operations into a continuous path.
-- ENGAGR: stochastic noise
--   The simultaneous presence of signal and noise in a lossy classical system.
-- EVALF: fidelity loss
--   The detection of information loss exceeding the 'age' limit.
-- EVALT: fidelity match
--   The confirmation that the operation maintains the required classical fidelity.
-- FFUSE: fidelity resolution
--   The reconstitution of the search state after the fidelity check.
-- FSPLIT: fidelity comparison
--   The branching of the search based on whether the current fidelity meets the 'age' threshold.
-- IFIX: search log
--   The permanent record of the search path and its fidelity metrics.
-- IMSCRIB: fidelity self-recognition
--   The system identifying its own state as 'age' (classical lossy).
-- TANCH: search termination
--   The final boundary where the search concludes and the result is returned.
-- VINIT: uninitialized search space
--   The state before any search parameters or fidelity constraints are defined.

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def the_primitive_type_called_age_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_age_s1 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_age_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_age_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_age_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_age_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_primitive_type_called_age_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_age_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_age_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_age_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_age_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_primitive_type_called_age_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def the_primitive_type_called_age_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_age_l1 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_age_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_age_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_age_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_age_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_primitive_type_called_age_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_age_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_age_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_age_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_age_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_age_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def the_primitive_type_called_age_protocol : IGProtocol the_primitive_type_called_age_s0 the_primitive_type_called_age_s11 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct the_primitive_type_called_age_s6 the_primitive_type_called_age_s6 = the_primitive_type_called_age_s6 (idempotent)
  (.seq (.arrow the_primitive_type_called_age_l0 the_primitive_type_called_age_s0 the_primitive_type_called_age_s1) (.seq (.arrow the_primitive_type_called_age_l1 the_primitive_type_called_age_s1 the_primitive_type_called_age_s2) (.seq (.prod (.arrow the_primitive_type_called_age_l2 the_primitive_type_called_age_s2 the_primitive_type_called_age_s6) (.arrow the_primitive_type_called_age_l2 the_primitive_type_called_age_s2 the_primitive_type_called_age_s6)) (.seq (.arrow the_primitive_type_called_age_l6 the_primitive_type_called_age_s6 the_primitive_type_called_age_s6) (.seq (.arrow the_primitive_type_called_age_l6 the_primitive_type_called_age_s6 the_primitive_type_called_age_s7) (.seq (.arrow the_primitive_type_called_age_l7 the_primitive_type_called_age_s7 the_primitive_type_called_age_s8) (.seq (.arrow the_primitive_type_called_age_l8 the_primitive_type_called_age_s8 the_primitive_type_called_age_s9) (.seq (.arrow the_primitive_type_called_age_l9 the_primitive_type_called_age_s9 the_primitive_type_called_age_s10) (.arrow the_primitive_type_called_age_l10 the_primitive_type_called_age_s10 the_primitive_type_called_age_s11)))))))))

def the_primitive_type_called_age_tier : OuroboricityTier := TierFunctor.obj the_primitive_type_called_age_s0

#eval the_primitive_type_called_age_tier  -- the Grammar's own verdict on its tier

/-- 'age' belongs to the Fidelity family at ordinal 0 -/
def the_primitive_type_called_age_family : String := "Fidelity"
def the_primitive_type_called_age_ordinal : Nat := 0

/-- The CLINK L8 fragment for 'age' (⋈ = 𐑱), as the organism-layer
    navigator emits it. Not authored here: the string is the navigator's. -/
def the_primitive_type_called_age_clinkFragmentL8 : String := "P(x) ∈ {0,1} ∧ det(x)"

/-- Its L8 proximity to the reference layer, and the atom it promotes. -/
def the_primitive_type_called_age_proximityL8 : String := "distant"
def the_primitive_type_called_age_promotedAtomL8 : String := ""

/-- The CLINK L9 fragment — the replicative-lateral reading of the same value.
    Where L9 annotates, the annotation is the transcendence content. -/
def the_primitive_type_called_age_clinkFragmentL9 : String := "P(x) ∈ {0,1} ∧ det(x)"
def the_primitive_type_called_age_proximityL9 : String := "distant"
def the_primitive_type_called_age_promotedAtomL9 : String := ""

/-- The fragment in ordinary mathematics, which is what a reader outside the
    Grammar reads. -/
def the_primitive_type_called_age_conventionalReading : String := "a Dirac measure: every event has probability zero or one."

/-- Whether the fragment IS the conventional statement rather than a picture of
    it: "always", "contextual" or "never". Read off the ★ marks in
    ig-docs/OVMs/conventional_statements.md, counted against the theorems that
    carry the value rather than assumed from one appearance. "contextual" means
    the same fragment is the statement in some domains and not in others, which
    the coordinate alone does not settle. -/
def the_primitive_type_called_age_fragmentIsStatement : String := "never"

/-- The count behind that verdict, so its strength is visible. -/
def the_primitive_type_called_age_fragmentIsStatementEvidence : String := "not carried by any of the seven sampled theorems"
def the_primitive_type_called_age_bootstrapSteps : Nat := 16

/-- Ordered executable construction retained alongside the typed protocol. -/
def the_primitive_type_called_age_opcodes : List String := ["VINIT", "IMSCRIB", "AFWD", "FSPLIT", "EVALT", "FFUSE", "CLINK", "IFIX", "FSPLIT", "EVALF", "AREV", "FFUSE", "ENGAGR", "CLINK", "IFIX", "TANCH"]
def the_primitive_type_called_age_domainActions : List String := ["initialize the search space for the age primitive", "identify the system as a classical lossy search environment", "begin the forward search morphism toward the target data", "branch the search to evaluate current fidelity against the age threshold", "confirm the search step remains within classical fidelity limits", "reunite the search path with the confirmed fidelity state", "compose the current search step with the previous state", "record the search step and its fidelity metric in the permanent log", "branch to check for potential information loss", "identify a lossy transition that exceeds the age primitive's tolerance", "reverse the search step to recover from the lossy state", "reconstitute the search state after the recovery attempt", "hold the search in a state of stochastic uncertainty where signal and noise coexist", "chain the uncertain state into the search history", "commit the final search result to the append-only record", "close the search boundary and terminate the process"]
def the_primitive_type_called_age_forkFusePairs : List (Nat × Nat) := [(3, 5), (8, 11)]
def the_primitive_type_called_age_glyphWord : String := Imscribing.glyphWordOf the_primitive_type_called_age_opcodes

theorem the_primitive_type_called_age_program_length :
    the_primitive_type_called_age_opcodes.length = the_primitive_type_called_age_bootstrapSteps := by decide
theorem the_primitive_type_called_age_actions_cover_program :
    the_primitive_type_called_age_domainActions.length = the_primitive_type_called_age_opcodes.length := by decide
theorem the_primitive_type_called_age_program_uses_native_opcodes :
    (the_primitive_type_called_age_opcodes.all fun op => Imscribing.glyphOf op != "?") = true := by decide
theorem the_primitive_type_called_age_pairs_name_fork_and_fuse :
    (the_primitive_type_called_age_forkFusePairs.all fun p =>
      (the_primitive_type_called_age_opcodes[p.1]? == some "FSPLIT") &&
      (the_primitive_type_called_age_opcodes[p.2]? == some "FFUSE")) = true := by decide

end Imscribing.Primitives.Types
