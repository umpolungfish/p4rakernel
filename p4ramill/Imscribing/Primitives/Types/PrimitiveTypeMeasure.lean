/-
  Imscribing.Primitives.Types.PrimitiveTypeMeasure

  Formalization of the primitive value type 'measure'
  Family: Grammar (ordinal 2)
  Surface tokens: causal_chain, temporal_ordering, sequential_gate
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

/-- Surface tokens for 'measure' -/
def the_primitive_type_called_measure_surfaceTokens : List String := ["causal_chain", "temporal_ordering", "sequential_gate"]

/-- Boundary condition for 'measure' -/
def the_primitive_type_called_measure_boundaryCondition : String := "the strict causal horizon of the execution thread"

/-- Belnap FOUR register descriptions -/
def the_primitive_type_called_measure_registerVoid : String := "uninitialized temporal state"
def the_primitive_type_called_measure_registerTrue : String := "valid sequential progression"
def the_primitive_type_called_measure_registerFalse : String := "causal inconsistency detected"
def the_primitive_type_called_measure_registerBoth : String := "entangled temporal orderings"

/-- Opcode domain-semantic mapping -/
-- AFWD: successor transition
--   the forward movement from step n to step n+1 in the sequence
-- AREV: traceback
--   the reverse traversal of the causal chain for debugging or state recovery
-- CLINK: step concatenation
--   the sequential chaining of discrete operations into a single measure
-- ENGAGR: superposed sequence
--   a state where multiple orderings are held simultaneously before collapse
-- EVALF: out-of-order failure
--   the detection of a causal violation or race condition
-- EVALT: ordered success
--   the confirmation that the sequence has maintained its strict ordering
-- FFUSE: causal synchronization
--   the point where parallel paths must synchronize to recover the original execution context
-- FSPLIT: causal bifurcation
--   the point where a sequence branches into parallel potential paths
-- IFIX: execution log
--   the permanent append-only record of the sequence as it occurred
-- IMSCRIB: step identity
--   the recognition of a specific operation as a discrete unit within the chain
-- TANCH: causal termination
--   the final boundary that closes the sequence and prevents further operations
-- VINIT: pre-sequential state
--   the uninitialized state before any temporal order is established

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def the_primitive_type_called_measure_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_measure_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_measure_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_measure_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_measure_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_measure_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_measure_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_measure_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_primitive_type_called_measure_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_primitive_type_called_measure_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_primitive_type_called_measure_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_primitive_type_called_measure_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def the_primitive_type_called_measure_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_measure_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_measure_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_measure_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_measure_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_measure_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_measure_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_measure_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_primitive_type_called_measure_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_measure_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_measure_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_measure_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def the_primitive_type_called_measure_protocol : IGProtocol the_primitive_type_called_measure_s0 the_primitive_type_called_measure_s11 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct the_primitive_type_called_measure_s10 the_primitive_type_called_measure_s10 = the_primitive_type_called_measure_s10 (idempotent)
  (.seq (.arrow the_primitive_type_called_measure_l0 the_primitive_type_called_measure_s0 the_primitive_type_called_measure_s1) (.seq (.prod (.arrow the_primitive_type_called_measure_l1 the_primitive_type_called_measure_s1 the_primitive_type_called_measure_s10) (.arrow the_primitive_type_called_measure_l1 the_primitive_type_called_measure_s1 the_primitive_type_called_measure_s10)) (.seq (.arrow the_primitive_type_called_measure_l10 the_primitive_type_called_measure_s10 the_primitive_type_called_measure_s10) (.arrow the_primitive_type_called_measure_l10 the_primitive_type_called_measure_s10 the_primitive_type_called_measure_s11))))

def the_primitive_type_called_measure_tier : OuroboricityTier := TierFunctor.obj the_primitive_type_called_measure_s0
theorem the_primitive_type_called_measure_frobenius :
    igFrobeniusAlg.mul the_primitive_type_called_measure_s0 the_primitive_type_called_measure_s0 = the_primitive_type_called_measure_s0 :=
  igFrobAlg_self_fusion the_primitive_type_called_measure_s0

#eval the_primitive_type_called_measure_tier  -- the Grammar's own verdict on its tier

/-- 'measure' belongs to the Grammar family at ordinal 2 -/
def the_primitive_type_called_measure_family : String := "Grammar"
def the_primitive_type_called_measure_ordinal : Nat := 2

/-- The CLINK L8 fragment for 'measure' (∋ = 𐑠), as the organism-layer
    navigator emits it. Not authored here: the string is the navigator's. -/
def the_primitive_type_called_measure_clinkFragmentL8 : String := "seq!(f, g) ∧ ⟨→⟩(f, g, τ) ∧ ¬ ⟨→⟩(g, f, τ)"

/-- Its L8 proximity to the reference layer, and the atom it promotes. -/
def the_primitive_type_called_measure_proximityL8 : String := "close"
def the_primitive_type_called_measure_promotedAtomL8 : String := "SEQAX"

/-- The CLINK L9 fragment — the replicative-lateral reading of the same value.
    Where L9 annotates, the annotation is the transcendence content. -/
def the_primitive_type_called_measure_clinkFragmentL9 : String := "seq!(f, g) ∧ ⟨→⟩(f, g, τ) ∧ ¬ ⟨→⟩(g, f, τ)"
def the_primitive_type_called_measure_proximityL9 : String := "distant"
def the_primitive_type_called_measure_promotedAtomL9 : String := "SEQAX"

/-- The fragment in ordinary mathematics, which is what a reader outside the
    Grammar reads. -/
def the_primitive_type_called_measure_conventionalReading : String := "a strict causal order: f precedes g within τ and g does not precede f. Antisymmetric precedence."

/-- Whether the fragment IS the conventional statement rather than a picture of
    it: "always", "contextual" or "never". Read off the ★ marks in
    ig-docs/OVMs/conventional_statements.md, counted against the theorems that
    carry the value rather than assumed from one appearance. "contextual" means
    the same fragment is the statement in some domains and not in others, which
    the coordinate alone does not settle. -/
def the_primitive_type_called_measure_fragmentIsStatement : String := "never"

/-- The count behind that verdict, so its strength is visible. -/
def the_primitive_type_called_measure_fragmentIsStatementEvidence : String := "starred in none of the 2 sampled theorem(s) that carry it"
def the_primitive_type_called_measure_bootstrapSteps : Nat := 15

/-- Ordered executable construction retained alongside the typed protocol. -/
def the_primitive_type_called_measure_opcodes : List String := ["VINIT", "IMSCRIB", "IFIX", "CLINK", "AFWD", "FSPLIT", "EVALT", "AFWD", "EVALF", "AREV", "FFUSE", "IMSCRIB", "CLINK", "IFIX", "TANCH"]
def the_primitive_type_called_measure_domainActions : List String := ["initialize the empty causal thread", "identify the first discrete operation in the measure", "record the start of the sequential chain", "link the first operation to the subsequent transition", "move forward to the next temporal slot", "branch the sequence to evaluate parallel dependencies", "confirm the primary dependency is satisfied in order", "advance the primary branch", "detect if the secondary branch violates causal constraints", "reverse the secondary branch to the last known valid state", "synchronize the branches back into a single execution context", "verify the integrity of the fused state", "compose the fused result with the final operation", "commit the completed measure to the permanent log", "seal the causal horizon of the measure"]
def the_primitive_type_called_measure_forkFusePairs : List (Nat × Nat) := [(5, 10)]
def the_primitive_type_called_measure_glyphWord : String := Imscribing.glyphWordOf the_primitive_type_called_measure_opcodes

theorem the_primitive_type_called_measure_program_length :
    the_primitive_type_called_measure_opcodes.length = the_primitive_type_called_measure_bootstrapSteps := by decide
theorem the_primitive_type_called_measure_actions_cover_program :
    the_primitive_type_called_measure_domainActions.length = the_primitive_type_called_measure_opcodes.length := by decide
theorem the_primitive_type_called_measure_program_uses_native_opcodes :
    (the_primitive_type_called_measure_opcodes.all fun op => Imscribing.glyphOf op != "?") = true := by decide
theorem the_primitive_type_called_measure_pairs_name_fork_and_fuse :
    (the_primitive_type_called_measure_forkFusePairs.all fun p =>
      (the_primitive_type_called_measure_opcodes[p.1]? == some "FSPLIT") &&
      (the_primitive_type_called_measure_opcodes[p.2]? == some "FFUSE")) = true := by decide

end Imscribing.Primitives.Types
