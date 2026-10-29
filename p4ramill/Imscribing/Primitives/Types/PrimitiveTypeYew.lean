/-
  Imscribing.Primitives.Types.PrimitiveTypeYew

  Formalization of the primitive value type 'yew'
  Family: Polarity (ordinal 1)
  Surface tokens: phase, symmetry, oscillator
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

/-- Surface tokens for 'yew' -/
def the_primitive_type_called_yew_surfaceTokens : List String := ["phase", "symmetry", "oscillator"]

/-- Boundary condition for 'yew' -/
def the_primitive_type_called_yew_boundaryCondition : String := "U(1) phase circle"

/-- Belnap FOUR register descriptions -/
def the_primitive_type_called_yew_registerVoid : String := "uninitialized phase space"
def the_primitive_type_called_yew_registerTrue : String := "constructive phase alignment"
def the_primitive_type_called_yew_registerFalse : String := "destructive phase alignment"
def the_primitive_type_called_yew_registerBoth : String := "coherent superposition of all phases"

/-- Opcode domain-semantic mapping -/
-- AFWD: phase rotation
--   A forward shift in the angular coordinate of the symmetry state.
-- AREV: phase inversion
--   A reverse shift or complex conjugation of the phase state.
-- CLINK: sequential rotation
--   The composition of multiple phase shifts into a single resultant angle.
-- ENGAGR: superposition
--   A state where multiple phase angles are held simultaneously without collapse.
-- EVALF: destructive interference
--   The negative alignment of phases resulting in signal cancellation.
-- EVALT: constructive interference
--   The affirmative alignment of phases resulting in signal gain.
-- FFUSE: interference pattern
--   The recombination of split phase paths to recover the original coherent wave.
-- FSPLIT: wavefront bifurcation
--   A single phase state splitting into a leading edge and a trailing edge.
-- IFIX: phase lock
--   The permanent fixation of a specific phase angle in memory.
-- IMSCRIB: phase identity
--   The zero-degree rotation where the state recognizes its own orientation.
-- TANCH: unitary group boundary
--   The closed circle of the U(1) group containing all possible phase rotations.
-- VINIT: unpolarized vacuum
--   The state before any phase angle or symmetry axis is defined.

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def the_primitive_type_called_yew_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_yew_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_yew_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_yew_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_yew_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_yew_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_yew_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_yew_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_yew_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_primitive_type_called_yew_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_primitive_type_called_yew_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_primitive_type_called_yew_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def the_primitive_type_called_yew_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_yew_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_yew_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_yew_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_yew_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_yew_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_yew_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_yew_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_yew_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_primitive_type_called_yew_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_yew_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_yew_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def the_primitive_type_called_yew_protocol : IGProtocol the_primitive_type_called_yew_s0 the_primitive_type_called_yew_s11 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct the_primitive_type_called_yew_s7 the_primitive_type_called_yew_s7 = the_primitive_type_called_yew_s7 (idempotent)
  (.seq (.arrow the_primitive_type_called_yew_l0 the_primitive_type_called_yew_s0 the_primitive_type_called_yew_s1) (.seq (.prod (.arrow the_primitive_type_called_yew_l1 the_primitive_type_called_yew_s1 the_primitive_type_called_yew_s7) (.arrow the_primitive_type_called_yew_l1 the_primitive_type_called_yew_s1 the_primitive_type_called_yew_s7)) (.seq (.arrow the_primitive_type_called_yew_l7 the_primitive_type_called_yew_s7 the_primitive_type_called_yew_s7) (.seq (.arrow the_primitive_type_called_yew_l7 the_primitive_type_called_yew_s7 the_primitive_type_called_yew_s8) (.seq (.arrow the_primitive_type_called_yew_l8 the_primitive_type_called_yew_s8 the_primitive_type_called_yew_s9) (.seq (.arrow the_primitive_type_called_yew_l9 the_primitive_type_called_yew_s9 the_primitive_type_called_yew_s10) (.arrow the_primitive_type_called_yew_l10 the_primitive_type_called_yew_s10 the_primitive_type_called_yew_s11)))))))

def the_primitive_type_called_yew_tier : OuroboricityTier := TierFunctor.obj the_primitive_type_called_yew_s0
theorem the_primitive_type_called_yew_frobenius :
    igFrobeniusAlg.mul the_primitive_type_called_yew_s0 the_primitive_type_called_yew_s0 = the_primitive_type_called_yew_s0 :=
  igFrobAlg_self_fusion the_primitive_type_called_yew_s0

#eval the_primitive_type_called_yew_tier  -- the Grammar's own verdict on its tier

/-- 'yew' belongs to the Polarity family at ordinal 1 -/
def the_primitive_type_called_yew_family : String := "Polarity"
def the_primitive_type_called_yew_ordinal : Nat := 1

/-- The CLINK L8 fragment for 'yew' (≺ = 𐑿), as the organism-layer
    navigator emits it. Not authored here: the string is the navigator's. -/
def the_primitive_type_called_yew_clinkFragmentL8 : String := "|ψ⟩ = Σ c_i |e_i⟩"

/-- Its L8 proximity to the reference layer, and the atom it promotes. -/
def the_primitive_type_called_yew_proximityL8 : String := "close"
def the_primitive_type_called_yew_promotedAtomL8 : String := ""

/-- The CLINK L9 fragment — the replicative-lateral reading of the same value.
    Where L9 annotates, the annotation is the transcendence content. -/
def the_primitive_type_called_yew_clinkFragmentL9 : String := "|ψ⟩ = Σ c_i |e_i⟩"
def the_primitive_type_called_yew_proximityL9 : String := "close"
def the_primitive_type_called_yew_promotedAtomL9 : String := ""

/-- The fragment in ordinary mathematics, which is what a reader outside the
    Grammar reads. -/
def the_primitive_type_called_yew_conventionalReading : String := "a vector expanded in an orthonormal basis: a superposition."

/-- Whether the fragment IS the conventional statement rather than a picture of
    it: "always", "contextual" or "never". Read off the ★ marks in
    ig-docs/OVMs/conventional_statements.md, counted against the theorems that
    carry the value rather than assumed from one appearance. "contextual" means
    the same fragment is the statement in some domains and not in others, which
    the coordinate alone does not settle. -/
def the_primitive_type_called_yew_fragmentIsStatement : String := "never"

/-- The count behind that verdict, so its strength is visible. -/
def the_primitive_type_called_yew_fragmentIsStatementEvidence : String := "starred in none of the 2 sampled theorem(s) that carry it"
def the_primitive_type_called_yew_bootstrapSteps : Nat := 12

/-- Ordered executable construction retained alongside the typed protocol. -/
def the_primitive_type_called_yew_opcodes : List String := ["VINIT", "IMSCRIB", "AFWD", "FSPLIT", "EVALT", "CLINK", "AREV", "EVALF", "FFUSE", "ENGAGR", "IFIX", "TANCH"]
def the_primitive_type_called_yew_domainActions : List String := ["establish the unpolarized vacuum state", "identify the base phase reference", "apply a continuous phase rotation", "bifurcate the signal into dual paths", "verify constructive alignment on the primary path", "compose the primary path with a secondary rotation", "apply a parity flip to the secondary path", "verify destructive alignment on the secondary path", "recombine paths into a single interference result", "hold the resulting phase in superposition", "record the final phase lock to the ledger", "seal the operation within the U(1) boundary"]
def the_primitive_type_called_yew_forkFusePairs : List (Nat × Nat) := [(3, 8)]
def the_primitive_type_called_yew_glyphWord : String := Imscribing.glyphWordOf the_primitive_type_called_yew_opcodes

theorem the_primitive_type_called_yew_program_length :
    the_primitive_type_called_yew_opcodes.length = the_primitive_type_called_yew_bootstrapSteps := by decide
theorem the_primitive_type_called_yew_actions_cover_program :
    the_primitive_type_called_yew_domainActions.length = the_primitive_type_called_yew_opcodes.length := by decide
theorem the_primitive_type_called_yew_program_uses_native_opcodes :
    (the_primitive_type_called_yew_opcodes.all fun op => Imscribing.glyphOf op != "?") = true := by decide
theorem the_primitive_type_called_yew_pairs_name_fork_and_fuse :
    (the_primitive_type_called_yew_forkFusePairs.all fun p =>
      (the_primitive_type_called_yew_opcodes[p.1]? == some "FSPLIT") &&
      (the_primitive_type_called_yew_opcodes[p.2]? == some "FFUSE")) = true := by decide

end Imscribing.Primitives.Types
