/- Executable Polarity.out construction, bound to the existing gate protocol. -/
import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Primitives.TierCrossing
import Imscribing.IGMorphism
import Imscribing.IGFunctor
import Imscribing.ConventionalRegister
import Imscribing.Ob3ects.GateCheck.the_primitive_type_called_out_gate_check

namespace Imscribing.Primitives.Types
open Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

/-- Surface tokens for 'out' -/
def the_primitive_type_called_out_surfaceTokens : List String := ["primitive", "crystal", "ouroboros"]

/-- Boundary condition for 'out' -/
def the_primitive_type_called_out_boundaryCondition : String := "Polarity.out: discrete sign-flip symmetry"

/-- Belnap FOUR register descriptions -/
def the_primitive_type_called_out_registerVoid : String := "unmarked polarity state"
def the_primitive_type_called_out_registerTrue : String := "affirmed sign branch"
def the_primitive_type_called_out_registerFalse : String := "refuted sign branch"
def the_primitive_type_called_out_registerBoth : String := "coheld sign branches"

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def the_primitive_type_called_out_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_s1 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_primitive_type_called_out_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_primitive_type_called_out_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def the_primitive_type_called_out_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_l1 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_primitive_type_called_out_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_primitive_type_called_out_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_primitive_type_called_out_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_primitive_type_called_out_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def the_primitive_type_called_out_protocol : IGProtocol the_primitive_type_called_out_s0 the_primitive_type_called_out_s11 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct the_primitive_type_called_out_s9 the_primitive_type_called_out_s9 = the_primitive_type_called_out_s9 (idempotent)
  (.seq (.arrow the_primitive_type_called_out_l0 the_primitive_type_called_out_s0 the_primitive_type_called_out_s1) (.seq (.arrow the_primitive_type_called_out_l1 the_primitive_type_called_out_s1 the_primitive_type_called_out_s2) (.seq (.prod (.arrow the_primitive_type_called_out_l2 the_primitive_type_called_out_s2 the_primitive_type_called_out_s9) (.arrow the_primitive_type_called_out_l2 the_primitive_type_called_out_s2 the_primitive_type_called_out_s9)) (.seq (.arrow the_primitive_type_called_out_l9 the_primitive_type_called_out_s9 the_primitive_type_called_out_s9) (.seq (.arrow the_primitive_type_called_out_l9 the_primitive_type_called_out_s9 the_primitive_type_called_out_s10) (.arrow the_primitive_type_called_out_l10 the_primitive_type_called_out_s10 the_primitive_type_called_out_s11))))))

def the_primitive_type_called_out_tier := Imscribing.the_primitive_type_called_out_tier
theorem the_primitive_type_called_out_frobenius :
    Imscribing.igFrobeniusAlg.mul Imscribing.the_primitive_type_called_out_ground
      Imscribing.the_primitive_type_called_out_ground = Imscribing.the_primitive_type_called_out_ground :=
  Imscribing.the_primitive_type_called_out_frobenius

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
def the_primitive_type_called_out_opcodes := Imscribing.the_primitive_type_called_out_opcodes
def the_primitive_type_called_out_domainActions := Imscribing.the_primitive_type_called_out_domainActions
def the_primitive_type_called_out_forkFusePairs := Imscribing.the_primitive_type_called_out_forkFusePairs
def the_primitive_type_called_out_glyphWord := Imscribing.the_primitive_type_called_out_glyphWord
def the_primitive_type_called_out_bootstrapSteps := the_primitive_type_called_out_opcodes.length

theorem the_primitive_type_called_out_program_length :
    the_primitive_type_called_out_opcodes.length = the_primitive_type_called_out_bootstrapSteps := by rfl
theorem the_primitive_type_called_out_actions_cover_program :
    the_primitive_type_called_out_domainActions.length = the_primitive_type_called_out_opcodes.length := by decide
theorem the_primitive_type_called_out_program_uses_native_opcodes :
    (the_primitive_type_called_out_opcodes.all fun op => Imscribing.glyphOf op != "?") = true := by decide
theorem the_primitive_type_called_out_pairs_name_fork_and_fuse :
    (the_primitive_type_called_out_forkFusePairs.all fun p =>
      (the_primitive_type_called_out_opcodes[p.1]? == some "FSPLIT") &&
      (the_primitive_type_called_out_opcodes[p.2]? == some "FFUSE")) = true := by decide

end Imscribing.Primitives.Types
