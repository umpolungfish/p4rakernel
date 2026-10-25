/- Executable Polarity.out construction, bound to the existing gate protocol. -/
import Imscribing.Ob3ects.GateCheck.the_primitive_type_called_out_gate_check

namespace Imscribing.Primitives.Types
open Primitives

/-- Surface tokens for 'out' -/
def the_primitive_type_called_out_surfaceTokens : List String := ["primitive", "crystal", "ouroboros"]

/-- Boundary condition for 'out' -/
def the_primitive_type_called_out_boundaryCondition : String := "Polarity.out: discrete sign-flip symmetry"

/-- Belnap FOUR register descriptions -/
def the_primitive_type_called_out_registerVoid : String := "unmarked polarity state"
def the_primitive_type_called_out_registerTrue : String := "affirmed sign branch"
def the_primitive_type_called_out_registerFalse : String := "refuted sign branch"
def the_primitive_type_called_out_registerBoth : String := "coheld sign branches"

noncomputable def the_primitive_type_called_out_protocol :=
  Imscribing.the_primitive_type_called_out_protocol
noncomputable def the_primitive_type_called_out_true_arm :=
  Imscribing.the_primitive_type_called_out_true_arm
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
