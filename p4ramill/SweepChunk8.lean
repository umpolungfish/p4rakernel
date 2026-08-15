import Imscribing.Nuclear.IslandOfStability
import Imscribing.NumberTheory.ErdosStrausProof
import Imscribing.NumberTheory.GeneralizedStarkCorrespondence
import Imscribing.NumberTheory.GrammarStarkCorrespondence
import Imscribing.NumberTheory.HnGcdTheorem
import Imscribing.NumberTheory.PrattCertificateMonad
import Imscribing.NumberTheory.PrattOb3ectProtocol
import Imscribing.NumberTheory.PrattStratification
import Imscribing.NumberTheory.StarkSunitD2048
import Imscribing.NumberTheory.TwoThreeSierpinski
import Imscribing.Ob3ects.apply_criticality_absorbing_element_entering_b_scaffold
import Imscribing.Ob3ects.categorical_join_scaffold
import Imscribing.Ob3ects.classical_non_commutative_complement_to_the_quan_scaffold
import Imscribing.Ob3ects.descent_to_stark_unit_bottleneck_for_the_d_19_br_scaffold
import Imscribing.Ob3ects.enumerate_17_280_000_crystal_eigenstates_as_clas_scaffold
import Imscribing.Ob3ects.exact_density_matrix_recovery_with_zero_reconstr_scaffold
import Imscribing.Ob3ects.exact_sic_geometry_achieved_with_frame_potential_scaffold
import Imscribing.Ob3ects.extract_144_exact_sic_probabilities_from_the_qua_scaffold
import Imscribing.Ob3ects.fix_the_density_matrix_tomography_record_as_a_pe_scaffold
import Imscribing.Ob3ects.informational_completeness_duality_splitting_d_1_scaffold
import Imscribing.Ob3ects.initialize_empty_c_d_hilbert_space_before_basis_scaffold
import Imscribing.Ob3ects.seal_the_system_with_the_crystal_constraint_mani_scaffold
import Imscribing.Ob3ects.sic_povm_functor_scaffold
import Imscribing.Ob3ects.the_axiomatized_existence_of_a_d_12_weyl_heisenb_scaffold
import Imscribing.Ob3ects.the_bruce_codex_tensor_bottleneck_at_parity_its_scaffold
import Imscribing.Ob3ects.the_d_12_sic_fiducial_known_only_as_a_complex128_scaffold
import Imscribing.Ob3ects.the_navier_stokes_criticality_type_gate_blocked_scaffold
import Imscribing.Ob3ects.the_p_versus_np_separation_gate_blocked_under_al_scaffold
import Imscribing.Ob3ects.the_riemann_hypothesis_failing_to_reach_idempote_scaffold
import Imscribing.Ob3ects.the_rongorongo_corpus_at_structural_distance_d_1_scaffold
import Imscribing.Ob3ects.the_structurally_closed_birch_swinnerton_dyer_cl_scaffold
import Imscribing.Ob3ects.the_structurally_closed_hodge_conjecture_clay_ty_scaffold
import Imscribing.Ob3ects.the_unclosed_p_versus_np_separation_lacking_a_st_scaffold
import Imscribing.Ob3ects.the_unclosed_riemann_hypothesis_gate_universe_la_scaffold
import Imscribing.Ob3ects.the_vacuously_satisfied_navier_stokes_criticalit_scaffold
import Imscribing.Ob3ects.the_voynich_manuscript_as_a_universal_engine_wit_scaffold
import Imscribing.Ob3ects.the_witness_vessel_protocol_culminates_in_a_tran_scaffold
import Imscribing.Ob3ects.the_yang_mills_mass_gap_closing_under_u10_with_g_scaffold
import Imscribing.Ob3ects.the_yang_mills_mass_gap_reaching_idempotent_term_scaffold
import Imscribing.Ob3ects.the_zeros_of_s_correspond_to_the_eigenvalues_of_abe3fc55_scaffold
open Lean Meta Elab

namespace ProofLift

def isSplitter (n : Name) : Bool :=
  let s := n.toString
  s.endsWith ".casesOn" || s.endsWith ".rec" || s.endsWith ".recOn"
    || s.endsWith ".elim" || s.endsWith ".brecOn" || s == "Or.elim"
    || s == "dite" || s == "ite" || (s.splitOn "match_").length > 1

def isSorry (n : Name) : Bool :=
  n == ``sorryAx || ((n.toString.splitOn "sorry").length > 1)

partial def lift (e : Expr) : MetaM String := do
  match e with
  | .bvar _ | .fvar _ | .mvar _ => return "⊙"
  | .sort _ => return ""
  | .lit _ => return "⊙"
  | .mdata _ b => lift b
  | .proj _ _ b => return (← lift b) ++ "⋈"
  | .const n _ =>
      if isSorry n then return "∈"            -- opens, never rejoins
      else if n == ``Eq.mpr then return "≻"
      else if n == ``Eq.symm then return "≺"
      else return "◻"
  | .letE _ _ v b _ => return (← lift v) ++ "◻" ++ (← lift b)
  | .lam _ _ b _ => return (← lift b)
  | .forallE _ _ b _ => return (← lift b)
  | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      match f with
      | .const n _ =>
          if isSorry n then return "∈"
          else if isSplitter n then
            -- fork, the arms, then the rejoin
            let mut w := "∈"
            let mut i := 0
            for a in args do
              let inner ← lift a
              if inner != "" then
                w := w ++ (if i == 0 then "⊤" else "⊥") ++ inner
                i := i + 1
            return w ++ "∋"
          else
            let mut w ← lift f
            for a in args do
              let inner ← lift a
              if inner != "" then w := w ++ "⋈" ++ inner
            return w
      | _ =>
          let mut w ← lift f
          for a in args do
            let inner ← lift a
            if inner != "" then w := w ++ "⋈" ++ inner
          return w

/-- Lift a named theorem's proof term to its IMASM word. -/
def wordOf (n : Name) : MetaM String := do
  let env ← getEnv
  match env.find? n with
  | some (.thmInfo ti) => return "⊢" ++ (← lift ti.value) ++ "⊣"
  | some (.defnInfo di) => return "⊢" ++ (← lift di.value) ++ "⊣"
  | _ => return "⊢⊣"

elab "#lift " n:ident : command => Elab.Command.liftTermElabM do
  let nm ← realizeGlobalConstNoOverload n
  let w ← wordOf nm
  logInfo m!"{nm} : {w}"

end ProofLift


open ProofLift
def ours (n : Lean.Name) : Bool :=
  let s := n.toString
  s.startsWith "Imscribing" || s.startsWith "Millennium" || s.startsWith "IG"
#eval show Lean.Meta.MetaM Unit from do
  let env ← Lean.getEnv
  for (nm, ci) in env.constants.toList do
    if ours nm then
      match ci with
      | .thmInfo ti =>
          let w ← (try lift ti.value catch _ => pure "")
          if w != "" && w.length < 60000 then IO.println s!"{nm}\t⊢{w}⊣"
      | _ => pure ()
