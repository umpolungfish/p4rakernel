import Imscribing.IGFunctor
import Imscribing.TimeWithinTheStone
import Imscribing.Paraconsistent.BelnapSplitFuse
set_option linter.style.setOption false
set_option linter.style.whitespace false
set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.cdot false
set_option linter.style.emptyLine false
set_option linter.style.dollarSyntax false
set_option linter.style.lambdaSyntax false
set_option linter.style.refine false
set_option linter.style.show false
set_option linter.style.cases false
set_option linter.style.induction false
set_option linter.style.nameCheck false
set_option linter.style.docString false
set_option linter.style.header false
set_option linter.style.missingEnd false
set_option linter.style.openClassical false
set_option linter.style.nativeDecide false
set_option linter.style.admit false
namespace ObjWitnessVessel
open Imscribing Imscribing.Primitives Imscribing.Frobenius Imscribing.TimeWithinTheStone
def board (p : List Belnap) : List (Belnap × Belnap) := p.map fsplit
def readback (q : List (Belnap × Belnap)) : List Belnap := q.map ffuse
theorem vessel_roundtrip (p : List Belnap) : readback (board p) = p := by
  induction p with
  | nil => rfl
  | cons a t ih =>
    simp only [board, readback, List.map_cons] at ih ⊢
    rw [split_fuse_id, ih]
def obj_payload : List Belnap := [Belnap.B, Belnap.F, Belnap.T]
def obj_s0 : Imscription := { dim := Dimensionality.dead, top := Topology.mime, rel := Relational.ear, pol := Polarity.or', fid := Fidelity.age, kin := KineticChar.on, gran := Granularity.ice, gram := Grammar.gag, crit := Criticality.err, chir := Chirality.wool, stoi := Stoichiometry.so, prot := Protection.awe }
theorem obj_is_valid_ob3ect : igFrobeniusAlg.mul obj_s0 obj_s0 = obj_s0 :=
  igFrobAlg_self_fusion obj_s0
def obj_tier : OuroboricityTier := TierFunctor.obj obj_s0
theorem obj_witness_vessel :
  readback (board obj_payload) = obj_payload
  ∧ igFrobeniusAlg.mul obj_s0 obj_s0 = obj_s0 :=
  ⟨vessel_roundtrip obj_payload, obj_is_valid_ob3ect⟩
end ObjWitnessVessel
