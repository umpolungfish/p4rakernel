import Imscribing.ManuscriptSpine.QuestionsExtended
import Imscribing.MetaYonedaCollapse
import Imscribing.Millennium.A1A2CoptMacrocycle
import Imscribing.Millennium.AlchemicalHermeticUniverse
import Imscribing.Millennium.BSD
import Imscribing.Millennium.BSD_Complete_Witness
import Imscribing.Millennium.BSD_GateInhabitants
import Imscribing.Millennium.BSD_MathBridge
import Imscribing.Millennium.BSD_Resolution
import Imscribing.Millennium.BSD_Witness
import Imscribing.Millennium.BanachMeasure
import Imscribing.Millennium.Beal
import Imscribing.Millennium.BosonMassRatios
import Imscribing.Millennium.CKMFullDerivation
import Imscribing.Millennium.CMPLX_IMGN
import Imscribing.Millennium.CanonicalOrdinalFaithfulness
import Imscribing.Millennium.Chema
import Imscribing.Millennium.ClayCandidateProfile
import Imscribing.Millennium.ClayCandidateTuples
import Imscribing.Millennium.ClayCanonicalTuples
import Imscribing.Millennium.Clay_TransportedClosure
import Imscribing.Millennium.Clay_UnclosedResistance
import Imscribing.Millennium.Clay_WitnessedClosure
import Imscribing.Millennium.Collatz
import Imscribing.Millennium.CompositionRules
import Imscribing.Millennium.ContinuumMacrocycle
import Imscribing.Millennium.Cosmogeny
import Imscribing.Millennium.Cramer
import Imscribing.Millennium.CrystalBoot
import Imscribing.Millennium.DarkEnergy
import Imscribing.Millennium.DialetheicUniverse
import Imscribing.Millennium.DimensionfulEmission
import Imscribing.Millennium.Dixmier
import Imscribing.Millennium.DualLinkVessel
import Imscribing.Millennium.E8G2_Vessel
import Imscribing.Millennium.E8G2_Vessel_Witnesses
import Imscribing.Millennium.EilenbergGanea
import Imscribing.Millennium.Erdos.AntiRamseyOddCycles
import Imscribing.Millennium.Erdos.Base
import Imscribing.Millennium.Erdos.BinomialGCD
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
