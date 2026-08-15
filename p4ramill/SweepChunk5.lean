import Imscribing.Millennium.OPN_PsiGraph
import Imscribing.Millennium.OPN_Witness
import Imscribing.Millennium.OmegaCorrClosure
import Imscribing.Millennium.OracleDelphi
import Imscribing.Millennium.PMNSFullDerivation
import Imscribing.Millennium.ParadoxBoot
import Imscribing.Millennium.PerfectCuboid
import Imscribing.Millennium.PerfectCuboid.Bootstrap
import Imscribing.Millennium.PerfectCuboid.CaseC
import Imscribing.Millennium.PerfectCuboid.CaseC_Attempt
import Imscribing.Millennium.PerfectCuboid.DescentOperator
import Imscribing.Millennium.PerfectCuboid.DescentTheorem
import Imscribing.Millennium.PerfectCuboid.FactorizationLemma
import Imscribing.Millennium.PerfectCuboid.PerfectCuboidWitness
import Imscribing.Millennium.PerfectCuboid.PrerequisiteLemmasL5_L7
import Imscribing.Millennium.Pkg
import Imscribing.Millennium.PrimitiveBridge
import Imscribing.Millennium.PrimitiveConventionalBridge
import Imscribing.Millennium.PrimordialOoze
import Imscribing.Millennium.ProofModules.DistinctDistances
import Imscribing.Millennium.ProofModules.ErdosFuchs
import Imscribing.Millennium.ProofModules.FurstenbergCorrespondence
import Imscribing.Millennium.ProofModules.FurstenbergSarkozy
import Imscribing.Millennium.ProofModules.HopfPannwitz
import Imscribing.Millennium.ProofModules.HypergraphRamsey
import Imscribing.Millennium.ProofModules.LCMSieve
import Imscribing.Millennium.ProofModules.RamseyGap
import Imscribing.Millennium.ProofModules.RamseyLimit
import Imscribing.Millennium.ProofModules.SumFreeSets
import Imscribing.Millennium.ProofModules.SunflowerProofModule
import Imscribing.Millennium.ProofModules.TrianglePartition
import Imscribing.Millennium.ProofModules.VerifiedConjectures
import Imscribing.Millennium.ProtonElectronMass
import Imscribing.Millennium.PvsNP
import Imscribing.Millennium.PvsNP_Certificates
import Imscribing.Millennium.PvsNP_Structural
import Imscribing.Millennium.PvsNP_Witness
import Imscribing.Millennium.QGUnifiedBridge
import Imscribing.Millennium.RH
import Imscribing.Millennium.RH_GateInhabitants
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
