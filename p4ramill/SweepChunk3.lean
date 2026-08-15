import Imscribing.Millennium.Erdos.ChromaticOddCycle
import Imscribing.Millennium.Erdos.DifferenceSets
import Imscribing.Millennium.Erdos.ErdosKacInterval
import Imscribing.Millennium.Erdos.ErdosTuranAP
import Imscribing.Millennium.Erdos.MonochromaticOddCycle
import Imscribing.Millennium.Erdos.PolynomAsymptotics
import Imscribing.Millennium.Erdos.PomeranceSDR
import Imscribing.Millennium.Erdos.Problems.Problem0003
import Imscribing.Millennium.Erdos.RamseyAsymptotics
import Imscribing.Millennium.Erdos.RatioSetSharp
import Imscribing.Millennium.Erdos.SchutteTClose
import Imscribing.Millennium.Erdos.SchutteTournament
import Imscribing.Millennium.Erdos.SidonCounting
import Imscribing.Millennium.Erdos.SquarefreePlusPowerOfTwo
import Imscribing.Millennium.Erdos.SquarefreePlusPowerOfTwoClose
import Imscribing.Millennium.Erdos.StrausGreedyFamily
import Imscribing.Millennium.Erdos.SubgroupOrders
import Imscribing.Millennium.Erdos.SumsetAvoidingAP
import Imscribing.Millennium.Erdos.TrianglePartition
import Imscribing.Millennium.Erdos.UnitDistance
import Imscribing.Millennium.ErdosFormalize
import Imscribing.Millennium.ErdosFormalize2
import Imscribing.Millennium.ErdosFormalize3
import Imscribing.Millennium.ErdosProblems
import Imscribing.Millennium.FieldTheoreticMacrocycle
import Imscribing.Millennium.FineStructureConstant
import Imscribing.Millennium.FrobeniusStructure
import Imscribing.Millennium.FrobeniusUnification
import Imscribing.Millennium.GapCompletion
import Imscribing.Millennium.GeneralizedPipeline
import Imscribing.Millennium.GodelCompleteSentence
import Imscribing.Millennium.GodelCompleteUniverse
import Imscribing.Millennium.GodelCompletion
import Imscribing.Millennium.GodelResolvedFinal
import Imscribing.Millennium.Goldbach
import Imscribing.Millennium.GoldbachABC
import Imscribing.Millennium.GrammarBridge
import Imscribing.Millennium.GrammarMetricDerivation
import Imscribing.Millennium.GrammarSICPOVM_ZaunerBridge
import Imscribing.Millennium.GrammarStructuralAnalysis
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
