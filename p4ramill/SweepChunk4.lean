import Imscribing.Millennium.GrammarUniversalDualFrameSICPOVM
import Imscribing.Millennium.GravitationalCoupling
import Imscribing.Millennium.GrothendieckA
import Imscribing.Millennium.HadwigerNelson
import Imscribing.Millennium.Hodge
import Imscribing.Millennium.Hodge_AlgebraicCycleConstruction
import Imscribing.Millennium.Hodge_Descent
import Imscribing.Millennium.Hodge_GateInhabitants
import Imscribing.Millennium.Hodge_Grammar
import Imscribing.Millennium.Hodge_KernelCrossing
import Imscribing.Millennium.Hodge_Mathematical_Witness
import Imscribing.Millennium.Hodge_RegulatorSurjectivity
import Imscribing.Millennium.Hodge_ThresholdCrossing
import Imscribing.Millennium.Hodge_Witness
import Imscribing.Millennium.HolonomyWinding
import Imscribing.Millennium.HornTorusEmission
import Imscribing.Millennium.HornTorusModularForm
import Imscribing.Millennium.HubbleConstant
import Imscribing.Millennium.IGThresholdAnalysis
import Imscribing.Millennium.ImaginaryNumbers
import Imscribing.Millennium.InflationarySlowRoll
import Imscribing.Millennium.LeeYang_Xi_Product_Construction
import Imscribing.Millennium.Lefschetz11
import Imscribing.Millennium.Lefschetz11_Grammar
import Imscribing.Millennium.LeptonMassRatios
import Imscribing.Millennium.LonelyRunner
import Imscribing.Millennium.Macrocycle107_1135_713
import Imscribing.Millennium.MacrocyclicClosure
import Imscribing.Millennium.MajoranaPhases
import Imscribing.Millennium.Manuscript_ZFCt
import Imscribing.Millennium.Master_Witness
import Imscribing.Millennium.MathProof
import Imscribing.Millennium.NS
import Imscribing.Millennium.NS_CriticalBound
import Imscribing.Millennium.NS_Mathematical_Witness
import Imscribing.Millennium.NS_Resolution
import Imscribing.Millennium.NS_Seige
import Imscribing.Millennium.NS_Witness
import Imscribing.Millennium.NS_ZFCt_Bridge
import Imscribing.Millennium.OPN
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
