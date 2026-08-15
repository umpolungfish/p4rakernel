import Imscribing.Millennium.SemanticBranchVerifier
import Imscribing.Millennium.SevenFortyFourDecomposition
import Imscribing.Millennium.SpiderMachine
import Imscribing.Millennium.StandardModelFromGrammar
import Imscribing.Millennium.StrongCPClosure
import Imscribing.Millennium.Suffering
import Imscribing.Millennium.SumsetImprovedBounds
import Imscribing.Millennium.SumsetNo3AP
import Imscribing.Millennium.TetractysInit
import Imscribing.Millennium.ThresholdFrobenius
import Imscribing.Millennium.Thresholds
import Imscribing.Millennium.TwinPrime
import Imscribing.Millennium.UnificationConvergence
import Imscribing.Millennium.UnifiedForcing
import Imscribing.Millennium.UniverseRulesets
import Imscribing.Millennium.Unsolved
import Imscribing.Millennium.VAE_Vita_ManuscriptSpine
import Imscribing.Millennium.VAE_Vita_Port
import Imscribing.Millennium.VAE_Vita_SIC_POVM_Bridge
import Imscribing.Millennium.VAE_Vita_Unify
import Imscribing.Millennium.VoidConsensus
import Imscribing.Millennium.WorldReligions
import Imscribing.Millennium.WormwoodRevelation
import Imscribing.Millennium.YM
import Imscribing.Millennium.YM_Closure
import Imscribing.Millennium.YM_GateInhabitants
import Imscribing.Millennium.YM_Mathematical_Witness
import Imscribing.Millennium.YM_Witness
import Imscribing.Millennium.YM_ZFCt_Bridge
import Imscribing.Millennium.Z7StructureConstants
import Imscribing.Millennium.ZFCt_Unified_Bridge
import Imscribing.Millennium.ZaunerEmbeddingEquivalence
import Imscribing.Millennium.ZaunerTransportMap
import Imscribing.Millennium.ZaunerUnitaryConstruction
import Imscribing.Millennium.Zosimos_Stilling
import Imscribing.Millennium.truth
import Imscribing.MoDoT.ManuscriptSpine
import Imscribing.MomonadOS
import Imscribing.MomonadOS.AutopoieticConvergence
import Imscribing.MomonadOS.SheafEnrichedFrobenius
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
