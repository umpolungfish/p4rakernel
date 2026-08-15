import Imscribing.AFDMC_MBL_Cohomology
import Imscribing.AgentSelf
import Imscribing.Agricola
import Imscribing.Algebra
import Imscribing.ArsAnimaglyphica
import Imscribing.ArsCrossDomain
import Imscribing.ArsFungiglyphica
import Imscribing.AtHomeSanguineHomunculus
import Imscribing.AutopoieticConvergence_UPDATED
import Imscribing.AxiomD_Demotion
import Imscribing.B4FactorBootstrap
import Imscribing.Barriers
import Imscribing.Basic
import Imscribing.BasilValentine
import Imscribing.BooksOfJeu
import Imscribing.BootstrapSequence
import Imscribing.BotanicalWalkthrough
import Imscribing.BoundaryOperators
import Imscribing.BruceCodex.BooksOfJeu
import Imscribing.BruceCodex.UntitledText
import Imscribing.CL9NK_Chain
import Imscribing.CLINK
import Imscribing.CLINK_L9
import Imscribing.CLU744Bridge
import Imscribing.CatalogImmutability
import Imscribing.CirculatumMinus
import Imscribing.Classical.APIntersectingFamily
import Imscribing.Classical.BoseChowla
import Imscribing.Classical.DifferenceSetSyndetic
import Imscribing.Classical.ErdosLaxDivergence
import Imscribing.Classical.ErdosProblem16
import Imscribing.Classical.ErdosPropertyP
import Imscribing.Classical.ErdosStrausDecomposition
import Imscribing.Classical.ErdosTuranBound
import Imscribing.Classical.ErdosTuranReduction
import Imscribing.Classical.ErdosTuranSmallC
import Imscribing.Classical.HajnalSpecker
import Imscribing.Classical.HeckeLandau
import Imscribing.Classical.InfiniteSidon
import Imscribing.Classical.MatchingSDR
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
