import Imscribing.PowerMath.AndrewsCurtisTheorem
import Imscribing.PowerMath.ArtinSTheoremOnPrimitiveRoots
import Imscribing.PowerMath.BarnetteSTheorem
import Imscribing.PowerMath.BerryTaborTheorem
import Imscribing.PowerMath.BorelTheorem
import Imscribing.PowerMath.BrennanTheorem
import Imscribing.PowerMath.BrocardSTheorem
import Imscribing.PowerMath.CasasAlveroTheorem
import Imscribing.PowerMath.DadeSTheorem
import Imscribing.PowerMath.EilenbergGaneaTheorem
import Imscribing.PowerMath.FarrellJonesTheorem
import Imscribing.PowerMath.FermatNumberCompositenessTheorem
import Imscribing.PowerMath.FugledeSTheorem
import Imscribing.PowerMath.HadamardSMaximalDeterminantTheorem
import Imscribing.PowerMath.HadamardTheorem
import Imscribing.PowerMath.HerzogSchNheimTheorem
import Imscribing.PowerMath.HilbertArnoldTheorem
import Imscribing.PowerMath.InscribedSquareTheoremToeplitzTheorem
import Imscribing.PowerMath.InvariantSubspaceTheorem
import Imscribing.PowerMath.JacobsonSTheorem
import Imscribing.PowerMath.KTheTheorem
import Imscribing.PowerMath.KaplanskySTheorems
import Imscribing.PowerMath.LegendreSTheorem
import Imscribing.PowerMath.LehmerSTheorem
import Imscribing.PowerMath.LonelyRunnerTheorem
import Imscribing.PowerMath.MargulisTheorem
import Imscribing.PowerMath.MckayTheorem
import Imscribing.PowerMath.MlcTheorem
import Imscribing.PowerMath.NoThreeInLineTheorem
import Imscribing.PowerMath.NovikovTheorem
import Imscribing.PowerMath.RokhlinSMultipleMixingTheorem
import Imscribing.PowerMath.RotaSBasisTheorem
import Imscribing.PowerMath.SendovSTheorem
import Imscribing.PowerMath.SerreSTheoremIi
import Imscribing.PowerMath.ShavianDefs
import Imscribing.PowerMath.SmoothFourDimensionalPoincarTheorem
import Imscribing.PowerMath.SunflowerTheorem
import Imscribing.PowerMath.The1323Theorem
import Imscribing.PowerMath.UnionClosedSetsTheorem
import Imscribing.PowerMath.WeinsteinTheorem
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
