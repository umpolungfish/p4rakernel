import Imscribing.PowerMath.ZariskiLipmanTheorem
import Imscribing.PrimitiveMismatch
import Imscribing.Primitives.AlchemicalIdentity
import Imscribing.Primitives.BSD_2adic
import Imscribing.Primitives.CLU
import Imscribing.Primitives.Catalog
import Imscribing.Primitives.Core
import Imscribing.Primitives.Crystal
import Imscribing.Primitives.EML
import Imscribing.Primitives.Imscription
import Imscribing.Primitives.Lattice
import Imscribing.Primitives.LinearOrder
import Imscribing.Primitives.OPN_2adic
import Imscribing.Primitives.SacredVessel
import Imscribing.Primitives.ScrollInvariant
import Imscribing.Primitives.TierCrossing
import Imscribing.Primitives.Types.PrimitiveTypeAdo
import Imscribing.Primitives.Types.PrimitiveTypeAge
import Imscribing.Primitives.Types.PrimitiveTypeAh
import Imscribing.Primitives.Types.PrimitiveTypeAir
import Imscribing.Primitives.Types.PrimitiveTypeAre
import Imscribing.Primitives.Types.PrimitiveTypeArray
import Imscribing.Primitives.Types.PrimitiveTypeAsh
import Imscribing.Primitives.Types.PrimitiveTypeAwe
import Imscribing.Primitives.Types.PrimitiveTypeBib
import Imscribing.Primitives.Types.PrimitiveTypeChurch
import Imscribing.Primitives.Types.PrimitiveTypeDead
import Imscribing.Primitives.Types.PrimitiveTypeEar
import Imscribing.Primitives.Types.PrimitiveTypeEat
import Imscribing.Primitives.Types.PrimitiveTypeEgg
import Imscribing.Primitives.Types.PrimitiveTypeErr
import Imscribing.Primitives.Types.PrimitiveTypeFee
import Imscribing.Primitives.Types.PrimitiveTypeGag
import Imscribing.Primitives.Types.PrimitiveTypeHaHa
import Imscribing.Primitives.Types.PrimitiveTypeHung
import Imscribing.Primitives.Types.PrimitiveTypeIan
import Imscribing.Primitives.Types.PrimitiveTypeIce
import Imscribing.Primitives.Types.PrimitiveTypeIf
import Imscribing.Primitives.Types.PrimitiveTypeJudge
import Imscribing.Primitives.Types.PrimitiveTypeKick
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
