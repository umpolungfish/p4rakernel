import Imscribing.Primitives.Types.PrimitiveTypeLoll
import Imscribing.Primitives.Types.PrimitiveTypeMeasure
import Imscribing.Primitives.Types.PrimitiveTypeMime
import Imscribing.Primitives.Types.PrimitiveTypeMonad
import Imscribing.Primitives.Types.PrimitiveTypeNun
import Imscribing.Primitives.Types.PrimitiveTypeOak
import Imscribing.Primitives.Types.PrimitiveTypeOil
import Imscribing.Primitives.Types.PrimitiveTypeOn
import Imscribing.Primitives.Types.PrimitiveTypeOoze
import Imscribing.Primitives.Types.PrimitiveTypeOr
import Imscribing.Primitives.Types.PrimitiveTypeOut
import Imscribing.Primitives.Types.PrimitiveTypePeep
import Imscribing.Primitives.Types.PrimitiveTypeRoar
import Imscribing.Primitives.Types.PrimitiveTypeSo
import Imscribing.Primitives.Types.PrimitiveTypeSure
import Imscribing.Primitives.Types.PrimitiveTypeThey
import Imscribing.Primitives.Types.PrimitiveTypeThigh
import Imscribing.Primitives.Types.PrimitiveTypeTot
import Imscribing.Primitives.Types.PrimitiveTypeUp
import Imscribing.Primitives.Types.PrimitiveTypeVow
import Imscribing.Primitives.Types.PrimitiveTypeWoe
import Imscribing.Primitives.Types.PrimitiveTypeWool
import Imscribing.Primitives.Types.PrimitiveTypeYea
import Imscribing.Primitives.Types.PrimitiveTypeYew
import Imscribing.Primitives.Types.PrimitiveTypeZoo
import Imscribing.ProofTheory
import Imscribing.Quantum.ExcitedStates
import Imscribing.Quantum.FibonacciAnyon
import Imscribing.Quantum.FrobeniusDualPOVM
import Imscribing.Quantum.GateObstruction
import Imscribing.Quantum.GrammarPOVM
import Imscribing.Quantum.OVM
import Imscribing.Quantum.PeriodReadout
import Imscribing.Quantum.WindingLattice
import Imscribing.Quersitanus
import Imscribing.RotatOpOpcode
import Imscribing.Scratch.ProverScratch
import Imscribing.Scratch.ProverScratchB
import Imscribing.Seals
import Imscribing.SerpentRod
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
