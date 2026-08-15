import Imscribing.Millennium.RH_LeeYang_Bridge
import Imscribing.Millennium.RH_Mathematical_Witness
import Imscribing.Millennium.RH_Witness
import Imscribing.Millennium.RH_ZFCt_Bridge
import Imscribing.Millennium.Rebis
import Imscribing.Millennium.RiemannSIC
import Imscribing.Millennium.RiemannSIC_FullProof
import Imscribing.Millennium.Ring2048_Bridge
import Imscribing.Millennium.RohoncCodexBraiding
import Imscribing.Millennium.RohoncCodexJarlskog
import Imscribing.Millennium.SICFlavorPartition
import Imscribing.Millennium.SIC_D12_ComputableCyclotomic
import Imscribing.Millennium.SIC_D12_Embedding
import Imscribing.Millennium.SIC_D12_Equiangularity
import Imscribing.Millennium.SIC_D12_ExistenceRing
import Imscribing.Millennium.SIC_D12_Field288Test
import Imscribing.Millennium.SIC_D12_Field48Test
import Imscribing.Millennium.SIC_D12_MagnitudeClasses
import Imscribing.Millennium.SIC_D12_Norm
import Imscribing.Millennium.SIC_D12_NumberField
import Imscribing.Millennium.SIC_D12_QuadraticTower
import Imscribing.Millennium.SIC_D12_RayCubic
import Imscribing.Millennium.SIC_D12_RayCubicNF
import Imscribing.Millennium.SIC_D12_RayTower
import Imscribing.Millennium.SIC_D12_SymmetricModuli
import Imscribing.Millennium.SIC_D12_WitnessVessel
import Imscribing.Millennium.SIC_D16_Moduli
import Imscribing.Millennium.SIC_D2048_A0Stratum
import Imscribing.Millennium.SIC_D2048_Moduli
import Imscribing.Millennium.SIC_D2048_Unconditional
import Imscribing.Millennium.SIC_D20_Moduli
import Imscribing.Millennium.SIC_Moduli_Report
import Imscribing.Millennium.SIC_POVM_DualLinkClosure
import Imscribing.Millennium.SIC_POVM_Functor
import Imscribing.Millennium.SIC_POVM_ParityGate
import Imscribing.Millennium.SIC_POVM_Stark
import Imscribing.Millennium.SIC_POVM_Stark_Ob3ect
import Imscribing.Millennium.SIC_StarkUnit
import Imscribing.Millennium.SMUGTConsummation
import Imscribing.Millennium.SacredConvergence
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
