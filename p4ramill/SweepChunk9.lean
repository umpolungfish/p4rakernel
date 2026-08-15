import Imscribing.Ob3ects.tomographic_injection_scaffold
import Imscribing.Ob3ects.unproven_status_lacking_exact_frobenius_closure_scaffold
import Imscribing.Ob3ects.weyl_heisenberg_orbit_generation_for_the_d_12_br_scaffold
import Imscribing.Ob3ects.zauner_conjecture_bifurcation_splitting_general_scaffold
import Imscribing.Ob3ects.zauner_fiducial_scaffold
import Imscribing.ObjWitnessCosmos
import Imscribing.ObjWitnessVessel
import Imscribing.OddRingIndex
import Imscribing.Paraconsistent.B4Measurement
import Imscribing.Paraconsistent.Belnap
import Imscribing.Paraconsistent.BelnapAgreement
import Imscribing.Paraconsistent.BelnapCategory
import Imscribing.Paraconsistent.BelnapLL
import Imscribing.Paraconsistent.BelnapSplitFuse
import Imscribing.Paraconsistent.BelnapTemporal
import Imscribing.Paraconsistent.Betting
import Imscribing.Paraconsistent.BlackHoleBelnap
import Imscribing.Paraconsistent.ConsciousKernel
import Imscribing.Paraconsistent.CosmologyBelnap
import Imscribing.Paraconsistent.CrystalScheduler
import Imscribing.Paraconsistent.DialetheicAlignment
import Imscribing.Paraconsistent.ElectroweakBelnap
import Imscribing.Paraconsistent.ExoticHadronBelnap
import Imscribing.Paraconsistent.FDEAsymptotic
import Imscribing.Paraconsistent.FTLTravel
import Imscribing.Paraconsistent.FlavorMixing
import Imscribing.Paraconsistent.FrobeniusFiltration
import Imscribing.Paraconsistent.FrobeniusIso
import Imscribing.Paraconsistent.GaugeBosonBelnap
import Imscribing.Paraconsistent.GeneralRelativity
import Imscribing.Paraconsistent.GravitationalWaves
import Imscribing.Paraconsistent.GravityStandardModel
import Imscribing.Paraconsistent.HadronBelnap
import Imscribing.Paraconsistent.HiggsMechanism
import Imscribing.Paraconsistent.Init
import Imscribing.Paraconsistent.Kernel
import Imscribing.Paraconsistent.LeptonBelnap
import Imscribing.Paraconsistent.Main
import Imscribing.Paraconsistent.MajoranaFixed
import Imscribing.Paraconsistent.MultiAgentBelnap
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
