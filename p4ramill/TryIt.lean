import Imscribing.Millennium.Erdos.Problems.Problem0003
/-!
Pick theorems whose verdict should SAY something, not merely confirm.

Four shapes worth separating:
  - a theorem whose whole content is a case analysis (expect T)
  - a theorem proved by `decide` (a decision procedure: does it fork?)
  - a theorem proved by `rfl` or a single rewrite (expect N)
  - the repaired Erdos statements, both the closed one and the open one
-/
open Lean Meta Elab

namespace ProofLift

def isSplitter (n : Name) : Bool :=
  let s := n.toString
  s.endsWith ".casesOn" || s.endsWith ".rec" || s.endsWith ".recOn"
    || s.endsWith ".elim" || s.endsWith ".brecOn" || s == "Or.elim"
    || s == "dite" || s == "ite" || (s.splitOn "match_").length > 1

/-- The axiom of unproved assertion, and ONLY it.

This was a substring test on the name, which is wrong in a way the corpus itself
exposed: a module reasoning ABOUT undischarged claims declares `sorryDepth`, a
function counting them, and `ym_has_stacked_not_parallel_sorries`, a theorem
comparing them. Both are fully proved. Both contain the substring, so both lifted
to an unpaired fork and read B. Eight false positives, every one in the one module
whose subject is the thing being detected. Match the axiom, not the spelling. -/
def isSorry (n : Name) : Bool := n == ``sorryAx

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
#lift Millennium.ErdosProblems.three_ap_of_not_threeAPFree
#lift Millennium.ErdosProblems.erdos_problem_3_k3
#lift Millennium.ErdosProblems.erdos_problem_3
#lift Millennium.ErdosProblems.ErdosTuran.dense_has_3ap
#lift Millennium.ErdosProblems.ErdosTuran.primes_reciprocal_diverges
#lift Nat.sub_add_cancel
#lift Nat.le_antisymm
#lift Nat.lt_irrefl
#lift List.reverse_reverse
#lift Nat.add_comm
