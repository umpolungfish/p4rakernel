import Imscribing.Frobenius
/-!
The nest: drop the machine checker into the auditor whose law it certified.

FIXED_POINT_NESTING_RULE says the class is decidable before the nest — A closes
inside B exactly when A is a fixed point of B's action, and one-shots when it
already sits at that fixed point. Here A is the Lean proof of μ∘δ = id and B is
the close condition. A states what B computes, so A should be fixed, so the nest
should close in one shot with nothing to iterate.
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
#lift Imscribing.Frobenius.mu_delta_A_id
#lift Imscribing.Frobenius.mu_delta_B_id
#lift Imscribing.Frobenius.mu_delta_D_id
