import Imscribing.Millennium.Erdos.Problems.Problem0041
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

/-- The three axioms Lean's own foundation rests on. Every classical proof in
Mathlib cites them, so counting them as undischarged makes every theorem read B
and the verdict says nothing. -/
def foundational : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- A name this corpus declares, as opposed to one it imports. -/
def ourDecl (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "Imscribing" || s.startsWith "Millennium" || s.startsWith "IG"


/-- A `axiom` declaration of this corpus: asserted, never derived.

`sorryAx` is not the only way to leave a claim open — it is only the way that
announces itself. A declared axiom is an ordinary constant in the term, so it
lifted to ◻, a commit, and read exactly like a proved lemma. That is the same
failure as matching the spelling instead of the axiom, in the other direction:
narrowing to `sorryAx` left the deliberate assertions invisible.

An axiom opens what nothing closes, so it lifts where a sorry lifts. -/
def isAssumed (n : Name) : MetaM Bool := do
  if foundational.contains n then return false
  let env ← getEnv
  match env.find? n with
  | some (.axiomInfo _) => return true
  | some _ =>
      -- Transitively, the way `#print axioms` is. A theorem whose body is one
      -- citation of a theorem that rests on an axiom lifted to a bare ◻ and read
      -- N — closed, because the lift stopped at the constant and never saw what
      -- held it up. Depending on an assertion is resting on it.
      --
      -- Only for names this corpus declares. Collecting axioms walks the whole
      -- dependency graph of a constant, and doing that for every Mathlib name in
      -- every term does not finish. A Mathlib constant was elaborated before this
      -- corpus existed, so it cannot rest on a corpus axiom, and the walk would
      -- only ever return the foundational three.
      if !(ourDecl n) then return false
      let (_, st) := ((Lean.CollectAxioms.collect n).run env).run {}
      return st.axioms.any (fun a => !foundational.contains a)
  | none => return false

partial def lift (e : Expr) : MetaM String := do
  match e with
  | .bvar _ | .fvar _ | .mvar _ => return "⊙"
  | .sort _ => return ""
  | .lit _ => return "⊙"
  | .mdata _ b => lift b
  | .proj _ _ b => return (← lift b) ++ "⋈"
  | .const n _ =>
      if isSorry n then return "∈"            -- opens, never rejoins
      else if (← isAssumed n) then return "∈" -- so does an asserted axiom
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
          else if (← isAssumed n) then return "∈"
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

#eval show Lean.Meta.MetaM Unit from do
  let env ← Lean.getEnv
  for (nm, ci) in env.constants.toList do
    let s := nm.toString
    if s.startsWith "Millennium.ErdosProblems" || s.startsWith "erdos_problem" then
      match ci with
      | .thmInfo ti =>
          let w ← (try lift ti.value catch _ => pure "")
          if w != "" then IO.println s!"{nm}	⊢{w}⊣"
      | _ => pure ()
