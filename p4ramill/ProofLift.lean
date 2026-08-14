import Mathlib
/-!
# ProofLift — a proof term is a control-flow graph, so Vox can audit it.

A Lean proof is a term, a term is a DAG, and the close condition Vox already
enforces on machine code is the same one a proof either meets or does not:
μ∘δ = id over a TRANSFORMED object — split, work, fuse. A case analysis IS a
fork; the branches rejoining on one goal IS the fuse; and a `sorry` is a fork
whose arm never comes back.

So the twelve read on a proof term as:

    ⊢  entry            ⊣  the closing term
    ∈  a recursor/match opens the case split
    ∋  its branches rejoin on one goal
    ⊤  the first arm            ⊥  a later arm
    ⋈  application — composition
    ⊙  a bound variable — identity, self-reference
    ◻  a `let`/`have` — irreversible fixation
    ≻  Eq.mpr / rewriting forward     ≺  Eq.symm / backward
    ⊞  a paradox HELD

`sorryAx` emits ∈ and nothing to pair it: the claim that was never rejoined.
That is not a metaphor for the verdict, it is the verdict — an open fork reads B.
-/
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

-- ── the demonstration ────────────────────────────────────────────────────────
section Demo
open ProofLift

theorem closed_trivial (p : Prop) (h : p) : p := h

theorem closed_fork (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

theorem open_fork (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => sorry

theorem all_sorry (p : Prop) : p := by sorry

#lift closed_trivial
#lift closed_fork
#lift open_fork
#lift all_sorry
end Demo

-- Real theorems, not toys.
section Real
open ProofLift
#lift Nat.succ_ne_zero
#lift Nat.le_of_lt_succ
#lift List.length_append
#lift Nat.strongRecOn
end Real
