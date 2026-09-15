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
