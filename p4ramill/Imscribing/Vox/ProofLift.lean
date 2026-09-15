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


/-- The independent oracle. `#print axioms` is what a reviewer would run, and it
knows nothing about the twelve. A sweep that only reports its own verdict cannot
be checked; a sweep that reports both can, and every disagreement between them is
a finding in one direction or the other. -/
def assumedAxioms (n : Name) : MetaM (List Name) := do
  let env ← getEnv
  let (_, st) := ((Lean.CollectAxioms.collect n).run env).run {}
  return st.axioms.toList.filter (fun a => !foundational.contains a)

/-- One line per declaration this corpus states: name, word, and the axiom
oracle's own answer. Vox verdicts the word; nothing here verdicts anything, so
there is exactly one implementation of the verdict and it is not in Lean. -/
def sweepAll (maxLen : Nat := 4000000) : MetaM Unit := do
  let env ← getEnv
  for (nm, ci) in env.constants.toList do
    if ourDecl nm then
      match ci with
      | .thmInfo ti =>
          let w ← (try lift ti.value catch _ => pure "")
          if w == "" then
            -- A declaration the lift could not read is REPORTED, never dropped in
            -- silence: an absent name would otherwise be indistinguishable from a
            -- declaration that does not exist.
            IO.println s!"#skip\t{nm}\tlift-failed\t0"
          else if w.length ≥ maxLen then
            -- The cap discards exactly the largest proofs, which are the ones most
            -- worth reading. Say so, with the length, so the cap can be raised on
            -- evidence rather than guessed at.
            IO.println s!"#skip\t{nm}\tmaxlen\t{w.length}"
          else
            let ax ← assumedAxioms nm
            let axs := if ax.isEmpty then "clean" else String.intercalate "," (ax.map toString)
            IO.println s!"{nm}\t⊢{w}⊣\t{axs}"
      | _ => pure ()

/-- The sweep that actually runs. Importing the whole corpus into one
environment is blocked by name collisions between modules, and it does not need
to be done: the lift is per declaration, so lifting one module at a time means
nothing ever has to coexist and the collisions stop mattering. `prefix` is the
namespace the module declares into. -/
def sweepModule (prefix_ : String) (maxLen : Nat := 4000000) : MetaM Unit := do
  let env ← getEnv
  for (nm, ci) in env.constants.toList do
    let s := nm.toString
    if s.startsWith prefix_ then
      match ci with
      | .thmInfo ti =>
          let w ← (try lift ti.value catch _ => pure "")
          if w == "" then
            -- A declaration the lift could not read is REPORTED, never dropped in
            -- silence: an absent name would otherwise be indistinguishable from a
            -- declaration that does not exist.
            IO.println s!"#skip\t{nm}\tlift-failed\t0"
          else if w.length ≥ maxLen then
            -- The cap discards exactly the largest proofs, which are the ones most
            -- worth reading. Say so, with the length, so the cap can be raised on
            -- evidence rather than guessed at.
            IO.println s!"#skip\t{nm}\tmaxlen\t{w.length}"
          else
            let ax ← assumedAxioms nm
            let axs := if ax.isEmpty then "clean" else String.intercalate "," (ax.map toString)
            IO.println s!"{nm}\t⊢{w}⊣\t{axs}"
      | _ => pure ()

end ProofLift
