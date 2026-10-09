/-
Copyright (c) 2024 Lando ⊗ ⊙perator. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

PARACONSISTENT KERNEL FORK — `reentry` command elaborator.

Syntax:   reentry def f : T := body
Semantics: the kernel computes v = lfp(F : Sixteen3 → Sixteen3) in the
information order le_i by Kleene iteration from sixteen3.none.  The body is
elaborated as a function of the single argument f; the declared type T is
preserved.  The computed lfp is stored as the constant's value (a ReentryVal);
whnf on the name returns it.

Monotonicity is enforced syntactically: the body may only use join_i, meet_i,
the sixteen3 constants, and the parameter f.  This guarantees a unique least
fixed point (Kleene's theorem) and termination in at most 16 steps.
-/

import Lean.Sixteen3

module

prelude

public section

namespace Lean.Elab.Command

open Lean Meta Elab TermElabM

/-- The sixteenth-three lattice operations the kernel exports. -/
opaque Lean.Sixteen3.join_i : Sixteen3 → Sixteen3 → Sixteen3
opaque Lean.Sixteen3.meet_i : Sixteen3 → Sixteen3 → Sixteen3

/-- Syntactic monotonicity check.  The body of a re-entry must be built only
from join_i, meet_i, the sixteen3 constants, and the parameter f. -/
inductive FInfo where
  | mk (occurrences : Nat) (allowed : Bool) (depth : Nat) : FInfo

def checkMonotone : Expr → FInfo
  | Expr.const c _ =>
      if c == ``Lean.Sixteen3.join_i ∨ c == ``Lean.Sixteen3.meet_i ∨
         c == ``Lean.Sixteen3.ofBelnap ∨ c == ``Lean.Sixteen3.none ∨
         c == ``Lean.Sixteen3.all then
        FInfo.mk 0 true 1
      else
        FInfo.mk 0 false 1
  | Expr.fvar f _ =>
      if f.isBound then FInfo.mk 1 true 1 else FInfo.mk 0 false 1
  | Expr.lam _ b _ =>
      let r := checkMonotone b
      FInfo.mk r.occurrences r.allowed r.depth + 1
  | Expr.app f a _ =>
      let rf := checkMonotone f
      let ra := checkMonotone a
      FInfo.mk (rf.occurrences + ra.occurrences) (rf.allowed && ra.allowed) (max rf.depth ra.depth) + 1
  | _ => FInfo.mk 0 false 1

/-- The elaborator of `reentry def f : T := body`. -/
builtin_elab_command "reentry" :
    TermDeclSyntax → CommandElabM Unit :=
  fun stx => do
    let (vis, attrs, _, name, lparams, sig, val) := stx.declBase
    let (binders, body) := sig.declBinderBody
    if binders.length != 1 then
      throwError "re-entry must bind exactly one parameter `f : Sixteen3`"
    let fBinder := binders[0]
    let fType   := fBinder.type
    let bodyType := fBinder.body
    -- The declared type of the constant is whatever follows the colon.
    let declType := sig.declType!
    -- Require sixteenth-three mode.
    let env ← getEnv
    if !env.holdsContradictions then
      throwError "re-entry `def f : T := body` is only allowed in paraconsistent / SIXTEEN_3 mode"
    -- Abstract over f to obtain F : Sixteen3 → Sixteen3.
    let F : Expr := Expr.lam fBinder.name fType bodyType
    -- Syntactic monotonicity check.
    let info := checkMonotone body
    if !info.allowed then
      throwError "re-entry body may only use join_i, meet_i, Sixteen3 constants, and the parameter f"
    if info.occurrences == 0 then
      throwError "re-entry body must mention the parameter f"
    -- Kleene iteration: v = none; repeat F v until v' == v.
    let mut v := Lean.Sixteen3.none
    let mut vExpr : Expr := `Lean.Sixteen3.none
    let mut it := 0
    let mut converged := false
    while it < 16 && !converged do
      let Fv := F.app vExpr
      let FvReduced ← reduce Fv
      vExpr := FvReduced
      -- Decode the resulting Sixteen3 literal into a kernel sixteen3.
      let hasN := FvReduced.getArg 0 |>.isTrue
      let hasT := FvReduced.getArg 1 |>.isTrue
      let hasF := FvReduced.getArg 2 |>.isTrue
      let hasB := FvReduced.getArg 3 |>.isTrue
      let v' := Lean.Sixteen3.mk hasN hasT hasF hasB
      if v' == v then
        converged := true
      else
        v := v'
        it := it + 1
    if !converged then
      throwError "re-entry lfp did not converge within 16 Kleene steps — monotonicity check may have failed"
    -- Build the kernel declaration.  The kernel stores v as the six3 payload.
    let decl := Declaration.reentryDecl ⟨name, lparams, declType, v⟩
    addDecl decl
    compileDecl decl

end Lean.Elab.Command
