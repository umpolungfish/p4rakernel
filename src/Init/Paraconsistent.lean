/-
Copyright (c) 2024 Lando ⊗ ⊙perator. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Lando ⊗ ⊙perator

PARACONSISTENT KERNEL FORK — User-facing module

This module provides the user interface for the paraconsistent Lean kernel,
where the principle of explosion (ex falso quodlibet) is disabled.

Usage:
  import Init.Paraconsistent
  open Paraconsistent

  enable_paraconsistent    -- toggles the *elaboration environment*, not just a banner
  -- False.elim / False.rec / absurd on `False` now rejected by the kernel
  -- for every declaration elaborated from here on in this file.
  disable_paraconsistent   -- toggle back to ordinary ex falso

The kernel rejects, while paraconsistent mode is on:
  - `False.elim` (False.rec) for empty inductive predicates
  - `False.casesOn` for pattern matching on False
  - `absurd` (which relies on False.rec)

This enables dialetheic reasoning where both a proposition and its
negation can be held without everything becoming provable.
-/
import Lean

namespace Paraconsistent

open Lean Elab Command

/--
Activate paraconsistent mode on the current (elaboration) environment: marks
the environment via `Lean.Environment.markParaconsistent`, so subsequent
declarations are kernel-checked with `paraconsistent = true` and
`src/kernel/type_checker.cpp`'s `infer_constant` rejects recursors on empty
`Prop` inductives. A real toggle, not a banner — call `disable_paraconsistent`
to switch back.
-/
elab "enable_paraconsistent" : command => do
  modifyEnv Lean.Environment.markParaconsistent
  logInfo "[Paraconsistent] Kernel mode activated — principle of explosion disabled."

/-- Deactivate paraconsistent mode: restores ordinary ex falso for declarations elaborated after this point. -/
elab "disable_paraconsistent" : command => do
  modifyEnv Lean.Environment.unmarkParaconsistent
  logInfo "[Paraconsistent] Kernel mode deactivated — principle of explosion restored."

/-- Report whether the current environment is in paraconsistent mode. -/
elab "#is_paraconsistent" : command => do
  let env ← getEnv
  logInfo s!"paraconsistent = {env.isParaconsistent}"

/--
The Belnap four-valued logic type for paraconsistent reasoning.
- `N` : Neither (not true, not false) — underdetermined
- `T` : True (true, not false)
- `F` : False (not true, false)
- `B` : Both (true and false) — a dialetheia
-/
inductive Belnap : Type where
  | N | T | F | B
  deriving DecidableEq, Repr, Inhabited

namespace Belnap

/-- Conjunction in Belnap logic. -/
def band (a b : Belnap) : Belnap :=
  match a, b with
  | .F, _ | _, .F => .F
  | .N, _ | _, .N => .N
  | .B, _ | _, .B => .B
  | .T, .T => .T

/-- Disjunction in Belnap logic. -/
def bor (a b : Belnap) : Belnap :=
  match a, b with
  | .T, _ | _, .T => .T
  | .B, _ | _, .B => .B
  | .N, _ | _, .N => .N
  | .F, .F => .F

/-- Negation in Belnap logic. -/
def bnot : Belnap → Belnap
  | .N => .N
  | .T => .F
  | .F => .T
  | .B => .B

/-- Implication in Belnap logic: a → b is (¬a) ∨ b -/
def bimply (a b : Belnap) : Belnap := bor (bnot a) b

/-- A dialetheia is a true contradiction: both true and false. -/
def dialetheia : Belnap := .B

/-- In paraconsistent logic, from a dialetheia not everything follows.
Example: B ∧ ¬B does NOT entail arbitrary Q. -/
theorem explosion_blocked : ¬ (∀ (P : Belnap), band .B (bnot .B) = P) := by
  intro h
  exact absurd (h .F) (by decide)

end Belnap

/--
Paraconsistent natural deduction style.

In paraconsistent logic, the rule of explosion (ex falso) is rejected:
  ¬(∀ (P : Prop), False → P)

Instead, contradictions are handled using Belnap-style four-valued semantics,
where a proposition can be true, false, both, or neither.
-/
def ParaconsistentLogic : Type := Unit

end Paraconsistent

-- Run this file directly with `lean --run` to test the paraconsistent module.
-- `main` is defined per-file; no top-level main here to avoid import conflicts.
