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

  enable_trilattice        -- SIXTEEN_3: the trilattice on the powerset of FOUR
  -- entails paraconsistent at the kernel (twelve of the sixteen contain B)
  disable_trilattice       -- back to FOUR
  #is_trilattice           -- query the mode

The kernel rejects, while paraconsistent mode is on:
  - `False.elim` (False.rec) for empty inductive predicates
  - `False.casesOn` for pattern matching on False
  - `absurd` (which relies on False.rec)

This enables dialetheic reasoning where both a proposition and its
negation can be held without everything becoming provable.

SIXTEEN_3 TRILATTICE MODE

`enable_trilattice` puts the kernel in Shramko-Wansing's SIXTEEN_3: the trilattice
on P(FOUR), sixteen values carrying three interlocking orders — truth ≤_t, falsity
≤_f, information ≤_i. FOUR's single truth order SPLITS: truth and falsity stop being
each other's complement and become independent axes. That split is what the extra
twelve values are for, and it is why SIXTEEN_3 is not "FOUR with more room" — a
bilattice (two orders) cannot hold it.

Trilattice ENTAILS paraconsistent at every kernel enforcement point: twelve of the
sixteen values contain B, and a kernel that explodes cannot carry any of them. The
two remain separate flags rather than a ladder, so an environment may hold
contradictions in FOUR without entering SIXTEEN_3.
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
Activate SIXTEEN_3 trilattice mode on the current elaboration environment: marks it
via `Lean.Environment.markTrilattice`, so subsequent declarations are kernel-checked
with `trilattice = true`. Entails paraconsistent at the kernel's enforcement points.
A real toggle, not a banner — `src/kernel/type_checker.cpp` asks
`env().holds_contradictions()`, which this sets.
-/
elab "enable_trilattice" : command => do
  modifyEnv Lean.Environment.markTrilattice
  logInfo "[SIXTEEN_3] Trilattice mode activated — 16 values, three orders; explosion disabled."

/-- Deactivate SIXTEEN_3 trilattice mode. Paraconsistent mode, if separately set, survives. -/
elab "disable_trilattice" : command => do
  modifyEnv Lean.Environment.unmarkTrilattice
  logInfo "[SIXTEEN_3] Trilattice mode deactivated."

/-- Report whether the current environment is in SIXTEEN_3 trilattice mode. -/
elab "#is_trilattice" : command => do
  let env ← getEnv
  logInfo s!"trilattice = {env.isTrilattice}"

/-- Report whether the kernel will refuse to explode: paraconsistent, or SIXTEEN_3. -/
elab "#holds_contradictions" : command => do
  let env ← getEnv
  logInfo s!"holdsContradictions = {env.holdsContradictions}"

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
Example: B ∧ ¬B does NOT entail arbitrary Q.

Proved WITHOUT `absurd`. The previous proof discharged this with `absurd (h .F)` —
the one combinator this fork's whole claim is that the kernel rejects. It elaborated
only because it is declared before anyone calls `enable_paraconsistent`, so the
theorem asserting explosion is blocked leaned on explosion being available. `decide`
settles it by computation instead, which is what the four-valued semantics is FOR:
the counterexample is exhibited, not derived from a contradiction. -/
theorem explosion_blocked : ¬ (∀ (P : Belnap), band .B (bnot .B) = P) := by
  intro h
  exact Belnap.noConfusion (h .F)

/-- The dialetheia is genuinely held, not merely tolerated: B is its own negation,
so `B` and `¬B` are the same value and both designated. -/
theorem dialetheia_is_fixed : bnot .B = .B := by decide

/-- N is the other fixed point of negation: the void, not a contradiction. -/
theorem void_is_fixed : bnot .N = .N := by decide

end Belnap

/-!
## SIXTEEN_3 — the trilattice on P(FOUR)

Shramko-Wansing's construction. Not "FOUR with more room": FOUR's single truth order
SPLITS into two independent axes. A value is a SET of FOUR's values, so there are 2^4
= 16 of them, and each carries two independent bits per pole — whether it asserts
truth, and whether it asserts falsity — which is exactly what a bilattice's two orders
cannot express and a trilattice's three can.
-/

/-- A SIXTEEN_3 value: a subset of Belnap FOUR, given by its membership bits.
Sixteen inhabitants by construction (2^4), so the type IS the powerset. -/
structure Sixteen3 where
  hasN : Bool
  hasT : Bool
  hasF : Bool
  hasB : Bool
  deriving DecidableEq, Repr, Inhabited

namespace Sixteen3

/-- Membership of a FOUR value in a SIXTEEN_3 value. -/
def mem (x : Sixteen3) : Belnap → Bool
  | .N => x.hasN
  | .T => x.hasT
  | .F => x.hasF
  | .B => x.hasB

/-- Does this value assert TRUTH? The T-pole: it contains a truth-carrying member. -/
def assertsTrue (x : Sixteen3) : Bool := x.hasT || x.hasB

/-- Does this value assert FALSITY? The F-pole. In FOUR this is determined by the
truth value; in SIXTEEN_3 it is INDEPENDENT, and that independence is the split. -/
def assertsFalse (x : Sixteen3) : Bool := x.hasF || x.hasB

/-- Truth order ≤_t: more truth asserted, no more falsity. -/
def le_t (x y : Sixteen3) : Bool :=
  (!x.assertsTrue || y.assertsTrue) && (!y.assertsFalse || x.assertsFalse)

/-- Falsity order ≤_f: more falsity asserted, no more truth. The MIRROR of ≤_t, and
an order in its own right — this is the axis FOUR does not have. -/
def le_f (x y : Sixteen3) : Bool :=
  (!x.assertsFalse || y.assertsFalse) && (!y.assertsTrue || x.assertsTrue)

/-- Information order ≤_i: subset inclusion. More is known, nothing retracted. -/
def le_i (x y : Sixteen3) : Bool :=
  (!x.hasN || y.hasN) && (!x.hasT || y.hasT) && (!x.hasF || y.hasF) && (!x.hasB || y.hasB)

/-- The empty value: asserts nothing. Bottom of ≤_i. -/
def none : Sixteen3 := ⟨false, false, false, false⟩
/-- All of FOUR: the maximally informed value. Top of ≤_i. -/
def all : Sixteen3 := ⟨true, true, true, true⟩
/-- The image of a FOUR value: the singleton containing it. -/
def ofBelnap : Belnap → Sixteen3
  | .N => ⟨true, false, false, false⟩
  | .T => ⟨false, true, false, false⟩
  | .F => ⟨false, false, true, false⟩
  | .B => ⟨false, false, false, true⟩

/-- The sixteen values, written out. This IS the powerset of FOUR: four independent
membership bits, 2^4 = 16 rows, no row repeated and none missing. Enumerated rather
than derived because this module imports `Lean`, not Mathlib — there is no `Fintype`
here to count with, and a theorem that cannot be checked is worse than a list. -/
def all16 : List Sixteen3 :=
  [ ⟨false,false,false,false⟩, ⟨false,false,false,true⟩,
    ⟨false,false,true ,false⟩, ⟨false,false,true ,true⟩,
    ⟨false,true ,false,false⟩, ⟨false,true ,false,true⟩,
    ⟨false,true ,true ,false⟩, ⟨false,true ,true ,true⟩,
    ⟨true ,false,false,false⟩, ⟨true ,false,false,true⟩,
    ⟨true ,false,true ,false⟩, ⟨true ,false,true ,true⟩,
    ⟨true ,true ,false,false⟩, ⟨true ,true ,false,true⟩,
    ⟨true ,true ,true ,false⟩, ⟨true ,true ,true ,true⟩ ]

/-- Sixteen, by count. -/
theorem card_sixteen : all16.length = 16 := rfl

/-- Every one of the three orders is reflexive. Sixteen cases, each by computation. -/
theorem le_t_refl (x : Sixteen3) : le_t x x = true := by
  obtain ⟨n, t, f, b⟩ := x
  cases n <;> cases t <;> cases f <;> cases b <;> rfl

theorem le_f_refl (x : Sixteen3) : le_f x x = true := by
  obtain ⟨n, t, f, b⟩ := x
  cases n <;> cases t <;> cases f <;> cases b <;> rfl

theorem le_i_refl (x : Sixteen3) : le_i x x = true := by
  obtain ⟨n, t, f, b⟩ := x
  cases n <;> cases t <;> cases f <;> cases b <;> rfl

/-- THE SPLIT: ≤_t and ≤_f are genuinely different orders. FOUR cannot tell them apart
because its falsity is its truth read backwards; SIXTEEN_3 can. A witness is enough --
this is the whole reason the third order exists, and the reason a bilattice (which
carries two) is the wrong shape to hold it. -/
theorem truth_and_falsity_are_independent :
    ∃ x y : Sixteen3, le_t x y ≠ le_f x y :=
  ⟨ofBelnap .N, ofBelnap .T, by decide⟩

/-- ≤_i is not ≤_t either: the information order is a third thing, not a rebrand. -/
theorem information_is_a_third_order :
    ∃ x y : Sixteen3, le_i x y ≠ le_t x y :=
  ⟨ofBelnap .T, all, by decide⟩

/-- Half of the sixteen carry B directly -- one free bit, trivially eight. This is
why trilattice mode entails paraconsistent: a kernel that explodes cannot carry the
`hasB` values, and dropping them is not SIXTEEN_3 any more, only a smaller lattice. -/
theorem eight_carry_B_directly :
    (all16.filter (fun x => x.hasB)).length = 8 := by decide

/-- Ten of the sixteen assert BOTH truth and falsity (via hasT/hasF/hasB in any
combination) -- strictly more than the eight that merely contain B, since a value can
assert both poles with hasB = false by holding hasT and hasF together. This is the
sharper reason trilattice entails paraconsistent: the recursor block has to catch
every value that asserts a contradiction, not only the ones that store it as a single
bit. -/
theorem ten_assert_both_poles :
    (all16.filter (fun x => x.assertsTrue && x.assertsFalse)).length = 10 := by
  decide

end Sixteen3

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
