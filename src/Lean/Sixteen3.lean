/-
Copyright (c) 2024 Lando ⊗ ⊙perator. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

PARACONSISTENT KERNEL FORK — SIXTEEN_3 trilattice (Shramko-Wansing's P(FOUR),
16 values) in Lean. Mirrors `kernel/sixteen3.h`: a 4-bit mask (hasN, hasT, hasF,
hasB) that IS the powerset of Belnap FOUR. Three interlocking orders — truth
≤_t, falsity ≤_f, information ≤_i. le_i (subset inclusion = bitwise OR as join)
is the order in which Kleene iteration converges to the least fixed point.

The Reentry command elaborator uses this to build lfp values and to fold the
Kleene iteration; the kernel stores each Sixteen3 as a single object_ref.
-/

namespace Lean

/-- The sixteenth-three trilattice. A Sixteen3 is a set of Belnap FOUR values,
    given by the four membership bits. There are exactly 16 inhabitants. -/
structure Sixteen3 where
  hasN : Bool -- contains N (neither)
  hasT : Bool -- contains T (true)
  hasF : Bool -- contains F (false)
  hasB : Bool -- contains B (both / dialetheia)

deriving BEq

namespace Sixteen3

/-- Construct from the four membership bits. -/
def mk (n t f b : Bool) : Sixteen3 := { hasN := n, hasT := t, hasF := f, hasB := b }

/-- The bottom element of ≤_i: asserts nothing. Starting point of Kleene iteration. -/
def none : Sixteen3 := { hasN := false, hasT := false, hasF := false, hasB := false }

/-- The top element of ≤_i: all of FOUR. -/
def all : Sixteen3 := { hasN := true, hasT := true, hasF := true, hasB := true }

/-- The image of a Belnap FOUR value as a singleton SIXTEEN_3 subset. -/
def ofBelnap (n t f b : Bool) : Sixteen3 := { hasN := n, hasT := t, hasF := f, hasB := b }

/-- Membership of a Belnap FOUR value in this SIXTEEN_3 value. -/
def mem (n t f b : Bool) (s : Sixteen3) : Bool :=
  ((n → s.hasN) ∧ (t → s.hasT) ∧ (f → s.hasF) ∧ (b → s.hasB)).asBool

/-- Does this value assert TRUTH? The T-pole: it contains a truth-carrying member. -/
def assertsTrue (s : Sixteen3) : Bool := s.hasT || s.hasB

/-- Does this value assert FALSITY? The F-pole. In SIXTEEN_3 truth and falsity
    are independent axes. -/
def assertsFalse (s : Sixteen3) : Bool := s.hasF || s.hasB

/-- Truth order ≤_t: more truth asserted, no more falsity. -/
def le_t (x y : Sixteen3) : Bool :=
  (!x.assertsTrue || y.assertsTrue) && (!y.assertsFalse || x.assertsFalse)

/-- Falsity order ≤_f: more falsity asserted, no more truth. -/
def le_f (x y : Sixteen3) : Bool :=
  (!x.assertsFalse || y.assertsFalse) && (!y.assertsTrue || x.assertsTrue)

/-- Information order ≤_i: subset inclusion. More is known, nothing retracted. -/
def le_i (x y : Sixteen3) : Bool :=
  (!x.hasN || y.hasN) && (!x.hasT || y.hasT) && (!x.hasF || y.hasF) && (!x.hasB || y.hasB)

/-- Join in the information order (supremum w.r.t. ≤_i = bitwise OR). -/
def join_i (x y : Sixteen3) : Sixteen3 :=
  { hasN := x.hasN || y.hasN, hasT := x.hasT || y.hasT,
    hasF := x.hasF || y.hasF, hasB := x.hasB || y.hasB }

/-- Meet in the information order (infimum w.r.t. ≤_i = bitwise AND). -/
def meet_i (x y : Sixteen3) : Sixteen3 :=
  { hasN := x.hasN && y.hasN, hasT := x.hasT && y.hasT,
    hasF := x.hasF && y.hasF, hasB := x.hasB && y.hasB }

end Sixteen3

end Lean
