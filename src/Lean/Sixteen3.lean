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

module
prelude
public import Init
public section

namespace Lean

/-- The sixteenth-three trilattice. A Sixteen3 is a set of Belnap FOUR values,
    given by the four membership bits. There are exactly 16 inhabitants. -/
structure Sixteen3 where
  hasN : Bool -- contains N (neither)
  hasT : Bool -- contains T (true)
  hasF : Bool -- contains F (false)
  hasB : Bool -- contains B (both / dialetheia)

deriving Inhabited, BEq, DecidableEq, Repr

namespace Sixteen3

/-- The bottom element of ≤_i: asserts nothing. Starting point of Kleene iteration. -/
def none : Sixteen3 := { hasN := false, hasT := false, hasF := false, hasB := false }

/-- The top element of ≤_i: all of FOUR. -/
def all : Sixteen3 := { hasN := true, hasT := true, hasF := true, hasB := true }

/-- The image of a Belnap FOUR value as a singleton SIXTEEN_3 subset. -/
def ofBelnap (n t f b : Bool) : Sixteen3 := { hasN := n, hasT := t, hasF := f, hasB := b }

/-- Membership of a Belnap FOUR value in this SIXTEEN_3 value. -/
def mem (n t f b : Bool) (s : Sixteen3) : Bool :=
  (!n || s.hasN) && (!t || s.hasT) && (!f || s.hasF) && (!b || s.hasB)

/-- Does this value assert TRUTH? The T-pole: it contains a truth-carrying member. -/
def assertsTrue (s : Sixteen3) : Bool := s.hasT || s.hasB

/-- Does this value assert FALSITY? The F-pole. In SIXTEEN_3 truth and falsity
    are independent axes. -/
def assertsFalse (s : Sixteen3) : Bool := s.hasF || s.hasB

/-- Truth order: inclusion on T/B memberships, reverse inclusion on N/F. -/
def le_t (x y : Sixteen3) : Bool :=
  (!y.hasN || x.hasN) && (!x.hasT || y.hasT) &&
  (!y.hasF || x.hasF) && (!x.hasB || y.hasB)

/-- Falsity order: inclusion on F/B memberships, reverse inclusion on N/T. -/
def le_f (x y : Sixteen3) : Bool :=
  (!y.hasN || x.hasN) && (!y.hasT || x.hasT) &&
  (!x.hasF || y.hasF) && (!x.hasB || y.hasB)

/-- Join and meet in the truth order. -/
def join_t (x y : Sixteen3) : Sixteen3 :=
  ⟨x.hasN && y.hasN, x.hasT || y.hasT, x.hasF && y.hasF, x.hasB || y.hasB⟩
def meet_t (x y : Sixteen3) : Sixteen3 :=
  ⟨x.hasN || y.hasN, x.hasT && y.hasT, x.hasF || y.hasF, x.hasB && y.hasB⟩

/-- Join and meet in the falsity order. -/
def join_f (x y : Sixteen3) : Sixteen3 :=
  ⟨x.hasN && y.hasN, x.hasT && y.hasT, x.hasF || y.hasF, x.hasB || y.hasB⟩
def meet_f (x y : Sixteen3) : Sixteen3 :=
  ⟨x.hasN || y.hasN, x.hasT || y.hasT, x.hasF && y.hasF, x.hasB && y.hasB⟩

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

/-- Enumerate the carrier in native membership-mask order. -/
def ofMask (m : Nat) : Sixteen3 :=
  ⟨m % 2 == 1, m / 2 % 2 == 1, m / 4 % 2 == 1, m / 8 % 2 == 1⟩

/-- Native kernel solver: reject malformed or nonmonotone tables, otherwise return the least fixed point. -/
@[extern "lean_sixteen3_fixed_point"]
opaque fixedPoint (table : @& Array Sixteen3) : Option Sixteen3

end Sixteen3

end Lean
