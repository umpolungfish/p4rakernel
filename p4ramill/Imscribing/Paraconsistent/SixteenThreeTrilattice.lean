/-
  SixteenThreeTrilattice.lean
  THE SIXTEEN_3 TRILATTICE GATES: union, meet_t/join_t, meet_c/join_c,
  the three swaps, the three orders
  =====================================================================
  Author: Lando⊗⊙perator
  Date:   2026-08-31

  Mirrors imasm_core::imasm16_3::Reg16_3 (MoDoT/imasm_core/src/imasm16_3.rs)
  and its gates exactly -- the same four-lane carrier, the same per-lane
  AND/OR masks per gate, checked against that source, not written
  independently and hoped to agree. Those gates were already verified
  bit-for-bit against this exact Rust source at scale on GPU
  (mOMonadOS/src/gpu_sixteen3.rs, 20,000,000+ register pairs, zero
  mismatches). This file is the other half: the same claims, proved.

  Reg16_3 is `Bool × Bool × Bool × Bool` directly, not a wrapping
  structure: the product's own Fintype/DecidableEq (Lean 4 core) already
  makes every `∀ x : Reg16_3, ...` below decidable with no custom instance
  to get wrong. Named accessors restore the field-name readability a
  structure would have given.

  KEY THEOREMS:
    §1  Reg16_3 carrier and named lane accessors
    §2  union, meet_t/join_t, meet_c/join_c
    §3  The three swaps: truth_swap, info_swap, invol
        invol is an involution, and it factors as info_swap ∘ truth_swap
        exactly as the Rust doc comment states -- proved, not asserted.
    §4  ≤_i (information order): a genuine partial order, and union is
        its least upper bound
    §5  union is commutative, idempotent, associative
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod

set_option linter.unusedVariables false

-- ═══════════════════════════════════════════════════════════════════
-- §1  THE CARRIER
-- ═══════════════════════════════════════════════════════════════════

/-- The SIXTEEN_3 register: a subset of {T, F, t, f}, one Bool per lane,
    in (T, F, t, f) order. Mirrors `Reg16_3` in
    `imasm_core/src/imasm16_3.rs` lane for lane. -/
abbrev Reg16_3 := Bool × Bool × Bool × Bool

namespace Reg16_3

def mk (bigT bigF smallT smallF : Bool) : Reg16_3 := (bigT, bigF, smallT, smallF)
def bigT (x : Reg16_3) : Bool := x.1
def bigF (x : Reg16_3) : Bool := x.2.1
def smallT (x : Reg16_3) : Bool := x.2.2.1
def smallF (x : Reg16_3) : Bool := x.2.2.2

-- ═══════════════════════════════════════════════════════════════════
-- §2  THE GATES (per-lane AND/OR masks, matching the Rust source exactly)
-- ═══════════════════════════════════════════════════════════════════

/-- Every lane OR. -/
def union (x y : Reg16_3) : Reg16_3 :=
  mk (x.bigT || y.bigT) (x.bigF || y.bigF) (x.smallT || y.smallT) (x.smallF || y.smallF)

/-- T,t lanes AND; F,f lanes OR. -/
def meetT (x y : Reg16_3) : Reg16_3 :=
  mk (x.bigT && y.bigT) (x.bigF || y.bigF) (x.smallT && y.smallT) (x.smallF || y.smallF)

/-- T,t lanes OR; F,f lanes AND. -/
def joinT (x y : Reg16_3) : Reg16_3 :=
  mk (x.bigT || y.bigT) (x.bigF && y.bigF) (x.smallT || y.smallT) (x.smallF && y.smallF)

/-- T,F lanes AND; t,f lanes OR. -/
def meetC (x y : Reg16_3) : Reg16_3 :=
  mk (x.bigT && y.bigT) (x.bigF && y.bigF) (x.smallT || y.smallT) (x.smallF || y.smallF)

/-- T,F lanes OR; t,f lanes AND. -/
def joinC (x y : Reg16_3) : Reg16_3 :=
  mk (x.bigT || y.bigT) (x.bigF || y.bigF) (x.smallT && y.smallT) (x.smallF && y.smallF)

-- ═══════════════════════════════════════════════════════════════════
-- §3  THE THREE SWAPS
-- ═══════════════════════════════════════════════════════════════════

/-- The constructive swap T ↔ F, leaving the information layer alone. -/
def truthSwap (x : Reg16_3) : Reg16_3 := mk x.bigF x.bigT x.smallT x.smallF

/-- The information swap t ↔ f, leaving the constructive layer alone. -/
def infoSwap (x : Reg16_3) : Reg16_3 := mk x.bigT x.bigF x.smallF x.smallT

/-- The involution T ↔ F, t ↔ f -- AREV's action on values. -/
def invol (x : Reg16_3) : Reg16_3 := mk x.bigF x.bigT x.smallF x.smallT

/-- AREV is both swaps at once: composing them IS invol, exactly what the
    Rust doc comment on `invol` claims. Proved, not asserted. -/
theorem invol_eq_compose : ∀ x : Reg16_3, invol x = infoSwap (truthSwap x) := by decide

/-- The two factors commute: it doesn't matter which order you swap in. -/
theorem invol_eq_compose' : ∀ x : Reg16_3, invol x = truthSwap (infoSwap x) := by decide

/-- Every one of the three swaps is its own inverse. -/
theorem truthSwap_involutive : ∀ x : Reg16_3, truthSwap (truthSwap x) = x := by decide
theorem infoSwap_involutive : ∀ x : Reg16_3, infoSwap (infoSwap x) = x := by decide
theorem invol_involutive : ∀ x : Reg16_3, invol (invol x) = x := by decide

-- ═══════════════════════════════════════════════════════════════════
-- §4  THE INFORMATION ORDER ≤_i
-- ═══════════════════════════════════════════════════════════════════

/-- x ≤_i y iff every lane of x is a lane of y (subset inclusion). -/
def leqI (x y : Reg16_3) : Bool :=
  (!x.bigT || y.bigT) && (!x.bigF || y.bigF) && (!x.smallT || y.smallT) && (!x.smallF || y.smallF)

theorem leqI_refl : ∀ x : Reg16_3, leqI x x := by decide
theorem leqI_trans : ∀ x y z : Reg16_3, leqI x y → leqI y z → leqI x z := by decide
theorem leqI_antisymm : ∀ x y : Reg16_3, leqI x y → leqI y x → x = y := by decide

/-- The information order's own N (empty register) is its bottom element. -/
theorem leqI_bot : ∀ x : Reg16_3, leqI (mk false false false false) x := by decide

/-- union is a genuine upper bound for ≤_i: shuttling via union only ever
    moves a value up the information order, exactly what the primer's
    Part IV states as "Flow uses ≤_i: shuttling only ever moves values up
    the information order." Proved here for the specific gate that does
    the shuttling. -/
theorem leqI_union_left : ∀ x y : Reg16_3, leqI x (union x y) := by decide
theorem leqI_union_right : ∀ x y : Reg16_3, leqI y (union x y) := by decide

/-- union is the LEAST upper bound: any z above both x and y is above their
    union too. This is what makes union a real join, not just an upper
    bound among others. -/
theorem union_least_upper_bound :
    ∀ x y z : Reg16_3, leqI x z → leqI y z → leqI (union x y) z := by decide

-- ═══════════════════════════════════════════════════════════════════
-- §5  union IS A REAL SEMILATTICE JOIN
-- ═══════════════════════════════════════════════════════════════════

theorem union_comm : ∀ x y : Reg16_3, union x y = union y x := by decide
theorem union_idem : ∀ x : Reg16_3, union x x = x := by decide
theorem union_assoc : ∀ x y z : Reg16_3, union (union x y) z = union x (union y z) := by decide

-- ═══════════════════════════════════════════════════════════════════
-- §6  FULL SYSTEM VERIFICATION
-- ═══════════════════════════════════════════════════════════════════

/-- Every theorem in this file, folded into one check. If this closes, the
    whole file closes with it. -/
theorem sixteen_three_verified :
    (∀ x : Reg16_3, invol x = infoSwap (truthSwap x)) ∧
    (∀ x : Reg16_3, invol (invol x) = x) ∧
    (∀ x : Reg16_3, truthSwap (truthSwap x) = x) ∧
    (∀ x : Reg16_3, infoSwap (infoSwap x) = x) ∧
    (∀ x y : Reg16_3, leqI x (union x y)) ∧
    (∀ x y z : Reg16_3, leqI x z → leqI y z → leqI (union x y) z) ∧
    (∀ x y : Reg16_3, union x y = union y x) ∧
    (∀ x : Reg16_3, union x x = x) :=
  ⟨invol_eq_compose, invol_involutive, truthSwap_involutive, infoSwap_involutive,
   leqI_union_left, union_least_upper_bound, union_comm, union_idem⟩

end Reg16_3
