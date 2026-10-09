/*
Copyright (c) 2024 Lando ⊗ ⊙perator. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

PARACONSISTENT KERNEL FORK — SIXTEEN_3 trilattice (Shramko-Wansing's
P(FOUR), 16 values) implemented in the C++ kernel so that reentry constants
compute lfp(F : Sixteen3 → Sixteen3) in the information order le_i.

The type is a 4-bit mask (hasN, hasT, hasF, hasB). It IS the powerset of the
Belnap four values, so there are exactly 16 inhabitants. Three interlocking
orders: truth ≤_t, falsity ≤_f, information ≤_i. le_i is the order in which the
Kleene iteration converges to the least fixed point.
*/
#pragma once
#include "kernel/expr.h"

namespace lean {

/** Sixteen3 value: a subset of Belnap FOUR given by its membership bits.
    hasN : does the value contain N (neither)?
    hasT : does the value contain T (true)?
    hasF : does the value contain F (false)?
    hasB : does the value contain B (both / dialetheia)? */
struct sixteen3 {
    bool hasN;
    bool hasT;
    bool hasF;
    bool hasB;

    sixteen3() : hasN(false), hasT(false), hasF(false), hasB(false) {}
    sixteen3(bool n, bool t, bool f, bool b) : hasN(n), hasT(t), hasF(f), hasB(b) {}

    bool operator==(sixteen3 const & o) const {
        return hasN == o.hasN && hasT == o.hasT && hasF == o.hasF && hasB == o.hasB;
    }
    bool operator!=(sixteen3 const & o) const { return !(*this == o); }

    /** Membership of a Belnap FOUR value in this SIXTEEN_3 value. */
    bool mem(bool n, bool t, bool f, bool b) const {
        return (n ? hasN : true) && (t ? hasT : true) && (f ? hasF : true) && (b ? hasB : true);
    }

    /** Does this value assert TRUTH? The T-pole: it contains a truth-carrying member. */
    bool assertsTrue() const { return hasT || hasB; }
    /** Does this value assert FALSITY? The F-pole. In FOUR this is determined by the
        truth value; in SIXTEEN_3 it is INDEPENDENT, and that independence is the split. */
    bool assertsFalse() const { return hasF || hasB; }

    /** Truth order ≤_t: more truth asserted, no more falsity. */
    bool le_t(sixteen3 const & y) const {
        return (!assertsTrue() || y.assertsTrue()) && (!y.assertsFalse() || assertsFalse());
    }
    /** Falsity order ≤_f: more falsity asserted, no more truth. */
    bool le_f(sixteen3 const & y) const {
        return (!assertsFalse() || y.assertsFalse()) && (!y.assertsTrue() || assertsTrue());
    }
    /** Information order ≤_i: subset inclusion. More is known, nothing retracted. */
    bool le_i(sixteen3 const & y) const {
        return (!hasN || y.hasN) && (!hasT || y.hasT) && (!hasF || y.hasF) && (!hasB || y.hasB);
    }
    /** Join in the information order (supremum w.r.t. ≤_i = bitwise OR). */
    sixteen3 join_i(sixteen3 const & y) const {
        return sixteen3(hasN || y.hasN, hasT || y.hasT, hasF || y.hasF, hasB || y.hasB);
    }
    /** Meet in the information order (infimum w.r.t. ≤_i = bitwise AND). */
    sixteen3 meet_i(sixteen3 const & y) const {
        return sixteen3(hasN && y.hasN, hasT && y.hasT, hasF && y.hasF, hasB && y.hasB);
    }
};

/** The bottom element of ≤_i: asserts nothing. Starting point of Kleene iteration. */
static inline sixteen3 sixteen3_none() { return sixteen3(false, false, false, false); }
/** The top element of ≤_i: all of FOUR. */
static inline sixteen3 sixteen3_all()  { return sixteen3(true, true, true, true); }

/** The image of a Belnap value as a singleton SIXTEEN_3 subset. */
static inline sixteen3 sixteen3_ofBelnap(bool n, bool t, bool f, bool b) {
    return sixteen3(n, t, f, b);
}

}