"""
belnap.py — Belnap four-valued logic.

Python mirror of Imscribing/Paraconsistent/Belnap.lean from the p4ramill
Lean 4 project. Every type, operation, and theorem is derived from and
matches the Lean kernel exactly.

Belnap FOUR:
    N — Neither (void, bottom)
    T — True
    F — False
    B — Both (dialetheia, top in information order)

Theorems verified (matching Lean rfl proofs):
    - B_fixed_point_negation: ¬B = B
    - no_explosion: B ∧ ¬B = B (not F)
    - B_ne_F: B ≠ F
    - only_B_is_dialetheic: B is the unique dialetheic value
    - designated: T and B are designated; N and F are not
"""

from __future__ import annotations
from enum import Enum
from typing import Tuple


class Belnap(Enum):
    """Belnap four-valued logic — mirrors the Lean inductive type."""
    N = "N"  # Neither
    T = "T"  # True
    F = "F"  # False
    B = "B"  # Both (dialetheia)

    def to_nat(self) -> int:
        """Mirrors belnapToNat: N→0, T→1, F→2, B→3."""
        return {"N": 0, "T": 1, "F": 2, "B": 3}[self.value]

    def __repr__(self) -> str:
        return f"Belnap.{self.value}"

    def __str__(self) -> str:
        return self.value


# ── Lattice operations (mirror Belnap.lean) ───────────────────────────────

def meet(a: Belnap, b: Belnap) -> Belnap:
    """Information-order meet (greatest lower bound)."""
    if a is Belnap.N or b is Belnap.N:
        return Belnap.N
    if a is Belnap.B:
        return b
    if b is Belnap.B:
        return a
    if a is Belnap.T and b is Belnap.F or a is Belnap.F and b is Belnap.T:
        return Belnap.N
    return a  # a == b here


def join(a: Belnap, b: Belnap) -> Belnap:
    """Information-order join (least upper bound)."""
    if a is Belnap.B or b is Belnap.B:
        return Belnap.B
    if a is Belnap.N:
        return b
    if b is Belnap.N:
        return a
    if a is Belnap.T and b is Belnap.F or a is Belnap.F and b is Belnap.T:
        return Belnap.B
    return a  # a == b here


def band(a: Belnap, b: Belnap) -> Belnap:
    """Truth-functional conjunction. Mirrors Belnap.lean `band`."""
    if a is Belnap.F or b is Belnap.F:
        return Belnap.F
    if (a is Belnap.B and b is Belnap.T) or (a is Belnap.T and b is Belnap.B) \
       or (a is Belnap.B and b is Belnap.N) or (a is Belnap.N and b is Belnap.B):
        return Belnap.B
    if a is Belnap.T and b is Belnap.T:
        return Belnap.T
    if (a is Belnap.T and b is Belnap.N) or (a is Belnap.N and b is Belnap.T):
        return Belnap.N
    if a is Belnap.N and b is Belnap.N:
        return Belnap.N
    return Belnap.B  # B ∧ B = B


def bor(a: Belnap, b: Belnap) -> Belnap:
    """Truth-functional disjunction. Mirrors Belnap.lean `bor`."""
    if a is Belnap.T or b is Belnap.T:
        return Belnap.T
    if (a is Belnap.B and b is Belnap.F) or (a is Belnap.F and b is Belnap.B) \
       or (a is Belnap.B and b is Belnap.N) or (a is Belnap.N and b is Belnap.B):
        return Belnap.B
    if a is Belnap.F and b is Belnap.F:
        return Belnap.F
    if (a is Belnap.F and b is Belnap.N) or (a is Belnap.N and b is Belnap.F):
        return Belnap.N
    if a is Belnap.N and b is Belnap.N:
        return Belnap.N
    return Belnap.B  # B ∨ B = B


def bnot(a: Belnap) -> Belnap:
    """Belnap negation: ¬N=N, ¬T=F, ¬F=T, ¬B=B. Mirrors Belnap.lean `bnot`."""
    return {
        Belnap.N: Belnap.N,
        Belnap.T: Belnap.F,
        Belnap.F: Belnap.T,
        Belnap.B: Belnap.B,
    }[a]


def designated(a: Belnap) -> bool:
    """Designated values: T and B count as 'true' for paraconsistent consequence."""
    return a in (Belnap.T, Belnap.B)


# ── Approximation order ───────────────────────────────────────────────────

def approx_le(a: Belnap, b: Belnap) -> bool:
    """Information order: N ≤ everything, everything ≤ B, otherwise reflexive."""
    if a is Belnap.N:
        return True
    if b is Belnap.B:
        return True
    return a is b


# ── WH2 bijection (Belnap ↔ ℤ₂×ℤ₂) ─────────────────────────────────────
# N→(0,0)=I, T→(0,1)=Z, F→(1,0)=X, B→(1,1)=XZ
_TO_WH2 = {
    Belnap.N: (0, 0),
    Belnap.T: (0, 1),
    Belnap.F: (1, 0),
    Belnap.B: (1, 1),
}
_FROM_WH2 = {v: k for k, v in _TO_WH2.items()}


def to_wh2(a: Belnap) -> Tuple[int, int]:
    """Belnap → ℤ₂×ℤ₂ bijection."""
    return _TO_WH2[a]


def from_wh2(ab: Tuple[int, int]) -> Belnap:
    """ℤ₂×ℤ₂ → Belnap bijection."""
    return _FROM_WH2[ab]


# ── Dialetheic predicate ─────────────────────────────────────────────────

def dialetheic(a: Belnap) -> bool:
    """A value is dialetheic iff it and its negation are both designated."""
    return designated(a) and designated(bnot(a))


# ── Module-level theorem verification ────────────────────────────────────

assert bnot(Belnap.B) is Belnap.B, "B_fixed_point_negation violated"
assert band(Belnap.B, bnot(Belnap.B)) is Belnap.B, "no_explosion violated"
assert Belnap.B is not Belnap.F, "B_ne_F violated"
assert designated(Belnap.T) is True
assert designated(Belnap.B) is True
assert designated(Belnap.N) is False
assert designated(Belnap.F) is False
assert dialetheic(Belnap.B)
for _v in Belnap:
    if _v is not Belnap.B:
        assert not dialetheic(_v), f"Only B should be dialetheic, but {_v} is"
for _v in Belnap:
    assert approx_le(_v, Belnap.B), f"B_is_top violated: {_v}"
for _v in Belnap:
    assert meet(Belnap.B, _v) is _v, f"B_meet_equiangular violated for {_v}"
for _v in Belnap:
    assert join(Belnap.B, _v) is Belnap.B, f"B_join_universal violated for {_v}"
assert len(set(Belnap)) == 4, "four_values_distinct violated"
