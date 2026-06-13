"""
kernel.py — Paraconsistent machine kernel.

Python mirror of Imscribing/Paraconsistent/Kernel.lean from the p4ramill
Lean 4 project. Implements the three-register Frobenius machine:

    ENGAGR r0       — sets r0 to B (dialetheia)
    FSPLIT r0 r1 r2 — B splits to (T, F); any other value duplicates
    FFUSE  r1 r2 r0 — join(r1, r2) fused back into r0

Frobenius invariant: ffuse(fsplit(r)) = r  for all r in Belnap.
This is the Python-level certificate of μ∘δ=id.
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Tuple

from .belnap import Belnap, join, band, bnot, designated


# ── Machine state ─────────────────────────────────────────────────────────

@dataclass
class MachineState:
    """Three-register paraconsistent machine state. Mirrors Kernel.lean."""
    r0: Belnap = Belnap.B
    r1: Belnap = Belnap.B
    r2: Belnap = Belnap.B
    paradoxCount: int = 0
    cycleCount: int = 0


def initial_state() -> MachineState:
    """All registers initialised to B — the dialetheic ground state."""
    return MachineState()


# ── Primitive operations ──────────────────────────────────────────────────

def engager(r: Belnap) -> Tuple[Belnap, bool]:
    """
    ENGAGR: engage a register into the dialetheic state.
    Returns (B, changed) where changed = r was not already B.
    """
    return (Belnap.B, r is not Belnap.B)


def fsplit(r0: Belnap) -> Tuple[Belnap, Belnap, bool]:
    """
    FSPLIT: B bifurcates into (T, F); all other values self-duplicate.
    Returns (r1, r2, bifurcated).
    - B  → (T, F, True)   — the unique bifurcation point
    - ~B → (r0, r0, False) — idempotent duplication
    """
    if r0 is Belnap.B:
        return (Belnap.T, Belnap.F, True)
    return (r0, r0, False)


def ffuse(r1: Belnap, r2: Belnap) -> Tuple[Belnap, bool]:
    """
    FFUSE: join r1 and r2 back into a single register.
    Returns (joined, dialetheic) where dialetheic = result is B.
    Frobenius: ffuse(fsplit(r)[0], fsplit(r)[1])[0] == r  for all r.
    """
    result = join(r1, r2)
    return (result, result is Belnap.B)


# ── Step and run ─────────────────────────────────────────────────────────

def step(ms: MachineState) -> MachineState:
    """
    One complete Frobenius cycle on r0: ENGAGR → FSPLIT → FFUSE.
    r1 and r2 are not modified — they preserve their values across cycles.
    paradoxCount is incremented when r0 bifurcates (i.e., r0 == B).
    cycleCount is incremented unconditionally.

    Invariant: if r0 == B before step, r0 == B after step (B is a fixed
    point of the Frobenius roundtrip).
    """
    r0_e, _changed = engager(ms.r0)
    r1_s, r2_s, bifurcated = fsplit(r0_e)
    r0_f, _dialetheic = ffuse(r1_s, r2_s)
    return MachineState(
        r0=r0_f,
        r1=ms.r1,
        r2=ms.r2,
        paradoxCount=ms.paradoxCount + (1 if bifurcated else 0),
        cycleCount=ms.cycleCount + 1,
    )


def run(ms: MachineState, n: int) -> MachineState:
    """Apply n steps to ms. run(ms, 0) = ms."""
    for _ in range(n):
        ms = step(ms)
    return ms


# ── Invariant predicates ─────────────────────────────────────────────────

def frobenius_invariant(r: Belnap) -> bool:
    """ffuse(fsplit(r)[0], fsplit(r)[1])[0] == r  (μ∘δ=id pointwise)."""
    r1, r2, _ = fsplit(r)
    result, _ = ffuse(r1, r2)
    return result is r


# ── Verification suite (mirrors Kernel.lean theorem block) ───────────────

def verify_frobenius_invariant() -> bool:
    """All four Belnap values satisfy the Frobenius roundtrip."""
    return all(frobenius_invariant(r) for r in Belnap)


def verify_run_B3(n: int = 8) -> bool:
    """After n steps from the all-B initial state, all three registers are still B."""
    ms = initial_state()
    for _ in range(n):
        ms = step(ms)
        if ms.r0 is not Belnap.B or ms.r1 is not Belnap.B or ms.r2 is not Belnap.B:
            return False
    return True


def verify_paradox_conservation(n: int = 8) -> bool:
    """Starting from B, each cycle produces exactly one paradox unit."""
    ms = initial_state()
    for i in range(1, n + 1):
        ms = step(ms)
        if ms.paradoxCount != i:
            return False
    return True


def verify_cycle_count(n: int = 8) -> bool:
    """After n steps, cycleCount == n."""
    ms = run(initial_state(), n)
    return ms.cycleCount == n


def verify_paraconsistency() -> bool:
    """B ∧ ¬B = B (no explosion — contradiction is contained, not detonating)."""
    return band(Belnap.B, bnot(Belnap.B)) is Belnap.B


def run_all_verifications() -> dict:
    """Run all kernel verifications. Returns a dict of name → bool."""
    return {
        "frobenius_invariant":    verify_frobenius_invariant(),
        "run_B3":                 verify_run_B3(),
        "paradox_conservation":   verify_paradox_conservation(),
        "cycle_count":            verify_cycle_count(),
        "paraconsistency":        verify_paraconsistency(),
    }


# ── Module-level certificate ──────────────────────────────────────────────

assert verify_frobenius_invariant(), "frobenius_invariant violated at kernel load"
assert verify_run_B3(), "run_B3 violated at kernel load"
assert verify_paradox_conservation(), "paradox_conservation violated at kernel load"
assert verify_cycle_count(), "cycle_count violated at kernel load"
assert verify_paraconsistency(), "paraconsistency violated at kernel load"
