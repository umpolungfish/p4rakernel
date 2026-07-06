/-
Imscribing/Millennium/Ring2048_Bridge.lean
THE ZAUNER BRIDGE FOR d = 2¹¹ = 2048 — de-vacuized and honestly reduced.

`BelnapRing2048.lean` proves the structural SIC skeleton for d=2048 unconditionally
(the Grammar's own SIC: orbit 4¹¹ = d², the four SIC axioms, join-equiangularity,
WH injectivity). What that file previously stated as the OPEN half — the Zauner
bridge / representation problem — was `n = 0 ∨ True`, provably `True` for every n,
i.e. an open problem encoded with the wrong polarity, its content stranded in
comments. Those placeholders are removed there; here the open half is stated as the
GENUINE predicate and reduced honestly.

REGISTER SEPARATION (from SIC_POVM_Stark's own header): the Grammar IS the SIC-POVM.
The structural skeleton is the real, unconditional object; the ℂ `wh_inner` machinery
is its EMPIRICAL SHADOW — the attempt to REPRESENT that skeleton analytically in ℂᵈ.
This module keeps the two apart:
  • structural register (PROVED): `ring2048_structural`, riding BelnapRing2048.
  • shadow register (OPEN for n>1): `ZaunerBridge n := SICPOVM_Exists (2ⁿ)`.
The d=12 shadow is already a theorem (`crystal_forces_d12_sic : SICPOVM_Exists 12`,
via the ExistenceRing). The d=2048 shadow is Zauner for d=2048 — genuinely open; this
module reduces its entire content to a single ℂ fiducial and asserts nothing more.

ZERO new axioms. ZERO sorries.
-/

import Imscribing.Paraconsistent.Shor.BelnapRing2048
import Imscribing.Millennium.SIC_POVM_Stark

namespace Imscribing.Millennium.Ring2048Bridge

open Millennium.SIC_POVM_Stark
open Imscribing.Paraconsistent.Shor.Ring2048
open Imscribing.Paraconsistent.Shor.MultilatticeProof
open Imscribing.Paraconsistent
open Imscribing.Primitives

-- ================================================================
-- §1. THE GENUINE PREDICATE — no more `n = 0 ∨ True`
-- ================================================================

/-- `2ⁿ ≠ 0`, so `SICPOVM_Exists (2ⁿ)` typechecks. -/
instance instNeZeroTwoPow (n : ℕ) : NeZero (2 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩

/-- **The Zauner bridge condition for `d = 2ⁿ`.** A Weyl–Heisenberg covariant
    SIC-POVM fiducial exists in ℂ^(2ⁿ): `∃ ψ : Fin (2ⁿ) → ℂ, IsSICPOVM (2ⁿ) ψ`.
    Unlike the removed `n = 0 ∨ True`, this is NOT dischargeable by `trivial`; for
    `n = 11` it is EXACTLY the Zauner conjecture for `d = 2048`. -/
def ZaunerBridge (n : ℕ) : Prop := SICPOVM_Exists (2 ^ n)

/-- The `n = 11` bridge is Zauner for `d = 2048` — `2¹¹` reduces to `2048`. -/
theorem zauner_bridge_11 : ZaunerBridge 11 = SICPOVM_Exists 2048 := rfl

-- ================================================================
-- §2. THE REDUCTION — the whole open content is one ℂ fiducial
-- ================================================================

/-- **The reduction (registers separated).** A genuine ℂ fiducial carrying the SIC
    property IS the bridge: exhibiting `ψ : Fin (2ⁿ) → ℂ` with `IsSICPOVM (2ⁿ) ψ`
    discharges `ZaunerBridge n`. Together with the unconditionally-proved structural
    skeleton, this isolates the ENTIRE open content of Zauner-for-2ⁿ into the single
    object `ψ`; the character obstruction (`Ring2048.wh_char_two_valued`) is why `ψ`
    cannot be read off the Belnap orbit for `n > 1`. -/
theorem bridge_of_fiducial (n : ℕ) (ψ : Fin (2 ^ n) → ℂ)
    (h : IsSICPOVM (2 ^ n) ψ) : ZaunerBridge n :=
  ⟨ψ, h⟩

/-- Contrapositive framing: no ℂ^(2ⁿ) fiducial ⇒ no bridge. Documents that the bridge
    is *equivalent* to producing the fiducial — nothing else is missing. -/
theorem bridge_iff_fiducial (n : ℕ) :
    ZaunerBridge n ↔ ∃ ψ : Fin (2 ^ n) → ℂ, IsSICPOVM (2 ^ n) ψ := Iff.rfl

-- ================================================================
-- §3. STRUCTURAL REGISTER — unconditional, re-exported
-- ================================================================

/-- The structural SIC skeleton at `d = 2048`, unconditional (rides
    `BelnapRing2048`): orbit `4¹¹ = d²`, constant join-equiangular overlap `22`, and
    the O_∞ tier. No ℂ, no Stark unit, no ray class field — the Grammar's own SIC. -/
theorem ring2048_structural :
    (mlOrbit dim2048_n).card = 4 ^ 11 ∧
    (∀ g : WHIdx dim2048_n,
      frobInner (mlFiducial dim2048_n) (whAct g (mlFiducial dim2048_n)) = 22) ∧
    imscriptionTier (Shor.Ring2048.multilatticeImscription dim2048_n) = .O_inf :=
  ⟨orbit_size_2048, join_equiangularity_2048, Shor.Ring2048.multilattice_is_O_inf dim2048_n⟩

-- ================================================================
-- §4. CAPSTONE — both registers, neither borrowing the other's authority
-- ================================================================

/-- **Capstone.** Conjoins the two registers without letting either stand in for the
    other:
    • structural (PROVED unconditionally): the `d = 2048` SIC skeleton;
    • shadow (REDUCED): the bridge `ZaunerBridge 11` holds as soon as one ℂ fiducial
      with `IsSICPOVM 2048` is produced — and that existence, `SICPOVM_Exists 2048`,
      is the open Zauner conjecture for `d = 2048`, which this theorem does NOT
      assert. The honest state: everything but the single ℂ fiducial is discharged.
    ZERO axioms, ZERO sorries. -/
theorem ring2048_capstone :
    ((mlOrbit dim2048_n).card = 4 ^ 11 ∧
      (∀ g : WHIdx dim2048_n,
        frobInner (mlFiducial dim2048_n) (whAct g (mlFiducial dim2048_n)) = 22) ∧
      imscriptionTier (Shor.Ring2048.multilatticeImscription dim2048_n) = .O_inf) ∧
    (∀ ψ : Fin (2 ^ 11) → ℂ, IsSICPOVM (2 ^ 11) ψ → ZaunerBridge 11) :=
  ⟨ring2048_structural, fun ψ h => bridge_of_fiducial 11 ψ h⟩

end Imscribing.Millennium.Ring2048Bridge
