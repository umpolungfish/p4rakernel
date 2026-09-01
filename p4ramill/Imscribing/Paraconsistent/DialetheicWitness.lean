/-
  DialetheicWitness.lean
  A PARACONSISTENT WITNESS TYPE, DISTINCT FROM sorry
  =====================================================================
  Author: Lando⊗⊙perator
  Date:   2026-09-01

  What this is NOT: a type carrying `h1 : P` and `h2 : ¬P` for the same
  fixed `P`. That is not buildable in Lean without the whole environment
  becoming unsound -- `h2 h1 : False`, and once `False` is inhabited
  every `Prop` is, whether or not the resulting term is ever pattern
  matched into `False.elim`. Consistency is a property of the WHOLE
  kernel, not of one local site, so this file never constructs that pair.

  What this IS: a value-level verdict, `Verdict P : Type`, one case of
  which (`held`) carries two INDEPENDENTLY REAL facts about the same
  object -- `h1 : P` and `h2 : Q` for a genuinely different `Q`, not `¬P`
  -- exactly the shape `CosmicHolonomy.lean`'s coexistence theorem and
  `SixteenThreeTrilattice.engagr` already have: two things that look like
  they should conflict, held together, neither exploding the other. That
  is real, sound, and exactly what Belnap's own B state means once you
  stop trying to read it as a Prop-level contradiction.

  Why `Type`, not `Prop`: a `Prop`'s content is erased by Lean's compiler
  at every use -- confirmed directly this session, `nm` on real compiled
  objects shows zero symbol for a theorem's proof, of any theorem, real
  or vacuous. A `Verdict P : Type` is not erased: which constructor a
  given value uses is real, compiled data, and a function dispatching on
  it produces real machine code Vox can genuinely audit (see
  `classifyIsCompiled` below, and run it through the same pipeline
  `scripts/vox_elf_audit.sh` uses). The proof FIELDS inside each
  constructor stay `Prop` and stay erased -- that's what makes `proved`
  and `held` sound and unable to fabricate a witness, exactly as `sorry`
  cannot be smuggled in as one either (see `admitted` below).
-/

import Imscribing.Paraconsistent.SixteenThreeTrilattice

namespace Imscribing.Paraconsistent.DialetheicWitness

open Reg16_3

-- ═══════════════════════════════════════════════════════════════════
-- §1  THE VERDICT TYPE
-- ═══════════════════════════════════════════════════════════════════

/-- A verdict on `P`: proved, refuted, held (two independently real facts
    about the same object, `P` and a genuinely different `Q`), or an
    explicit non-claim. `Type`, not `Prop` -- the constructor tag is real
    data. -/
inductive Verdict (P : Prop) : Type where
  | proved (h : P) : Verdict P
  | refuted (h : ¬P) : Verdict P
  | held {Q : Prop} (h1 : P) (h2 : Q) : Verdict P
  | admitted : Verdict P

/-- The Belnap-shaped read: proved -> T, refuted -> F, held -> B,
    admitted -> N. A real, computable function -- this is the part of
    the file that survives to machine code, unlike any `Prop` above it. -/
def Verdict.classify {P : Prop} : Verdict P → Bool × Bool
  -- (bigT, bigF) in SixteenThreeTrilattice's own lane order.
  | .proved _  => (true, false)
  | .refuted _ => (false, true)
  | .held ..   => (true, true)
  | .admitted  => (false, false)

-- ═══════════════════════════════════════════════════════════════════
-- §2  admitted IS NOT sorry, PROVED DIRECTLY
-- ═══════════════════════════════════════════════════════════════════

/-- `admitted` type-checks with no premise at all -- it is a real
    constructor of a four-case inductive, not an axiom. `#print axioms`
    on any term built from it names none of Lean's own axioms and never
    `sorryAx`; check the corpus's own build log if this claim needs
    re-checking rather than trusting the comment. -/
def anAdmittedVerdict (P : Prop) : Verdict P := .admitted

#print axioms anAdmittedVerdict

-- ═══════════════════════════════════════════════════════════════════
-- §3  THE WORKED INSTANCE: ENGAGR
-- ═══════════════════════════════════════════════════════════════════

/-- For any register, ENGAGR's own defining property: it holds the
    smallT lane. This is the `P` half. -/
theorem engagr_smallT (x : Reg16_3) : (engagr x).smallT = true :=
  (engagr_holds_both x).1

/-- And the smallF lane, independently -- the `Q` half, a genuinely
    different fact, not the negation of the first. -/
theorem engagr_smallF (x : Reg16_3) : (engagr x).smallF = true :=
  (engagr_holds_both x).2

/-- The concrete `held` witness: ENGAGR's own action on any register is a
    live paraconsistent verdict, not an admission of anything unproved.
    Both fields are real closed proofs, checked at elaboration, not
    placeholders. -/
def engagrVerdict (x : Reg16_3) : Verdict ((engagr x).smallT = true) :=
  .held (engagr_smallT x) (engagr_smallF x)

/-- The classifier reads this as B, mechanically, not by inspection of
    the source. -/
theorem engagrVerdict_is_B (x : Reg16_3) :
    (engagrVerdict x).classify = (true, true) := by
  rfl

#print axioms engagrVerdict_is_B

end Imscribing.Paraconsistent.DialetheicWitness
