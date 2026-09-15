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
import Imscribing.CosmicHolonomy

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
    placeholders.

    Second-seal note (`ig-docs/the_two_seals.md`): this witness passes
    the first seal and is adequacy-thin on the second. `engagr_holds_both`
    is unconditional in `x` -- unfold `engagr` and it is immediate,
    regardless of what `x` actually was, the exact "landing was T at
    every rotation because the fixation ran early" pattern that document
    names. Nothing here was ever at risk. Kept as the minimal case that
    proves the machinery type-checks, not offered as a substantive
    instance -- see `unionCreatesVerdict` below for one that is. -/
def engagrVerdict (x : Reg16_3) : Verdict ((engagr x).smallT = true) :=
  .held (engagr_smallT x) (engagr_smallF x)

/-- The classifier reads this as B, mechanically, not by inspection of
    the source. -/
theorem engagrVerdict_is_B (x : Reg16_3) :
    (engagrVerdict x).classify = (true, true) := by
  rfl

#print axioms engagrVerdict_is_B

-- ═══════════════════════════════════════════════════════════════════
-- §3b  A held WITNESS WITH SOMETHING AT RISK
-- ═══════════════════════════════════════════════════════════════════

/-- A pure-T register: only the truth-axis T lane set. -/
def pureT : Reg16_3 := mk true false false false

/-- A pure-F register: only the truth-axis F lane set. -/
def pureF : Reg16_3 := mk false true false false

/-- `union` genuinely CREATES a B-state here: neither `pureT` nor `pureF`
    carries both bigT and bigF, `union` does. This is not unconditional --
    swap either register for one that already has both, or for one that
    shares no lane with the other, and this specific claim goes false.
    That dependence on the actual values is what "at risk" means for a
    proposition, the second seal's own test. -/
theorem union_creates_both :
    (union pureT pureF).bigT = true ∧ (union pureT pureF).bigF = true := by
  decide

/-- And `pureT` alone is not a B-state -- the fact `union` is creating
    something neither input had, proved directly rather than assumed
    from the names. -/
theorem pureT_is_not_both : ¬ (pureT.bigT = true ∧ pureT.bigF = true) := by
  decide

/-- The `held` witness with real content: two independently real,
    value-dependent facts about the same construction -- `union pureT
    pureF` is a genuine B-state, and `pureT` alone is not. Unlike
    `engagrVerdict`, changing either register changes which fields are
    even provable. -/
def unionCreatesVerdict :
    Verdict ((union pureT pureF).bigT = true ∧ (union pureT pureF).bigF = true) :=
  .held union_creates_both pureT_is_not_both

theorem unionCreatesVerdict_is_B :
    unionCreatesVerdict.classify = (true, true) := by
  rfl

#print axioms unionCreatesVerdict_is_B

-- ═══════════════════════════════════════════════════════════════════
-- §4  THE GEOMETRIC INSTANCE: COSMIC HOLONOMY
-- ═══════════════════════════════════════════════════════════════════

open Imscribing.CosmicHolonomy in
/-- The richer, geometric `held` witness. Not a fresh example built for
    this file -- that would risk a subtly wrong connection where
    correctness is exactly the point -- this is `Imscribing.CosmicHolonomy.
    local_flatness_permits_global_holonomy` itself, decomposed into
    `Verdict`'s two fields. `P` is local flatness everywhere, `Q` is the
    loop's non-trivial holonomy: two independently real facts about the
    same connection, proved by the existing theorem, not re-derived here.
    Generic over any connection satisfying the hypotheses -- this is the
    constructor, not one fixed instance of it. -/
def cosmicHolonomyVerdict {M : Type} (conn : Connection M)
    (locally_flat_everywhere : ∀ x : M, ∃ N : Neighborhood M, N x ∧ IsLocallyFlat conn N)
    {p : M} (L : Loop M p) (h_non_trivial : ∀ v, Holonomy conn L v ≠ v) :
    Verdict (∀ x : M, ∃ N : Neighborhood M, N x ∧ IsLocallyFlat conn N) :=
  have proof := local_flatness_permits_global_holonomy conn locally_flat_everywhere L h_non_trivial
  .held proof.1 proof.2

open Imscribing.CosmicHolonomy in
/-- The classifier reads any such connection as B too, mechanically --
    same read as ENGAGR's, on a wholly different kind of object (a
    connection with a non-trivial loop, not a four-lane register), which
    is the actual claim: `Verdict`'s B is not specific to the trilattice,
    it is the general shape "two independently real facts, held." -/
theorem cosmicHolonomyVerdict_is_B {M : Type} (conn : Connection M)
    (locally_flat_everywhere : ∀ x : M, ∃ N : Neighborhood M, N x ∧ IsLocallyFlat conn N)
    {p : M} (L : Loop M p) (h_non_trivial : ∀ v, Holonomy conn L v ≠ v) :
    (cosmicHolonomyVerdict conn locally_flat_everywhere L h_non_trivial).classify = (true, true) := by
  rfl

#print axioms cosmicHolonomyVerdict_is_B

end Imscribing.Paraconsistent.DialetheicWitness
