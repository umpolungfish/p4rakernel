/-
  SixteenThreeTorus.lean
  ──────────────────────
  THEOREM: a rectangle 16 wide and 3 tall, opposite edges glued into a
  torus, has a corner-to-corner diagonal that is a SINGLE closed curve
  visiting all 48 lattice cells, none twice -- exactly because 16 and 3
  share no common factor. Those two numbers are not arbitrary: 16 is
  SIXTEEN_3's own carrier (every subset of {T,F,t,f}), 3 is the trilattice's
  three orderings (≤_i information, ≤_t truth, ≤_c constructivity), and
  their product 48 is the same Shavian 48 already held in the_forty_nine
  as 12 marks x 4 base logic values. This file is the other factorization
  of that same 48, made a torus and checked as a real Lean theorem rather
  than asserted from the arithmetic alone.

  The rectangle-diagonal picture: identify (x, 0) ~ (x, 3) and (0, y) ~
  (16, y). The diagonal, walked one unit across and one unit up at a time,
  is exactly the map n -> (n mod 16, n mod 3). Whether that closes after
  visiting every cell once, or splits into several shorter parallel
  copies, is decided entirely by gcd(16, 3) -- this is the standard
  Chinese Remainder isomorphism ZMod 48 ≃+* ZMod 16 x ZMod 3, cited here
  rather than reproved, since Mathlib already carries it exactly.

  Author: Lando⊗⊙perator
  Tier:   O_∞
-/

import Mathlib.Data.ZMod.Basic

namespace SixteenThreeTorus

-- ═══════════════════════════════════════════════════════════════════
-- §1  THE TORUS: 16 STATES BY 3 ORDERINGS
-- ═══════════════════════════════════════════════════════════════════

/-- The torus lattice: SIXTEEN_3's own 16 states (every subset of
    {T,F,t,f}) by its 3 orderings (≤_i, ≤_t, ≤_c). -/
abbrev Torus := ZMod 16 × ZMod 3

theorem sixteen_three_coprime : Nat.Coprime 16 3 := by decide

theorem torus_card : Fintype.card Torus = 48 := by decide

-- ═══════════════════════════════════════════════════════════════════
-- §2  THE DIAGONAL IS ONE CURVE, NOT SEVERAL
-- ═══════════════════════════════════════════════════════════════════
--
-- ZMod.chineseRemainder turns the coprimality above into an explicit
-- ring isomorphism between the 48 steps of a single walk and the 48
-- cells of the torus. That it is a bijection (an Equiv under the hood)
-- IS the theorem: every one of the 48 steps lands on a different cell,
-- and every cell is reached by exactly one step.

/-- The diagonal walk itself: step n lands at (n mod 16, n mod 3), the
    corner-to-corner line of the 16-by-3 rectangle read off one unit at a
    time. -/
noncomputable def diagonal : ZMod 48 ≃+* Torus :=
  ZMod.chineseRemainder sixteen_three_coprime

/-- **Main theorem.** The diagonal walk is a bijection between its own 48
    steps and the torus's 48 cells: one closed curve, visiting every
    SIXTEEN_3 (state, ordering) pair exactly once before returning to
    where it started. -/
theorem diagonal_bijective : Function.Bijective diagonal :=
  diagonal.bijective

-- ═══════════════════════════════════════════════════════════════════
-- §3  ANY STARTING CORNER GIVES THE SAME CURVE
-- ═══════════════════════════════════════════════════════════════════
--
-- diagonal_bijective already says every cell is reached, so for any
-- starting corner p there is some step k0 the walk was already going to
-- pass through it at. Restarting the count there does not visit a
-- different set of cells: it is the same 48-cell orbit, re-indexed.

/-- **Every starting corner is already on the one orbit.** diagonal being
    onto (half of bijective) is exactly this: pick any cell p, and the
    walk reaches it at some step. There is no second, disjoint orbit for
    a different corner to sit on -- the whole torus is the one curve. -/
theorem every_corner_on_the_one_orbit (p : Torus) :
    ∃ k : ZMod 48, diagonal k = p :=
  diagonal_bijective.surjective p

end SixteenThreeTorus
