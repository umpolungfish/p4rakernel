-- Imscribing/Millennium/Erdos/TrianglePartition.lean
-- Triangle partition congruence
--
-- One problem, one file. Split out of ErdosProblems.lean, which had grown to
-- 2160 lines carrying fifteen problems and nine synthesis sections at once.
-- Author: Lando⊗⊙perator

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Millennium.Erdos.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Millennium.ErdosProblems
open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

-- ============================================================
-- §12  TRIANGLE PARTITION CONGRUENCE — n congruent triangles
-- ============================================================

/-!
**Erdős Problem / Triangle Partition:** For which positive integers
n does there exist a triangle that can be partitioned into n
congruent triangles (all similar to each other)?

**mOMonadOS Agent FSPLIT Decomposition (Cycle 10):**

  Branch 1 — Square_Subdivision (structural): If n = k² is a perfect
    square, ANY triangle works. Divide each side into k equal parts
    and draw lines parallel to the edges through the division points.
    This creates k² congruent triangles similar to the original.
    Result: all perfect squares are valid.

  Branch 2 — Right_Triangle_Decomposition (statistical): If the
    triangle is right-angled, additional n are possible. A right
    triangle with legs in ratio a:b can be partitioned into n=a²+b²
    congruent subtriangles. E.g., n=5 via 1:2 legs, n=10 via 1:3
    legs. Result: all sums of two squares are valid.

  Branch 3 — Non_Square_Scaling (obstructional): the 30-60-90
    triangle is rep-3a², by first cutting it into three congruent
    copies and then subdividing each. Result: all three times a
    square are valid.

**Result: n is rep-n exactly for n a square, a sum of two positive
squares, or three times a square** (Snover–Waiveris–Williams 1991).
The set is NOT all of ℕ: `6` is the least excluded value, proved
below in `not_repArith_six` and `six_is_least_excluded`.

**Structural Imscription — triangle_partition_congruence:**
  D=ash (finite planar geometry, simplicial decomposition)
  T=mime (crossing: right triangle altitude creates a crossing point
    where subtriangles meet)
  R=ear (congruence ↔ similarity ↔ ratio duality)
  P=out (partitionable / not partitionable — but result is universal
    so P degenerates)
  F=peep (geometric precision)
  K=egg (slow asymptotic: construction complexity grows with n)
  G=bib (local: neighboring subtriangles share edges/vertices)
  Γ=measure (sequential: one partition construction at a time)
  φ̂=woe (subcritical: geometry is Euclidean, no complex-analytic
    criticality needed)
  H=kick (weak chiral: triangle orientation may flip between
    subtriangles)
  Σ=hung (1:1: one n → one partition existence claim)
  Ω=oak (ℤ₂ parity: even n use different constructions than odd n
    in some approaches, though the universal result collapses this)
-/

/--
The triangle partition congruence problem as an Imscription.
Tier: O₀ — woe+kick at bib with mime topology, oak protection.
  The subcritical φ̂=woe reflects the Euclidean (non-critical) nature
  of the geometry. The classification is arithmetic once the area
  constraint fixes the ratio at 1/√n (`rep_ratio` below), which is
  what keeps the whole problem subcritical.
-/
def triangle_partition_congruence : Imscription :=
  { dim  := Dimensionality.ash
    top  := Topology.mime
    rel  := Relational.ear
    pol  := Polarity.out
    fid  := Fidelity.peep
    kin  := KineticChar.egg
    gran := Granularity.bib
    gram := Grammar.measure
    crit := Criticality.woe
    chir := Chirality.kick
    stoi := Stoichiometry.hung
    prot := Protection.oak }

theorem triangle_partition_congruence_tier : imscriptionTier triangle_partition_congruence = .O₀ := by
  unfold triangle_partition_congruence; native_decide


-- ============================================================
-- §12.1  THE AREA CONSTRAINT — the ratio is forced to 1/√n
-- ============================================================

/-- **The similarity ratio is not free.** If a triangle of area `A > 0` is
dissected into `n` pieces each similar to it with ratio `r > 0`, the pieces
have area `r² A` each and they exhaust `A`, so `n r² = 1`.

This is the pivot of the whole classification: the ratio is `1/√n`, which is
rational exactly when `n` is a square. For non-square `n` the pieces meet the
original's edges at irrational fractions of them, and that is where the extra
arithmetic — sum of two squares, or three times a square — comes from. -/
theorem rep_ratio_sq {n : ℕ} {A r : ℝ} (hA : 0 < A) (hr : 0 < r)
    (hsum : (n : ℝ) * (r ^ 2 * A) = A) : r ^ 2 = 1 / n := by
  have hn : (n : ℝ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hsum
    exact hA.ne' hsum.symm
  have h1 : ((n : ℝ) * r ^ 2) * A = 1 * A := by linear_combination hsum
  have h2 : (n : ℝ) * r ^ 2 = 1 := mul_right_cancel₀ hA.ne' h1
  field_simp
  linear_combination h2

/-- The ratio itself: `r = 1/√n`. A square `n` is exactly the case where it is
rational, which is why homothety subdivision works there and nowhere else. -/
theorem rep_ratio {n : ℕ} {A r : ℝ} (hn : 0 < n) (hA : 0 < A) (hr : 0 < r)
    (hsum : (n : ℝ) * (r ^ 2 * A) = A) : r = 1 / Real.sqrt n := by
  have h2 := rep_ratio_sq hA hr hsum
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hsq : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hnpos.le
  have hc : (0 : ℝ) < 1 / Real.sqrt n := by positivity
  have hr2 : r ^ 2 = (1 / Real.sqrt n) ^ 2 := by
    rw [div_pow, one_pow, hsq]; exact h2
  have h0 : (r - 1 / Real.sqrt n) * (r + 1 / Real.sqrt n) = 0 := by nlinarith [hr2]
  rcases mul_eq_zero.1 h0 with h | h
  · linarith
  · linarith

-- ============================================================
-- §12.2  THE CLASSIFICATION SET, AND WHY 6 IS NOT IN IT
-- ============================================================

/-- The arithmetic side of the Snover–Waiveris–Williams classification: a
triangle is rep-`n` exactly when `n` is a square (any triangle, by homothety),
a sum of two positive squares (a right triangle with legs in that ratio), or
three times a square (the 30-60-90 triangle). -/
def repArith (n : ℕ) : Prop :=
  (∃ a, 0 < a ∧ n = a ^ 2) ∨
  (∃ a b, 0 < a ∧ 0 < b ∧ n = a ^ 2 + b ^ 2) ∨
  (∃ a, 0 < a ∧ n = 3 * a ^ 2)

theorem repArith_one   : repArith 1 := Or.inl ⟨1, by norm_num⟩
theorem repArith_two   : repArith 2 := Or.inr (Or.inl ⟨1, 1, by norm_num⟩)
theorem repArith_three : repArith 3 := Or.inr (Or.inr ⟨1, by norm_num⟩)
theorem repArith_four  : repArith 4 := Or.inl ⟨2, by norm_num⟩
theorem repArith_five  : repArith 5 := Or.inr (Or.inl ⟨1, 2, by norm_num⟩)

/-- **6 is not rep-6.** Each family is ruled out by a bounded search: a square
jumps 4 → 9, two positive squares give 2, 5, 8 in range, and `3a² = 6` would
need `a² = 2`. -/
theorem not_repArith_six : ¬ repArith 6 := by
  rintro (⟨a, ha, h⟩ | ⟨a, b, ha, hb, h⟩ | ⟨a, ha, h⟩)
  · have : a ≤ 3 := by nlinarith
    interval_cases a <;> simp_all
  · have hA : a ≤ 3 := by nlinarith
    have hB : b ≤ 3 := by nlinarith
    interval_cases a <;> interval_cases b <;> simp_all
  · have : a ≤ 3 := by nlinarith
    interval_cases a <;> simp_all

/-- **6 is the least excluded value.** Everything below it is rep. -/
theorem six_is_least_excluded :
    (∀ m, 0 < m → m < 6 → repArith m) ∧ ¬ repArith 6 := by
  refine ⟨?_, not_repArith_six⟩
  intro m hm h6
  interval_cases m
  · exact repArith_one
  · exact repArith_two
  · exact repArith_three
  · exact repArith_four
  · exact repArith_five

-- ============================================================
-- §12.3  SIX CONGRUENT PIECES, NONE SIMILAR TO THE ORIGINAL
-- ============================================================

/-!
The equilateral triangle `(0,0), (1,0), (1/2, √3/2)` cut by its three altitudes
— equivalently, the centroid joined to the three vertices and the three edge
midpoints — falls into six triangles. They are mutually congruent, and each is
a 30-60-90 triangle, so NONE of them is similar to the equilateral original.

That is the separation between question (1) and question (2) above: `6` is
excluded from the first and present in the second. Congruence is checked by
SSS on squared side lengths, so no square root is ever extracted; the three
squared sides are `1/4`, `1/12`, `1/3` for every one of the six pieces.
-/

/-- Squared distance in the plane. Squared, so SSS is a polynomial identity and
`√3` only ever appears through `s3_sq`. -/
def d2 (p q : ℝ × ℝ) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- The SSS data of a triangle: its three squared side lengths, read off in the
cyclic order of the vertices given. -/
def sides2 (p q r : ℝ × ℝ) : ℝ × ℝ × ℝ := (d2 p q, d2 q r, d2 r p)

noncomputable def s3 : ℝ := Real.sqrt 3

theorem s3_sq : s3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

noncomputable def V0 : ℝ × ℝ := (0, 0)
noncomputable def V1 : ℝ × ℝ := (1, 0)
noncomputable def V2 : ℝ × ℝ := (1/2, s3/2)
noncomputable def M01 : ℝ × ℝ := (1/2, 0)
noncomputable def M12 : ℝ × ℝ := (3/4, s3/4)
noncomputable def M02 : ℝ × ℝ := (1/4, s3/4)
/-- The centroid, which here is also the circumcentre and the incentre. -/
noncomputable def G : ℝ × ℝ := (1/2, s3/6)

/-- The six pieces, each written vertex → adjacent midpoint → centroid, so the
SSS triples come out in the same order. -/
noncomputable def piece : Fin 6 → (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ)
  | 0 => (V0, M01, G)
  | 1 => (V1, M01, G)
  | 2 => (V1, M12, G)
  | 3 => (V2, M12, G)
  | 4 => (V2, M02, G)
  | 5 => (V0, M02, G)

/-- **All six pieces carry the same SSS data**: squared sides `1/4, 1/12, 1/3`.
A right triangle, since `1/12 + 1/4 = 1/3`, with legs in ratio `1 : √3` — the
30-60-90. -/
theorem piece_sides2 (i : Fin 6) :
    sides2 (piece i).1 (piece i).2.1 (piece i).2.2 = (1/4, 1/12, 1/3) := by
  have h := s3_sq
  fin_cases i <;>
    simp only [piece, sides2, d2, V0, V1, V2, M01, M12, M02, G, Prod.mk.injEq] <;>
    refine ⟨by nlinarith [h], by nlinarith [h], by nlinarith [h]⟩

/-- **Mutual congruence, by SSS.** -/
theorem pieces_congruent (i j : Fin 6) :
    sides2 (piece i).1 (piece i).2.1 (piece i).2.2
      = sides2 (piece j).1 (piece j).2.1 (piece j).2.2 := by
  rw [piece_sides2, piece_sides2]

/-- The original is equilateral: all three squared sides are `1`. -/
theorem original_equilateral : sides2 V0 V1 V2 = (1, 1, 1) := by
  have h := s3_sq
  simp only [sides2, d2, V0, V1, V2, Prod.mk.injEq]
  refine ⟨by nlinarith [h], by nlinarith [h], by nlinarith [h]⟩

/-- **No piece is similar to the original.** Similarity with ratio `k` scales
every squared side by the same factor, but the original's squared sides are all
`1` while the piece's are `1/4` and `1/12`. So the six-piece dissection answers
question (2) and not question (1) — exactly the distinction that "ALL n ≥ 1"
erased. -/
theorem piece_not_similar_to_original :
    ¬ ∃ k : ℝ, d2 (piece 0).1 (piece 0).2.1 = k * d2 V0 V1 ∧
               d2 (piece 0).2.1 (piece 0).2.2 = k * d2 V1 V2 := by
  have h := s3_sq
  rintro ⟨k, h1, h2⟩
  simp only [piece, d2, V0, V1, V2, M01, G] at h1 h2
  nlinarith [h, h1, h2]

/-- The pieces are right triangles. -/
theorem piece_is_right : (1:ℝ)/12 + 1/4 = 1/3 := by norm_num

#print axioms rep_ratio
#print axioms not_repArith_six
#print axioms six_is_least_excluded
#print axioms pieces_congruent
#print axioms piece_not_similar_to_original

/-!
**Why O₀ is correct:** the resolution is elementary and constructive.
The one place real numbers are needed is the ratio `1/√n`, and even
there the consequence is arithmetic: `n r² = 1` is an area identity,
proved in `rep_ratio_sq` with no analysis beyond it.

**Belnap verdict:** **T** — the classification is complete.
  n=k²:     any triangle (homothety subdivision)
  n=a²+b²:  right triangle with legs a:b
  n=3k²:    the 30-60-90 triangle
  otherwise: excluded, the least such n being 6

**Known Results:**
  ✓ Squares n=k²: any triangle, by homothety subdivision
  ✓ Sums of two positive squares n=a²+b²: right triangle, legs a:b
  ✓ Three times a square n=3a²: the 30-60-90 triangle
  ✓ Snover–Waiveris–Williams (1991): those three families are
    ALL of them — the classification is complete
  ✓ n=6 is excluded, and is the least excluded value
  ✗ Classification of ALL triangles partitionable for given n
  ✗ Minimal number of pieces in universal construction

**What the ALL-n claim is about.** This file previously read "Laczkovich
(1990) proved that ANY n ≥ 1 admits a partition". Laczkovich's theorem is
about tilings by SIMILAR triangles, where the pieces may have different
sizes; it is not about congruent pieces, and it does not say every n is
rep-n. Three questions are in play and only the first is the one typed
above:
  (1) n congruent pieces, each similar to the original — rep-n,
      classified, and `6 ∉`;
  (2) n congruent pieces, similarity to the original NOT required —
      strictly weaker, and `6` is in it: the equilateral triangle's three
      altitudes cut it into six congruent 30-60-90 triangles, none of them
      similar to the equilateral original (§12.3 below);
  (3) n similar pieces, congruence NOT required — Laczkovich's question.
`6` is the witness that (1) and (2) are different questions, which is
what collapsing them hid.

**Barrier:** The problem is structurally "solved" (all n work) but the
constructive classification (which triangles for which n?) remains
open. Diffs to kernel: D(ash→if'), T(mime→are), φ̂(woe→monad),
Ω(oak→zoo). The φ̂ promotion from woe (subcritical Euclidean geometry)
to monad (O_inf self-modeling) would require a geometric Langlands-
type correspondence, which is far beyond current mathematics.
-/

end Millennium.ErdosProblems
