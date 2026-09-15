-- Imscribing/Millennium/Erdos/MonochromaticOddCycle.lean
-- Monochromatic odd cycle in K_{2ⁿ+1} (q609)
--
-- One problem, one file. Split out of ErdosProblems.lean, which had grown to
-- 2160 lines carrying fifteen problems and nine synthesis sections at once.
-- Author: Lando⊗⊙perator

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Millennium.Erdos.Base
import Mathlib.Tactic
import Mathlib.Data.Fintype.Pi

namespace Millennium.ErdosProblems
open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

-- ============================================================
-- §22  MONOCHROMATIC ODD CYCLE IN K_{2ⁿ+1} (q609)
-- ============================================================

/-!
**MoDoT Broadcast (q609):** mOMonadOS kernel, crystal FS: 2192 records.
SELECTIVITY: model=B FFUSE gate=B→B, conflict d=0, match 2/3, collisions 1/2.

**Problem:** Let f(n) be the minimal length of a monochromatic odd cycle
guaranteed in any n-coloring of K_{2ⁿ+1}. What is f(n)?

**Kernel Claim:** f(n)=3 for all n.
  Proof sketch: If all n color classes were bipartite, χ(K_{2ⁿ+1})≤2ⁿ,
  but χ(K_{2ⁿ+1})=2ⁿ+1>2ⁿ, contradiction. Thus some color class is
  non-bipartite → contains an odd cycle → shortest odd cycle is C₃.

**Mathematical Correction:** The kernel's claim is incorrect for n≥2.
  f(1)=3: K₃ with 1 color forces monochromatic C₃.
  f(2)=5: R(3,3)=6, so K₅ CAN be 2-colored without monochromatic C₃.
    The unique such coloring: each color class is C₅. Shortest
    monochromatic odd cycle = C₅ (length 5).
  f(n)≤5 for all n≥2 (Bondy 1971).
  For n≥3: R_n(3)≫2ⁿ+1 (for n=3, R₃(3)=17>9), so triangles are
  avoidable. Likely f(n)=5 for all n≥2, but exact values are open.

  The kernel's bipartite argument correctly forces a monochromatic odd
  cycle to exist, but does NOT force that cycle to be a triangle.
  The Bondy bound gives f(n)≤5; the lower bound f(2)≥5 is tight.
  The kernel conflates "odd cycle exists" with "triangle exists."

  Tier: O₁ (critical, no topological protection). Belnap: B, but
  carried by the OPEN question, not by a conflict. The claim f(n)=3 is
  F: `col5` is a 2-colouring of K₅ with no monochromatic triangle, so
  it is refuted, not held. B is for a conflict both of whose sides
  stand; a claim with a counterexample does not stand. What remains
  open — and carries the B on the obstructional branch alone — is
  whether f(n)=5 for every n ≥ 3. See §22.4.

  This is O₁: roar criticality (the Bondy threshold is a critical
  Ramsey-type transition) but no Ω-protection (the odd cycle length
  is not topologically protected).
-/

def monochromatic_odd_cycle_k2n1 : Imscription :=
  Imscription.mk
    (.ash)     -- D: finite (K_{2ⁿ+1})
    (.eat)     -- T: inclusion (color classes are spanning subgraphs)
    (.ado)     -- R: supervenient
    (.church)  -- P: no symmetry
    (.age)     -- F: classical (Bondy-Erdős, 1971)
    (.egg)     -- K: non-equilibrium
    (.ice)     -- G: maximal/global (complete graph K_N)
    (.measure) -- Γ: sequential
    (.roar)    -- φ̂: complex critical (Bondy threshold)
    (.kick)    -- H: Markov order 1
    (.hung)    -- Σ: 1:1
    (.awe)     -- Ω: trivial protection

theorem monochromatic_odd_cycle_tier_is_O1 : imscriptionTier monochromatic_odd_cycle_k2n1 = .O₁ := by
  unfold monochromatic_odd_cycle_k2n1; native_decide


-- ============================================================
-- §22.1  THE BIPARTITE ARGUMENT, IN FULL GENERALITY
-- ============================================================

/-!
The half of the kernel's claim that is correct: if every colour class is
bipartite, the classes can be multiplied together into a proper
`2^n`-colouring, so a complete graph on more than `2^n` vertices must have
a non-bipartite class. Stated below for arbitrary `N` and `n`, with the
bipartition of each class given as a side-function.
-/

/-- Each colour class is bipartite, witnessed by `side i` splitting the
vertices so that no edge of colour `i` stays inside a part. -/
def ClassesBipartite {N n : ℕ} (col : Fin N → Fin N → Fin n) (side : Fin n → Fin N → Bool) : Prop :=
  ∀ u v : Fin N, u ≠ v → side (col u v) u ≠ side (col u v) v

/-- **The product colouring separates vertices.** Two vertices agreeing on
every side-function would have their own edge inside a part of that edge's
own colour class. This is the whole content of the bipartite argument, and
it needs no graph theory: it is injectivity of `v ↦ (side · v)`. -/
theorem product_injective {N n : ℕ} {col : Fin N → Fin N → Fin n}
    {side : Fin n → Fin N → Bool} (h : ClassesBipartite col side) :
    Function.Injective (fun v : Fin N => fun i : Fin n => side i v) := by
  intro u v huv
  by_contra hne
  exact h u v hne (congrFun huv (col u v))

/-- **`N ≤ 2^n` when every class is bipartite.** So on `K_{2^n+1}` some
class is NOT bipartite, and therefore contains an odd cycle. -/
theorem card_le_of_classes_bipartite {N n : ℕ} {col : Fin N → Fin N → Fin n}
    {side : Fin n → Fin N → Bool} (h : ClassesBipartite col side) : N ≤ 2 ^ n := by
  have := Fintype.card_le_of_injective _ (product_injective h)
  simpa using this

/-- The contrapositive, which is the statement the kernel wanted: on more
than `2^n` vertices no side-assignment can make every class bipartite. -/
theorem some_class_not_bipartite {N n : ℕ} (col : Fin N → Fin N → Fin n) (hN : 2 ^ n < N) :
    ¬ ∃ side : Fin n → Fin N → Bool, ClassesBipartite col side := by
  rintro ⟨side, h⟩
  exact absurd (card_le_of_classes_bipartite h) (by omega)

-- ============================================================
-- §22.2  ODD CYCLE IS NOT TRIANGLE — THE K₅ WITNESS
-- ============================================================

/-!
That argument produces an odd cycle and stops there. The kernel's claim
`f(n) = 3` needs the cycle to be a TRIANGLE, and nothing above delivers
one. At `n = 2` the gap is visible at once: `K_{2²+1} = K₅` has a
2-colouring with no monochromatic triangle at all, both classes being
5-cycles. The shortest monochromatic odd cycle is then `C₅`, so
`f(2) = 5`, not 3.
-/

/-- Colour 0 is the pentagon `i ~ i±1`, colour 1 the pentagram `i ~ i±2`.
Together they are all ten edges of `K₅`. -/
def col5 (i j : Nat) : Bool := (j + 5 - i) % 5 == 1 || (j + 5 - i) % 5 == 4

/-- The two classes partition the edges: every pair gets exactly one
colour, and the colouring is symmetric. -/
theorem col5_symm :
    ((List.range 5).all fun i => (List.range 5).all fun j =>
      (i == j) || (col5 i j == col5 j i)) = true := by decide

/-- **No monochromatic triangle in `K₅`.** Both classes are triangle-free —
each is a 5-cycle. -/
theorem col5_no_mono_triangle :
    ((List.range 5).all fun i => (List.range 5).all fun j =>
      (List.range 5).all fun k =>
        (i == j) || (j == k) || (i == k) ||
        !((col5 i j == col5 j k) && (col5 j k == col5 i k))) = true := by decide

/-- Each class is 2-regular, which with triangle-freeness on five vertices
makes each one a 5-cycle: the shortest monochromatic odd cycle is `C₅`. -/
theorem col5_classes_two_regular :
    ((List.range 5).all fun i =>
      (((List.range 5).filter fun j => j != i && col5 i j).length == 2) &&
      (((List.range 5).filter fun j => j != i && !col5 i j).length == 2)) = true := by decide

-- ============================================================
-- §22.3  AND K₆ IS WHERE THE TRIANGLE APPEARS — R(3,3) = 6
-- ============================================================

/-- Pair index in the upper triangle of `K₆`: fifteen edges. -/
def pidx6' (i j : Nat) : Nat := i * (11 - i) / 2 + (j - i - 1)

/-- The colour of edge `ij` in the 2-colouring encoded by the bits of `b`. -/
def col6 (b i j : Nat) : Bool :=
  if i < j then (b >>> pidx6' i j) % 2 == 1 else (b >>> pidx6' j i) % 2 == 1

theorem col6_symm (b i j : Nat) (h : i < j) : col6 b i j = col6 b j i := by
  have hj : ¬ j < i := by omega
  simp [col6, h, hj]

def hasMonoTriangle6 (b : Nat) : Bool :=
  (List.range 6).any fun i => (List.range 6).any fun j => (List.range 6).any fun k =>
    i < j && j < k && (col6 b i j == col6 b j k) && (col6 b j k == col6 b i k)

/-- **`R(3,3) ≤ 6`**: every one of the `2^15` two-colourings of `K₆` has a
monochromatic triangle. With `col5_no_mono_triangle` giving `R(3,3) > 5`,
this pins `R(3,3) = 6` — and `2² + 1 = 5 < 6` is exactly why `K₅` escapes. -/
theorem all_colourings_K6_have_mono_triangle :
    ((List.range 32768).all fun b => hasMonoTriangle6 b) = true := by native_decide

-- ============================================================
-- §22.4  A REFUTED CLAIM IS F, NOT B
-- ============================================================

/-!
The verdict recorded here was `B`, on the ground that "the kernel claim
(f=3, structural branch) conflicts with the mathematical correction
(f(2)=5, obstructional branch)" and that the FFUSE gate "fuses them to B —
dialetheia held, not resolved".

It is not a dialetheia. The file's own text says why, two paragraphs
earlier: the kernel "conflates 'odd cycle exists' with 'triangle exists'".
That is a diagnosis of an ERROR, and the error is exhibited — `col5` is a
2-colouring of `K₅` with no monochromatic triangle, so `f(2) = 3` is false.
B is for a conflict both of whose sides stand. A claim with a
counterexample does not stand, and recording it at B keeps a refuted
statement half-alive.

The branch verdicts here read T/T/T, under a B, with the third branch being
the correction that contradicts the first. The claim `f(n) = 3` is F, and
the surviving open question — whether `f(n) = 5` for every `n ≥ 3` — is what
carries the B, on the obstructional branch alone.
-/

/-- The refuted claim, and its counterexample, in one place. `f(2) = 3`
would need a monochromatic triangle in every 2-colouring of `K₅`; `col5`
is one without. -/
theorem kernel_claim_f_eq_three_is_false :
    ((List.range 5).all fun i => (List.range 5).all fun j =>
      (List.range 5).all fun k =>
        (i == j) || (j == k) || (i == k) ||
        !((col5 i j == col5 j k) && (col5 j k == col5 i k))) = true :=
  col5_no_mono_triangle

#print axioms card_le_of_classes_bipartite
#print axioms col5_no_mono_triangle
#print axioms all_colourings_K6_have_mono_triangle

/-- B, carried by the obstructional branch alone: f(n) is open for n ≥ 3.
The structural claim f(n)=3 is F, refuted by `col5`. -/
def monochromatic_odd_cycle_belnap_verdict : String := "B"

def monochromatic_odd_cycle_branch_verdicts : List (FsplitBranch × String) :=
  [(FsplitBranch.structural, "F"),
   (FsplitBranch.statistical, "T"),
   (FsplitBranch.obstructional, "B")]

def monochromatic_odd_cycle_selectivity_report : String :=
  "model=B FFUSE_gate=B->B conflict_d=0 match_2/3 collisions_1/2"

def monochromatic_odd_cycle_known_results : List (Bool × String) :=
  [(true,  "f(1)=3: K₃ with 1 color forces monochromatic C₃"),
   (true,  "f(2)=5: col5 avoids monochromatic C₃ on K₅, and every"),
   (true,  "  2-colouring of K₆ has one — R(3,3)=6, both halves checked"),
   (true,  "Every class bipartite forces N ≤ 2ⁿ (card_le_of_classes_bipartite)"),
   (true,  "Bondy (1971): f(n)≤5 for all n≥2"),
   (true,  "f(n)≥3 trivially (shortest odd cycle is C₃)"),
   (false, "Exact value of f(n) for n≥3: f(3)=3 or 5?"),
   (false, "R_n(3): can K_{2ⁿ+1} with n=3 (K₉) avoid C₃?"),
   (false, "Asymptotics of minimal odd cycle in n-colorings of K_N")]

def monochromatic_odd_cycle_kernel_output : String :=
  "f(n)=3 is REFUTED at n=2 by col5. f(1)=3, f(2)=5, f(n)≤5 for n≥2 (Bondy 1971)."

/-- What was a `: True` placeholder now names the two halves that pin
`f(2) = 5`: `K₅` escapes the triangle and `K₆` cannot. -/
theorem r33_eq_six :
    ((List.range 5).all fun i => (List.range 5).all fun j =>
      (List.range 5).all fun k =>
        (i == j) || (j == k) || (i == k) ||
        !((col5 i j == col5 j k) && (col5 j k == col5 i k))) = true ∧
    ((List.range 32768).all fun b => hasMonoTriangle6 b) = true :=
  ⟨col5_no_mono_triangle, all_colourings_K6_have_mono_triangle⟩

end Millennium.ErdosProblems
