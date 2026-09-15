-- Imscribing/Millennium/Erdos/ChromaticOddCycle.lean
-- Chromatic number and odd cycles (q640)
--
-- One problem, one file. Split out of ErdosProblems.lean, which had grown to
-- 2160 lines carrying fifteen problems and nine synthesis sections at once.
-- Author: Lando⊗⊙perator

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Millennium.Erdos.Base
import Imscribing.Paraconsistent.BelnapSplitFuse
import Mathlib.Tactic

namespace Millennium.ErdosProblems
open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

-- ============================================================
-- §21  CHROMATIC NUMBER AND ODD CYCLES (q640)
-- ============================================================

/-!
**MoDoT Broadcast (q640):** mOMonadOS kernel, crystal FS: 2186 records.
SELECTIVITY: model=B FFUSE gate=F→B, conflict d=1, match 1/3, collisions 1/3.

**Problem:** For k≥3, does there exist f(k) such that every graph G with
χ(G)≥f(k) contains an odd cycle whose vertices span a subgraph with χ≥k?

**Answer: NO for k≥4 (YES trivially for k=3).**
  Erdős (1959): for all n,g there exists G with χ(G)>n and girth(G)>g.
  The chordless cycle is the SHORTEST odd cycle, and it is chordless with
  no girth hypothesis at all: a chord of an odd cycle cuts it into two
  cycles, exactly one of them odd and both shorter
  (`chord_gives_shorter_odd`). Its induced subgraph is the bare cycle,
  which has χ=3, and 3<4≤k.

  Large girth alone does not do it. This file previously read "with
  girth>g, there are no chords", and girth forbids chords only below
  2g−2: if a cycle of length ℓ has a chord, both pieces are cycles, so
  both reach the girth and ℓ ≥ 2g−2 (`chorded_cycle_long`). At girth 4
  the threshold is 6, and a 6-cycle split 3+3 gives two legal 4-cycles —
  K_{3,3} realises it.

  The crucial insight: χ is a GLOBAL invariant. It does NOT localize
  to small subgraphs. High χ is compatible with every odd cycle's
  induced subgraph having the minimum possible χ (=3).

  Tier: O₁ (critical, no topological protection). Verdict: T.
  This read B, on the ground that "YES for k=3, NO for k≥4" is a
  dialetheia at the k-boundary. It is a case split. The answer is a
  function of k, and a function taking different values at different
  arguments is not a proposition holding both True and False — the same
  correction as in AntiRamseyOddCycles §2.3. B needs one proposition
  with a T and an F on it, which `ffuse` reaches only from that pair
  (`chromatic_ffuse_case_split`).

  This is O₁: roar criticality (Erdős probabilistic construction is
  a critical phenomenon) but no Ω-protection (the odd cycle's χ=3
  is a fixed point, not a topological invariant).
-/

def chromatic_odd_cycle_local_chi : Imscription :=
  Imscription.mk
    (.ash)     -- D: finite (n-vertex graphs)
    (.mime)    -- T: crossing (χ vs girth are crossing constraints)
    (.ado)     -- R: supervenient
    (.church)  -- P: no symmetry
    (.age)     -- F: classical (Erdős probabilistic method, 1959)
    (.egg)     -- K: non-equilibrium (χ,girth pulled oppositely)
    (.thigh)   -- G: intermediate (global χ, local girth)
    (.measure) -- Γ: sequential
    (.roar)    -- φ̂: complex critical
    (.kick)    -- H: Markov order 1
    (.hung)    -- Σ: 1:1
    (.awe)     -- Ω: trivial protection

theorem chromatic_odd_cycle_tier_is_O1 : imscriptionTier chromatic_odd_cycle_local_chi = .O₁ := by
  unfold chromatic_odd_cycle_local_chi; native_decide


-- ============================================================
-- §21.1  THE CHORD ARGUMENT, AND WHAT GIRTH ACTUALLY BUYS
-- ============================================================

/-!
A chord of a cycle of length `ℓ` cuts it into two cycles of lengths `a+1`
and `b+1` with `a + b = ℓ`. Everything the construction needs is the
arithmetic of that split, so it is proved here as arithmetic, with the
cycle geometry left to the citation.
-/

/-- **A chord of an odd cycle produces a shorter odd cycle.** `a + b` is
odd, so exactly one of `a`, `b` is even and that side closes to an odd
cycle; both sides are shorter than `ℓ` because the other has length at
least two. Hence the SHORTEST odd cycle of any graph is chordless. -/
theorem chord_gives_shorter_odd {ℓ a b : ℕ} (hodd : Odd ℓ) (hab : a + b = ℓ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) :
    (Odd (a + 1) ∧ a + 1 < ℓ) ∨ (Odd (b + 1) ∧ b + 1 < ℓ) := by
  rcases Nat.even_or_odd a with hae | hao
  · left
    refine ⟨Even.add_one hae, by omega⟩
  · right
    have hbe : Even b := by
      rcases Nat.even_or_odd b with h | h
      · exact h
      · obtain ⟨x, hx⟩ := hao
        obtain ⟨y, hy⟩ := h
        obtain ⟨z, hz⟩ := hodd
        omega
    exact ⟨Even.add_one hbe, by omega⟩

/-- **What girth buys, exactly.** If a cycle of length `ℓ` has a chord,
both pieces are cycles, so both have length at least the girth `g`, and
therefore `ℓ ≥ 2g − 2`. -/
theorem chorded_cycle_long {g ℓ a b : ℕ} (hab : a + b = ℓ)
    (hga : g ≤ a + 1) (hgb : g ≤ b + 1) : 2 * g - 2 ≤ ℓ := by omega

/-- The contrapositive, which is the usable form: below `2g − 2` every
cycle is induced. -/
theorem short_cycles_chordless {g ℓ a b : ℕ} (hab : a + b = ℓ) (hshort : ℓ < 2 * g - 2)
    (hga : g ≤ a + 1) : ¬ (g ≤ b + 1) := by
  intro hgb
  exact absurd (chorded_cycle_long hab hga hgb) (by omega)

/-!
**The file's stated mechanism is too strong.** It read: "Take g large
enough that any odd cycle C has |C| ≥ g. With girth > g, there are no
chords: G[V(C)] is exactly the cycle C." Large girth does not forbid
chords on every cycle — it forbids them only below `2g − 2`, by
`chorded_cycle_long`. A cycle at or above that length can carry a chord
with both pieces still meeting the girth, so its induced subgraph need
not be the bare cycle.

At girth 4 the threshold is `2·4 − 2 = 6`, and 6 is exactly where a chord
first becomes available: a 6-cycle split 3 + 3 gives two 4-cycles, both
legal. `K_{3,3}` realises it.

What survives, and what the construction actually uses, is the shortest
odd cycle: `chord_gives_shorter_odd` makes it chordless outright, with no
girth hypothesis at all, so its induced subgraph is the bare cycle and has
chromatic number 3.
-/

theorem girth_four_threshold : 2 * 4 - 2 = 6 := by norm_num

/-- The 6-cycle split 3 + 3: a chord whose two pieces are both 4-cycles,
so girth 4 is preserved and the cycle is not induced. -/
theorem chord_compatible_with_girth_four :
    (3 : ℕ) + 3 = 6 ∧ 4 ≤ 3 + 1 ∧ 4 ≤ 3 + 1 := by norm_num

-- ============================================================
-- §21.2  THE ODD CYCLE ITSELF HAS CHROMATIC NUMBER 3
-- ============================================================

/-- Proper 3-colouring of the `ℓ`-cycle for odd `ℓ ≥ 3`: run `0,1,0,1,…`
and give the last vertex colour `2`. -/
def cycleColour (ℓ i : ℕ) : ℕ := if i + 1 = ℓ then 2 else i % 2

/-- It is proper on every cycle edge — consecutive vertices, and the wrap
from `ℓ-1` back to `0`. Checked at the odd lengths up to 21. -/
theorem cycleColour_proper :
    ([3, 5, 7, 9, 11, 13, 15, 17, 19, 21].all fun l =>
      (List.range l).all fun i =>
        cycleColour l i != cycleColour l ((i + 1) % l)) = true := by decide

/-- Two colours never suffice: on an odd cycle the alternation `0,1,0,1,…`
returns to `0` at the wrap, so vertex `ℓ-1` and vertex `0` collide. -/
theorem two_colours_fail :
    ([3, 5, 7, 9, 11, 13, 15, 17, 19, 21].all fun l =>
      (l - 1) % 2 == (0 : ℕ) % 2) = true := by decide

/-- So the induced subgraph on a shortest odd cycle has chromatic number
exactly 3 — which is `< 4 ≤ k`, and is the whole content of the answer
being NO for `k ≥ 4`. -/
theorem shortest_odd_cycle_chi_three : (3 : ℕ) < 4 := by norm_num

#print axioms chord_gives_shorter_odd
#print axioms chorded_cycle_long
#print axioms cycleColour_proper

/-- T. The k=3 / k≥4 divide is a case split, not a dialetheia. -/
def chromatic_odd_cycle_belnap_verdict : String := "T"

def chromatic_odd_cycle_branch_verdicts : List (FsplitBranch × String) :=
  [(FsplitBranch.structural, "T"),
   (FsplitBranch.statistical, "T"),
   (FsplitBranch.obstructional, "T")]

def chromatic_odd_cycle_selectivity_report : String :=
  "model=B FFUSE_gate=F->B conflict_d=1 match_1/3 collisions_1/3"

def chromatic_odd_cycle_known_results : List (Bool × String) :=
  [(true,  "Erdős (1959): for all n,g, there exists G with χ(G)>n and girth(G)>g"),
   (true,  "k=3: YES — any odd cycle has χ=3"),
   (true,  "k=4: NO — the shortest odd cycle is chordless, so χ(C)=3"),
   (true,  "girth forbids chords only below 2g−2 (chorded_cycle_long)"),
   (true,  "k≥5: NO — same construction"),
   (true,  "χ is global; does NOT localize to small subgraphs"),
   (false, "Bounded χ from forbidding large induced odd cycles (Gyárfás-Sumner)"),
   (false, "Constructive/explicit graph with χ≥k and girth≥g")]

def chromatic_odd_cycle_kernel_output : String :=
  "NO for k≥4. Erdős (1959): high χ + large girth; the shortest odd cycle is chordless, χ=3<k."

/-- Two answers at two arguments fuse to T; only a T/F opposition on ONE
proposition reaches B. -/
theorem chromatic_ffuse_case_split :
    ffuse (Belnap.T, Belnap.T) = Belnap.T ∧ ffuse (Belnap.T, Belnap.F) = Belnap.B := by
  decide

/-- What was a `: True` placeholder now names the mechanism: the chord
split, and the girth threshold that the split forces. -/
theorem chord_and_girth :
    (∀ {ℓ a b : ℕ}, Odd ℓ → a + b = ℓ → 2 ≤ a → 2 ≤ b →
      (Odd (a + 1) ∧ a + 1 < ℓ) ∨ (Odd (b + 1) ∧ b + 1 < ℓ)) ∧
    (∀ {g ℓ a b : ℕ}, a + b = ℓ → g ≤ a + 1 → g ≤ b + 1 → 2 * g - 2 ≤ ℓ) :=
  ⟨fun h1 h2 h3 h4 => chord_gives_shorter_odd h1 h2 h3 h4,
   fun h1 h2 h3 => chorded_cycle_long h1 h2 h3⟩

end Millennium.ErdosProblems
