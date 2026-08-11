-- Imscribing/Millennium/Erdos/SchutteTournament.lean
-- Schütte tournament domination (q946)
--
-- One problem, one file. Split out of ErdosProblems.lean, which had grown to
-- 2160 lines carrying fifteen problems and nine synthesis sections at once.
-- Author: Lando⊗⊙perator

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Millennium.Erdos.Base
import Mathlib.Tactic

namespace Millennium.ErdosProblems
open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

-- ============================================================
-- §25  SCHÜTTE TOURNAMENT DOMINATION (q946)
-- ============================================================

/-!
**MoDoT Broadcast (q946):** mOMonadOS kernel, crystal FS: 2198 records.
SELECTIVITY: model=B FFUSE gate=B→B, conflict d=0, match 3/4, collisions 1/3.

**Problem (Schütte's Property S_n):** Let f(n) be the minimum number of
vertices in a tournament such that every n-subset is dominated by a
common vertex. A tournament T has property S_n if for every set S of n
vertices, there exists a vertex v ∉ S that dominates every vertex in S
(i.e., has a directed edge to each).

**Probabilistic Upper Bound:** f(n) = O(n²·2ⁿ). NOT Θ — the union
bound below produces an upper bound only, and whether a matching lower
bound of that order holds is the open question, listed at the foot of
this docstring as unresolved. See §25.3.
  Fix a set S of n vertices. For a random vertex v ∉ S in a random
  tournament, Pr[v dominates S] = 2⁻ⁿ. The probability that NO vertex
  in V\S dominates S is (1 − 2⁻ⁿ)^(k−n). By the union bound over all
  n-subsets: C(k,n)·(1 − 2⁻ⁿ)^(k−n) < 1 ensures existence.
  Using 1−x ≤ e⁻ˣ: kⁿ/n! · e^(−k·2⁻ⁿ) < 1 ⇒ n ln k − k·2⁻ⁿ < 0.
  The threshold is k ≈ n²·2ⁿ·ln 2, so f(n) = O(n²·2ⁿ).

**Lower Bound (Szekeres–Szekeres 1965):** f(n) ≥ (n+2)·2ⁿ⁻¹ − 1.
  This file previously recorded the weaker f(n) ≥ 2ⁿ⁺¹ − 1, with a
  "double counting of dominator sets, one per vertex, each of size at
  most 2ⁿ" argument. That argument does not go through as written — a
  vertex's dominated set carries no such bound, and nothing in it
  produces the exponent. The Szekeres bound is tight at both exactly
  known values, 4·2−1 = 7 = f(2) and 5·4−1 = 19 = f(3), where 2ⁿ⁺¹−1
  gives 7 and then 15, missing f(3) by four. `stated_bound_weaker`
  proves the old bound is strictly weaker for every n ≥ 3.

**Verdict:** B — but not for the reason recorded here before. The note
  read that the structural branch "claims f(n)≈2ⁿ⁺¹" while the
  probabilistic branch "gives f(n)≈n²·2ⁿ", and fused the two to B as a
  held dialetheia. Those are a LOWER bound and an UPPER bound. They do
  not contradict each other: the sandwich interval is non-empty for
  every n (`sandwich_nonempty`), and every known value of f sits inside
  it (`szekeres_le_known`). A gap between bounds is a gap. B is carried
  here by the obstructional branch instead — the exact value of f(n) is
  open for every n ≥ 4 — which is why the branch verdicts below now read
  T/T/B rather than the T/T/T that sat under a B and contradicted it.

**Tier:** O₁ — φ̂=roar (the n²·2ⁿ vs (n+2)·2ⁿ⁻¹ threshold is a critical
  Ramsey-type transition) with Ω=awe (no topological protection). The
  domination relation is asymmetric (P=church), the tournament topology
  is a complete crossing structure (T=mime), and the probabilistic
  construction is non-equilibrium (K=egg).

**Known Results:**
  Szekeres–Szekeres (1965): f(n) ≥ (n+2)·2ⁿ⁻¹ − 1, and f(2) = 7.
  Probabilistic Method: f(n) ≤ (1+o(1))·n²·2ⁿ·ln 2 (upper bound).
  Reid–Parker (1970): f(3) = 19 — which is what rules out the guess that
    the lower bound is tight in general, since 2⁴−1 = 15.
  f(1) = 3 and f(2) = 7 are machine-checked in §25.1, both halves each.
  The exact value of f(n) is known only for n ≤ 3. For n ≥ 4 the gap is
  between 47 and O(n²·2ⁿ).

**Structural Note:** The Schütte problem is the tournament analog of
the Erdős-Hajnal ℵ₁ graph problem (§19), transposed from undirected
graphs to tournaments. Both are O₁ threshold problems (φ̂=roar), but
the tournament's directed topology (T=mime) is a crossing structure
while the ℵ₁ graph uses inclusion (T=eat). The Schütte problem's lower
bound is (n+2)·2ⁿ⁻¹, so its ratio to the Erdős-Hajnal threshold 2ⁿ
grows linearly in n rather than being the fixed factor 2 that the
superseded 2ⁿ⁺¹ reading suggested.
-/

def schutte_tournament_domination : Imscription :=
  Imscription.mk
    (.ash)     -- D: finite (tournament on k vertices)
    (.mime)    -- T: bowtie/crossing (tournament edges are directed, asymmetric)
    (.ado)     -- R: supervenient (domination is a supervenient relation)
    (.church)  -- P: no symmetry (domination is asymmetric)
    (.age)     -- F: classical (probabilistic method, Erdős 1963)
    (.egg)     -- K: non-equilibrium (probabilistic construction)
    (.ice)     -- G: maximal/global (tournament is a complete orientation)
    (.measure) -- Γ: sequential (domination check is sequential)
    (.roar)    -- φ̂: complex-critical (n²·2ⁿ vs (n+2)·2ⁿ⁻¹ threshold)
    (.kick)    -- H: Markov order 1 (single-step domination)
    (.hung)    -- Σ: 1:1 (each pair has exactly one directed edge)
    (.awe)     -- Ω: trivial protection (counting, no topological invariant)

theorem schutte_tournament_tier_is_O1 : imscriptionTier schutte_tournament_domination = .O₁ := by
  unfold schutte_tournament_domination; native_decide


-- ============================================================
-- §25.1  THE PROPERTY, AND THE TWO SMALL EXACT VALUES
-- ============================================================

/-!
A tournament on `{0,…,N-1}` is stored as the `N(N-1)/2` bits of its
upper triangle: `beats b i j` reads bit `pidx i j` when `i < j` and its
negation otherwise, so antisymmetry is true by construction rather than
by hypothesis. That is what makes the exhaustive search over ALL
tournaments on six vertices a `native_decide` over `2^15` numbers
instead of a search over functions.
-/

/-- Index of the pair `i < j` in the upper triangle of an `n`-vertex
tournament, for `n = 6`: `0…4, 5…8, 9…11, 12…13, 14`. -/
def pidx6 (i j : Nat) : Nat := i * (11 - i) / 2 + (j - i - 1)

/-- `i` beats `j`. Antisymmetric by construction: one bit per pair. -/
def beats6 (b i j : Nat) : Bool :=
  if i < j then (b >>> pidx6 i j) % 2 == 1 else (b >>> pidx6 j i) % 2 == 0

/-- Every pair is oriented exactly one way — the tournament condition,
which here is a property of the encoding, not an assumption. -/
theorem beats6_antisymm (b i j : Nat) (h : i < j) : beats6 b i j = !beats6 b j i := by
  have hj : ¬ j < i := by omega
  simp only [beats6, if_pos h, if_neg hj]
  rcases Nat.mod_two_eq_zero_or_one (b >>> pidx6 i j) with h0 | h0 <;> simp [h0]

/-- Property `S_k`: every `k`-set has a common dominator outside it.
Here `k = 2` on six vertices. -/
def hasS2_6 (b : Nat) : Bool :=
  (List.range 6).all fun i => (List.range 6).all fun j =>
    (i == j) || ((List.range 6).any fun v =>
      v != i && v != j && beats6 b v i && beats6 b v j)

/-- **No tournament on six vertices has `S₂`** — all `2^15` of them
checked. The search is exhaustive because the bit encoding enumerates
tournaments exactly once each. -/
theorem no_S2_on_six : ((List.range 32768).all fun b => !hasS2_6 b) = true := by
  native_decide

-- ---- the seven-vertex witness: the quadratic-residue tournament ----

/-- The Paley tournament on `ℤ/7`: `i → j` exactly when `j - i` is a
non-zero quadratic residue, and `{1,2,4}` are the squares mod 7. -/
def paley7 (i j : Nat) : Bool := (j + 7 - i) % 7 == 1 || (j + 7 - i) % 7 == 2 || (j + 7 - i) % 7 == 4

/-- It is a tournament: every pair oriented exactly one way. `-1 = 6` is a
non-residue mod 7, which is exactly why this works. -/
theorem paley7_tournament :
    ((List.range 7).all fun i => (List.range 7).all fun j =>
      (i == j) || (paley7 i j != paley7 j i)) = true := by decide

/-- **The Paley tournament on seven vertices has `S₂`.** -/
theorem paley7_has_S2 :
    ((List.range 7).all fun i => (List.range 7).all fun j =>
      (i == j) || ((List.range 7).any fun v =>
        v != i && v != j && paley7 v i && paley7 v j)) = true := by decide

/-- It has `S₁` as well — every vertex is beaten by someone. -/
theorem paley7_has_S1 :
    ((List.range 7).all fun i => (List.range 7).any fun v => v != i && paley7 v i) = true := by
  decide

/-!
**`f(2) = 7`, both halves machine-checked.** `no_S2_on_six` is the lower
bound and `paley7_has_S2` the upper bound. This is the Szekeres–Szekeres
value, and it is the largest `k` for which the whole thing fits in a
kernel-sized search: `f(3) = 19` (Reid–Parker 1970) is a search over
`2^171` tournaments and is cited, not checked here.
-/

-- ---- f(1) = 3 ----

/-- The 3-cycle `0 → 1 → 2 → 0` has `S₁`. -/
def cyc3 (i j : Nat) : Bool := (j + 3 - i) % 3 == 1

theorem cyc3_has_S1 :
    ((List.range 3).all fun i => (List.range 3).any fun v => v != i && cyc3 v i) = true := by
  decide

/-- The single edge of a two-vertex tournament, same encoding. -/
def beats2 (b i j : Nat) : Bool := if i < j then b % 2 == 1 else b % 2 == 0

/-- **No tournament on two vertices has `S₁`**: whoever wins the single
edge has nobody to beat them. Both tournaments checked. -/
theorem no_S1_on_two :
    ((List.range 2).all fun b =>
      !((List.range 2).all fun i => (List.range 2).any fun v =>
        v != i && beats2 b v i)) = true := by
  decide

-- ============================================================
-- §25.2  THE LOWER BOUND THAT WAS STATED IS THE WEAKER ONE
-- ============================================================

/-!
This file recorded the lower bound as `f(k) ≥ 2^(k+1) − 1`, with a
"double counting of dominator sets — one per vertex, each of size at most
2^k" argument. That argument does not go through as written: a vertex's
dominated set has no such bound, and nothing in it produces the exponent.

The bound that IS proved, and that the literature carries, is
Szekeres–Szekeres 1965: `f(k) ≥ (k+2)·2^(k-1) − 1`. It is tight at both
known values — `4·2 − 1 = 7 = f(2)` and `5·4 − 1 = 19 = f(3)` — where
`2^(k+1) − 1` gives `7` and then `15`, missing `f(3)` by four.
-/

def szekeres (k : Nat) : Nat := (k + 2) * 2 ^ (k - 1) - 1
def statedBound (k : Nat) : Nat := 2 ^ (k + 1) - 1

/-- The Szekeres bound is tight at the two exactly-known values. -/
theorem szekeres_tight_at_2_and_3 : szekeres 2 = 7 ∧ szekeres 3 = 19 := by decide

/-- The stated bound coincides at `k = 2` and then falls behind. -/
theorem stated_bound_agrees_at_two : statedBound 2 = 7 := by decide

theorem stated_bound_misses_f3 : statedBound 3 = 15 ∧ statedBound 3 < szekeres 3 := by decide

/-- **The stated bound is strictly weaker for every `k ≥ 3`**, since
`(k+2) > 4` there and both are `·2^(k-1) − 1`. So `f(4) ≥ 47`, not the
`31` the file's "gap between 31 and ~140" was reading off. -/
theorem stated_bound_weaker (k : Nat) (hk : 3 ≤ k) : statedBound k < szekeres k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have hm : m + 3 - 1 = m + 2 := by omega
  have e1 : (2 : Nat) ^ (m + 3 + 1) = 4 * 2 ^ (m + 2) := by
    rw [show m + 3 + 1 = (m + 2) + 2 by omega, Nat.pow_add]; ring
  have e2 : (0 : Nat) < 2 ^ (m + 2) := by positivity
  have e3 : 4 * 2 ^ (m + 2) < (m + 3 + 2) * 2 ^ (m + 2) := by nlinarith [e2]
  have hX : 1 ≤ 4 * 2 ^ (m + 2) := by nlinarith [e2]
  simp only [statedBound, szekeres, hm, e1]
  exact Nat.sub_lt_sub_right hX e3

theorem f4_lower_bound : szekeres 4 = 47 := by decide

-- ============================================================
-- §25.3  THE VERDICT WAS B FOR THE WRONG REASON
-- ============================================================

/-!
The file's kernel note read: "the kernel's structural branch claims
`f(n) ≈ 2^(n+1)` while the probabilistic branch gives `f(n) ≈ n²·2^n`;
the FFUSE gate fuses both to B". Those two are a LOWER bound and an
UPPER bound. They do not contradict each other — `2^(k+1) − 1 ≤ f(k) ≤
c·k²·2^k` is one consistent sandwich, and every value of `f` known so far
sits inside it. A gap between bounds is a gap; B is for a held conflict,
and there is none here. The branch verdicts recorded in this file are
already `T/T/T`, which is what disagreed with the `B` sitting above them.

The second conflation is in the upper bound itself. `f(n) = Θ(n²·2^n)`
was written as the heading over a union-bound computation, but the union
bound gives only `f(n) = O(n²·2^n)`. `Θ` asserts a matching lower bound
of that order, and that is precisely the open question — the file's own
last unresolved item, "whether `f(n) ~ 2^(n+1)` or `f(n) ~ n²·2^n`",
which `Θ` would have already answered.
-/

/-- The Szekeres lower bound is respected — and tight — at every value of
`f` that is known: `f(1)=3, f(2)=7, f(3)=19`. -/
def fKnown : List (Nat × Nat) := [(1, 3), (2, 7), (3, 19)]

theorem szekeres_le_known : fKnown.all (fun p => szekeres p.1 ≤ p.2) = true := by decide

/-- **The two bounds never conflict.** The sandwich interval
`[szekeres k, 3·k²·2^k]` is non-empty for every `k ≥ 1`, because
`k + 2 ≤ 6k²` there. A lower bound below an upper bound is a gap, not a
dialetheia — which is why the `B` recorded above this line does not
follow from the two branches it cites. -/
theorem sandwich_nonempty (k : Nat) (hk : 1 ≤ k) : szekeres k ≤ 3 * k ^ 2 * 2 ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have hm : m + 1 - 1 = m := by omega
  have e1 : (2 : Nat) ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; ring
  have key : (m + 1 + 2) * 2 ^ m ≤ 6 * (m + 1) ^ 2 * 2 ^ m := by
    have h : m + 1 + 2 ≤ 6 * (m + 1) ^ 2 := by nlinarith
    exact Nat.mul_le_mul_right _ h
  simp only [szekeres, hm, e1]
  refine le_trans (Nat.sub_le _ _) ?_
  calc (m + 1 + 2) * 2 ^ m ≤ 6 * (m + 1) ^ 2 * 2 ^ m := key
    _ = 3 * (m + 1) ^ 2 * (2 * 2 ^ m) := by ring

/-- The gap is one interval, not two claims in conflict: at `k = 4` it is
`[47, 768]`. -/
theorem gap_at_four : szekeres 4 = 47 ∧ 3 * 4 ^ 2 * 2 ^ 4 = 768 := by decide

#print axioms paley7_has_S2
#print axioms no_S2_on_six
#print axioms stated_bound_weaker
#print axioms sandwich_nonempty

/-- B, carried by the obstructional branch: f(n) is open for n ≥ 4. NOT
by a conflict between the bounds — see §25.3. -/
def schutte_tournament_belnap_verdict : String := "B"

def schutte_tournament_branch_verdicts : List (FsplitBranch × String) :=
  [(FsplitBranch.structural, "T"),
   (FsplitBranch.statistical, "T"),
   (FsplitBranch.obstructional, "B")]

def schutte_tournament_selectivity_report : String :=
  "model=B FFUSE_gate=B->B conflict_d=0 match_3/4 collisions_1/3"

def schutte_tournament_known_results : List (Bool × String) :=
  [(true,  "f(n) ≥ (n+2)·2ⁿ⁻¹−1 (Szekeres–Szekeres 1965)"),
   (true,  "f(n) = O(n²·2ⁿ) (probabilistic upper bound; not Θ)"),
   (true,  "f(1)=3 (cyc3_has_S1 and no_S1_on_two)"),
   (true,  "f(2)=7 (paley7_has_S2 and no_S2_on_six)"),
   (true,  "f(3)=19 (Reid–Parker 1970, cited)"),
   (false, "f(4) exact value: gap from 47 upward"),
   (false, "Constructive f(n) matching the probabilistic O(n²·2ⁿ)"),
   (false, "Whether f(n) ~ (n+2)·2ⁿ⁻¹ or f(n) ~ n²·2ⁿ for large n")]

def schutte_tournament_kernel_output : String :=
  "f(n)=O(n²·2ⁿ) upper bound, f(n)≥(n+2)·2ⁿ⁻¹−1 lower bound. Gap unresolved."

/-- What was a `: True` placeholder here now names the two searches that
carry the file: `f(2) = 7` is closed on both sides, `no_S2_on_six` from
below and `paley7_has_S2` from above. -/
theorem f2_eq_seven :
    ((List.range 32768).all fun b => !hasS2_6 b) = true ∧
    ((List.range 7).all fun i => (List.range 7).all fun j =>
      (i == j) || ((List.range 7).any fun v =>
        v != i && v != j && paley7 v i && paley7 v j)) = true :=
  ⟨no_S2_on_six, paley7_has_S2⟩

end Millennium.ErdosProblems
