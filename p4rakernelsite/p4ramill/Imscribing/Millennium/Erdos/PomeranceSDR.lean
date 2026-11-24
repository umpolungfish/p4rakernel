-- Imscribing/Millennium/Erdos/PomeranceSDR.lean
-- Erdős–Pomerance SDR interval, with the q5 rerun
--
-- One problem, one file. Split out of ErdosProblems.lean, which had grown to
-- 2160 lines carrying fifteen problems and nine synthesis sections at once.
-- Author: Lando⊗⊙perator

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Millennium.Erdos.Base
import Mathlib.Order.Interval.Finset.Nat

namespace Millennium.ErdosProblems
open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

-- ============================================================
-- §11  ERDŐS-POMERANCE PROBLEM — SDR interval for multiples
-- ============================================================

/-!
**Erdős-Pomerance Problem (1980):** `f(n,m)` is the least integer such
that the interval `(m, m+f(n,m)]` contains n distinct integers a_1,…,a_n
with i ∣ a_i for every i. It is a function of TWO arguments: the interval
length is not the only variable, WHERE the window sits matters, and that
is the whole problem.

This section previously defined a one-argument f(n) as the minimal length
over all intervals. That reading is trivial — see `SDRWindow` below, which
machine-checks that the window just above lcm(1,…,n) works and that no
window shorter than n can hold n distinct integers, so the minimum over
starting points is exactly n. The interesting quantities are f(n,n), the
window starting at n, and max_m f(n,m), the worst window.

**The Hall Marriage formulation:** There exist a_1,…,a_n all distinct
in I with k ∣ a_k iff the Hall condition holds: for every J ⊆ {1,…,n},
|⋃_{k∈J} {m : km ∈ I}| ≥ |J|.

**mOMonadOS Agent FSPLIT Decomposition (Cycle 9):**

  Branch 1 — Lower_Bound_Sieving (structural): The lower bound uses
    the Chinese Remainder Theorem to force overlap constraints.
    To prevent two indices k,j from claiming the same integer, the
    interval must be long enough to accommodate y-smooth number
    distributions. Result: f(n) ≥ (2/√e) n √(log n / log log n).

  Branch 2 — Upper_Bound_Hall_Marriage (statistical): The upper
    bound uses Hall's theorem with density estimates on the
    distribution of integers with large prime factors. Erdős-
    Pomerance (1980) bounded f(n) by analyzing integers with
    p > n/f(n). Result: f(n) ≲ c·n √(log n / log log n).

  Branch 3 — Matching_Asymptotics (obstructional): the upper and lower
    bounds do not match, so there is no constant c to name yet. The prize
    Erdős attached here (1000 rupees) was for a different question: that
    max_m f(n,m) − f(n,n) → ∞, i.e. that the worst window is genuinely
    worse than the window at n. That conjecture is now settled — see §17.

**Result:** the order of f(n,n) is NOT known. Erdős-Pomerance (1980) proved

    (2/√e + o(1))·n √(log n / log log n)  <  f(n,n)  <  (2 + o(1))·n √(log n)

and the two ends differ by a factor √(log log n). The section formerly
asserted f(n) ≍ n √(log n / log log n), which promotes their lower bound to
a matching order it does not have.

**Structural Imscription — erdos_pomerance_problem:**
  D=array (n→∞ asymptotic parameter)
  T=judge (irregular divisibility lattice on ℤ)
  R=ear (Hall marriage ↔ SDR existence duality)
  P=out (SDR exists / does not exist)
  F=peep (analytic NT precision: y-smooth number estimates)
  K=egg (slow: n √(log n/log log n) is barely superlinear)
  G=ice (global: all primes ≤ n contribute via CRT)
  Γ=measure (sequential: distribute 1,…,n across interval)
  φ̂=roar (complex-axis: Dickman ρ via Laplace transform in ℂ)
  H=sure (persistent chiral: k∣a_k is directed)
  Σ=hung (1:1: one interval → one SDR existence claim)
  Ω=ah (integer winding: interval length is an integer)
-/

-- ============================================================
-- §11.1  f(n,n) COMPUTED, AND HALL'S CONDITION AS THE MECHANISM
-- ============================================================

/-!
The window at `n` is the quantity Erdős–Pomerance bracket, and for small
`n` it can simply be found. The search is a backtracking matcher over the
divisibility candidates, which is Hall's theorem run constructively: an
SDR exists exactly when the walk with backtracking finds one.
-/

/-- Multiples of `i` inside the window `(n, n+L]`. -/
def cands (n L i : Nat) : List Nat :=
  ((List.range L).map (fun j => n + 1 + j)).filter (fun a => a % i == 0)

/-- Backtracking assignment: give each index a distinct multiple of itself
drawn from the window. -/
def matchFrom (n L : Nat) : List Nat → List Nat → Bool
  | _,    []        => true
  | used, i :: rest =>
      (cands n L i).any (fun a => !(used.contains a) && matchFrom n L (a :: used) rest)

/-- The window `(n, n+L]` admits a system of distinct representatives. -/
def hasSDR (n L : Nat) : Bool := matchFrom n L [] ((List.range n).map (· + 1))

/-- `f(n,n)`: the least window length at `n` that works. -/
def fnn (n : Nat) : Nat := ((List.range 40).find? (fun L => hasSDR n L)).getD 0

/-- **`f(n,n)` for `n = 1…9`**: 1, 2, 3, 5, 5, 8, 8, 10, 12. It parts from
`n` at `n = 4`. -/
theorem fnn_table :
    [fnn 1, fnn 2, fnn 3, fnn 4, fnn 5, fnn 6, fnn 7, fnn 8, fnn 9]
      = [1, 2, 3, 5, 5, 8, 8, 10, 12] := by native_decide

/-- The obstruction at `n = 4`, in the raw. The window `(4,8]` carries only
`6` and `8` as multiples of two; index 4 is forced onto `8` and index 2
takes `6`, leaving index 3 with nothing, since `6` was its only candidate.
The window has to reach 9. -/
theorem four_window_fails : hasSDR 4 4 = false := by native_decide

theorem four_window_works : hasSDR 4 5 = true := by native_decide

/-- `f(n,n) ≥ n` throughout: `n` distinct integers need `n` slots. -/
theorem fnn_ge_index_count :
    ([fnn 1, fnn 2, fnn 3, fnn 4, fnn 5, fnn 6, fnn 7, fnn 8, fnn 9].zip
      [1, 2, 3, 4, 5, 6, 7, 8, 9]).all (fun p => p.2 ≤ p.1) = true := by native_decide

/-- And strictly exceeds it from `n = 4` on — the superlinearity the
asymptotic bracket is about. -/
theorem fnn_exceeds_index_from_four :
    [(fnn 4, 4), (fnn 6, 6), (fnn 8, 8), (fnn 9, 9)].all
      (fun p => p.2 < p.1) = true := by native_decide

#print axioms fnn_table
#print axioms four_window_fails


/-! ### Which quantity is the problem, machine-checked

The statement above minimises over the interval as well as over its length, and
that reading is trivial: the window `(L, L+n]` sitting just above
`L = lcm(1,…,n)` already carries distinct multiples, namely `a_i = L + i`, and
no window shorter than `n` can hold `n` distinct integers. So the minimum over
starting points is exactly `n`, with no number theory in it at all.

The Erdős–Pomerance quantity is therefore not that minimum. It is `f(n,m)`, the
least length such that `(m, m+f(n,m)]` contains distinct multiples of `1,…,n` —
a function of WHERE the window sits. Both theorems below are about the easy
end of that function; they are here to fix which quantity the section is about.
-/

namespace SDRWindow

open Finset

/-- `lcmUpTo n = lcm(1,…,n)`, by recursion rather than through `Finset.lcm`,
which would drag in the `NormalizedGCDMonoid` machinery for no gain here. -/
def lcmUpTo : ℕ → ℕ
  | 0 => 1
  | (n + 1) => Nat.lcm (n + 1) (lcmUpTo n)

theorem dvd_lcmUpTo : ∀ {n i : ℕ}, i ∈ Finset.Icc 1 n → i ∣ lcmUpTo n := by
  intro n
  induction n with
  | zero => intro i hi; simp at hi
  | succ n ih =>
      intro i hi
      rw [Finset.mem_Icc] at hi
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · exact dvd_trans (ih (Finset.mem_Icc.2 ⟨hi.1, by omega⟩)) (Nat.dvd_lcm_right _ _)
      · have : i = n + 1 := by omega
        subst this
        exact Nat.dvd_lcm_left _ _

/-- **The window just above the lcm.** `a_i = lcm(1,…,n) + i` are `n` distinct
integers in an interval of length `n`, each divisible by its index: the minimum
over starting points is attained at once, so `min_m f(n,m) ≤ n`. -/
theorem exists_distinct_multiples_window (n : ℕ) :
    ∃ a : ℕ → ℕ, (∀ i ∈ Finset.Icc 1 n, i ∣ a i) ∧
      Set.InjOn a (Finset.Icc 1 n) ∧
      (∀ i ∈ Finset.Icc 1 n, lcmUpTo n < a i ∧ a i ≤ lcmUpTo n + n) := by
  refine ⟨fun i => lcmUpTo n + i, ?_, ?_, ?_⟩
  · intro i hi
    exact Nat.dvd_add (dvd_lcmUpTo hi) dvd_rfl
  · intro i _ j _ h
    dsimp only at h
    omega
  · intro i hi
    rw [Finset.mem_Icc] at hi
    dsimp only
    omega

/-- **And no shorter window works, anywhere.** `n` distinct integers need `n`
integer slots, so `f(n,m) ≥ n` for every `m` — the bound that makes the
construction above exactly optimal for the minimising reading. -/
theorem window_length_ge (n m len : ℕ) (a : ℕ → ℕ)
    (hinj : Set.InjOn a (Finset.Icc 1 n))
    (hmem : ∀ i ∈ Finset.Icc 1 n, m < a i ∧ a i ≤ m + len) :
    n ≤ len := by
  classical
  have hsub : (Finset.Icc 1 n).image a ⊆ Finset.Ioc m (m + len) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_Ioc.2 (hmem i hi)
  have hcard := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injOn hinj, Nat.card_Icc, Nat.card_Ioc,
    Nat.add_sub_cancel_left, Nat.add_sub_cancel] at hcard

#print axioms exists_distinct_multiples_window
#print axioms window_length_ge

end SDRWindow

/--
The Erdős-Pomerance SDR problem as an Imscription.
Tier: O₂dag — roar+ice+ah with judge topology.
-/
def erdos_pomerance_problem : Imscription :=
  { dim  := Dimensionality.array
    top  := Topology.judge
    rel  := Relational.ear
    pol  := Polarity.out
    fid  := Fidelity.peep
    kin  := KineticChar.egg
    gran := Granularity.ice
    gram := Grammar.measure
    crit := Criticality.roar
    chir := Chirality.sure
    stoi := Stoichiometry.hung
    prot := Protection.ah }

theorem erdos_pomerance_problem_tier : imscriptionTier erdos_pomerance_problem = .O₂dag := by
  unfold erdos_pomerance_problem; native_decide

/-!
**Why ice (global correlations)?** The SDR condition involves ALL
k=1,…,n simultaneously. The CRT couples primes across the entire
range [1,n], making the correlation range truly global (ice).
This contrasts with problems where only intermediate-range
correlations (thigh) suffice.

**mOMonadOS Agent Verdict:** Belnap **B** — and it survives the
correction, though not for the reason recorded. Not "order established,
constant open": the order of f(n,n) is itself open. What is True is the
max_m branch, settled by van Doorn in 2026; what is Neither is f(n,n),
where lower and upper bound differ by √(log log n).

**Known Results:**
  ✓ min_m f(n,m) = n, attained just above lcm(1,…,n) — `SDRWindow`,
    machine-checked. The minimising reading of the problem is trivial.
  ✓ Erdős-Pomerance (1980): (2/√e + o(1))·n√(log n/log log n) < f(n,n)
  ✓ Erdős-Pomerance (1980): f(n,n) < (2 + o(1))·n√(log n)
  ✓ van Doorn (2026, arXiv:2601.16972): max_m f(n,m) − f(n,n) >
    0.36·n log n / log log n for all large n — the 1000-rupee conjecture
  ✓ Hall's Marriage Theorem provides the SDR formulation
  ✗ The order of f(n,n): a factor √(log log n) separates the two bounds
  ✗ Any asymptotic constant — premature while the order is open

**Barrier:** closing the √(log log n) gap in f(n,n) requires controlling
the Dickman function ρ(u) in the critical range u ≈ √(log n / log log n),
which pushes probabilistic number theory beyond current methods. Diffs to kernel:
T(judge→are), Γ(measure→ooze), Ω(ah→zoo).
-/

-- ============================================================
-- §17  ERDŐS-POMERANCE ASYMPTOTIC DIVERGENCE — mOMonadOS q5 Rerun
-- ============================================================

/-!
**The q5 rerun was not wrong, and this section used to say it was.**

  ORIGINAL RUN (Cycle 9):  f ≍ n √(log n / log log n)
  RERUN (Cycle 14):        f ∼ n log n / log log n

This section formerly diagnosed the rerun as a kernel ERROR: it claimed the
rerun had confused the SDR problem with the Jacobsthal function g(n), and gave
n log n / log log n as the Jacobsthal asymptotic, attributed to Iwaniec (1978).
Both halves of that diagnosis are false, and they were checked against the
literature rather than argued with.

**First:** Iwaniec (1978, *On the problem of Jacobsthal*, Demonstratio Math. 11,
225–231) proves g(n) ≪ (log n)², not n log n / log log n. The asymptotic this
file attributed to him is not his and is not Jacobsthal's function.

**Second, and the real point:** n log n / log log n is the right order for a
real quantity in this problem. Van Doorn (2026, arXiv:2601.16972) proves

    max_m f(n,m) − f(n,n) > 0.36 · n log n / log log n   for all large n,

settling the Erdős–Pomerance 1000-rupee conjecture that max_m f(n,m) − f(n,n)
→ ∞. So the worst window exceeds the window at n by exactly the order the
rerun broadcast.

**What actually diverged is the quantifier over m.** The original run answered
about f(n,n); the rerun answered about max_m f(n,m). Two different functions,
two different orders, both defensible — the one-argument "f(n)" in §11 is what
made them look like rival answers to one question. That places this divergence
in the same category as Polynom Q3: structural ambiguity, a kernel fork where
both branches are defensible, NOT a factual error.

**Consequence for the reliability note.** The hub's §18 recorded 3 consistent /
2 divergent reruns, of which one was called a kernel error and one an ambiguity.
Both divergences are ambiguities. The claim that Frobenius closure does not
guarantee external correctness survives on the Polynom Q3 case, but it is no
longer evidenced by a factual error here, because there was none.
-/

/--
Iwaniec's actual bound on the Jacobsthal function, kept because this file
previously misquoted it. g(n) is the largest gap between consecutive integers
coprime to n.
-/
def jacobsthal_asymptotic_note : String :=
  "Iwaniec 1978: g(n) ≪ (log n)². The n log n/log log n attributed to him here was neither his nor Jacobsthal's."

/--
The two asymptotics, with the quantity each is about. They are not rival
answers: they are answers about different functions.
-/
def pomerance_asymptotic_divergence : List (String × String × String) :=
  [("original_cycle9",      "f(n,n)",          "≍ n √(log n / log log n) — but the order is open: EP1980 bracket it between (2/√e)n√(log n/log log n) and 2n√(log n)"),
   ("rerun_cycle14",        "max_m f(n,m)",    "∼ n log n / log log n — the order van Doorn 2026 proves for the excess over f(n,n)"),
   ("erdos_pomerance_1980", "f(n,n)",          "lower bound (2/√e + o(1)) n √(log n / log log n)"),
   ("van_doorn_2026",       "max_m f(n,m)",    "max_m f(n,m) − f(n,n) > 0.36 n log n / log log n for large n")]

/--
What the q5 rerun episode does and does not show. The FSPLIT→FFUSE pair was
internally consistent (Frobenius ratio 1.0) and the fused answer was also
externally correct — for the quantity it was about. The failure was in this
file: a one-argument f(n) for a two-argument function, which made a difference
of quantifier look like a difference of fact.
-/
def pomerance_divergence_kind : String := "structural ambiguity (quantifier over m), not kernel error"

end Millennium.ErdosProblems
