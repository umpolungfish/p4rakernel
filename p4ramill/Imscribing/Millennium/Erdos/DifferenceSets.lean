-- Imscribing/Millennium/Erdos/DifferenceSets.lean
-- Difference-set syndeticity
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
-- §10  DIFFERENCE SETS SYNDETICITY — when D(A) has bounded gaps
-- ============================================================

/-!
**Erdős Problem / Difference Sets and Syndeticity:**
Let A ⊆ ℤ and define D(A) = {d : |A ∩ (A-d)| = ∞} — the set of
differences occurring infinitely often. Under what conditions on A
does D(A) have bounded gaps (i.e., is syndetic)?

**mOMonadOS Agent FSPLIT Decomposition (Cycle 8):**

  Branch 1 — Density_Conditions (structural): If A has positive
    upper Banach density d*(A) > 0, then D(A) is syndetic. The
    Furstenberg Correspondence Principle lifts A to a measure-
    preserving system where recurrence ensures bounded gaps.

  Branch 2 — Combinatorial_Gaps (statistical): Lacunary sequences
    (e.g., A = {2^n}) have finite D(A) → unbounded gaps. The
    threshold is: D(A) is syndetic iff A is NOT a (Bohr₀)-sparse set.

  Branch 3 — Furstenberg_Correspondence (obstructional): The
    correspondence A ↔ (X,ℬ,μ,T,E) maps difference-recurrence to
    measure-recurrence. The set R = {n : μ(E∩T^{-n}E) > 0} is a
    set of recurrence, which for μ(E) > 0 is always syndetic.
    The obstruction: the converse (syndetic D(A) → d*(A) > 0) is FALSE.
    The witness recorded here was "thick sets have d*(A)=0", and that is
    backwards — a thick set contains arbitrarily long intervals, so a
    window of every length is completely full and its upper Banach
    density is 1, not 0 (`thick_not_banach_zero`). A counterexample to
    the converse has to be a set of density zero whose difference set
    still has bounded gaps; thickness supplies the opposite.

**Result:** d*(A) > 0 is SUFFICIENT but NOT NECESSARY. Piecewise
syndetic A also yield syndetic D(A) containing a Bohr set.

**Structural Imscription — difference_sets_syndeticity:**
  D=array (A ⊆ ℤ, infinite subset of integers)
  T=judge (heterogeneous: recurrence is non-uniform across ℤ)
  R=tot (Furstenberg functor: A ↦ (X,T,μ,E) preserves measure and
    recurrence relations)
  P=out (syndetic / not syndetic dichotomy)
  F=peep (ergodic-theoretic precision)
  K=egg (slow: recurrence emerges from density, not speed)
  G=thigh (intermediate: Bohr sets connect local to global recurrence)
  Γ=measure (sequential: n=1→2→… for gap analysis)
  φ̂=roar (complex-axis: Bohr sets are cut from characters → ℂ^×)
  H=sure (persistent chiral: difference set is directed: d vs -d)
  Σ=hung (1:1: one set A → one D(A) recurrence structure)
  Ω=ah (integer winding: gaps in D(A) are ℤ-valued)
-/

/--
The difference sets syndeticity problem as an Imscription.
Tier: O₂dag — roar+ah with judge topology and tot relational.
-/
def difference_sets_syndeticity : Imscription :=
  { dim  := Dimensionality.array
    top  := Topology.judge
    rel  := Relational.tot
    pol  := Polarity.out
    fid  := Fidelity.peep
    kin  := KineticChar.egg
    gran := Granularity.thigh
    gram := Grammar.measure
    crit := Criticality.roar
    chir := Chirality.sure
    stoi := Stoichiometry.hung
    prot := Protection.ah }

theorem difference_sets_syndeticity_tier : imscriptionTier difference_sets_syndeticity = .O₂dag := by
  unfold difference_sets_syndeticity; native_decide


-- ============================================================
-- §10.1  SYNDETIC, THICK, AND THE DENSITY OF A THICK SET
-- ============================================================

/-!
Bounded gaps and long blocks are the two halves of one dichotomy, and
the file's stated counterexample gets the density of a thick set exactly
backwards. Both notions are defined here on ℤ and the density is computed.
-/

/-- Bounded gaps: some window of length `N` around every point meets `S`. -/
def Syndetic (S : ℤ → Bool) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∀ x : ℤ, ∃ i : ℕ, i < N ∧ S (x + i)

/-- Arbitrarily long blocks: `S` contains a run of every finite length. -/
def Thick (S : ℤ → Bool) : Prop :=
  ∀ N : ℕ, ∃ x : ℤ, ∀ i : ℕ, i < N → S (x + i)

/-- How many of the `N` points from `x` lie in `S`. -/
def windowCount (S : ℤ → Bool) (x : ℤ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun i : ℕ => S (x + (i : ℤ)))).card

/-- A thick set fills whole windows: for every length there is a window of
that length entirely inside it. -/
theorem thick_window_full {S : ℤ → Bool} (h : Thick S) (N : ℕ) :
    ∃ x : ℤ, windowCount S x N = N := by
  obtain ⟨x, hx⟩ := h N
  refine ⟨x, ?_⟩
  have hfe : (Finset.range N).filter (fun i : ℕ => S (x + (i : ℤ))) = Finset.range N :=
    Finset.filter_eq_self.2 (fun i hi => hx i (Finset.mem_range.1 hi))
  unfold windowCount
  rw [hfe, Finset.card_range]

/-- Upper Banach density zero: at some scale every window falls below any
prescribed fraction. -/
def UpperBanachZero (S : ℤ → Bool) : Prop :=
  ∀ c : ℚ, 0 < c → ∃ N : ℕ, 0 < N ∧ ∀ x : ℤ, (windowCount S x N : ℚ) < c * N

/-- **A thick set does NOT have upper Banach density zero — it has density
one.** This file recorded the converse's counterexample as "thick sets have
d*(A)=0 but syndetic D(A)". A thick set contains arbitrarily long intervals,
so a window of every length is completely full and the supremum of window
densities is 1. The counterexample as stated does not exist. -/
theorem thick_not_banach_zero {S : ℤ → Bool} (h : Thick S) : ¬ UpperBanachZero S := by
  intro hz
  obtain ⟨N, hN, hall⟩ := hz 1 (by norm_num)
  obtain ⟨x, hx⟩ := thick_window_full h N
  have hlt := hall x
  rw [hx] at hlt
  norm_num at hlt

/-- A syndetic set meets EVERY window of its gap length, so its lower
density is already positive — strictly more than the thick set was being
asked to supply. -/
theorem syndetic_window_nonempty {S : ℤ → Bool} (h : Syndetic S) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : ℤ, 1 ≤ windowCount S x N := by
  obtain ⟨N, hN, hx⟩ := h
  refine ⟨N, hN, fun x => ?_⟩
  obtain ⟨i, hiN, hi⟩ := hx x
  unfold windowCount
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hiN, hi⟩⟩

/-- The duality the whole dichotomy rests on: a set is thick exactly when
its complement fails to be syndetic. -/
theorem thick_iff_compl_not_syndetic {S : ℤ → Bool} :
    Thick S ↔ ¬ Syndetic (fun z => !S z) := by
  constructor
  · rintro ht ⟨N, hN, hs⟩
    obtain ⟨x, hx⟩ := ht N
    obtain ⟨i, hiN, hi⟩ := hs x
    simp [hx i hiN] at hi
  · intro h N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact ⟨0, fun i hi => absurd hi (by omega)⟩
    · by_contra hc
      push_neg at hc
      refine h ⟨N, hN, fun x => ?_⟩
      obtain ⟨i, hiN, hi⟩ := hc x
      exact ⟨i, hiN, by simp [hi]⟩

-- ============================================================
-- §10.2  THE LACUNARY SIDE — POWERS OF TWO HAVE NO RECURRENCE
-- ============================================================

/-!
Branch 2 says lacunary sequences have finite `D(A)`. For `A = {2ⁿ}` the
reason is a bound rather than an asymptotic: a fixed non-zero difference
pins both exponents outright, so only finitely many pairs realise it and
no non-zero difference recurs.
-/

/-- `2^a − 2^b = d` with `d > 0` bounds BOTH exponents: `2^b ≤ d` because
the factor `2^{a−b} − 1` is at least one, and then `2^a = d + 2^b ≤ 2d`.
So each non-zero `d` is realised only finitely often and `D({2ⁿ}) = {0}`. -/
theorem lacunary_diff_bounded {d a b : ℕ} (hd : 0 < d) (hba : b < a)
    (h : 2 ^ a - 2 ^ b = d) : 2 ^ b ≤ d ∧ 2 ^ a ≤ 2 * d := by
  have hsucc : 2 ^ (b + 1) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hba
  have h2 : 2 ^ (b + 1) = 2 * 2 ^ b := by ring
  have hpos : 0 < 2 ^ b := by positivity
  omega

/-- The same bound in the form that kills recurrence: above the threshold
no pair of exponents can realise `d` at all. -/
theorem lacunary_no_recurrence {d a b : ℕ} (hd : 0 < d) (hba : b < a)
    (hbig : d < 2 ^ b) : 2 ^ a - 2 ^ b ≠ d := by
  intro h
  exact absurd (lacunary_diff_bounded hd hba h).1 (by omega)

#print axioms thick_not_banach_zero
#print axioms thick_iff_compl_not_syndetic
#print axioms lacunary_diff_bounded

/-!
**Why judge topology?** The Furstenberg correspondence embeds A into
a heterogeneous measure space (judge): the topology of recurrence
in (X,T) is non-uniform, depending on the spectral properties of the
Koopman operator U_T on L²(X). Bohr sets emerge from the Kronecker
factor of this system.

**Verdict:** T on the sufficient condition — d*(A)>0 ⇒ syndetic D(A) is
established. The rest was overstated. This file called the gap
"CLASSIFIED", giving syndeticity of D(A) as equivalent to A being
piecewise syndetic modulo a null set, while the results list two lines
below marks "full classification of D(A)-syndeticity in terms of A" as
open. Both cannot hold; the classification is the open one.

**Known Results:**
  ✓ Furstenberg (1981): d*(A)>0 ⇒ D(A) syndetic (via Correspondence)
  ✓ Bohr set characterization: D(A) contains Bohr₀ set
  ✓ Thick and syndetic are dual: thick ⟺ complement not syndetic
    (`thick_iff_compl_not_syndetic`)
  ✓ Lacunary A={2ⁿ}: every non-zero difference bounds both exponents,
    so D(A)={0} (`lacunary_diff_bounded`)
  ✗ Full classification of D(A)-syndeticity in terms of A
  ✗ Spectral characterization of the D(A) gap structure

**Barrier:** The Furstenberg correspondence is functorial only for
positive density; the thin-set case requires non-functorial
extensions. Diffs to kernel: T(judge→are), R(tot→ian), Σ(hung→up).
-/

end Millennium.ErdosProblems
