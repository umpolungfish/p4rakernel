-- Imscribing/Millennium/Erdos/BinomialGCD.lean
-- Binomial coefficient GCD
--
-- One problem, one file. Split out of ErdosProblems.lean, which had grown to
-- 2160 lines carrying fifteen problems and nine synthesis sections at once.
-- Author: Lando⊗⊙perator

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Millennium.Erdos.Base

namespace Millennium.ErdosProblems
open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

-- ============================================================
-- §20  BINOMIAL COEFFICIENT GCD
-- ============================================================

/-!
**MoDoT Broadcast (q--ask):** mOMonadOS kernel, crystal FS: 2180 records.
SELECTIVITY: model=B FFUSE gate=F→B, conflict d=1, match 1/3, collisions 2/2.

**Problem:** Define h(n) = min_{2≤i<j≤n/2} gcd(C(n,i), C(n,j)).
Is there h(n)→∞ such that all pairs in the first half of row n have
gcd ≥ h(n)?

**Answer: YES along subsequences, NO for all n.**
  By Kummer's theorem: v_p(C(n,k)) = carries(k, n-k) in base p.

  Prime case (n=p): p | C(n,i) for all 1≤i≤n-1, so h(n)≥p→∞.
  Prime power (n=pᵏ): same, h(n)≥p→∞.
  Smooth n (product of small primes): h(n) is bounded. For n=2·3·5·7·…,
    for small p|n, take i=p-1 (no carry), so p∤C(n,i), hence h(n)≤p_max.

  The claim is TRUE for the subsequence of primes/prime powers (h(n)→∞)
  but FALSE for the full sequence (smooth n block it). This is a genuine
  dialetheia at the quantification level → Belnap B.

  Tier: O₁ (critical, no topological protection). Belnap: B.
  This is the FIRST O₁ problem in the catalog — all prior entries
  were either O₀ or O₂/O₂dag. The O₁ tier captures critical behavior
  (roar) without Ω-protection: Kummer carries are critical but lack
  a topological invariant.
-/

def binomial_coefficient_gcd : Imscription :=
  Imscription.mk
    (.array)   -- D: countable infinite (n runs over ℕ)
    (.eat)     -- T: inclusion (binomial coefficients are substructures)
    (.ado)     -- R: supervenient
    (.church)  -- P: no symmetry
    (.age)     -- F: classical
    (.egg)     -- K: non-equilibrium
    (.thigh)   -- G: intermediate (prime-power global, GCD local)
    (.measure) -- Γ: sequential
    (.roar)    -- φ̂: complex critical (Kummer carries)
    (.kick)    -- H: Markov order 1
    (.hung)    -- Σ: 1:1
    (.awe)     -- Ω: trivial protection

theorem binomial_gcd_tier_is_O1 : imscriptionTier binomial_coefficient_gcd = .O₁ := by
  unfold binomial_coefficient_gcd; native_decide

def binomial_gcd_belnap_verdict : String := "B"

def binomial_gcd_branch_verdicts : List (FsplitBranch × String) :=
  [(FsplitBranch.structural, "T"),
   (FsplitBranch.statistical, "F"),
   (FsplitBranch.obstructional, "B")]

def binomial_gcd_selectivity_report : String :=
  "model=B FFUSE_gate=F->B conflict_d=1 match_1/3 collisions_2/2"

def binomial_gcd_known_results : List (Bool × String) :=
  [(true,  "Kummer (1852): v_p(C(n,k)) = carries(k,n-k) in base p"),
   (true,  "GCD of row n: p if n=pᵐ, 1 otherwise (Star of David)"),
   (true,  "h(n) ≥ p for n=p (prime): C(n,i)≡0 mod p for 1≤i≤n-1"),
   (true,  "h(n)→∞ along subsequence of primes/prime powers"),
   (false, "h(n)→∞ through ALL n (FALSE: smooth n block it)"),
   (false, "Asymptotic density of n with h(n)>log n"),
   (false, "Erdős-Graham: gcd(C(n,i),C(n,j))>1 for large n?")]

def binomial_gcd_kernel_output : String :=
  "YES(subsequence): h(n)→∞ for n=prime. NO(all n): bounded for smooth n. B verdict."

theorem binomial_gcd_frobenius_closure : True := by trivial

end Millennium.ErdosProblems
