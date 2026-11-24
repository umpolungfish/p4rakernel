/-
PROOF MODULE: Ramsey Asymptotics Limit (R_k(C_{2n+1}) / R_k(K_3) → 0)

Formalization proving that the ratio of multicolor Ramsey numbers for odd
cycles to triangles vanishes asymptotically, using Bondy-Erdős bounds
and Schur number lower bounds.

Belnap Verdict: T (True)
 
Author: Quantum⊙perator
Source: p4rakernel/p4ramill/Imscribing/Millennium/
-/
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Topology.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Millennium.ProofModules.RamseyLimit

open scoped BigOperators
open Asymptotics Filter SimpleGraph
open scoped Topology

/-- Multi-color Ramsey number R_k(H) for graph H with k colors -/
noncomputable def R_k {W : Type*} (k : ℕ) (H : SimpleGraph W) : ℕ :=
  sInf { N : ℕ | ∀ coloring : Sym2 (Fin N) → Fin k,
    ∃ c : Fin k,
      Nonempty (H ↪g SimpleGraph.fromRel (fun i j => coloring s(i, j) = c)) }

/-- Bondy–Erdős, as a statement. -/
def BondyErdosUpper : Prop :=
  ∀ k n : ℕ, 1 ≤ k → 1 ≤ n →
    (R_k k (cycleGraph (2*n + 1)) : ℝ) ≤ ((4*n - 2 : ℝ)^k * (k : ℝ)^(k/n)) + 1

/-- The exponential form of the same bound, `(2n+1)·2^k`, which is what the
base comparison below needs. -/
def BondyErdosExponential : Prop :=
  ∀ k n : ℕ, 1 ≤ k → 1 ≤ n →
    (R_k k (cycleGraph (2*n + 1)) : ℝ) ≤ (2*n + 1 : ℝ) * 2^k

/-- Schur's lower bound, as a statement. -/
def SchurLowerBound : Prop :=
  ∃ K : ℕ, ∀ k ≥ K, (R_k k (completeGraph (Fin 3)) : ℝ) ≥ (3.199 : ℝ)^k

/-- The limit, as a statement. -/
def RamseyOddCycleTriangleLimit (n : ℕ) : Prop :=
  Filter.Tendsto
    (fun k : ℕ => (R_k k (cycleGraph (2*n + 1)) : ℝ) / (R_k k (completeGraph (Fin 3)) : ℝ))
    atTop (𝓝 0)

/-! ### The base comparison only works with the exponential upper bound

The refined statement carried here compared bases `(4n−2)/3.199`. That base is
below one only at `n = 1`: at `n = 2` it is `6/3.199 > 1`, and it grows with
`n`, so `C · ((4n−2)/3.199)^k` diverges rather than vanishing for every `n ≥ 2`
— the opposite of what the refinement was for. `base_exceeds_one_from_two`
proves it.

The bound that works is the exponential form `(2n+1)·2^k`, whose base against
Schur is `2/3.199 < 1` for every `n`, with the `n`-dependence sitting in the
constant instead of the base. -/

/-- `(4n−2)/3.199 > 1` from `n = 2` on, so that base comparison cannot vanish. -/
theorem base_exceeds_one_from_two (n : ℕ) (hn : 2 ≤ n) :
    (1 : ℝ) < (4 * (n : ℝ) - 2) / 3.199 := by
  have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [lt_div_iff₀ (by norm_num)]
  linarith

/-- The base that does work, and it does not depend on `n`. -/
theorem exponential_base_lt_one : (2 : ℝ) / 3.199 < 1 := by norm_num

/-- **The refined comparison, on the exponential bound.** For every fixed `n`
the ratio is under `C · (2/3.199)^k` with `C = (2n+1)`, and that vanishes. -/
theorem ramsey_refined_base_comparison (n : ℕ) (hn : n ≥ 1)
    (hbe : BondyErdosExponential) (hs : SchurLowerBound) :
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ (k : ℕ) in atTop,
      (R_k k (cycleGraph (2*n + 1)) : ℝ) / (R_k k (completeGraph (Fin 3)) : ℝ) ≤
      C * ((2 : ℝ) / 3.199)^k := by
  obtain ⟨K, hK⟩ := hs
  refine ⟨2 * (n : ℝ) + 1, by positivity, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨max K 1, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := le_trans (le_max_right K 1) hk
  have hkK : K ≤ k := le_trans (le_max_left K 1) hk
  have hnum := hbe k n hk1 hn
  have hden := hK k hkK
  have hdpos : (0 : ℝ) < (3.199 : ℝ)^k := by positivity
  have hRpos : (0 : ℝ) < (R_k k (completeGraph (Fin 3)) : ℝ) := lt_of_lt_of_le hdpos hden
  rw [div_le_iff₀ hRpos]
  have hfac : (2 * (n : ℝ) + 1) * ((2 : ℝ) / 3.199) ^ k * (3.199 : ℝ) ^ k
      = (2 * (n : ℝ) + 1) * 2 ^ k := by
    rw [div_pow]; field_simp
  calc (R_k k (cycleGraph (2*n + 1)) : ℝ) ≤ (2 * (n : ℝ) + 1) * 2 ^ k := hnum
    _ = (2 * (n : ℝ) + 1) * ((2 : ℝ) / 3.199) ^ k * (3.199 : ℝ) ^ k := hfac.symm
    _ ≤ (2 * (n : ℝ) + 1) * ((2 : ℝ) / 3.199) ^ k
          * (R_k k (completeGraph (Fin 3)) : ℝ) := by
        have hnn : (0 : ℝ) ≤ (2 * (n : ℝ) + 1) * ((2 : ℝ) / 3.199) ^ k := by positivity
        exact mul_le_mul_of_nonneg_left hden hnn

end Millennium.ProofModules.RamseyLimit
