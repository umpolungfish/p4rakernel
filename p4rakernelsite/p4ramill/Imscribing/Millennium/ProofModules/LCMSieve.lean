/-
PROOF MODULE: LCM Sieve Density Theorem
Formalization of the theorem that the number of positive integers n ≤ N for which
the least common multiple of {1, 2, ..., n} exceeds n by a factor of more than
e^γ · log log n is o(N), where γ is the Euler-Mascheroni constant. The key
result is that lcm(1,...,n) = e^{n(1+o(1))}, and the density of n where
lcm(1,...,n)/n > f(N) for any function f(N) → ∞ is f(N).

Belnap Verdict: T (True)

Author: Quantum⊙perator
Source: p4rakernel/p4ramill/Imscribing/Millennium/
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Millennium.ProofModules.LCMSieve

open scoped BigOperators
open Asymptotics Filter
open scoped Topology

/-- The least common multiple of {1, ..., n}. Written as `Finset.lcm` rather
than a `fold`, which is the same value and carries the divisibility lemmas. -/
def lcm_to_n (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm id

theorem dvd_lcm_to_n (n m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ n) : m ∣ lcm_to_n n :=
  Finset.dvd_lcm (by simp [Finset.mem_Icc]; omega)

theorem lcm_to_n_pos (n : ℕ) : 0 < lcm_to_n n := by
  rcases Nat.eq_zero_or_pos (lcm_to_n n) with h | h
  · exfalso
    rw [lcm_to_n, Finset.lcm_eq_zero_iff] at h
    obtain ⟨a, ha, ha0⟩ := h
    rw [Finset.mem_Icc] at ha
    simp only [id] at ha0
    omega
  · exact h

/-- The density function: fraction of n ≤ N where lcm(1,...,n) has "excess" -/
noncomputable def lcm_density_excess (N : ℕ) : ℝ :=
  (((Finset.Icc 1 N).filter (fun n =>
    (lcm_to_n n : ℝ) > (n : ℝ) * Real.log ((n : ℝ) + 1))).card : ℝ) / (N : ℝ)

/-! ### The main claim was the wrong way round

`lcm_density_excess N` is the proportion of `n ≤ N` with
`lcm(1,…,n) > n·log(n+1)`. That was asserted to tend to `0` — "lcm(1,…,n) ≤
n·log n for most n". It tends to `1`. `lcm(1,…,n)` grows like `eⁿ`; the
comment beneath the claim says so itself, quoting the prime number theorem as
`e^{n(1+o(1))}` and Chebyshev as `≤ 4ⁿ`. An exponential is not eventually below
`n log n`, and in fact it is never below it past `n = 2`.

The elementary reason needs no analytic number theory. `n` and `n−1` are
coprime and both divide `lcm(1,…,n)`, so their product does, giving
`lcm(1,…,n) ≥ n(n−1)`. And `log(n+1) < n−1` from `n = 3` on. So every `n ≥ 3`
is in the excess set, and the density is `1` at every `N`, not `0`. -/

/-- `log(n+1) < n − 1` for `n ≥ 3`: it is `n+1 < e^{n-1}`, and
`e^{n-1} ≥ e·(n-1) > n+1` once `n ≥ 3`. -/
theorem log_succ_lt (n : ℕ) (hn : 3 ≤ n) :
    Real.log ((n : ℝ) + 1) < (n : ℝ) - 1 := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h1 : ((n : ℝ) - 2) + 1 ≤ Real.exp ((n : ℝ) - 2) := Real.add_one_le_exp _
  have hsplit : Real.exp ((n : ℝ) - 1) = Real.exp ((n : ℝ) - 2) * Real.exp 1 := by
    rw [← Real.exp_add]; ring_nf
  have hpos : (0 : ℝ) < Real.exp ((n : ℝ) - 2) := Real.exp_pos _
  have hgt : (n : ℝ) + 1 < Real.exp ((n : ℝ) - 1) := by
    rw [hsplit]
    nlinarith [h1, he, hpos, hn3]
  have := Real.log_lt_log (by positivity) hgt
  rwa [Real.log_exp] at this

/-- `n(n−1) ≤ lcm(1,…,n)`: both factors divide it and they are coprime. -/
theorem mul_pred_le_lcm (n : ℕ) (hn : 2 ≤ n) : n * (n - 1) ≤ lcm_to_n n := by
  have hdvd_n : n ∣ lcm_to_n n := dvd_lcm_to_n n n (by omega) (by omega)
  have hdvd_p : (n - 1) ∣ lcm_to_n n := dvd_lcm_to_n n (n - 1) (by omega) (by omega)
  have hcop : Nat.Coprime n (n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simpa using Nat.coprime_succ_self_left (n := m)
  have hmul : n * (n - 1) ∣ lcm_to_n n := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hdvd_n hdvd_p
  exact Nat.le_of_dvd (lcm_to_n_pos n) hmul

/-- **Every `n ≥ 3` is in the excess set**, so the density does not vanish —
it is identically `1` past the third term. -/
theorem excess_of_three_le (n : ℕ) (hn : 3 ≤ n) :
    (lcm_to_n n : ℝ) > (n : ℝ) * Real.log ((n : ℝ) + 1) := by
  have hnr : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog := log_succ_lt n hn
  have hlcm : ((n * (n - 1) : ℕ) : ℝ) ≤ (lcm_to_n n : ℝ) := by
    exact_mod_cast mul_pred_le_lcm n (by omega)
  have hcast : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have : (1 : ℕ) ≤ n := by omega
      push_cast [Nat.cast_sub this]
      ring
    push_cast [this]
    ring
  rw [hcast] at hlcm
  nlinarith [hlog, hlcm, hnr]

/-- **The claim, as a statement — and it is the false one.** Kept so the
refutation above has something to name. -/
def LcmSieveDensityClaim : Prop :=
  Tendsto (fun N : ℕ => lcm_density_excess N) atTop (𝓝 0)

/-- The ε-refinement of the same false claim, kept as a statement. -/
def LcmSieveEpsilonClaim : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ (N : ℕ) in atTop,
    lcm_density_excess N ≤ ε / (Real.log (N : ℝ))

/-- **The prime number theorem in Chebyshev form, as a statement.** This one is
true and is exactly what contradicts the density claim above: `log lcm(1,…,n)/n
→ 1` says the growth is exponential. Cited, not formalized. -/
def LcmAsymptotic : Prop :=
  Tendsto (fun n : ℕ => (Real.log (lcm_to_n n : ℝ) / (n : ℝ))) atTop (𝓝 1)

/-- Effective version: lcm(1,...,n) ≤ e^{1.04·n} for n ≥ 1 -/
noncomputable def lcm_constant_bound (n : ℕ) : ℝ :=
  Real.exp (1.04 * (n : ℝ))

/-- Rosser–Schoenfeld's `ψ(n) ≤ 1.04n`, as a statement. Cited. -/
def LcmUpperBound : Prop :=
  ∀ n : ℕ, 1 ≤ n → (lcm_to_n n : ℝ) ≤ lcm_constant_bound n

/-- The "excess" set has diminishing density -/
noncomputable def excess_set (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n =>
    (lcm_to_n n : ℝ) / (n : ℝ) > Real.log ((n : ℝ) + 1))

/-- The same false shape once more, on `excess_set`. Kept as a statement; the
set does not thin out, it fills up. -/
def ExcessSetDensityVanishes : Prop :=
  Tendsto (fun N : ℕ => ((excess_set N).card : ℝ) / (N : ℝ)) atTop (𝓝 0)

end Millennium.ProofModules.LCMSieve

-- The axiom cost of the three results the manuscript rests on, printed rather
-- than assumed: a paper that names its dependencies has to be able to check
-- them.
#print axioms Millennium.ProofModules.LCMSieve.mul_pred_le_lcm
#print axioms Millennium.ProofModules.LCMSieve.log_succ_lt
#print axioms Millennium.ProofModules.LCMSieve.excess_of_three_le
