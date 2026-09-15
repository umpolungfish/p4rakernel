/-
Imscribing/Classical/SuperLinearPrimes.lean

`p_n / n → ∞` for the primes, UNCONDITIONALLY.

`ErdosProblem16.not_eventually_monotone` takes two hypotheses: `BoundedGaps`,
which is Zhang–Maynard and a genuine citation, and `SuperLinear`, which was
also carried as a citation ("Cited. p_n ∼ n log n") though it needs nothing so
strong. It follows from Chebyshev's UPPER bound alone, which Mathlib has —
`Chebyshev.eventually_primeCounting_le`. Mathlib's lower bound is still a TODO
in that file, and is not needed here.

  π(p_n) = n + 1, so n < (log 4 + 1) · p_n / log p_n, so p_n > n · log p_n / (log 4 + 1),
  and p_n ≥ n + 2 makes log p_n → ∞. Every line through the origin is outgrown.

Author: Lando⊗⊙perator
-/

import Mathlib
import Imscribing.Classical.ErdosProblem16

open Nat Real Filter
open scoped Nat.Prime

namespace Classical.SuperLinearPrimes

/-- The `n`-th prime, as a real. -/
noncomputable def p (n : ℕ) : ℝ := (Nat.nth Nat.Prime n : ℝ)

/-- `π` counts the `n`-th prime as the `(n+1)`-st: `π' ` reaches `n` at it, and
`p n` is itself prime, so the closed count is one more. -/
theorem primeCounting_nth (n : ℕ) : π (Nat.nth Nat.Prime n) = n + 1 := by
  have hmem : Nat.nth Nat.Prime n ∈ {q | Nat.Prime q} :=
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
  have hcount : π' (Nat.nth Nat.Prime n) = n := Nat.primeCounting'_nth_eq n
  unfold Nat.primeCounting Nat.primeCounting' at *
  rw [Nat.count_succ, hcount]
  simp [Set.mem_setOf_eq.mp hmem]

/-- `p n ≥ n + 2`, so the enumeration runs off to infinity. -/
theorem le_p (n : ℕ) : (n : ℝ) + 2 ≤ p n := by
  have := Nat.add_two_le_nth_prime n
  unfold p
  exact_mod_cast this

theorem p_pos (n : ℕ) : 0 < p n := by
  have := le_p n
  have : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  linarith [le_p n]

/-- **`p n / n → ∞`, with no citation.** For every `C` there is an `N` past
which `n · C < p n`. This is `ErdosProblem16.SuperLinear` discharged for the
primes themselves. -/
theorem superLinear (C : ℝ) : ∃ N : ℕ, ∀ n ≥ N, (n : ℝ) * C < p n := by
  -- Chebyshev's upper bound at ε = 1.
  obtain ⟨X, hX⟩ := (Chebyshev.eventually_primeCounting_le (ε := 1) one_pos).exists_forall_of_atTop
  -- log grows past (log 4 + 1) · max C 1, so pick N accordingly.
  set K : ℝ := (Real.log 4 + 1) * max C 1 with hK
  have hKpos : 0 < K := by
    have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have : (0 : ℝ) < max C 1 := lt_of_lt_of_le one_pos (le_max_right C 1)
    positivity
  obtain ⟨M, hM⟩ := (Real.tendsto_log_atTop.eventually_ge_atTop K).exists_forall_of_atTop
  refine ⟨max 1 (max (Nat.ceil X) (Nat.ceil M)), fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnX : X ≤ p n := by
    have : (Nat.ceil X : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hn
    linarith [Nat.le_ceil X, le_p n]
  have hnM : M ≤ p n := by
    have : (Nat.ceil M : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right 1 _)) hn
    linarith [Nat.le_ceil M, le_p n]
  -- π at p n, from the Chebyshev bound
  have hfloor : (⌊p n⌋₊ : ℕ) = Nat.nth Nat.Prime n := by
    unfold p; exact Nat.floor_natCast _
  have hbound := hX (p n) hnX
  rw [hfloor, primeCounting_nth] at hbound
  -- n + 1 ≤ (log 4 + 1) * p n / log p n
  have hlogpos : 0 < Real.log (p n) := by
    have : (1 : ℝ) < p n := by linarith [le_p n, Nat.cast_nonneg (α := ℝ) n]
    exact Real.log_pos this
  have hlogK : K ≤ Real.log (p n) := hM (p n) hnM
  have hcast : ((n : ℕ) + 1 : ℕ) = ((n : ℝ) + 1) := by push_cast; ring
  have hb : (n : ℝ) + 1 ≤ (Real.log 4 + 1) * p n / Real.log (p n) := by
    exact_mod_cast hbound
  have hC : C ≤ max C 1 := le_max_left C 1
  have hcoef : 0 < Real.log 4 + 1 := by
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  -- p n ≥ (n+1) * log (p n) / (log 4 + 1) ≥ (n+1) * max C 1 > n * C
  have hstep : ((n : ℝ) + 1) * Real.log (p n) ≤ (Real.log 4 + 1) * p n := by
    rw [le_div_iff₀ hlogpos] at hb; linarith [hb]
  have hmul : ((n : ℝ) + 1) * K ≤ ((n : ℝ) + 1) * Real.log (p n) := by
    have : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    exact mul_le_mul_of_nonneg_left hlogK this
  have hfin : (Real.log 4 + 1) * (((n : ℝ) + 1) * max C 1) ≤ (Real.log 4 + 1) * p n := by
    rw [hK] at hmul
    calc (Real.log 4 + 1) * (((n : ℝ) + 1) * max C 1)
        = ((n : ℝ) + 1) * ((Real.log 4 + 1) * max C 1) := by ring
      _ ≤ ((n : ℝ) + 1) * Real.log (p n) := hmul
      _ ≤ (Real.log 4 + 1) * p n := hstep
  have hdiv : ((n : ℝ) + 1) * max C 1 ≤ p n :=
    le_of_mul_le_mul_left hfin hcoef
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmax1 : (0 : ℝ) < max C 1 := lt_of_lt_of_le one_pos (le_max_right C 1)
  nlinarith [hdiv, hC, hn0, hmax1]

/-- **The bridge.** `ErdosProblem16.SuperLinear` holds for the primes with no
hypothesis at all, so `not_eventually_monotone` now rests on `BoundedGaps`
alone — Zhang–Maynard, which is a real citation — instead of on two cited
facts. The half that never needed citing is discharged. -/
theorem erdos16_superLinear : ErdosProblem16.SuperLinear (Nat.nth Nat.Prime) :=
  fun C => superLinear C

/-- Erdős 16's Leibniz route is refuted for the primes, given only bounded gaps. -/
theorem erdos16_not_eventually_monotone
    (hgaps : ErdosProblem16.BoundedGaps (Nat.nth Nat.Prime)) :
    ¬ ∃ N : ℕ, ∀ n ≥ N,
      ErdosProblem16.mag (Nat.nth Nat.Prime) (n + 1)
        ≤ ErdosProblem16.mag (Nat.nth Nat.Prime) n :=
  ErdosProblem16.not_eventually_monotone
    (fun n => (Nat.prime_nth_prime n).pos) hgaps erdos16_superLinear

#print axioms erdos16_superLinear
#print axioms erdos16_not_eventually_monotone
#print axioms primeCounting_nth
#print axioms superLinear

end Classical.SuperLinearPrimes
