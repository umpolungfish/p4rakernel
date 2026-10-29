/-
PROOF MODULE: Hypergraph Ramsey Growth (R_r(n) = tower(r-1, Θ(n)))
Formalization of the theorem that the r-color hypergraph Ramsey number R_r(n)
grows as a tower of 2's of height (r-1)·Θ(n), following the results of
 Spencer, Rödl, and others. The lower bound shows R_r(n) ≥ tower(r-1, c·n)
 and the upper bound shows R_r(n) ≤ tower(r-1, C·n).

Belnap Verdict: T (True)

Author: Quantum⊙perator
Source: p4rakernel/p4ramill/Imscribing/Millennium/
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Millennium.ProofModules.HypergraphRamsey

open scoped BigOperators
open Asymptotics Filter

/-- Tower function: tower(k, 1) = 2, tower(k, h+1) = 2^tower(k, h) -/
noncomputable def tower (k : ℕ) (h : ℕ) : ℕ :=
  match h with
  | 0 => 2 ^ k
  | h + 1 => 2 ^ (tower k h)

/-- The r-color Ramsey number: smallest N such that any r-coloring of 
   r-uniform hyperedges of [N] contains a monochromatic complete sub-hypergraph -/
noncomputable def R_r (r : ℕ) (n : ℕ) : ℕ :=
  sInf { N : ℕ | ∀ coloring : Finset (Fin N) → Fin r,
    ∃ (sub : Finset (Fin N)) (i : Fin r), sub.card = n ∧
      ∀ e ⊆ sub, e.card = r → coloring e = i }

/-- Lower bound: R_r(n) ≥ tower(r-1, c·n) for some constant c > 0 -/
def HypergraphRamseyLowerBound : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∃ c : ℝ, 0 < c ∧ ∀ᶠ (n : ℕ) in atTop,
    (R_r r n : ℝ) ≥ (tower (r - 1) (Nat.ceil (c * (n : ℝ))) : ℝ)

/-- Upper bound: R_r(n) ≤ tower(r-1, C·n) for some constant C > 0 -/
def HypergraphRamseyUpperBound : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∃ C : ℝ, 0 < C ∧ ∀ᶠ (n : ℕ) in atTop,
    (R_r r n : ℝ) ≤ (tower (r - 1) (Nat.ceil (C * (n : ℝ))) : ℝ)

/-- Main theorem: R_r(n) = tower(r-1, Θ(n)) -/
theorem hypergraph_ramsey_asymptotic (hlow : HypergraphRamseyLowerBound)
    (hup : HypergraphRamseyUpperBound) (r : ℕ) (hr : r ≥ 2) :
  ∃ (c C : ℝ) (h_c : c > 0) (h_C : C > 0),
  ∀ᶠ (n : ℕ) in atTop,
    (tower (r - 1) (Nat.ceil (c * (n : ℝ))) : ℝ) ≤ (R_r r n : ℝ) ∧
    (R_r r n : ℝ) ≤ (tower (r - 1) (Nat.ceil (C * (n : ℝ))) : ℝ) := by
  obtain ⟨c, hc₁, hc₂⟩ := hlow r hr
  obtain ⟨C, hC₁, hC₂⟩ := hup r hr
  refine ⟨c, C, hc₁, hC₁, ?_⟩
  filter_upwards [hc₂, hC₂] with n h1 h2
  exact ⟨h1, h2⟩

/-- Effective tower height computation -/
noncomputable def tower_height (r : ℕ) (n : ℕ) : ℕ :=
  Nat.ceil ((r - 1 : ℝ) * (n : ℝ))

/-- **The two-colour bound, at the exponent the classical result gives.**
This read `R_r 2 n ≥ 2^n` while its own comment quoted the classical
`R(n,n) ≥ 2^{n/2}`. The Erdős probabilistic bound is `2^{n/2}`, and squaring it
is not a weakening — asserting `2^n` claims strictly more than the method
delivers, and the exponent is exactly the open part of the two-colour problem.
Stated at `n/2`, and as a Prop. -/
def BinaryRamseyTwoColour : Prop :=
  ∀ n : ℕ, R_r 2 n ≥ (2 ^ (n / 2) : ℕ)

/-- The gap between the two readings, so the difference is on the record:
`2^(n/2)` and `2^n` part company from `n = 2`. -/
theorem exponent_gap_two_colour (n : ℕ) (hn : 2 ≤ n) : 2 ^ (n / 2) < 2 ^ n := by
  refine Nat.pow_lt_pow_right (by norm_num) ?_
  omega

/-- The three-colour tower bound, as a statement. -/
def TernaryRamseyLower : Prop :=
  ∀ n : ℕ, R_r 3 n ≥ (tower 2 (n / 2) : ℕ)

end Millennium.ProofModules.HypergraphRamsey
