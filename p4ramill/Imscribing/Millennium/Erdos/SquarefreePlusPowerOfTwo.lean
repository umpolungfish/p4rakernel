/-
# Squarefree plus a power of two: the universal form is false

Erdős asked which integers are the sum of a squarefree number and a power of
two. The statement in the corpus asserted it of EVERY `N ≥ 2`. That is false,
and this file refutes it — not by one witness but by an infinite family, with
the obstruction identified.

The obstruction is a congruence. If `4 ∣ N` then for every `k ≥ 2` the power
`2ᵏ` is divisible by `4`, so `N − 2ᵏ` is too, and a number divisible by `4` is
not squarefree. Only `k = 0` and `k = 1` remain, leaving `N − 1` and `N − 2` as
the only candidates. Force those to be divisible by `9` and `49` and nothing is
left:

  `N ≡ 0 (mod 4)`,  `N ≡ 1 (mod 9)`,  `N ≡ 2 (mod 49)`

which by the Chinese remainder theorem is `N ≡ 100 (mod 1764)`. The least such
`N` is `100` itself, the smallest counterexample: `99 = 9·11`, `98 = 2·7²`, and
`96, 92, 84, 68, 36` are all divisible by `4`.

What survives of the question is the density statement — how many integers fail
— which is a genuine open direction, and it is stated at the end as a `Prop`
rather than asserted.
-/

import Mathlib
import Imscribing.Millennium.ErdosFormalize

namespace Erdos.SquarefreePow2

/-- The counterexample family: `N ≡ 100 (mod 1764)`. -/
def bad (t : ℕ) : ℕ := 1764 * t + 100

/-- A number divisible by the square of a prime is not squarefree. -/
theorem not_squarefree_of_sq_dvd {p s : ℕ} (hp : 1 < p) (h : p * p ∣ s) : ¬ Squarefree s := by
  intro hs
  have := hs p h
  rw [Nat.isUnit_iff] at this
  omega

/-- **The refutation.** No member of the family is a squarefree number plus a
power of two.

The three cases are the three ways a power of two can meet a multiple of four:
`k = 0` leaves `N − 1`, which is a multiple of nine; `k = 1` leaves `N − 2`,
a multiple of forty-nine; and every larger `k` leaves a multiple of four. -/
theorem bad_not_representable (t : ℕ) :
    ¬ ∃ s k : ℕ, Squarefree s ∧ bad t = s + 2 ^ k := by
  rintro ⟨s, k, hs, heq⟩
  unfold bad at heq
  match k with
  | 0 =>
    -- `s = 1764t + 99`, and `9 ∣ 1764` and `9 ∣ 99`.
    refine not_squarefree_of_sq_dvd (p := 3) (by norm_num) ?_ hs
    have : s = 1764 * t + 99 := by simpa using heq.symm
    omega
  | 1 =>
    -- `s = 1764t + 98`, and `49 ∣ 1764` and `49 ∣ 98`.
    refine not_squarefree_of_sq_dvd (p := 7) (by norm_num) ?_ hs
    have : s = 1764 * t + 98 := by
      have h2 : (2 : ℕ) ^ 1 = 2 := by norm_num
      omega
    omega
  | (m + 2) =>
    -- `2^(m+2) = 4·2^m`, and `4 ∣ 1764t + 100`.
    refine not_squarefree_of_sq_dvd (p := 2) (by norm_num) ?_ hs
    have hpow : (2 : ℕ) ^ (m + 2) = 4 * 2 ^ m := by ring
    rw [hpow] at heq
    omega

/-- `100` is the least counterexample, and it is in the family at `t = 0`. -/
theorem hundred_not_representable : ¬ ∃ s k : ℕ, Squarefree s ∧ 100 = s + 2 ^ k := by
  simpa [bad] using bad_not_representable 0

/-- **The universal statement is false.** -/
theorem not_forall_squarefree_plus_pow_two :
    ¬ ∀ N : ℕ, 2 ≤ N → ∃ s k : ℕ, Squarefree s ∧ N = s + 2 ^ k := by
  intro h
  exact hundred_not_representable (h 100 (by norm_num))

/-- **Infinitely many counterexamples**, since the family is unbounded: past any
`M` there is an `N` that is not a squarefree number plus a power of two. -/
theorem infinitely_many_counterexamples (M : ℕ) :
    ∃ N : ℕ, M < N ∧ ¬ ∃ s k : ℕ, Squarefree s ∧ N = s + 2 ^ k := by
  refine ⟨bad M, ?_, bad_not_representable M⟩
  unfold bad
  omega

/-- Not a sum of a squarefree number and a power of two. -/
def NotRepresentable (N : ℕ) : Prop := ¬ ∃ s k : ℕ, Squarefree s ∧ N = s + 2 ^ k

/-- What remains of the question, stated rather than asserted: the counting
direction. The family above already puts at least `x/1764` counterexamples below
`x`; whether that is the true order — Erdős asked for the density — is not
settled here, so it is a `Prop` and not a claim. -/
def CounterexampleDensity : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x : ℕ, 1764 ≤ x →
    c * (x : ℝ) ≤ Nat.card {N : ℕ // N < x ∧ NotRepresentable N}

/-- The family is injective, so it is infinite, so the counterexamples are. This
is the lower bound any density claim has to beat. -/
theorem family_injective : Function.Injective bad := by
  intro t₁ t₂ h
  unfold bad at h
  omega

/-- Every member of the family is a counterexample, in the named form. -/
theorem bad_notRepresentable (t : ℕ) : NotRepresentable (bad t) :=
  bad_not_representable t

/-- **The corpus statement, refuted.** `ErdosFormalize.SquarefreePlusPowerOfTwo`
asserted the representation for every `N ≥ 2`. It is false, and `100` is why. -/
theorem not_squarefreePlusPowerOfTwo : ¬ ErdosFormalize.SquarefreePlusPowerOfTwo :=
  not_forall_squarefree_plus_pow_two

#print axioms Erdos.SquarefreePow2.not_squarefreePlusPowerOfTwo
#print axioms Erdos.SquarefreePow2.bad_not_representable
#print axioms Erdos.SquarefreePow2.not_forall_squarefree_plus_pow_two
#print axioms Erdos.SquarefreePow2.infinitely_many_counterexamples
#print axioms Erdos.SquarefreePow2.family_injective

end Erdos.SquarefreePow2
